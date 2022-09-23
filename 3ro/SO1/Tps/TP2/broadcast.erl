-module(broadcast).
-include("struct.hrl"). %% 'msg' structure 
%% Import the secondary functions
-import(SecFunc, [maxProp/1, encolar/2, modificar/5, ordenar/2, buscarProp/2, deriverable/1]).
-export([start/0, quit/0, aDeliver/0,aBroadcast/1, loopBr/5]).
-define(NODES, 2). %% number of nodes
-define(F, 0). %% number of nodes than can crash
-define(TO, 200). %% TO value (milliseconds)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Principal functions %%%

%% We register 2 process:
%% 'node' for node boradcast and 'deliver' for the messages 
%% sent by the node
start() ->
    register(node, spawn(?MODULE, loopBr, [0, 0, [], dict:new(), infinity])),
    register(deliver, spawn(?MODULE, aDeliver, [])),
    ok.

%% We end the two process
quit() ->
    node ! fin,
    deliver ! fin,
    ok.

%% Broadcast of Msg
aBroadcast(Msg) ->
    node ! {broadcast, Msg},
    ok.

%% Show the message in screen
aDeliver() ->
    receive
        fin ->
            unregister(deliver);
        M ->
            io:format("~p ~n", [M]),
            aDeliver()
    end.

%% Loop Broadcast
loopBr(S, Cont, Cola, Prop, TO) ->
    receive
        %% We received a broadcast request with the respective message
        {broadcast, Msg} ->
            %% We check if the number of nodes is correct
            Nodes = length(nodes())+1,
            case Nodes >= ?NODES - ?F of
                %% If it is correct, we send the message
                true ->
                    Cont1 = Cont + 1,
                    M = #msg{msg = Msg, sender = node(), sn = Cont1},

                    %% We create the list of proposals for the message with id Cont1
                    Prop1 = dict:append(Cont1, [], Prop),

                    %% we send the message to ourselves, and to all other nodes
                    node ! {recv, M},
                    lists:foreach(fun (X) -> {node, X} ! {recv, M} end, nodes()),
                    case dict:size(Prop) > 0 of
                        true ->
                            loopBr(S, Cont1, Cola, Prop1, ?TO);
                        false ->
                            loopBr(S, Cont1, Cola, Prop1, infinity)
                    end;

                %% If not, we send an error message
                false ->
                    io:format("Error, la cantidad de nodos no es la adecuada ~n")
            end;
        
        %% We receive a message from a node
        {recv, M} ->
            Msg = M#msg.msg,
            Node = M#msg.sender,
            Id = M#msg.sn,
            S1 = S + 1,

            %% We propose a sequence number
            {node, Node} ! {prop, Id, S1, node()},

            %% We add the message to the queue with identifier 'underiverable'
            Cola1 = encolar({Msg, Id, Node, S1, node(), underiverable}, Cola),
            case dict:size(Prop) > 0 of
                true ->
                    loopBr(S1, Cont, Cola1, Prop, ?TO);
                false ->
                    loopBr(S1, Cont, Cola1, Prop, infinity)
            end;
        
        %% We received a proposal from Node
        {prop, Id, S1, Node} ->
            %% We save the proposal with the respective Node
            {ok, [Lista|_]} = dict:find(Id, Prop),
            Lista1 = Lista ++ [{S1, Node}],
            Prop1 = dict:erase(Id, Prop),
            Prop2 = dict:append(Id, Lista1, Prop1),
            loopBr(S, Cont, Cola, Prop2, ?TO);
        
        %% We receive the consensus of a sequence number for a message with ID identifier
        {consenso, Id, Node1, S1, Node2} ->
            S2 = max(S, S1),
            %% We modify the messages within the queue and order it
            Cola1 = modificar(Id, Node1, S1, Node2, Cola),
            Cola2 = ordenar(Cola1, []),
            [Hd|Tl] = Cola2,
            
            case deriverable(Hd) of
                %% If the message at the head of the queue is 'deriverable' we send it
                true ->
                    {Msg, _, _, _, _, deriverable} = Hd,
                    deliver ! Msg,
                    case dict:size(Prop) > 0 of
                        true ->
                            loopBr(S2, Cont, Tl, Prop, ?TO);
                        false ->
                            loopBr(S2, Cont, Tl, Prop, infinity)
                    end;

                %% If we do not keep waiting, at some point we will sort the queue so that 
                %% we have a 'deriverable' message in the head of the queue.
                false ->
                    case dict:size(Prop) > 0 of
                        true ->
                            loopBr(S2, Cont, Cola, Prop, ?TO);
                        false ->
                            loopBr(S2, Cont, Cola, Prop, infinity)
                    end
            end;
        
        %% End case
        fin ->
            unregister(node)

    after
        %% each respective TO we check if any list of proposals received all the proposals.
        TO ->
            %% We look for a complete list of proposals
            K = buscarProp(Prop, Cont),
            case K == -1 of
                %% If there is, we look for it, we look for the maximum proposal, and we send it as consensus
                false ->
                    {ok, [L|_]} = dict:find(K, Prop),
                    {S1, Node} = maxProp(L),
                    {node, node()} ! {consenso, K, node(), S1, Node},
                    lists:foreach(fun (X) -> {node, X} ! {consenso, K, node(), S1, Node} end, nodes()),

                    %% We delete the list from the dictionary
                    Prop1 = dict:erase(K, Prop),
                    case dict:size(Prop) > 0 of
                        true ->
                            loopBr(S, Cont, Cola, Prop1, ?TO);
                        false ->
                            loopBr(S, Cont, Cola, Prop1, infinity)
                    end;

                %% If not, we keep waiting
                true ->
                    case dict:size(Prop) > 0 of
                        true ->
                            loopBr(S, Cont, Cola, Prop, ?TO);
                        false ->
                            loopBr(S, Cont, Cola, Prop, infinity)
                    end
            end
    end.