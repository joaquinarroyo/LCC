-module(client).
-include("struct.hrl"). %% 'send' structure
-export([start/0, quit/0, get/0, append/1, client/2]).

%% We register the client process
start() ->
    register(cliente, spawn(?MODULE, client, [0, 0])),
    ok.

%% We finish the client process
quit() ->
    cliente ! fin,
    ok.

%% Get operation
get() ->
    cliente ! get,
    ok.

%% Append operation
append(X) ->
    cliente ! {append, X},
    ok.

%% Loop client
%% C is the identifier with which we send a message
%% K is the identifier with which we check if we have already received a message
client(C, K) ->
    receive
        %% GET case
        get ->
            %% We send a message to all servers
            M = #send{msg = {requestGet, C}, sender = node()},
            [Hd|_] = nodes(hidden),
            {node, Hd} ! {broadcast, M},

            client(C+1, K);

        %% APPEND case
        {append, X} ->
            %% We send a message to all servers
            M = #send{msg = {requestAppend, {X, C}}, sender = node()},
            [Hd|_] = nodes(hidden),
            {node, Hd} ! {broadcast, M},

            client(C+1, K);

        %% We wait for the response of the requestGet from some node
        {getRes, Seq, C1} ->
            case K == C1 of
                true ->
                    io:format("~p ~n", [Seq]),
                    client(C, K+1);
                false ->
                    client(C, K)
            end;

        %% We wait for the response of the requestAppend from some node
        {appendRes, V, C1} ->
            case K == C1 of
                true ->
                    io:format("~p ~n", [V]),
                    client(C, K+1);
                false ->
                    client(C, K)
            end;
        
        %% Error case
        error ->
            io:format("Error, la cantidad de nodos no es la adecuada ~n"),
            cliente ! fin;
        
        %% End case
        fin ->
            unregister(cliente);

        %% Junk message
        _ ->
            client(C, K)
    end.

