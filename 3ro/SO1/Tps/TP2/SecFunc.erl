-module(SecFunc).
-compile([export_all]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Secondary functions %%%

%% We return the biggest proposal from the list of proposals
maxProp([Hd]) -> Hd;
maxProp([Hd|Tl]) ->
    {P1, Node1} = maxProp(Tl),
    {P, Node} = Hd,
    if
        P > P1 -> {P, Node};
        true -> {P1, Node1}
    end.

%% Add the data to the queue in order, according to its S,
%% and in some cases also according to its label 'deriverable' or 'underiverable'
encolar(Dato, []) -> [Dato];
encolar(Dato, [Hd]) ->
    {_, _, _, S1, _, Tipo1} = Hd,
    {_, _, _, S2, _, Tipo2} = Dato,
    case S1 > S2 of
        true ->
            [Dato, Hd];
        false ->
            case S1 == S2 of
                true ->
                    if
                        (Tipo1 == deriverable) and (Tipo2 == underiverable) ->
                            [Dato, Hd];
                        (Tipo1 == undderiverable) and (Tipo2 == deriverable) ->
                            [Hd, Dato];
                        true ->
                            [Hd, Dato]
                    end;
                false ->
                    [Hd, Dato]
            end
    end;
encolar(Dato, [Hd|Tl]) ->
    {_, _, _, S1, _, Tipo1} = Hd,
    {_, _, _, S2, _, Tipo2} = Dato,
    case S1 > S2 of
        true ->
            [Dato, Hd] ++ Tl;
        false ->
            case S1 == S2 of
                true ->
                    if
                        (Tipo1 == deriverable) and (Tipo2 == underiverable) ->
                            [Dato, Hd] ++ Tl;
                        (Tipo1 == underiverable) and (Tipo2 == deriverable) ->
                            [Hd, Dato] ++ Tl;
                        true ->
                            [Hd, Dato] ++ Tl
                    end;
                false ->
                    [Hd] ++ encolar(Dato, Tl)
            end
    end.

%% Modify the items in the queue that have
%% Id1 equal to received (Id) and Node1 equal to received (I)
modificar(_, _, _, _, []) -> [];
modificar(Id, I, Sk, K, [Hd]) ->
    {Msg, Id1, Node1, _, _, _} = Hd,
    case (Id == Id1) and (I == Node1) of
        true ->
            [{Msg, Id1, Node1, Sk, K, deriverable}];
        false ->
            [Hd]
    end;
modificar(Id, I, Sk, K, [Hd|Tl]) ->
    {Msg, Id1, Node1, _, _, _} = Hd,
    case (Id == Id1) and (I == Node1) of
        true ->
            [{Msg, Id1, Node1, Sk, K, deriverable}] ++ modificar(Id, I, Sk, K, Tl);
        false ->
            [Hd] ++ modificar(Id, I, Sk, K, Tl)
    end.

%% Sort the queue
ordenar([], _) -> [];
ordenar([Hd], L) ->
    L1 = encolar(Hd, L),
    L1;
ordenar([Hd|Tl], L) ->
    L1 = encolar(Hd, L),
    ordenar(Tl, L1).

%% Search if any list of proposals received all proposals
buscarProp(_, 0) -> -1;
buscarProp(Prop, Cont) ->
    Dato = dict:find(Cont, Prop),
    case Dato == error of
        true ->
            -1;
        false ->
            {ok, [L|_]} = Dato,
            case length(L) >= length(nodes())+1 of
                true ->
                    Cont;
                false ->
                    buscarProp(Prop, Cont-1)
            end
    end.

%% Check if the data received has the label 'derivable'
deriverable(Dato) ->
    {_, _, _, _, _, Tipo} = Dato,
    Tipo == deriverable.

%% Add X to the received sequence, in order.
%% If X belongs to the sequence, it don't add it
agregarSeq(X, []) -> [X];
agregarSeq(X, [Hd]) ->
    case X < Hd of
        true ->
            [X, Hd];
        false ->
            if
                X == Hd -> [Hd];
                true ->
                    [Hd, X]
            end
    end;
agregarSeq(X, [Hd|Tl]) ->
    case X < Hd of
        true ->
            [X, Hd] ++ Tl;
        false ->
            if
                X == Hd -> [Hd] ++ Tl;
                true ->
                    [Hd] ++ agregarSeq(X, Tl)
            end
    end.
