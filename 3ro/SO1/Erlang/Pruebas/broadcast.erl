-module(broadcast).
-export([iniciar/0, finalizar/1]).
-export([broadcast/2, registrar/1]).
-export([loopBroad/1]).

iniciar() -> spawn(?MODULE, loopBroad, [[]]).

finalizar(Broadcast) -> Broadcast ! fin.

broadcast(Broadcast, Mensaje) -> Broadcast ! {msg, Mensaje}.

registrar(Broadcast) -> Broadcast ! {registrar, self()}.

loopBroad(Lista) ->
    receive
        fin -> ok;
        {msg, Mensaje} ->
            lists:foreach(fun(Pid) -> Pid ! Mensaje end, Lista),
            loopBroad(Lista);
        {registrar, PId} -> 
            if 
                Lista == [] -> loopBroad([PId]);
                true -> loopBroad([Lista|PId])
            end
    end.