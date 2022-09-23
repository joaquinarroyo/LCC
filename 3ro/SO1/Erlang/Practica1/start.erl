-module(start).
-export([start/2, loopMsj/0]).

start(M, Msj) -> 
    PId1 = spawn(?MODULE, loopMsj, []),
    PId2 = spawn(?MODULE, loopMsj, []),
    PId1 ! {M, Msj, PId2}.

loopMsj() ->
    receive
        fin -> ok;
        {M, Msj, PId} -> 
            if 
                M > 0 ->  
                    io:format("~s ~n", [Msj]),
                    PId ! {M - 1, Msj, self()},
                    loopMsj();
                true -> 
                    self() ! fin
                    PId ! fin
            end
    after
        2 * 1000 -> adios;
    end.

