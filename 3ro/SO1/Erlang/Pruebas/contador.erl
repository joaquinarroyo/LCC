-module(contador).
-export([iniciar/0,terminar/1,incrementar/1,valor/1,loop/1]).

iniciar() -> spawn(contador, loop, [0]).

terminar(Contador) -> Contador ! fin.

incrementar(Contador) -> Contador ! inc.

valor(Contador) -> 
    Contador ! {val, self()},
    receive
        N -> N
    end.

loop(N) ->
    receive
        fin -> ok;
        inc -> loop(N+1);
        {val, PId} -> PId ! N,
                      loop(N)
    end.