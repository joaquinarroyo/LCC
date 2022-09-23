-module(prueba).
-export([factorial/1, min/1]).

factorial(0) -> 1;
factorial(N) -> N * factorial(N-1).

min([]) -> 'Error, la lista debe ser no vacia';
min([Hd]) -> Hd;
min([Hd|Tl]) ->
    Rest = min(Tl),
    if 
        Hd > Rest -> 
            Rest;
        true -> 
            Hd
    end.

