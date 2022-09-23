-module(listas).
-export([min/1, max/1, min_max/1, map/2]).

min([]) -> io:format("Error, la lista debe ser no vacia");
min([Hd]) -> Hd;
min([Hd|Tl]) ->
    Rest = min(Tl),
    if 
        Hd > Rest -> 
            Rest;
        true -> 
            Hd
    end.

max([]) -> io:format("Error, la lista debe ser no vacia");
max([Hd]) -> Hd;
max([Hd|Tl]) ->
    Rest = max(Tl),
    if 
        Hd > Rest -> 
            Hd;
        true -> 
            Rest
    end.

min_max([]) -> io:format("Error, la lista debe ser no vacia");
min_max([Hd]) -> (Hd, Hd);
min_max([Hd|Tl]) -> (min([Hd|Tl], max([Hd|Tl]))).

map(f, []) -> [];
map(f, [Hd]) -> [f(Hd)];
map(f, [Hd|Tl]) ->  [map(f, Hd)|f(Tl)].
