-module(bin).

-record(btree, {dato = -1, izq, der}).

agregar(Num, #btree{dato = Dato, der = Der, izq = Izq} = T) ->
    if 
        Dato == -1 -> T#btree{dato = Num},
        true -> if
                    Num <= Dato -> agregarIzq(Num, Izq),
                    true -> agregarDer(Num, Der).
                end
    end.

play() ->
    agregar(100),
    agregar(150),
    agregar(2),
    agregar(0),
    ok.