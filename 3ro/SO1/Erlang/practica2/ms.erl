-module(ms).
-export([start/1, to_service/2]).
-export([servicio/1, cliente/0]).

%% funciones auxiliares 
registrar(0) -> 'registracion completa';
registrar(N) -> 
    Cliente = spawn(?MODULE, cliente, []),
    Supervisor = whereis(supervisor),
    Supervisor ! {registrar, Cliente}, 
    registrar(N - 1).

buscar_enviar(_, _, []) -> io:format("No se encontro el cliente ~n");
buscar_enviar(N, Msg, [Hd]) ->
    if
        N == 0 -> Hd ! {mensaje, Msg};
        true -> buscar_enviar(N - 1, Msg, [])
    end;
buscar_enviar(N, Msg, [Hd|Tl]) ->
    if
        N == 0 -> Hd ! {mensaje, Msg};
        true -> buscar_enviar(N - 1, Msg, Tl)
    end.

%% funciones principales
start(N) ->
    Supervisor = spawn(?MODULE, servicio, [[]]),
    register(supervisor, Supervisor),
    registrar(N).

to_service(N, Msg) ->
    Supervisor = whereis(supervisor),
    Supervisor ! {enviar, N, Msg}.

servicio(Lista) ->
    receive
        {enviar, N, Msg} -> 
            buscar_enviar(N, Msg, Lista),
            servicio(Lista);
        {registrar, PId} ->
            if 
                Lista == [] -> servicio([PId]);
                true -> servicio(Lista ++ [PId])
            end
    end.

cliente() ->
    receive
        {mensaje, Msg} ->
            io:format("Recibido: '~s' ~n", [Msg]);
        _ -> 
            io:format("Error")
    end.

