-module(servid).
-compile([debug_info]).

%%%%%%
%% Pequeño ejercicio de clase
%% el servidor aceptara 4 tipos de pedidos:
%% + nuevoId(Nombre, PidResp) -> Se generará un nuevo identificar para `Nombre` y se responderá al cliente.
%% + buscarId(Id, PidResp) -> Se responde a `PidResp` el nombre asociado a `Id`.
%% + verLista(PidResp) -> Se envía a `Pidresp` la lista de pares (Id,Nombre).
%% + finalizar(PidResp) -> Se finaliza el servicio y se responde con un `ok`.

%% Creación y eliminación del servicio
-export([iniciar/0, finalizar/0]).

%% Servidor
-export([serverinit/1]).

%% Librería de Acceso
-export([nuevoNombre/1, quienEs/1, listaDeIds/0]).

% Iniciar crea el proceso servidor, y devuelve el PId.
iniciar() ->
    register(servidorIds, spawn( ?MODULE
         , serverinit
         , [self()])),
    ok.

%%%%%%%%%%%%%% Librería de Acceso
%%
%% Dado un nombre y un servidor le pide que cree un identificador
%% único.
nuevoNombre(Nombre) ->
    servidorIds ! {nuevoId, Nombre, self()},
    receive
        _ -> vacioilegal
    end.

%% Función que recupera el nombre desde un Id
quienEs(Id) ->
    servidorIds ! {buscarId, Id, self()},
    receive
        _ -> vacioilegal
    end.

%% Pedimos la lista completa de nombres e identificadores.
listaDeIds() ->
    servidorIds ! {verLista, self()},
    receive
        _ -> vacioilegal
    end.

% Ya implementada :D!
finalizar() ->
    servidorIds ! {finalizar, self()},

cliente() ->
    receive
        nuevoId -> 
            io:format("Registrado ~n");
        {ok, Nombre} -> 
            io:format("Nombre asociado: ~s ~n", [Nombre]);
        {lista, Clave, Valor} ->
            io:format("{~s, ~s} ~n", [Clave, Valor]);
        error ->
            io:format("Error, no existe un nombre asociado a la clave ~n");
    end.

%%%%%%%%%%% Servidor
%% Función de servidor de nombres.
serverinit(PInit) ->
    PInit ! ok,
    %% Comenzamos con un mapa nuevo, y un contador en 0.
    servnombres(maps:new(), 0).

servnombres(Map, N) ->
    receive
        %% Llega una petición para crear un Id para nombre
        {nuevoId, Nombre, CId} ->
            Map2 = maps:put(N, Nombre, Map),
            CId ! nuevoId,
            servnombres(Map2, N + 1);
        %% Llega una petición para saber el nombre de tal Id
        {buscarId, NId, CId} ->
            CId ! maps:find(NId, Map),
            servnombres(Map, N);
        %% Entrega la lista completa de Ids con Nombres.
        {verLista, CId} ->
            lists:foreach(fun(N) -> CId ! N end, Map),
            servnombres(Map, N);
        %% Cerramos el servidor. Va gratis
        {finalizar, CId} ->
            unregister(servidorIds),
            ok;
    end.
