-module(servidor).
-define(Puerto, 1234).
-export([start/0,resp/2,trabajador/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FUNCIONES AUXILIARES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Bucle que recibe una lista con los nicknames de los clientes y un nickname, 
%% y devuelve 1 si nickname esta en la lista, y 0 en caso contrario
repetido([], _) -> 0;
repetido([Hd], Name) ->
    if
        Hd == Name -> 1;
        true -> 0
    end;
repetido([Hd|Tl], Name) ->
    if
        Hd == Name -> 1;
        true -> repetido(Tl, Name)
    end.

%% Funcion que recibe el comando del cliente, y devuelve un identificador por caso
caso([]) -> error;
caso([Hd]) ->
    case string:str(Hd, "/") of
        1 ->
            if  Hd == "/exit" -> exit;
                true -> error
            end;
        0 -> msgGen
    end;
caso([Hd|_]) ->
    case string:str(Hd, "/") of
        1 ->
            if  Hd == "/msg" -> msgPriv;
                Hd == "/nickname" -> changeName;
                true -> error
            end;
        0 -> msgGen
    end.

%% Envia el mensaje recibido al socket relacionado con la Key recibida
enviar(Key, Map, Msg) ->
    {ok, Socket} = maps:find(Key, Map),
    gen_tcp:send(Socket, string:join([Key, ":", Msg], " ")).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%% FUNCIONES PRINCIPALES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Crear un socket, y se pone a escuchar
start()->
    {ok, Socket} = gen_tcp:listen(?Puerto
                                 , [binary, {active, false}]),
    io:format("Listening in Port ~p ~n", [?Puerto]),

    %% Inicializamos el mapa
    Map = maps:new(),

    %% Registramos el proceso trabajador, el cual va a adminisitrar los mensajes de los clientes
    register(trabajador, spawn(?MODULE, trabajador, [Socket, Map, []])),

    %% Pasamos a recibir a los clientes
    receptor(Socket, 0).

%% Espera a los clientes y crea nuevos actores para atender los pedidos
receptor(Socket, N) ->
    case gen_tcp:accept(Socket) of
        %% Si se acepto a un cliente, se pasa a la funcion resp, el cual recibe sus mensajes
        {ok, CSocket} ->
            User = lists:flatten(io_lib:format("~p", [N])),
            io:format("User[~s] connected ~n", [User]),
            spawn(?MODULE, resp, [CSocket, User]),
            trabajador ! {actualizar, CSocket, User},
            %% Volvemos a esperar a un cliente
            receptor(Socket, N + 1);

        {error, closed} ->
            io:format("Se termino la conexion ~n"),
            exit(normal);

        {error, Reason} ->
            io:format("Falló la espera del client por: ~p ~n",[Reason]),
            exit(normal)
    end.

%% Funcion que se queda a la espera de un mensaje, para luego dependiendo ese mensaje
%% realiza una determinada accion.
trabajador(Socket, Map, KeyList) ->
    receive
        %% Caso actualizar informacion de los clientes
        {actualizar, CSocket, Key} ->
            Map1 = maps:put(Key, CSocket, Map),
            KeyList1 = lists:append(KeyList, [Key]),
            %% Volvemos a esperar un mensaje
            trabajador(Socket, Map1, KeyList1);

        %% Caso mensaje general
        {msgGen, Mensaje, Key} ->
            lists:foreach(fun(KeyRmt) -> enviar(KeyRmt, Map, Mensaje) end, KeyList),
            io:format("User[~s] to ALL -> ~s ~n", [Key, Mensaje]),
            %% Volvemos a esperar un mensaje
            trabajador(Socket, Map, KeyList);

        %% Caso mensaje privado
        {msgPriv, [Recp|Msg], Key} ->
            {ok, RemtSock} = maps:find(Key, Map),
            Msg1 = string:join(Msg, " "),
            case maps:find(Recp, Map) of
                %% Si existe el receptor
                {ok, RecpSock} ->
                    gen_tcp:send(RecpSock, string:join([Key, "to you :", Msg1], " ")),
                    gen_tcp:send(RemtSock, string:join(["You to", Recp, ":", Msg1], " ")),
                    io:format("User[~s] to User[~s] -> ~s ~n", [Key, Recp, Msg1]);
                
                %% Si no existe el receptor
                error ->
                    gen_tcp:send(RemtSock, "Usuario no encontrado"),
                    io:format("User[~s] to User[~s] -> ~s [USER NOT FOUND] ~n", [Key, Recp, Msg1])
            end,
            %% Volvemos a esperar un mensaje
            trabajador(Socket, Map, KeyList);

        %% Caso cambiar nickname
        {changeName, NewName, Key, PId} ->
            {ok, Sock} = maps:find(Key, Map),
            case repetido(KeyList, NewName) of
                %% Si el nickname estaba desocupado
                0 ->
                    gen_tcp:send(Sock, "Usuario cambiado"),
                    Map1 = maps:remove(Key, Map),
                    Map2 = maps:put(NewName, Sock, Map1),
                    KeyList1 = lists:delete(Key, KeyList),
                    KeyList2 = lists:append(KeyList1, [NewName]),
                    io:format("User[~s] -> CHANGE USER TO ~s ~n", [Key, NewName]),
                    PId ! cambiado,
                    %% Volvemos a esperar un mensaje, con el Map y la KeyList actualizados
                    trabajador(Socket, Map2, KeyList2);

                %% Si el nickname estaba ocupado
                1 ->
                    gen_tcp:send(Sock, "Usuario ocupado"),
                    io:format("User[~s] -> TRIED TO CHANGE USER TO ~s [OCUPPIED] ~n", [Key, NewName]),
                    PId !noCambiado,
                    %% Volvemos a esperar un mensaje, sin cambiar el Map y la KeyList
                    trabajador(Socket, Map, KeyList)
            end;

        %% Caso salir
        {exit, Key} ->
            {ok, Sock} = maps:find(Key, Map),
            gen_tcp:send(Sock, "/exit"),
            gen_tcp:close(Sock),
            Map1 = maps:remove(Key, Map),
            KeyList1 = lists:delete(Key, KeyList),
            io:format("User[~s] -> EXIT ~n", [Key]),
            %% Volvemos a esperar un mensaje
            trabajador(Socket, Map1, KeyList1);

        %% Caso comando invalido
        {error, Key} -> 
            {ok, Sock} = maps:find(Key, Map),
            gen_tcp:send(Sock, "Error comando invalido"),
            io:format("User[~s] -> [INVALID] ~n", [Key]),
            %% Volvemos a esperar un mensaje
            trabajador(Socket, Map, KeyList)
    end.

%% Recibe los mensajes del cliente
resp(CSocket, Key) ->
    case gen_tcp:recv(CSocket, 0) of
        {ok, Paquete} ->
            %% Transformamos el paquete a string
            Paquete1 = binary:bin_to_list(Paquete),
            Mensaje = string:lexemes(Paquete1, " "),

            %% Revisamos el caso en el que se debe entrar
            case caso(Mensaje) of
                %% Caso mensaje general
                msgGen -> 
                    Mensaje1 = string:join(Mensaje, " "),
                    trabajador ! {msgGen, Mensaje1, Key},
                    resp(CSocket, Key);

                %% Caso mensaje privado
                msgPriv ->
                    [_|Tl] = Mensaje,
                    trabajador ! {msgPriv, Tl, Key},
                    resp(CSocket, Key);

                %% Caso cambiar nickname
                changeName ->
                    [_|Tl] = Mensaje,
                    [User] = Tl,
                    trabajador ! {changeName, User, Key, self()},
                    receive
                        cambiado -> resp(CSocket, User);
                        noCambiado -> resp(CSocket, Key)
                    end;

                %% Caso salir
                exit -> 
                    trabajador ! {exit, Key};

                %% Caso comando invalido
                error ->
                    trabajador ! {error, Key},
                    resp(CSocket, Key)
            end;
        {error, closed} ->
            %% En caso de que el cliente se desconecte, el servidor
            %% mostrara este mensaje
            io:format("User[~s] -> EXIT ~n", [Key])
   end.