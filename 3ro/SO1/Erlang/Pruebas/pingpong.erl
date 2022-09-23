-module(pingpong).
-export([play/0, ping/0, pong/0]).

pong() ->
    receive
        {0, PId} ->
            io:format("Pong! Final! ~n"),
            PId ! fin;
        {N, PId} ->
            io:format("Pong! Recv: ~p ~n", [N]),
            PId ! {(N-1), self()},
            pong()
    end.

ping() ->
    receive
        fin -> fin;
        {N, PId} ->
            io:format("Ping!~n"),
            PId ! {N, self()},
            ping()
    end.

play() ->
    PIdPong = spawn(pingpong, pong, []),
    PIdPing = spawn(pingpong, ping, []),
    PIdPing ! {10, PIdPong}.