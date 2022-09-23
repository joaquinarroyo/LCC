-module(emptymailbox).
-export([emptymailbox/0]).

emptymailbox() ->
    receive
        true -> vaciando,
                emptymailbox().
    after 
        0 -> vacio;
    end.
