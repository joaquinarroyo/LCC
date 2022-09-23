%% Send information msg + sender
-record(send, {msg, sender}).

%% Msg info Msg x Sender x Seq Num
-record(msg, {msg, sender, sn}).
