%%%%%%%%%%%%%%%%%% Sinonimos de tipos
def_type(stocktype, rel(pid, int)).                 % PID <-> N
def_type(productstype, rel(pid, product)).          % PID <-> PRODUCT
def_type(sellstype, rel(pid, rel(int, int))).       % PID <-> Seq N
def_type(msg, enum([ok, error])).                   % Msg ::= ok | error

%%%%%%%%%%%%%%%%%% Funciones sobre listas tipadas
% Estas funciones fueron tomadas de la librería 'setlogliblist.slog' mencionada en la página 
% oficial de setlog. Se encuentran aquí porque fue necesario tiparlas.
dec_p_type(sadd(rel(int, int), int, rel(int, int))).
sadd(S,E,T) :-
    dec(D, set(int)) & dec(M, int) & dec(N, int) &
    pfun(S) & 
    dom(S,D) &
    size(D,N) &
    subset(D,int(1,N)) &
    M is N + 1 &
    T = {[M,E] / S}.

dec_p_type(slist(rel(int, int))).
slist(S) :-
    dec(D, set(int)) & dec(N, int) &
    pfun(S) & 
    dom(S,D) &
    size(D,N) &
    subset(D,int(1,N)).

%%%%%%%%%%%%%%%%%% Variables de estado
variables([Stock, Products, Sells]).

%%%%%%%%%%%%%%%%%% Invariantes
invariant(pfunStockInv).
dec_p_type(pfunStockInv(stocktype)).
pfunStockInv(Stock) :- 
    pfun(Stock).

dec_p_type(n_pfunStockInv(stocktype)).
n_pfunStockInv(Stock) :- 
    neg(pfun(Stock)).

invariant(pfunProductsInv).
dec_p_type(pfunProductsInv(productstype)).
pfunProductsInv(Products) :- 
    pfun(Products).

dec_p_type(n_pfunProductsInv(productstype)).
n_pfunProductsInv(Products) :- 
    neg(pfun(Products)).

invariant(pfunSellsInv).
dec_p_type(pfunSellsInv(sellstype)).
pfunSellsInv(Sells) :- 
    pfun(Sells).

dec_p_type(n_pfunSellsInv(sellstype)).
n_pfunSellsInv(Sells) :- 
    neg(pfun(Sells)).

invariant(productsStockInv).
dec_p_type(productsStockInv(productstype, stocktype)).
productsStockInv(Products, Stock) :- 
    dec(P, set(pid)) & dec(S, set(pid)) &
    dom(Products, P) &
    dom(Stock, S) & P = S.

dec_p_type(n_productsStockInv(productstype, stocktype)).
n_productsStockInv(Products, Stock) :- 
    dec(P, set(pid)) & dec(S, set(pid)) &
    dom(Products, P) & 
    dom(Stock, S) & P neq S.

invariant(stockQuantityInv).
dec_p_type(stockQuantityInv(stocktype)).
stockQuantityInv(Stock) :- 
    dec(A, set(int)) & dec(X, int) &
    ran(Stock, A) & 
    foreach(X in A, X >= 0).

dec_p_type(n_stockQuantityInv(stocktype)).
n_stockQuantityInv(Stock) :- 
    dec(A, set(int)) & dec(X, int) &
    ran(Stock, A) & 
    X in A & X < 0.

invariant(productsSellsInv).
dec_p_type(productsSellsInv(productstype, sellstype)).
productsSellsInv(Products, Sells) :- 
    dec(P, set(pid)) & dec(S, set(pid)) &
    dom(Products, P) & 
    dom(Sells, S) & P = S.

dec_p_type(n_productsSellsInv(productstype, sellstype)).
n_productsSellsInv(Products, Sells) :- 
    dec(P, set(pid)) & dec(S, set(pid)) &
    dom(Products, P) & 
    dom(Sells, S) & P neq S.

%%%%%%%%%%%%%%%%%% Estado Inicial
initial(storeInit).
dec_p_type(storeInit(stocktype, productstype, sellstype)).
storeInit(Stock, Products, Sells) :-
    Stock = {} &
    Products = {} &
    Sells = {}.

%%%%%%%%%%%%%%%%%% Operaciones

% Operacion parcial: AddNewProductOk
% input: PID, Product
% output: Msg
dec_p_type(addNewProductOk(stocktype, productstype, sellstype, pid, product, msg, stocktype, productstype, sellstype)).
addNewProductOk(Stock, Products, Sells, PID, Product, Msg, Stock_, Products_, Sells_) :-
    dec(Pids, set(pid)) &
    dom(Products, Pids) &
    PID nin Pids &
    un(Products, {[PID, Product]}, Products_) &
    un(Stock, {[PID, 0]}, Stock_) &
    un(Sells, {[PID, {}]}, Sells_) &
    Msg = ok.

% Operacion parcial: ExistingPidError
% input: PID
% output: Msg
dec_p_type(existingPidError(productstype, pid, msg)).
existingPidError(Products, PID, Msg) :-
    dec(Pids, set(pid)) &
    dom(Products, Pids) &
    PID in Pids &
    Msg = error.

% Operacion completa: AddNewProduct
% input: PID, Product
% output: Msg
operation(addNewProduct).
dec_p_type(addNewProduct(stocktype, productstype, sellstype, pid, product, msg, stocktype, productstype, sellstype)).
addNewProduct(Stock, Products, Sells, PID, Product, Msg, Stock_, Products_, Sells_) :-
    addNewProductOk(Stock, Products, Sells, PID, Product, Msg, Stock_, Products_, Sells_)
    or
    existingPidError(Products, PID, Msg) & Stock_ = Stock & Products_ = Products & Sells_ = Sells.

% Operacion parcial: AddStockOk
% input: PID, C
% output: Msg
dec_p_type(addStockOk(stocktype, productstype, pid, int, msg, stocktype)).
addStockOk(Stock, Products, PID, C, Msg, Stock_) :-
    dec(Pids, set(pid)) & dec(OldC, int) & dec(NewC, int) &
    C > 0 &
    dom(Products, Pids) &
    PID in Pids &
    applyTo(Stock, PID, OldC) &             % stock(pid?) = oldC
    NewC is OldC + C &                      % newC = oldC + c
    oplus(Stock, {[PID, NewC]}, Stock_) &   % stock' = stock + {pid? -> newC}
    Msg = ok.

% Operacion parcial: quantityError
% input: C
% output: Msg
dec_p_type(quantityError(int, msg)).
quantityError(C, Msg) :-
    C =< 0 &
    Msg = error.

% Operacion parcial: UnexistingPidError
% input: PID
% output: Msg
dec_p_type(unexistingPidError(productstype, pid, msg)).
unexistingPidError(Products, PID, Msg) :-
    dec(Pids, set(pid)) &
    dom(Products, Pids) &
    PID nin Pids &
    Msg = error.

% Operacion completa: AddStock
% input: PID, C
% output: Msg
operation(addStock).
dec_p_type(addStock(stocktype, productstype, sellstype, pid, int, msg, stocktype, productstype, sellstype)).
addStock(Stock, Products, Sells, PID, C, Msg, Stock_, Products_, Sells_) :-
    addStockOk(Stock, Products, PID, C, Msg, Stock_) & Products_ = Products & Sells_ = Sells
    or
    quantityError(C, Msg) & Stock_ = Stock & Products_ = Products & Sells_ = Sells
    or
    unexistingPidError(Products, PID, Msg) & Stock_ = Stock & Products_ = Products & Sells_ = Sells.

% Operacion parcial: RemoveStockOk
% input: PID, C
% output: Msg
dec_p_type(removeStockOk(stocktype, productstype, pid, int, msg, stocktype)).
removeStockOk(Stock, Products, PID, C, Msg, Stock_) :-
    dec(Pids, set(pid)) & dec(OldC, int) & dec(NewC, int) &
    C > 0 &
    dom(Products, Pids) &
    PID in Pids &
    applyTo(Stock, PID, OldC) &             % stock(pid?) = oldC
    NewC is OldC - C &                      % newC = oldC - c 
    NewC >= 0 &                             % newC >= 0
    oplus(Stock, {[PID, NewC]}, Stock_) &   % stock' = stock + {pid? -> newC}
    Msg = ok.

% Operacion parcial: StockQuantityError
% input: PID, C
% output: Msg
dec_p_type(stockQuantityError(stocktype, productstype, pid, int, msg)).
stockQuantityError(Stock, Products, PID, C, Msg) :-
    dec(Pids, set(pid)) & dec(OldC, int) & dec(NewC, int) &
    C > 0 &
    dom(Products, Pids) &
    PID in Pids &
    applyTo(Stock, PID, OldC) &
    NewC is OldC - C &
    NewC < 0 &
    Msg = error.

% Operacion completa: RemoveStock
% input: PID, C
% output: Msg
operation(removeStock).
dec_p_type(removeStock(stocktype, productstype, sellstype, pid, int, msg, stocktype, productstype, sellstype)).
removeStock(Stock, Products, Sells, PID, C, Msg, Stock_, Products_, Sells_) :-
    removeStockOk(Stock, Products, PID, C, Msg, Stock_) & Products_ = Products & Sells_ = Sells
    or
    quantityError(C, Msg) & Stock_ = Stock & Products_ = Products & Sells_ = Sells
    or
    unexistingPidError(Products, PID, Msg) & Stock_ = Stock & Products_ = Products & Sells_ = Sells
    or
    stockQuantityError(Stock, Products, PID, C, Msg) & Stock_ = Stock & Products_ = Products & Sells_ = Sells. 

% Operacion parcial: NewSellOk
% input: PID, C
% output: Msg
dec_p_type(newSellOk(stocktype, productstype, sellstype, pid, int, msg, stocktype, sellstype)).
newSellOk(Stock, Products, Sells, PID, C, Msg, Stock_, Sells_) :-
    dec(Pids, set(pid)) & dec(OldSells, rel(int, int)) & dec(NewSells, rel(int, int)) & dec(OldC, int) & dec(NewC, int) &
    C > 0 &
    dom(Products, Pids) &
    PID in Pids &
    applyTo(Sells, PID, OldSells) &
    slist(OldSells) & slist(NewSells) &
    sadd(OldSells, C, NewSells) &
    oplus(Sells, {[PID, NewSells]}, Sells_) &
    applyTo(Stock, PID, OldC) &
    NewC is OldC - C &
    NewC >= 0 &
    oplus(Stock, {[PID, NewC]}, Stock_) & 
    Msg = ok.

% Operacion completa: NewSell
% input: PID, C
% output: Msg
operation(newSell).
dec_p_type(newSell(stocktype, productstype, sellstype, pid, int, msg, stocktype, productstype, sellstype)).
newSell(Stock, Products, Sells, PID, C, Msg, Stock_, Products_, Sells_) :-
    newSellOk(Stock, Products, Sells, PID, C, Msg, Stock_, Sells_) & Products_ = Products
    or
    quantityError(C, Msg) & Stock_ = Stock & Products_ = Products & Sells_ = Sells
    or
    unexistingPidError(Products, PID, Msg) & Stock_ = Stock & Products_ = Products & Sells_ = Sells
    or
    stockQuantityError(Stock, Products, PID, C, Msg) & Stock_ = Stock & Products_ = Products & Sells_ = Sells.