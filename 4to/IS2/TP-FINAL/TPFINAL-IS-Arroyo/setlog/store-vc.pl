% Verification conditions for store.pl

% Run check_vcs_store to see if the program verifies all the VCs

:- notype_check.

:- consult('store.pl').

:- prolog_call((
    retractall(all_unsat_vc(_,_,_,_,_,_)),
    retractall(dinvariant(_,_,_)),
    retractall(daxiom(_,_,_)),
    (exists_file('store-all.pl') ->
       open('store-all.pl',read,StreamVC)
    ;
       print_notfile('store-all.pl')
    ),
    style_check(-singleton),
    setlog:consult_vc(StreamVC),
    style_check(+singleton),
    close(StreamVC))).

% Change this number for a different timeout (ms)
def_to(60000).

:- prolog_call(nb_setval(vc_num,0)).
:- prolog_call(nb_setval(vc_ok,0)).
:- prolog_call(nb_setval(vc_err,0)).
:- prolog_call(nb_setval(vc_to,0)).
:- prolog_call(nb_setval(vc_time,0)).

:- prolog_call(dynamic(unsat_sol/5)).
:- prolog_call(dynamic(vc_proved/1)).

storeInit_sat_pfunStockInv :-
  storeInit(Stock,Products,Sells) &
  pfunStockInv(Stock).

storeInit_sat_pfunProductsInv :-
  storeInit(Stock,Products,Sells) &
  pfunProductsInv(Products).

storeInit_sat_pfunSellsInv :-
  storeInit(Stock,Products,Sells) &
  pfunSellsInv(Sells).

storeInit_sat_productsStockInv :-
  storeInit(Stock,Products,Sells) &
  productsStockInv(Products,Stock).

storeInit_sat_stockQuantityInv :-
  storeInit(Stock,Products,Sells) &
  stockQuantityInv(Stock).

storeInit_sat_productsSellsInv :-
  storeInit(Stock,Products,Sells) &
  productsSellsInv(Products,Sells).

addNewProduct_is_sat :-
  addNewProduct(Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) & 
  delay([Stock,Products,Sells] neq [Stock_,Products_,Sells_],false).

addNewProduct_pi_pfunStockInv(Stock,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunStockInv(Stock) &
    addNewProduct(Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) implies
    pfunStockInv(Stock_)
  ).

addNewProduct_pi_pfunProductsInv(Products,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunProductsInv(Products) &
    addNewProduct(Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) implies
    pfunProductsInv(Products_)
  ).

addNewProduct_pi_pfunSellsInv(Sells,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunSellsInv(Sells) &
    addNewProduct(Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) implies
    pfunSellsInv(Sells_)
  ).

addNewProduct_pi_productsStockInv(Products,Stock,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    productsStockInv(Products,Stock) &
    addNewProduct(Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) implies
    productsStockInv(Products_,Stock_)
  ).

addNewProduct_pi_stockQuantityInv(Stock,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    stockQuantityInv(Stock) &
    addNewProduct(Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) implies
    stockQuantityInv(Stock_)
  ).

addNewProduct_pi_productsSellsInv(Products,Sells,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    productsSellsInv(Products,Sells) &
    addNewProduct(Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_) implies
    productsSellsInv(Products_,Sells_)
  ).

addStock_is_sat :-
  addStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) & 
  delay([Stock,Products,Sells] neq [Stock_,Products_,Sells_],false).

addStock_pi_pfunStockInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunStockInv(Stock) &
    addStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    pfunStockInv(Stock_)
  ).

addStock_pi_pfunProductsInv(Products,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunProductsInv(Products) &
    addStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    pfunProductsInv(Products_)
  ).

addStock_pi_pfunSellsInv(Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunSellsInv(Sells) &
    addStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    pfunSellsInv(Sells_)
  ).

addStock_pi_productsStockInv(Products,Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    productsStockInv(Products,Stock) &
    addStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    productsStockInv(Products_,Stock_)
  ).

addStock_pi_stockQuantityInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    stockQuantityInv(Stock) &
    addStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    stockQuantityInv(Stock_)
  ).

addStock_pi_productsSellsInv(Products,Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    productsSellsInv(Products,Sells) &
    addStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    productsSellsInv(Products_,Sells_)
  ).

removeStock_is_sat :-
  removeStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) & 
  delay([Stock,Products,Sells] neq [Stock_,Products_,Sells_],false).

removeStock_pi_pfunStockInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunStockInv(Stock) &
    removeStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    pfunStockInv(Stock_)
  ).

removeStock_pi_pfunProductsInv(Products,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunProductsInv(Products) &
    removeStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    pfunProductsInv(Products_)
  ).

removeStock_pi_pfunSellsInv(Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunSellsInv(Sells) &
    removeStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    pfunSellsInv(Sells_)
  ).

removeStock_pi_productsStockInv(Products,Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    productsStockInv(Products,Stock) &
    removeStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    productsStockInv(Products_,Stock_)
  ).

removeStock_pi_stockQuantityInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    stockQuantityInv(Stock) &
    removeStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    stockQuantityInv(Stock_)
  ).

removeStock_pi_productsSellsInv(Products,Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    productsSellsInv(Products,Sells) &
    removeStock(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    productsSellsInv(Products_,Sells_)
  ).

newSell_is_sat :-
  newSell(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) & 
  delay([Stock,Products,Sells] neq [Stock_,Products_,Sells_],false).

newSell_pi_pfunStockInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunStockInv(Stock) &
    newSell(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    pfunStockInv(Stock_)
  ).

newSell_pi_pfunProductsInv(Products,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunProductsInv(Products) &
    newSell(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    pfunProductsInv(Products_)
  ).

newSell_pi_pfunSellsInv(Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    pfunSellsInv(Sells) &
    newSell(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    pfunSellsInv(Sells_)
  ).

newSell_pi_productsStockInv(Products,Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    productsStockInv(Products,Stock) &
    newSell(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    productsStockInv(Products_,Stock_)
  ).

newSell_pi_stockQuantityInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    stockQuantityInv(Stock) &
    newSell(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    stockQuantityInv(Stock_)
  ).

newSell_pi_productsSellsInv(Products,Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) :-
  % here conjoin other ax/inv as hypothesis if necessary
  neg(
    productsSellsInv(Products,Sells) &
    newSell(Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_) implies
    productsSellsInv(Products_,Sells_)
  ).

update_time(Tf,Ti) :-
  prolog_call(
    (nb_getval(vc_time,VCT),
     VCT_ is VCT + Tf - Ti,
     nb_setval(vc_time,VCT_)
    )
  ).

update_count(C) :-
  prolog_call(
    (nb_getval(C,VCN),
     VCN_ is VCN + 1,
     nb_setval(C,VCN_)
    )
  ).

check_sat_vc(VCID) :-
  prolog_call((setlog:vc_proved(VCID) -> R = proved ; R = unproved)) &
  (R == unproved &
   write('\nChecking ') & write(VCID) & write(' ... ') &
   update_count(vc_num) &
   ((prolog_call(setlog(VCID)) &
    update_count(vc_ok) &
    prolog_call(assertz(vc_proved(VCID))) &
    write_ok)!
    or
    update_count(vc_err) &
    write_err
   )
   or
   R == proved
  ).

check_unsat_vc(VCID) :-
  def_to(TO) &
  prolog_call(
    (VCID =.. [H | _],
     (\+setlog:vc_proved(H) ->
        setlog:all_unsat_vc(H,T,ID,VC,Op,VN),
        write('\nChecking '), write(H), write(' ... '), flush_output,
        setlog(update_count(vc_num)),
        get_time(Ti),
        rsetlog(VC,TO,Cons,Res,[nopfcheck]),
        get_time(Tf)
     ;
        Res = proved
     )
    )
  ) &
  ((Res = failure)! &
    update_count(vc_ok) &
    update_time(Tf,Ti) &
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_)),
                 assertz(vc_proved(H)))) &
    write_ok
  or
   (Res = timeout)! &
    update_count(vc_to) &
    write_to
  or
    (Res = proved)!
  or
    update_count(vc_err) &
    % saves the solution to be used by findh
    prolog_call((retractall(setlog:unsat_sol(_,H,_,_,_)),
                 assertz(unsat_sol(T,H,ID,Cons,VN)))) &
    write_err
  ).

write_ok :-
  prolog_call(ansi_format([bold,fg(green)],'OK',[])).

write_to :-
  prolog_call(ansi_format([bold,fg(255,255,50)],'TIMEOUT',[])).

write_err :-
  prolog_call(ansi_format([bold,fg(red)],'ERROR',[])).

check_vcs_store :- prolog_call(setlog(check_aux!)).

check_aux :-
  prolog_call(
    (retractall(unsat_sol(_,_,_,_,_)),
     nb_setval(vc_num,0),
     nb_setval(vc_time,0),
     nb_setval(vc_ok,0),
     nb_setval(vc_err,0),
     nb_setval(vc_to,0)
    )
  ) &
  check_sat_vc(storeInit_sat_pfunStockInv) &
  check_sat_vc(storeInit_sat_pfunProductsInv) &
  check_sat_vc(storeInit_sat_pfunSellsInv) &
  check_sat_vc(storeInit_sat_productsStockInv) &
  check_sat_vc(storeInit_sat_stockQuantityInv) &
  check_sat_vc(storeInit_sat_productsSellsInv) &
  check_sat_vc(addNewProduct_is_sat) &
  check_sat_vc(addStock_is_sat) &
  check_sat_vc(removeStock_is_sat) &
  check_sat_vc(newSell_is_sat) &
  check_unsat_vc(addNewProduct_pi_pfunStockInv(Stock,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addNewProduct_pi_pfunProductsInv(Products,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addNewProduct_pi_pfunSellsInv(Sells,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addNewProduct_pi_productsStockInv(Products,Stock,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addNewProduct_pi_stockQuantityInv(Stock,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addNewProduct_pi_productsSellsInv(Products,Sells,Stock,Products,Sells,PID,Product,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addStock_pi_pfunStockInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addStock_pi_pfunProductsInv(Products,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addStock_pi_pfunSellsInv(Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addStock_pi_productsStockInv(Products,Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addStock_pi_stockQuantityInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(addStock_pi_productsSellsInv(Products,Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(removeStock_pi_pfunStockInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(removeStock_pi_pfunProductsInv(Products,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(removeStock_pi_pfunSellsInv(Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(removeStock_pi_productsStockInv(Products,Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(removeStock_pi_stockQuantityInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(removeStock_pi_productsSellsInv(Products,Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(newSell_pi_pfunStockInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(newSell_pi_pfunProductsInv(Products,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(newSell_pi_pfunSellsInv(Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(newSell_pi_productsStockInv(Products,Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(newSell_pi_stockQuantityInv(Stock,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  check_unsat_vc(newSell_pi_productsSellsInv(Products,Sells,Stock,Products,Sells,PID,C,Msg,Stock_,Products_,Sells_)) &
  prolog_call(
    (nb_getval(vc_num,VCN),
     nb_getval(vc_time,VCT),
     nb_getval(vc_ok,VCOK),
     nb_getval(vc_err,VCE),
     nb_getval(vc_to,VCTO)
    )
  ) &
  nl & nl &
  write("Total VCs: ") & write(VCN) &
  write(" (discharged: ") & write(VCOK) &
  write(", failed: ") & write(VCE) &
  write(", timeout: ") & write(VCTO) & write(")") & nl &
  write("Execution time (discharged): ") & write(VCT) & write(" s").

:- nl & prolog_call(ansi_format([bold,fg(green)],'Type checking has been deactivated.',[])) & nl & nl.

:- nl & prolog_call(ansi_format([bold,fg(green)],'Call check_vcs_store to run the verification conditions.',[])) & nl & nl.

