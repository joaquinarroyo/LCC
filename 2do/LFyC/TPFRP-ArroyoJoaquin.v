
(* Formalización Matemática de las Funciones Recursivas Primitivas en
 * Lenguaje Coq (2021)
 * Docentes: Daniel Severín, Alejandro Hernández
 *
 * ¿Cómo leer este documento? Simplemente instalar Coq de:
 *
 *     https://github.com/coq/coq/releases
 *
 * o, en Ubuntu, directamente con: sudo apt-get install coq
 *
 * Luego abrir este documento con CoqIde y usar las flechitas para procesar el código.
 * Lo que ya esté en verde es lo procesado y verificado.
 *
 * Este documento tiene dos objetivos: uno más operativo en donde se pretende que
 * el lector pueda escribir rápidamente FRPs y evaluarlas, como una "calculadora".
 * El otro objetivo, que es de caracter optativo, es introducir al lector al área de la
 * Formalización de la Matemática. Esta rama (de las Cs. de la Computación) aun no se ha
 * desarrollado lo suficiente como para que los matemáticos la utilicen con frecuencia.
 * Sin embargo, como ha ocurrido con otro tipo de tecnologías, eventualmente se incorporan
 * a la vida diaria, ya sea: procesadores de texto (e.g. LaTeX), lenguajes de cálculo
 * numérico (e.g. Matlab) o simbólico (e.g. Maple). Asimismo, existen factores que permiten
 * predecir que en el futuro se podrían imponer los asistentes de pruebas, como Coq,
 * donde matemáticos y LCCs deberán trabajar "codo a codo". La digitalización del
 * conocimiento matemático es uno de estos factores; para aplicarse luego a herramientas de
 * búsqueda y Data Mining. También hay ejemplos concretos de la necesidad de contar con la
 * formalización de pruebas extensas como la clasificación de grupos finitos simples.
 *
 * Algunos de los caracteres de este documento no se pueden escribir con el teclado, por
 * lo que deberán copiarse de abajo:
 *     λ - abstracción lambda               Φ - composición
 *     ∀ - para todo                        ∃ - existe
 *     ∨ - disjunción                       ∧ - conjunción
 *     → - implicancia                      ¬ - negación
 *     ↔ - si y solo si                     ≠ - no igual
 *     ℕ - conjunto de los naturales        ℝ - conjunto de los reales
 *     ∈ - pertenece a                      ∅ - conjunto vacío
 *     ∪ - unión                            ∩ - intersección
 *     Σ - adición                          Π - producto *)

Require Import Utf8 Reals.

Notation ℕ := nat.
Notation "n .+1" := (S n) (at level 2, left associativity).

Section Funciones_Recursivas_Primitivas.

(* Algunos "tipos" de FRPs *)

Definition FRP0 := ℕ.
Definition FRP1 := ℕ → ℕ.
Definition FRP2 := ℕ → ℕ → ℕ.             (* léase como ℕ^2 → ℕ *)
Definition FRP3 := ℕ → ℕ → ℕ → ℕ.         (* léase como ℕ^3 → ℕ *)
Definition FRP4 := ℕ → ℕ → ℕ → ℕ → ℕ.     (* léase como ℕ^4 → ℕ *)
Definition FRP5 := ℕ → ℕ → ℕ → ℕ → ℕ → ℕ. (* léase como ℕ^5 → ℕ *)



(******************************************************)
(* Definición de Funciones Recursivas Primitivas Base *)
(******************************************************)

(* Cero de distintos argumentos *)

Definition c0 := 0.
Definition c1 := λ _ : ℕ, 0.
Definition c2 := λ _ _ : ℕ, 0.
Definition c3 := λ _ _ _ : ℕ, 0.

(* Para conocer el tipo de una función, podemos usar el comando Check.
 * EJEMPLO: ¿cuál es el tipo de c2? *)

Check c2.

(* Check también permite verificar el tipo de una función u otro objeto.
 * Si el comando falla, no nos va a permitir avanzar. En ese caso, el comando Fail
 * permite "seguir de largo". Este comando también no nos deja avanzar si el que lo
 * produce no falla.
 * EJEMPLO: cero2 es una FRP de 2 argumentos pero no de 3. *)

Check c2 : FRP2.
Fail Check c2 : FRP3.

(* Hay un tipo especial llamado "Prop" que hace referencia a las proposiciones.
 * Es decir, a enunciados matemáticos. Por ejemplo: *)

Check ∀ x y : ℕ, x * (y + 1) = x * y + x.

(* A continuación se define el sucesor, las proyecciones y composición de funciones.
 * ↓ Omita esta parte y vaya directamente a los ejemplos ↓ *) 

(* Sucesor *)

Definition s := λ x : ℕ, x.+1.

(* Proyecciones:
 * pn_k es una FRP de n argumentos que devuelve la componente k-ésima. *)

Definition p1_1 := λ x : ℕ, x.

Definition p2_1 := λ x _ : ℕ, x.
Definition p2_2 := λ _ x : ℕ, x.

Definition p3_1 := λ x _ _ : ℕ, x.
Definition p3_2 := λ _ x _ : ℕ, x.
Definition p3_3 := λ _ _ x : ℕ, x.



(******************************************)
(* Definición de Composición de Funciones *)
(******************************************)
(* Φn_k compone una función de n argumentos con n funciones de k
 *      argumentos, para generar una nueva función de k argumentos. *)

Definition Φ1_0 (f : FRP1) (g1 : FRP0) := f g1.
Definition Φ1_1 (f : FRP1) (g1 : FRP1) := λ x : ℕ, f (g1 x).
Definition Φ1_2 (f : FRP1) (g1 : FRP2) := λ x y : ℕ, f (g1 x y).
Definition Φ1_3 (f : FRP1) (g1 : FRP3) := λ x y z : ℕ, f (g1 x y z).

Definition Φ2_1 (f : FRP2) (g1 : FRP1) (g2 : FRP1) :=
       λ x : ℕ, f (g1 x) (g2 x).
Definition Φ2_2 (f : FRP2) (g1 : FRP2) (g2 : FRP2) :=
       λ x y : ℕ, f (g1 x y) (g2 x y).
Definition Φ2_3 (f : FRP2) (g1 : FRP3) (g2 : FRP3) :=
       λ x y z: ℕ, f (g1 x y z) (g2 x y z).

Definition Φ3_1 (f : FRP3) (g1 : FRP1) (g2 : FRP1) (g3 : FRP1) :=
       λ x : ℕ, f (g1 x) (g2 x) (g3 x).
Definition Φ3_2 (f : FRP3) (g1 : FRP2) (g2 : FRP2) (g3 : FRP2) :=
       λ x y : ℕ, f (g1 x y) (g2 x y) (g3 x y).
Definition Φ3_3 (f : FRP3) (g1 : FRP3) (g2 : FRP3) (g3 : FRP3) :=
       λ x y z : ℕ, f (g1 x y z) (g2 x y z) (g3 x y z).


(* EJEMPLO:
 * Definamos la constante "2" de 3 argumentos: dos3(x,y,z) = 2. Para hacerlo, componemos
 * el sucesor con una función constante "1" de 3 argumentos, quien a su vez es el
 * sucesor del cero de 3 argumentos. Como ejemplo, evaluamos dos3(3,9,4), que justamente
 * es 2. Para ello usamos "Eval compute in" y luego la expresión a evaluar. *)

Example dos3 := Φ1_3 s (Φ1_3 s c3).
Check dos3 : FRP3.
Eval compute in dos3 3 9 4.

(* Ojo! al evaluar, si ponemos más argumentos de los esperados, da error. Sin embargo
 * si ponemos menos, no da error. Pero en vez de obtener un número obtenemos una
 * función que, al aplicársele los argumentos faltantes nos daría el resultado esperado.
 * Ante la duda, usar la cantidad esperada de argumentos. *)

Fail Eval compute in dos3 3 9 4 1.
Eval compute in dos3 3 9.

(* Una definición alternativa de dos3 podría ser haber compuesto una función que
 * consiste de aplicar 2 sucesores, es decir una función que suma 2, con el cero de 3
 * argumentos. *)

Example dos3' := Φ1_3 (Φ1_1 s s) c3.
Eval compute in dos3' 3 9 4.

(* ¿Será que la función dos da realmente 2 en todos los casos? Probémoslo.
 * Al comenzar la prueba observemos la ventana derecha, hay una raya que
 * separa las hipótesis (de momento ninguna) y el enunciado.
 * Al lugar donde van las hipótesis las llamaremos -> CONTEXTO.
 * Al enunciado a probar -> OBJETIVO.
 * Para probar el objetivo se utilizan comando denominados TACTICAS.
 * La táctica "intros" le da nombre a las variables del "∀" y las introduce
 * en el contexto, para poder disponer de ellas luego.
 * La táctica "unfold" reemplaza un objeto por su definición y la aplica
 * (todas las veces que el objeto ocurre en el objetivo).
 * La táctica "reflexivity" prueba una identidad. Esta última además
 * finaliza la prueba (no queda más por probar). *)

Proposition dos3_es_2 : ∀ x y z : ℕ, dos3 x y z = 2.
Proof.
  intros a b c.
  unfold dos3.
  unfold Φ1_3.
  unfold c3.
  unfold s.
  reflexivity.
Qed.

(* TP FRP - ARROYO JOAQUIN *)
(* EJERCICIO 1: Defina una FRP tres(x,y) = 3, chequee que efectivamente tiene tipo FRP3.
 * Compruébela evaluándola en (2,5) y (9,1). *)
Example tres2 := Φ1_2 s (Φ1_2 s (Φ1_2 s c2)). (* Definicion de tres *)
Check tres2 : FRP2.
Eval compute in tres2 2 5.
Eval compute in tres2 9 1.

(* EJERCICIO 2: Usando "Check" enuncie formalmente que tres(x,y) = 3. *)
Check ∀ x y : ℕ, tres2 x y = 3.

(* EJERCICIO 3: Defina una funcion f1(x,y,z) = z + 4, luego evalúela en (5,8,0) y
 * (4,3,7), ¿da el valor correcto? *)
Example f13 := Φ1_3 s (Φ1_3 s (Φ1_3 s (Φ1_3 s p3_3))). (* Definicion de f1 *)
Eval compute in f13 5 8 0.
Eval compute in f13 4 3 7.

(* EJERCICIO 4: ¿Se anima a probar que dos3' también vale siempre 2? *)
(* Para todo x,y,z ∈ ℕ, dos3'(x,y,z) = 2 *)
Proposition dos3'_es_2 : ∀ x y z : ℕ, dos3' x y z = 2.
Proof.
  intros a b c.
  unfold dos3'.
  unfold Φ1_3.
  unfold Φ1_1.
  unfold c3.
  unfold s.
  reflexivity.
Qed.

(* EJERCICIO 5: Demuestre que la función tres definida en el Ejercicio 1
 * es igual a 3. *)
(* Para todo x,y ∈ ℕ, tres(x,y) = 3 *)
Proposition tres2_es_3 : ∀ x y : ℕ, tres2 x y = 3.
Proof.
  intros a b.
  unfold tres2.
  unfold Φ1_2.
  unfold c2.
  unfold s.
  reflexivity.
Qed.

(**************************************************)
(* Definición del Operador de Recursión Primitiva *)
(**************************************************)
(* El operador Ri toma una FRP de i-1 argumento y otra de i+1 argumentos y devuelve una
 * nueva FRP de i argumentos.
 * Esta sección utiliza comandos más avanzados de Coq para definir este operador y
 * contar con herramientas para manipularlo.
 * ↓ Vaya directamente a la sección de EJEMPLOS ↓ *)

Fixpoint R1 (g : FRP0) (h : FRP2) (y : ℕ) :=
   match y with
   | 0    => g
   | S y' => h y' (R1 g h y')
   end.

Fixpoint R2 (g : FRP1) (h : FRP3) (y : ℕ) :=
   λ x1 : ℕ, match y with
             | 0    => g x1
             | S y' => h y' x1 (R2 g h y' x1)
             end.

Fixpoint R3 (g : FRP2) (h : FRP4) (y : ℕ) :=
   λ x1 x2 : ℕ, match y with
                | 0    => g x1 x2
                | S y' => h y' x1 x2 (R3 g h y' x1 x2)
                end.

Fixpoint R4 (g : FRP3) (h : FRP5) (y : ℕ) :=
   λ x1 x2 x3 : ℕ, match y with
                   | 0    => g x1 x2 x3
                   | S y' => h y' x1 x2 x3 (R4 g h y' x1 x2 x3)
                   end.


(* EJEMPLO: Vamos a definir la suma como se vio en clase. Primero necesitaríamos una
 * función de la forma h(x,y,z) = z + 1, no es difícil ver que "h" se puede definir
 * como "Φ1_3 s p3_3". *)

Check Φ1_3 s p3_3 : FRP3.
Eval compute in (Φ1_3 s p3_3) 3 9 27.

(* Luego la suma se define como la función f(x,y) = x + y tal que, cuando y = 0,
 * devolvemos x, es decir una identidad "p1_1", y cuando "y" es un número positivo, es
 * decir un y'+1 para algún y', devolvemos el sucesor de x + y' <-- justamente la
 * función h (pues z = x + y'). *)

Example Σ := R2 p1_1 (Φ1_3 s p3_3).

(* Ahora chequeemos que realmente toma 2 argumentos y hagamos un ejemplo. *)

Check Σ : FRP2.
Eval compute in Σ 5 7.

(* Una suma más complicada: (23 + 19) + (52 + 84). *)

Eval compute in Σ (Σ 23 19) (Σ 52 84).

(* Una más complicada aún: 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10. *)

Eval compute in (R1 c0 Σ) 11.

(* El enunciado sobre la conmutatividad de la suma (solo chequeamos que sea
 * correcto sintácticamente, la demostración en Coq está al final de este documento): *)

Check ∀ x y : ℕ, Σ x y = Σ y x.

(* Otro EJEMPLO, el distintor de cero "D": para definirlo creamos una función f(x,y)
 * que devuelve 1 para x=0 y 0 para x>0, esta función es una rec. primitiva
 * "R2 (Φ1_1 s c1) c3". Luego D(x) = f(x,x). *)

Example D := Φ2_1 (R2 (Φ1_1 s c1) c3) p1_1 p1_1.
Eval compute in D 0.
Eval compute in D 1.
Eval compute in D 37.

(* EJERCICIO 6: escriba el producto Π como FRP y evalue (7*3)+2 *)
Example Π := R2 c1 (Φ2_3 Σ p3_3 p3_2). (* Funcion producto *)
Check Π : FRP2.
Eval compute in Σ (Π 7 3) 2.

(* EJERCICIO 7: definir las FRPs exponencial, factorial y predecesor, y
 * evaluarlas sobre distintas combinaciones de valores para verificar su
 * comportamiento; también el distintor de cero, pero utilizando R1. *)
Example Exp := R2 (Φ1_1 s c1) (Φ2_3 Π p3_3 p3_2). (* Funcion exponencial *)
Check Exp : FRP2.
Eval compute in Exp 3 2.

Example Fact := R1 (Φ1_0 s c0) (Φ2_2 Π p2_2 (Φ1_2 s p2_1)). (* Funcion factorial *)
Check Fact : FRP1.
Eval compute in Fact 4.

Example Pd := R1 c0 p2_1. (* Funcion predecesor *)
Check Pd : FRP1.
Eval compute in Pd 5.

(* EJERCICIO 8: Escriba un enunciado que declare que el distintor de cero
 * devuelve cero para cualquier valor de entrada positivo estricto. *)
Example D0 := R1 (Φ1_0 s c0) c2. (* Funcion distinguidora de cero *)
Check D0 : FRP1.
Eval compute in D0 1.
Eval compute in D0 0.

End Funciones_Recursivas_Primitivas.

(*********************************************************)
(* A PARTIR DE AQUI EL CONTENIDO ES DE CARACTER OPTATIVO *)
(*********************************************************)
(* CONJUNTOS RECURSIVOS PRIMITIVOS: son conjuntos cuya función característica es una
 * FRP (devuelven 0 si el elemento no pertenece y 1 si pertenecen). En lo que sigue
 * solo abordamos el caso en que los conjuntos son subconjuntos de ℕ.
 * ↓ Vaya directamente a los ejemplos ↓ *)

Section Conjuntos_Recursivos_Primitivos.

Local Notation "x ∈ X" := (X x) (at level 60, no associativity).
Definition es_uno n := n = 1.
Coercion es_uno : ℕ >-> Sortclass.

(* EJEMPLOS: el conjunto vacío se representa con función cero. En particular, el 3 no
 * pertenece al vacío. *)

Example conjunto_vacio := c1.
Local Notation "∅" := conjunto_vacio.

Eval compute in 3 ∈ ∅.

(* El conjunto {0}, es decir el que solo contiene el cero se representa con el
 * distintor de cero. Obviamente, el cero pertenece, pero el 3 no. *)
 
Example conjunto_con_cero := D.
Local Notation "{0}" := conjunto_con_cero.

Eval compute in 0 ∈ {0}.
Eval compute in 3 ∈ {0}.

(* Dadas dos funciones f, g que caracterizan conjuntos A y B, se puede caracterizar la
 * union A ∪ B como D(D(f(x) + g(x))): *)

Definition union f g := Φ1_1 D (Φ1_1 D (Φ2_1 Σ f g)).
Local Notation "X ∪ Y" := (union X Y)  (at level 50, left associativity).

Eval compute in 0 ∈ {0} ∪ {0}.
Eval compute in 1 ∈ ∅ ∪ {0}.

(* Ciertamente se puede enunciar (y probar) que lo que acabamos de definir es
 * efectivamente una unión entre conjuntos. *)

Check ∀ A B : FRP1, (∀ x : ℕ, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B).

(* EJERCICIO 9: Escriba la FRP que caracteriza el conjunto {2}. *)

(* EJERCICIO 10: Descomente y complete lo siguiente para caracterizar la intersección.

Definition interseccion f g := ...
Local Notation "X ∩ Y" := (interseccion X Y)  (at level 50, left associativity).

Eval compute in 0 ∈ {0} ∩ {0}.
Eval compute in 0 ∈ ∅ ∩ {0}.

Check ∀ A B : FRP1, (∀ x : ℕ, x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B).

*)

End Conjuntos_Recursivos_Primitivos.



(*************************************************)
(* Prueba de Resultados más avanzados sobre FRPs *)
(*************************************************)

Section Formalizacion_Matematica.
(* Lo que sigue es a modo ilustrativo para ver como con Coq es posible probar propiedades
 * y resultados más avanzados. Un ejemplo es la conmutatividad de la suma y el cero como
 * elemento neutro de la suma. A continuación se dejan algunos resultados que surgen de
 * las definiciones de R2, R3 y R4. *)

Lemma caso_base1 : ∀ (g : FRP1) (h : FRP3) (x1 : ℕ),
                   R2 g h 0 x1 = g x1.
Proof. auto. Qed.

Lemma caso_inductivo1: ∀ (g : FRP1) (h : FRP3) (y' x1 : ℕ),
                       R2 g h (y'.+1) x1 = h y' x1 (R2 g h y' x1).
Proof. auto. Qed.

Lemma caso_base2 : ∀ (g : FRP2) (h : FRP4) (x1 x2 : ℕ),
                   R3 g h 0 x1 x2 = g x1 x2.
Proof. auto. Qed.

Lemma caso_inductivo2: ∀ (g : FRP2) (h : FRP4) (y' x1 x2 : ℕ),
                     R3 g h (y'.+1) x1 x2 = h y' x1 x2 (R3 g h y' x1 x2).
Proof. auto. Qed.

Lemma caso_base3 : ∀ (g : FRP3) (h : FRP5) (x1 x2 x3 : ℕ),
                   R4 g h 0 x1 x2 x3 = g x1 x2 x3.
Proof. auto. Qed.

Lemma caso_inductivo3: ∀ (g : FRP3) (h : FRP5) (y' x1 x2 x3 : ℕ),
            R4 g h (y'.+1) x1 x2 x3 = h y' x1 x2 x3 (R4 g h y' x1 x2 x3).
Proof. auto. Qed.

(* Comencemos por "0 + n = n": luego de reemplazar la suma por su definición obtenemos
 * una igualdad que es el "caso base" de la recursión primitiva. Entonces podemos
 * "aplicar" (táctica apply) el resultado:
 *     caso_base1 : R2 g h 0 x1 = g x1
 * Aplicar un resultado significa intentar asignar expresiones a las variables del
 * resultado (en este caso g, h, x1) con el fin de que coincida con el actual objetivo.
 * En nuestro caso, al alcanzar el objetivo
 *     R2 p1_1 (Φ1_3 s p3_3) 0 n = n
 * la asignación va a ser:
 *     p1_1           -> g
 *     (Φ1_3 s p3_3)  -> h
 *     x1             -> n
 * "apply" es, al igual que "reflexivity", una táctica que demuestra un objetivo. *)

Proposition suma_0_n_da_n : ∀ n : ℕ, Σ 0 n = n.
Proof.
  intros n.
  unfold Σ.
  apply caso_base1.
Qed.

(* En la siguiente demostración usaremos tres tácticas nuevas.
 * 1) "induction" genera los objetivos de manera de hacer una prueba por inducción, a
 * partir de alguna variable. En nuestro caso teníamos el objetivo "Σ n 0 = n", y lo
 * convierte en dos nuevos objetivos:
 *   Σ 0 0 = 0          <- caso base
 *   Σ n.+1 0 = n.+1    <- caso inductivo
 * Además en el caso inductivo se genera una nueva hipótesis, que es justamente la
 * hipótesis inductiva:
 *   IHn : Σ n 0 = n
 * En lo que sigue, habrá que probar cada objetivo por separado, una vez demostrado uno
 * se continúa con el siguiente.
 * 2) "fold" hace lo contrario a "unfold", es decir al encontrar la definición de un
 * objeto, lo reemplaza por el nombre del objeto.
 * 3) "rewrite" es tal vez el comando más importante de Coq, dado un resultado de la
 * forma A = B, permite reemplazar las ocurrencias de A por B en el objetivo. Gran parte
 * del contenido matemático se puede pensar en término de reglas de reescritura.
 * A diferencia de "apply" que trabaja sobre todo el objetivo, "rewrite" solo reemplaza
 * expresiones dentro del mismo y no lo prueba. *)

Proposition suma_n_0_da_n : ∀ n : ℕ, Σ n 0 = n.
Proof.
  intros n.
  induction n.
  (* caso base: n = 0 *)
  apply caso_base1.
  (* caso inductivo, la hipótesis inductiva es IHn : Σ n 0 = n *)
  unfold Σ.
  rewrite caso_inductivo1.
  fold Σ.
  rewrite IHn.
  unfold Φ1_3.
  unfold p3_3.
  unfold s.
  reflexivity.
Qed.

(* En la siguiente demostración nos encontraremos con que, luego de introducir x,y,z en
 * el contexto, queremos reemplazar Σ en la primera ocurrencia pero no la 2da.
 * Para esto se puede usar:
 *   "unfold OBJETO at N" <- reemplaza OBJETO en la ocurrencia N-ésima *)

Proposition suma_suc_x_da_suc_suma : ∀ x y : ℕ, Σ (x.+1) y = (Σ x y).+1.
Proof.
  intros x y.
  unfold Σ at 1.
  rewrite caso_inductivo1.
  fold Σ.
  unfold Φ1_3.
  unfold p3_3.
  unfold s.
  reflexivity.
Qed.

Proposition suma_suc_y_da_suc_suma : ∀ x y : ℕ, Σ x (y.+1) = (Σ x y).+1.
Proof.
  intros x y.
  induction x.
  (* caso base: x = 0 *)
  rewrite suma_0_n_da_n.
  rewrite suma_0_n_da_n.
  reflexivity.
  (* caso inductivo *)
  rewrite suma_suc_x_da_suc_suma.
  rewrite IHx.
  unfold Σ at 2.
  rewrite caso_inductivo1.
  fold Σ.
  unfold Φ1_3.
  unfold p3_3.
  unfold s.
  reflexivity.
Qed.

Proposition suma_conmutativa : ∀ x y : ℕ, Σ x y = Σ y x.
Proof.
  intros x y.
  induction x.
  (* caso base: x = 0 *)
  rewrite suma_n_0_da_n.
  apply suma_0_n_da_n.
  (* caso inductivo *)
  rewrite suma_suc_x_da_suc_suma.
  rewrite suma_suc_y_da_suc_suma.
  rewrite IHx.
  reflexivity.
Qed.

Proposition suma_asociativa : ∀ x y z : ℕ, Σ (Σ x y) z = Σ x (Σ y z).
Proof.
  intros x y z.
  induction z.
  (* caso base: z = 0 *)
  rewrite suma_n_0_da_n.
  rewrite suma_n_0_da_n.
  reflexivity.
  (* caso inductivo *)
  rewrite suma_suc_y_da_suc_suma.
  rewrite suma_suc_y_da_suc_suma.
  rewrite IHz.
  rewrite suma_suc_y_da_suc_suma.
  reflexivity.
Qed.

(* EJERCICIO 11: enunciar formalmente las siguientes propiedades, pero SIN
 * probarlas: conmutativa del producto, distributiva suma-producto. *)

(* EJERCICIO 12: probar que (a + (b + c)) + d = a + (b + (c + d)). *)

(* EJERCICIO 13: probar que 0.n = 0. *)

(* EJERCICIO 14: probar que 1.n = n. *)

(* La formalización de la matemática no se limita a las funciones recursivas
 * sino que se extiende sobre casi todas las áreas de la Matemática:
 * Algebra, Cálculo, Geometría, Lógica, Matemática Discreta, Teoría de conjuntos,
 * Teoría de números, etc.
 * A continuación se presentan algunos conceptos y pruebas, sin entrar en detalles
 * ¿puede reconocer a qué área de la Matemática pertenecen? *)

Open Scope R_scope.
Notation ℝ := R.

Variable abs : ℝ → ℝ.
Notation "| x |" := (abs x) (at level 50).

Hypothesis abs_negativo : ∀ x : ℝ, x < 0 → |x| = - x.

Hypothesis abs_positivo : ∀ x : ℝ, x >= 0 → |x| = x.

Lemma abs_0_es_0 : |0| = 0.
Proof.
  assert (obvio : 0 >= 0).
  unfold Rge.
  right.
  apply eq_refl.
  rewrite (abs_positivo 0 obvio).
  apply eq_refl.
Qed.

Definition es_par (f : ℝ → ℝ) := ∀ x : ℝ, f x = f (- x).

Lemma el_valor_absoluto_es_par: es_par abs.
Proof.
  unfold es_par.
  intro x.
  case (Rtotal_order x 0).
  intro xnegativa.
  rewrite (abs_negativo x xnegativa).
  apply Ropp_gt_lt_0_contravar in xnegativa.
  apply Rgt_ge in xnegativa.
  rewrite (abs_positivo (- x) xnegativa).
  reflexivity.
  intro H.
  apply or_comm in H.
  fold (Rge x 0) in H.
  rewrite (abs_positivo x H).
  unfold Rge in H.
  case H.
  intro xpositiva.
  apply Ropp_lt_gt_0_contravar in xpositiva.
  rewrite (abs_negativo (- x) xpositiva).
  rewrite (Ropp_involutive x).
  reflexivity.
  intro xes0.
  rewrite xes0.
  rewrite Ropp_0.
  assert (obvio : 0 >= 0).
  unfold Rge.
  right.
  reflexivity.
  rewrite (abs_positivo 0 obvio).
  reflexivity.
Qed.

Definition limite (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
    ∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x : ℝ,
        0 < |x - c| < δ → |f x - L| < ε)).

Definition nula (x : ℝ) := 0.

Theorem nula_siempre_tiende_a_cero : ∀ c : ℝ, limite nula c 0.
Proof.
  intros c.
  unfold limite.
  intros eps epspositivo.
  exists 1.
  split.
  unfold Rgt.
  apply Rlt_0_1.
  intros x H.
  unfold nula.
  rewrite (Rminus_diag_eq 0 0 (eq_refl 0)).
  rewrite abs_0_es_0.
  unfold Rgt in epspositivo.
  apply epspositivo.
Qed.

(* EJERCICIO 15: Defina el concepto de continuidad de función real. *)

End Formalizacion_Matematica.
