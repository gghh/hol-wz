(* -*- holl -*- *)

needs "z_binomial_int.ml";;
needs "WZ_THM_Z_finsup_no_analysis.ml";;

let TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

let ZBINOM_TOP_STEP_STEP_TAC = ZBINOM_TOP_STEP_TAC THEN ZBINOM_TOP_STEP_TAC;;

(* ============================================================ *)
(* ||                                                        || *)
(* ||     Affronto \sum_k \binom{n}{k}^2 = \binom{2n}{n}     || *)
(* ||                                                        || *)
(* ============================================================ *)

g `sum(:int)(\k. (\n k. (real_of_int (z_binom n k)) pow 2) n k) =
  (\j. (real_of_int (z_binom (int_of_num 2 * j) j))) n` ;;  

e (MATCH_MP_TAC int_WZ_THM);;
e (REPEAT STRIP_TAC);;

(* la nuova ipotesi, ci penso dopo *)
r 1;;

e (EXISTS_TAC `(\n k.  
  (-- ((real_of_num 3) * real_of_int n - (real_of_num 2) * real_of_int k + real_of_num 3) *  
  (real_of_int (z_binom n (k - int_of_num 1))) pow 2) / (  
  real_of_num 2 * (real_of_num 2 * (real_of_int n) + real_of_num 1) *  
  real_of_int (z_binom (int_of_num 2 * n) n)))`);;  

e (BETA_TAC);;

e (GEN_TAC);;
e (REPEAT CONJ_TAC);;

r 2;;

(* ---------------------------------------------------- *)
(* Riscrivo per preparare il terreno alle tattiche che  *)
(* manipolano gli z_binomiali                           *)
(* ---------------------------------------------------- *)

e (SUBGOAL_THEN `!k:int. (k + int_of_num 1) - int_of_num 1 = k`
  (fun th -> REWRITE_TAC [th]) THENL [ARITH_TAC; ALL_TAC]);;
e (SUBGOAL_THEN `!k:int. int_of_num 2 * (k + int_of_num 1) = (int_of_num 2 * k + int_of_num 1) + int_of_num 1`
  (fun th -> REWRITE_TAC [th]) THENL [ARITH_TAC; ALL_TAC]);;

(* ---------------------------------------------------- *)
(* converto ~(\binom{n}{k} = 0) in condizioni su n e k  *)
(* ---------------------------------------------------- *)

(* solo per unificare con GSYM real_num_int *)
e (ONCE_REWRITE_TAC [REAL_ARITH `!a:real b. a = b <=> b = a`]);;
e (REWRITE_TAC [GSYM real_num_int]);;
e (ONCE_REWRITE_TAC [ARITH_RULE `!a:int b. a = b <=> b = a`]);;
e (ONCE_REWRITE_TAC [REAL_ARITH `!a:real b. a = b <=> b = a`]);;
(* e tutto torna a posto *)
e (REWRITE_TAC [ZBINOM_EQ_0]);;
e (STRIP_TAC);;

(* ---------------------------------------------------- *)
(* Lancio le tattiche che riscrivono i binomiali e      *)
(* mantengono ipotesi sui denominatori che aggiungono.  *)
(* Includo anche una "reagola di igiene" che elimina    *)
(* i subgoals con ipotesi contraddittorie.              *)
(* Sul mio porcessore AMD Sempron a 64 bit questa       *)
(* operazione richiede circa 5 minuti.                  *)
(* ---------------------------------------------------- *)

e (GEN_TAC);;
e (ZBINOM_TOP_STEP_STEP_TAC THEN
   TRY ZBINOM_BOTTOM_BACKSTEP_TAC THEN
   TRY ZBINOM_TOP_BACKSTEP_TAC THEN
   TRY ZBINOM_BOTTOM_STEP_TAC THEN
   TRY (REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC));;

(* ---------------------------------------------------- *)
(* Vengono prodotti cosi` solo 4 nuovi subgoals.        *)
(* Affronto il                                          *) 
(*                                                      *)
(*         P R I M O   S U B - S U B G O A L            *)
(*                                                      *)
(* Non manca nessun binomiale, quindi li cancello e poi *)
(* lavoro di aritmetica.                                *)
(* ---------------------------------------------------- *)

(* espando le potenze *)
e (REWRITE_TAC [REAL_FIELD `(a/b) pow 2 = (a pow 2)/(b pow 2)`;
  REAL_POW_MUL]);;
(* riduco a (numeratore)/(denominatore) *)
e (REWRITE_TAC [REAL_FIELD `(a/b)*(c/d) = (a*c)/(b*d)`;
  REAL_FIELD `a/b/c  = a/(b*c)`;
  REAL_FIELD `(a/b)*c = (a*c)/b`;
  REAL_FIELD `a*(b/c) = (a*b)/c`;
  REAL_FIELD `a/(b/c) = (a*c)/b`]);;
(* imposto l'associativita` inversa per ... *)
e (REWRITE_TAC [REAL_ARITH `a*b*c = (a*b)*c`]);;
(* ...spostare tutti i binomiali a sinistra cosi`*)
e (REWRITE_TAC [REAL_ARITH `a*(real_of_int(z_binom n k) pow 2)= (real_of_int(z_binom n k) pow 2)*a`]);;
(* adesso imposto l'associativita` a destra, cosi` cancellero` i binomiali *)
e (REWRITE_TAC [REAL_ARITH `(a*b)*c = a*b*c`]);;

(* cancello i binomiali *)
(* con un trucco sporchissimo, confronta con la
precedente tattica *)
e (MATCH_MP_TAC (REAL_FIELD `b/c - (real_of_num 1)/f = g/h - i/l ==> 
  (a*b)/c - a/f = (a*g)/h - (a*i)/l`));;
(* e (MATCH_MP_TAC (REAL_FIELD `b/c - e/f = g/h - i/l ==> 
  (a*b)/c - (a*e)/f = (a*g)/h - (a*i)/l`));; *)

(* anche sotto! *)

e (REWRITE_TAC [REAL_FIELD `(a/b)*(c/d) = (a*c)/(b*d)`;
  REAL_FIELD `a/b/c  = a/(b*c)`;
  REAL_FIELD `(a/b)*c = (a*c)/b`;
  REAL_FIELD `a*(b/c) = (a*b)/c`;
  REAL_FIELD `a/(b/c) = (a*c)/b`]);;
e (REWRITE_TAC [REAL_ARITH `a*b*c = (a*b)*c`]);;
e (REWRITE_TAC [REAL_ARITH `a*(real_of_int(z_binom n k))= (real_of_int(z_binom n k))*a`]);;
e (REWRITE_TAC [REAL_ARITH `(a*b)*c = a*b*c`]);;
e (MATCH_MP_TAC (REAL_FIELD `b/c - d/(real_of_num 1) = g/h - i/l ==> 
  b/(a*c) - d/a = g/(a*h) - i/(a*l)`));;

(* i binomiali sono spariti *)

(* Faccio a mano quello che sara` automatico *)

(* sciogliere le potenze !!! ARITH_TAC non lo sa fare *)

e (REWRITE_TAC [int_add_th; int_mul_th; int_of_num_th; REAL_POW_2]);;
e (REWRITE_TAC [
  REAL_ARITH `!n:int. (&2 * real_of_int n + &1 - (real_of_int n + &1)) =
    real_of_int n`;
  REAL_ARITH `((&2 * real_of_int n + &1) + &1 - (real_of_int n + &1)) =
    real_of_int n + &1`;
  REAL_ARITH `(&2 * real_of_int n + &1) + &1 = &2 * (real_of_int n + &1)`;
  REAL_ARITH `(&2 * real_of_int n - real_of_int n) = real_of_int n`;
  REAL_ARITH `(&3 * real_of_int n - &2 * (real_of_int k + &1) + &3) =
    (&3 * real_of_int n - &2 * real_of_int k + &1)`]);;
(* dimostro a mano che i denominatori non sono nulli *)
(* primo *)
e (SUBGOAL_THEN `~(((real_of_int n + &1 - real_of_int k) *
  (real_of_int n + &1 - real_of_int k)) *
  (&2 * (real_of_int n + &1)) *
  (&2 * real_of_int n + &1) *
  real_of_int n = real_of_num 0)` ASSUME_TAC THENL
  [REWRITE_TAC [REAL_ENTIRE] THEN 
  REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
(* sembra che ad ARITH_TAC manchi REAL_ENTIRE, mentre REAL_ARITH_TAC
  proprio non ce la fa (neppure con REAL_ENTIRE) *)

(* secondo *)
e (SUBGOAL_THEN `~(&2 * (&2 * real_of_int n + &1) = real_of_num 0)`
  ASSUME_TAC THENL
  [REWRITE_TAC [REAL_ENTIRE] THEN 
  REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
(* terzo *)
e (SUBGOAL_THEN `~(((real_of_int n + &1 - real_of_int k) *
  (real_of_int n + &1 - real_of_int k)) *
  &2 *
  (&2 * real_of_int n + &1) = real_of_num 0)` ASSUME_TAC THENL
  [REWRITE_TAC [REAL_ENTIRE] THEN 
  REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;

(* fallisce
e (REPEAT (FIRST_X_ASSUM MP_TAC) THEN REAL_FIELD_TAC);; *)

(* raccolgo a denominatore comune *)
e (ASM_SIMP_TAC [REAL_FIELD `!a:real b c d e f g h. 
  (~(b = &0) /\ ~(d = &0) /\ ~(f = &0) /\ ~(h = &0)) ==>
  ((a/b - c/d = e/f - g/h) <=> ((a*d - b*c)*f*h = (e*h - g*f)*b*d))`;
  REAL_ARITH `~(real_of_num 1 = real_of_num 0)`]);;

e (REAL_ARITH_TAC);;

(* ---------------------------------------------------- *)
(*                                                      *)
(*       S E C O N D O   S U B - S U B G O A L          *)
(*                                                      *)
(* I binomiali "sopra" ci sono tutti, mentre "sotto" ne *)
(* manca uno: questo significa che in ipotesi ho delle  *)
(* condizioni forti, come uguaglianze o disequazioni.   *)
(* Le sfruttero` per calcolare esplicitamente i         *)
(* binomiali che restano.                               *)
(* ---------------------------------------------------- *)

(* espando le potenze *)
e (REWRITE_TAC [REAL_FIELD `(a/b) pow 2 = (a pow 2)/(b pow 2)`;
  REAL_POW_MUL]);;

(* cancello i binomiali, esattamente come prima *)
e (REWRITE_TAC [REAL_FIELD `(a/b)*(c/d) = (a*c)/(b*d)`;
  REAL_FIELD `a/b/c  = a/(b*c)`;
  REAL_FIELD `(a/b)*c = (a*c)/b`;
  REAL_FIELD `a*(b/c) = (a*b)/c`;
  REAL_FIELD `a/(b/c) = (a*c)/b`]);;
e (REWRITE_TAC [REAL_ARITH `a*b*c = (a*b)*c`]);;
e (REWRITE_TAC [REAL_ARITH `a*(real_of_int(z_binom n k) pow 2)= (real_of_int(z_binom n k) pow 2)*a`]);;
e (REWRITE_TAC [REAL_ARITH `(a*b)*c = a*b*c`]);;
e (MATCH_MP_TAC (REAL_FIELD `b/c - (real_of_num 1)/f = g/h - i/l ==> 
  (a*b)/c - a/f = (a*g)/h - (a*i)/l`));;

(* sotto non si puo`: in un addendo mancano *)
(* ma n = 0 *)
e (SUBGOAL_THEN `n = int_of_num 0` ASSUME_TAC
  THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
e (ASM_REWRITE_TAC [ZBINOM_EMPTY_SET;REAL_MUL_LZERO; REAL_MUL_RZERO;
  int_of_num_th; int_mul_th; int_add_th; REAL_ADD_LID; REAL_ADD_RID;
  INT_MUL_LZERO; INT_MUL_RZERO; REAL_MUL_LID; REAL_MUL_RID; REAL_POW_2]);;

(* dimostro che i denominatori non sono nulli *)
(* esattamente come prima *)

(* primo denominatore*)
e (SUBGOAL_THEN `~(((&1 - real_of_int k) * (&1 - real_of_int k)) *
  (&1 + &1) = real_of_num 0)` ASSUME_TAC THENL
  [REWRITE_TAC [REAL_ENTIRE] THEN 
  REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
(* secondo *)
e (SUBGOAL_THEN `~(((&1 - real_of_int k) * (&1 - real_of_int k)) * &2
  = real_of_num 0)` ASSUME_TAC THENL
  [REWRITE_TAC [REAL_ENTIRE] THEN 
  REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
(* elimino i denominatori *)
e (ASM_SIMP_TAC [REAL_FIELD `!a:real b c d e f g h. 
  (~(b = &0) /\ ~(d = &0) /\ ~(f = &0) /\ ~(h = &0)) ==>
  ((a/b - c/d = e/f - g/h) <=> ((a*d - b*c)*f*h = (e*h - g*f)*b*d))`;
  REAL_ARITH `~(real_of_num 1 = real_of_num 0)`;
  REAL_ARITH `~(real_of_num 2 = real_of_num 0)`]);;

e (REAL_ARITH_TAC);;

(* ---------------------------------------------------- *)
(*                                                      *)
(*           T E R Z O   S U B - S U B G O A L          *)
(*                                                      *)
(* Stavolta i binomiali "sotto" ci sono tutti, ma       *)
(* "sopra" manca uno. Utilizzero` l'ipotesi che         *)
(* k = n + 1 per domostrare che valgono 0               *)
(* ---------------------------------------------------- *)

(* cancello i binomiali sotto, come gia` fatto*)

e (REWRITE_TAC [REAL_FIELD `(a/b)*(c/d) = (a*c)/(b*d)`;
  REAL_FIELD `a/b/c  = a/(b*c)`;
  REAL_FIELD `(a/b)*c = (a*c)/b`;
  REAL_FIELD `a*(b/c) = (a*b)/c`;
  REAL_FIELD `a/(b/c) = (a*c)/b`]);;
e (REWRITE_TAC [REAL_ARITH `a*b*c = (a*b)*c`]);;
e (REWRITE_TAC [REAL_ARITH `a*(real_of_int(z_binom n k))= (real_of_int(z_binom n k))*a`]);;
e (REWRITE_TAC [REAL_ARITH `(a*b)*c = a*b*c`]);;
e (MATCH_MP_TAC (REAL_FIELD `b/c - d/(real_of_num 1) = g/h - i/l ==> 
  b/(a*c) - d/a = g/(a*h) - i/(a*l)`));;

(* i binomiali sono spariti *)

(* osservo che k = n + 1 *)
e (SUBGOAL_THEN `n < k:int` ASSUME_TAC THENL
  [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
e (SUBGOAL_THEN `z_binom n k = int_of_num 0`
  (fun th -> REWRITE_TAC [th]) THENL [ASM_SIMP_TAC [ZBINOM_EQ_0]; ALL_TAC]);;
e (ASM_REWRITE_TAC [REAL_POW_2; int_of_num_th; int_mul_th; int_add_th;
  REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_LID; REAL_MUL_RID; 
  INT_MUL_LZERO; INT_MUL_RZERO]);;

(* dimostro che i denominatori non sono nulli, come prima *)
(* primo *)
e (SUBGOAL_THEN `~(((&2 * real_of_int n + &1) + &1) *
  (&2 * real_of_int n + &1) *
  (&2 * real_of_int n - real_of_int n) = real_of_num 0)` ASSUME_TAC THENL
  [REWRITE_TAC [REAL_ENTIRE] THEN 
  REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
(* secondo *)
e (SUBGOAL_THEN `~(&2 * (&2 * real_of_int n + &1) = real_of_num 0)`
  ASSUME_TAC THENL [REWRITE_TAC [REAL_ENTIRE] THEN 
  REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
(* elimino i denominatori *)
e (ASM_SIMP_TAC [REAL_FIELD `!a:real b c d e f g h. 
  (~(b = &0) /\ ~(d = &0) /\ ~(f = &0) /\ ~(h = &0)) ==>
  ((a/b - c/d = e/f - g/h) <=> ((a*d - b*c)*f*h = (e*h - g*f)*b*d))`;
  REAL_ARITH `~(real_of_num 1 = real_of_num 0)`;
  REAL_ARITH `~(real_of_num 2 = real_of_num 0)`]);;

e (REAL_ARITH_TAC);;

(* ---------------------------------------------------- *)
(*                                                      *)
(*         Q U A R T O   S U B - S U B G O A L          *)
(*                                                      *)
(* Stavolta i binomiali n = 0, k = 1.                   *)
(* Che si vuole di piu`?                                *)
(* ---------------------------------------------------- *)

(* qui abbiamo n = 0, k = 1 *)
e (SUBGOAL_THEN `n < k:int` ASSUME_TAC THENL
  [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
e (SUBGOAL_THEN `z_binom n k = int_of_num 0`
  (fun th -> REWRITE_TAC [th]) THENL [ASM_SIMP_TAC [ZBINOM_EQ_0]; ALL_TAC]);;
e (SUBGOAL_THEN `n = int_of_num 0` ASSUME_TAC THENL
  [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
e (SUBGOAL_THEN `k = int_of_num 1` ASSUME_TAC THENL
  [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
e (ASM_REWRITE_TAC [REAL_POW_2; int_of_num_th; int_mul_th; int_add_th;
  REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_LID; REAL_MUL_RID; 
  INT_MUL_LZERO; INT_MUL_RZERO]);;
e (REWRITE_TAC [ZBINOM_EMPTY_SET]);;
e (REAL_FIELD_TAC);;

(* ---------------------------------------------------- *)
(* Adesso ritornano i subgoals originari:               *)
(* (i) vale nel caso in cui il secondo membro e` nullo  *)
(* (ii) vale in un punto                                *)
(* (iii) U(n,k) ha supporto finito                      *)
(* (iv) G(n,k) ha supporto finito                       *)
(* ---------------------------------------------------- *)

(* ---------------------------------------------------- *)
(*              SECONDO MEMBRO NULLO                    *)
(* ---------------------------------------------------- *)

e (ASM_REWRITE_TAC []);;

e (FIRST_X_ASSUM MP_TAC);;
e (REWRITE_TAC []);;
(* solo per unificare con GSYM real_num_int *)
e (ONCE_REWRITE_TAC [REAL_ARITH `!a:real b. a = b <=> b = a`]);;
e (REWRITE_TAC [GSYM real_num_int]);;
e (ONCE_REWRITE_TAC [ARITH_RULE `!a:int b. a = b <=> b = a`]);;
e (ONCE_REWRITE_TAC [REAL_ARITH `!a:real b. a = b <=> b = a`]);;
(* e tutto torna a posto *)
e (REWRITE_TAC [ZBINOM_EQ_0]);;
e (STRIP_TAC);;
(* ho convertito ~(\binom{n}{k} = 0) in condizioni su n e k *)

(* 3 subsubgoals *)

(* il primo *)

e (SUBGOAL_THEN `~(int_of_num 0 <= n)` ASSUME_TAC THENL
  [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;
e (SUBGOAL_THEN `(\k. real_of_int (z_binom n k) pow 2) =
  (\k. real_of_num 0)`
  (fun th -> REWRITE_TAC [th]) THENL
  [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC [REAL_POW_EQ_0] THEN 
  CONJ_TAC THENL [MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [GSYM real_num_int]
  THEN MATCH_MP_TAC EQ_SYM THEN ASM_SIMP_TAC [ZBINOM_EQ_0]; ARITH_TAC];
  ALL_TAC]);;
e (MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC []);;

(* il secondo *)

e (SUBGOAL_THEN `(\k. real_of_int (z_binom n k) pow 2) =
  (\k. real_of_num 0)`
  (fun th -> REWRITE_TAC [th]) THENL
  [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC [REAL_POW_EQ_0] THEN 
  CONJ_TAC THENL [MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [GSYM real_num_int]
  THEN MATCH_MP_TAC EQ_SYM THEN ASM_SIMP_TAC [ZBINOM_EQ_0]; ARITH_TAC];
  ALL_TAC]);;
e (MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC []);;

(* il terzo *)

e (ASM_CASES_TAC `int_of_num 0 <= n` THENL
  [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]);;

e (SUBGOAL_THEN `(\k. real_of_int (z_binom n k) pow 2) =
  (\k. real_of_num 0)`
  (fun th -> REWRITE_TAC [th]) THENL
  [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC [REAL_POW_EQ_0] THEN 
  CONJ_TAC THENL [MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [GSYM real_num_int]
  THEN MATCH_MP_TAC EQ_SYM THEN ASM_SIMP_TAC [ZBINOM_EQ_0]; ARITH_TAC];
  ALL_TAC]);;
e (MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC []);;

(* ---------------------------------------------------- *)
(*                    VALE SE n = O                     *)
(* ---------------------------------------------------- *)

(* con questa nuova versione, devi fornire tu il valore di test *)
e (EXISTS_TAC `int_of_num 0`);;
e (BETA_TAC);;
e (REWRITE_TAC [ZBINOM_EMPTY_SET]);;
e (SUBGOAL_THEN `(\k:int. (if k = &0 then &1 else &0) pow 2) =
  (\k. if k = &0 then &1 pow 2 else &0 pow 2)`
  (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [FUN_EQ_THM] THEN
  GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC]);;

e (SUBGOAL_THEN `real_of_num 0 pow 2 = real_of_num 0`
  (fun th -> REWRITE_TAC [th]) THENL [REAL_ARITH_TAC; ALL_TAC]);;
e (REWRITE_TAC [SUM_DELTA; IN_UNIV; 
  REAL_ARITH `real_of_num 1 pow 2 = real_of_num 1`; INT_MUL_RZERO;
  ZBINOM_REFL]);;
e (ARITH_TAC);;

(* la nuova ipotesi, dopo *)

r 1;;

(* ---------------------------------------------------- *)
(*              U(n,k) HA SUPPORTO FINITO               *)
(* ---------------------------------------------------- *)

(* nota che nel teorema FINITE_SUPPORT_RATIO c'e` una *)
(* divisione per zero nascosta*)

e (SUBGOAL_THEN
  `(\k. real_of_int (z_binom n k) pow 2 / real_of_int (z_binom (&2 * n) n)) = 
  (\k. (\j. real_of_int (z_binom n j) pow 2) k / real_of_int (z_binom (&2 * n) n))`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [REWRITE_TAC []; ALL_TAC]);;
e (MATCH_MP_TAC FINITE_SUPPORT_RATIO);;
e (SUBGOAL_THEN
  `(\j. real_of_int (z_binom n j) pow 2) = 
  (\k. ((\j. real_of_int (z_binom n j)) k) pow 2)`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [REWRITE_TAC []; ALL_TAC]);;
e (MATCH_MP_TAC FINITE_SUPPORT_POW);;
e (CONJ_TAC);;
e (REWRITE_TAC [ZBINOM_FINITE_SUPPORT]);;
e (ARITH_TAC);;

(* ---------------------------------------------------- *)
(*              G(n,k) HA SUPPORTO FINITO               *)
(* ---------------------------------------------------- *)

(* nota che nel teorema FINITE_SUPPORT_RATIO c'e` una *)
(* divisione per zero nascosta*)
e (SUBGOAL_THEN
  `(\k. (--(&3 * real_of_int n - &2 * real_of_int k + &3) *
        real_of_int (z_binom n (k - &1)) pow 2) /
       (&2 * (&2 * real_of_int n + &1) * real_of_int (z_binom (&2 * n) n))) =
  (\k. (\j. (--(&3 * real_of_int n - &2 * real_of_int j + &3) *
        real_of_int (z_binom n (j - &1)) pow 2)) k /
       (&2 * (&2 * real_of_int n + &1) * real_of_int (z_binom (&2 * n) n)))`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [REWRITE_TAC []; ALL_TAC]);;
e (MATCH_MP_TAC FINITE_SUPPORT_RATIO);;
e (SUBGOAL_THEN
  `(\j. --(&3 * real_of_int n - &2 * real_of_int j + &3) *
       real_of_int (z_binom n (j - &1)) pow 2) =
  (\j. (\w. --(&3 * real_of_int n - &2 * real_of_int w + &3)) j *
       (\i. real_of_int (z_binom n (i - &1)) pow 2) j)`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [REWRITE_TAC []; ALL_TAC]);;
e (MATCH_MP_TAC FINITE_SUPPORT_MUL);;
e (SUBGOAL_THEN
  `(\j. real_of_int (z_binom n (j - int_of_num 1)) pow 2) = 
  (\k. ((\j. real_of_int (z_binom n (j - int_of_num 1))) k) pow 2)`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [REWRITE_TAC []; ALL_TAC]);;
e (MATCH_MP_TAC FINITE_SUPPORT_POW);;
e (CONJ_TAC);;
e (SUBGOAL_THEN
  `(\i. real_of_int (z_binom n (i - &1))) =
  (\i. (\k. real_of_int (z_binom n k))(i - int_of_num 1))`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [REWRITE_TAC []; ALL_TAC]);;
e (MATCH_MP_TAC FINSUPPORT_RIGHT_SHIFT);;
e (REWRITE_TAC [ZBINOM_FINITE_SUPPORT]);;
e (ARITH_TAC);;

(* -------------------------------------------------- *)
(*       Il supporto di r(n) non ha buchi             *)
(* -------------------------------------------------- *)

e (POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC);;
e (BETA_TAC);;

e (REWRITE_TAC [ZBINOM_SUPPORT_HALFLINE]);;

e (REWRITE_TAC [IN_ELIM_THM; SUBSET]);;
e (ARITH_TAC);;


let the_first_Wilf_Zeilberg_Harrison_Fateman_Maggesi_Gherdovich_identity = top_thm();;
