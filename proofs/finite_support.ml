(* -*- holl -*- *)

(* ====================================================================== *)
(* ||                                                                  || *)
(* ||        Some useful lemmas about finite support functions         || *)
(* ||        of type :int->real and :num->real.                         || *)
(* ||                                                                  || *)
(* ||     Giovanni Gherdovich, gherdovich@students.math.unifi.it       || *)
(* ||       Universita` degli Studi di Firenze, december 2006          || *)
(* ||                                                                  || *)
(* ====================================================================== *)

let TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

let REAL_FIELD_TAC = CONV_TAC REAL_FIELD;;

let SUPPORT_MONOTONIC = prove(`!op (f:A->B) (s:A->bool) t.
  s SUBSET t ==> (support op f s) SUBSET (support op f t)`,
  MESON_TAC [SUBSET; IN_SUPPORT]);;

(* f:int->real *)

(* basic operations *)

let SUPPORT_SUM_int = prove
(`!f:int->real g:int->real. support (+) (\x. f x + g x) (:int) SUBSET
  ((support (+) f (:int)) UNION (support (+) g (:int)))`,
 REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; SUBSET; UNION] THEN
 (REPEAT GEN_TAC) THEN REWRITE_TAC [SET_RULE `!x:A. x IN {x| P x} <=> P x`]
 THEN DISCH_TAC THEN
 FIRST_X_ASSUM MP_TAC THEN ONCE_REWRITE_TAC 
  [TAUT `!P Q. P ==> Q <=> ~Q ==> ~P`] THEN REAL_ARITH_TAC);;

let SUPPORT_NEG_int = prove
(`!g:int->real. support (+) g (:int) = support (+) (real_neg o g) (:int)`,
 STRIP_TAC THEN REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; o_DEF;
  SET_RULE `!P Q. ({x | P x} = {x | Q x}) <=> 
  ({x | P x} SUBSET {x | Q x} /\ {x | Q x} SUBSET {x | P x})`] THEN
 CONJ_TAC THENL [REWRITE_TAC [SUBSET] THEN
  GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
 REWRITE_TAC [SUBSET] THEN GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM]
 THEN REAL_ARITH_TAC);;

let SUPPORT_SUB_int = prove
(`!f:int->real g:int->real. support (+) (\x. f x - g x) (:int) SUBSET
  ((support (+) f (:int)) UNION (support (+) g (:int)))`,
 REPEAT GEN_TAC THEN REWRITE_TAC [REAL_ARITH `!a:real b. a - b = a + (-- b)`]
 THEN SUBGOAL_THEN 
  `support (+) (g:int->real) (:int) = support (+) (real_neg o g) (:int)` 
  (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [GSYM SUPPORT_NEG_int]; ALL_TAC]
 THEN SUBGOAL_THEN `(\x:int. f x + real_neg (g x)) = (\x. f x + ((--) o g) x)` 
  (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [o_THM]; ALL_TAC] THEN
 REWRITE_TAC [SUPPORT_SUM_int]);;

let FINITE_SUPPORT_SUB_int = prove
(` !(f:int->real) (g:int->real). FINITE (support (+) f (:int)) /\ 
  FINITE (support (+) g (:int)) ==>
  FINITE (support (+) (\x. f x - g x) (:int))`,
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN `(\x. (f:int->real) x - (g:int->real) x) = (\x. f x + (real_neg o g) x)`
  (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC
  THEN REWRITE_TAC [o_DEF] THEN REAL_ARITH_TAC; ALL_TAC] THEN
 SUBGOAL_THEN `FINITE (support (+) ((--) o g) (:int))` ASSUME_TAC
  THENL [ASM_REWRITE_TAC [GSYM SUPPORT_NEG_int]; ALL_TAC] THEN
 MATCH_MP_TAC FINITE_SUBSET THEN
 EXISTS_TAC `support (+) (f:int->real) (:int) UNION support (+) ((--) o g)(:int)`
 THEN REWRITE_TAC [SUPPORT_SUM_int] THEN MATCH_MP_TAC FINITE_UNION_IMP
 THEN ASM_REWRITE_TAC []);;

let FINITE_SUPPORT_RATIO = prove
(`!(a:real) (f:int->real). FINITE (support (+) f (:int))
  ==> FINITE (support (+) (\k. (f k) / a) (:int))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(support (+) (f:int->real) (:int))`
  THEN CONJ_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN
  REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; SUBSET; IN_ELIM_THM]
  THEN REAL_FIELD_TAC);;
(* divisione per zero passata inosservata? *)

let FINITE_SUPPORT_POW = prove
(`!(a:real) (f:int->real) n:num.
  (FINITE (support (+) f (:int)) /\ ~(n = 0))
  ==> FINITE (support (+) (\k. (f k) pow n) (:int))`,
(* in HOL 0^0=1 ma REAL_POW_EQ_0 ne sembra imbarazzato (chiede ~(n=0)) *)
  REPEAT STRIP_TAC THEN REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD]
  THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(support (+) (f:int->real) (:int))`
  THEN CONJ_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN
  ASM_REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; SUBSET;
  IN_ELIM_THM; REAL_POW_EQ_0; DE_MORGAN_THM]);;

let FINITE_SUPPORT_MUL = prove
(`!(g:int->real) (f:int->real). FINITE (support (+) f (:int))
  ==> FINITE (support (+) (\k. (g k) * (f k)) (:int))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD]
  THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(support (+) (f:int->real) (:int))` THEN CONJ_TAC
    THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN
  ASM_REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; SUBSET;
  IN_ELIM_THM] THEN REAL_FIELD_TAC);;

(* composition *)

let FINITE_SUPPORT_COMPOS = prove
(` !(f:int->real) (g:num->int). FINITE (support (+) f (:int))
  /\ INJ g (:num) (:int) ==>
  FINITE (support (+) (f o g) (:num))`,
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN `(support (+) ((f:int->real) o (g:num->int)) (:num)) = 
  {x | g x IN (support (+) (f:int->real) (:int))}` 
  (fun th -> REWRITE_TAC [th]) THENL
  [REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; IN_ELIM_THM; o_DEF]; ALL_TAC]
 THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN
 (FIRST_X_ASSUM MP_TAC) THEN REWRITE_TAC [INJ; IN_UNIV]);;

let FINITE_SUPPORT_COMPOS_bis = prove
(` !(f:int->real) (g:int->int). FINITE (support (+) f (:int))
  /\ INJ g (:int) (:int) ==>
  FINITE (support (+) (f o g) (:int))`,
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN `(support (+) ((f:int->real) o (g:int->int)) (:int)) = 
  {x | g x IN (support (+) (f:int->real) (:int))}` 
  (fun th -> REWRITE_TAC [th]) THENL
  [REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; IN_ELIM_THM; o_DEF]; ALL_TAC]
 THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN
 (FIRST_X_ASSUM MP_TAC) THEN REWRITE_TAC [INJ; IN_UNIV]);;

(* g` !(f:int->real) (g:int->int). FINITE (support (+) f (:int)) 
  /\ INJ g (:int) (:int) ==>
  FINITE (support (+) (f o g) (:int))`;;
e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `(support (+) ((f:int->real) o (g:int->int)) (:int)) = 
  {x | g x IN (support (+) (f:int->real) (:int))}` 
  (fun th -> REWRITE_TAC [th]));;
e (REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; IN_ELIM_THM]);;
e (REWRITE_TAC [o_DEF]);;
e (MATCH_MP_TAC FINITE_IMAGE_INJ);;
e (ASM_REWRITE_TAC []);;
e ((FIRST_X_ASSUM MP_TAC) THEN REWRITE_TAC [INJ; IN_UNIV]);;
let FINITE_SUPPORT_COMPOS_bis = top_thm();; *)

(* CHIEDERE A MARCO *)
(* ho provato a generalizzare il precedente
teorema, ma non riesco a far passare il nuovo enunciato.
Da` eccezione "tryfind"
g` !(g:A->B) (f:B->C) s. FINITE (support (+) f (IMAGE g s)) /\ 
  INJ g s (IMAGE g s) ==>
  FINITE (support (+) (f o g) s)`;;
Probabilmente nell'insieme C non c'e` l'addizione!
*)

let FINITE_SUPPORT_SUM_INJ = prove
(` !(f:int->real) (g:int->int). FINITE (support (+) f (:int))
  /\ INJ g (:int) (:int) ==>
  FINITE (support (+) (\x. f x + (f o g) x) (:int))`,
 REPEAT STRIP_TAC THEN 
 SUBGOAL_THEN `FINITE (support (+) ((f:int->real) o (g:int->int)) (:int))`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `(support (+) ((f:int->real) o (g:int->int)) (:int)) = 
  {x | g x IN (support (+) (f:int->real) (:int))}` 
  (fun th -> REWRITE_TAC [th]) THENL
  [REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; IN_ELIM_THM; o_DEF]; ALL_TAC]
  THEN MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC [] THEN
  FIRST_ASSUM MP_TAC THEN REWRITE_TAC [INJ; IN_UNIV]; ALL_TAC] THEN
 MATCH_MP_TAC FINITE_SUBSET THEN
 EXISTS_TAC `(support (+) (f:int->real) (:int)) UNION 
  (support (+) ((f:int->real) o (g:int->int)) (:int))` THEN
 CONJ_TAC THENL [(MATCH_MP_TAC FINITE_UNION_IMP) THEN ASM_REWRITE_TAC [];
  REWRITE_TAC [SUPPORT_SUM_int]]);;

(* shifting *)

let FINSUPPORT_LEFT_SHIFT = prove
(`!(f:int->real) n:int. FINITE (support (+) f (:int)) ==>
 FINITE (support (+) (\k. f (k + n)) (:int))`,
 REPEAT STRIP_TAC THEN 
 SUBGOAL_THEN `(\k. (f:int->real) (k + n)) = f o (\t. t + n)`
  (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [o_DEF]; ALL_TAC] THEN
 MATCH_MP_TAC FINITE_SUPPORT_COMPOS_bis THEN
 CONJ_TAC THENL [ASM_REWRITE_TAC []; 
  REWRITE_TAC [INJ; IN_UNIV] THEN ARITH_TAC]);;

let FINSUPPORT_RIGHT_SHIFT = prove
(`!(f:int->real) n:int. FINITE (support (+) f (:int)) ==>
 FINITE (support (+) (\k. f (k - n)) (:int))`,
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN `!(k:int) n. k - n = k + (-- n)` (fun th -> REWRITE_TAC [th])
  THENL [ARITH_TAC; ALL_TAC] THEN MATCH_MP_TAC FINSUPPORT_LEFT_SHIFT THEN
 ASM_REWRITE_TAC []);;

(* ingrandire l'insieme di somma, se questo e` gia` il massimo *)

let ITERATE_SUPPORT_UNION = prove
(`!f:A->B op s:A->bool. 
  iterate op (support op f (:A)) f = iterate op ((support op f (:A)) UNION s) f`,
 ONCE_REWRITE_TAC [SET_RULE `!s t. s UNION t = s UNION (t DIFF s)`] THEN
 ONCE_REWRITE_TAC [GSYM ITERATE_SUPPORT] THEN
 REWRITE_TAC [SUPPORT_SUPPORT; SUPPORT_CLAUSES; SUPPORT_SUPPORT] THEN
 REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
 SUBGOAL_THEN `!s:A->bool f:A->B. support op f s DIFF support op f (:A) = {}`
  (fun th -> REWRITE_TAC [th]) THENL [REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM SUPPORT_CLAUSES] THEN
  SUBGOAL_THEN `s SUBSET (:A)` ASSUME_TAC THENL
    [REWRITE_TAC [SUBSET; IN_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC [SET_RULE `!s t. s SUBSET t ==> s DIFF t = {}`] THEN
  REWRITE_TAC [SUPPORT_CLAUSES]; SET_TAC []]);;

(* I cannot specialize the previous theorem.. why? *)
(* I must prove by hand the specialized version :( *)

let SUM_SUPPORT_UNION_int = prove
(`!f:int->real s:int->bool. 
  sum (support (+) f (:int)) f = sum ((support (+) f (:int)) UNION s) f`,
 ONCE_REWRITE_TAC [SET_RULE `!s t. s UNION t = s UNION (t DIFF s)`] THEN
 ONCE_REWRITE_TAC [GSYM SUM_SUPPORT] THEN
 REWRITE_TAC [SUPPORT_CLAUSES; SUPPORT_SUPPORT] THEN
 REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
 SUBGOAL_THEN
  `!s:int->bool f:int->real. support (+) f s DIFF support (+) f (:int) = {}`
  (fun th -> REWRITE_TAC [th]) THENL [REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM SUPPORT_CLAUSES] THEN 
  SUBGOAL_THEN
    `s SUBSET (:int)` ASSUME_TAC THENL [REWRITE_TAC [SUBSET; IN_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC [SET_RULE `!s t. s SUBSET t ==> s DIFF t = {}`] THEN
  REWRITE_TAC [SUPPORT_CLAUSES]; SET_TAC []]);;

let SUM_SUPPORT_UNION_int = prove
(`!f:int->real s:int->bool. 
  sum (support (+) (f:int->real) (:int)) (f:int->real) =
  sum ((support (+) (f:int->real) (:int)) UNION s) f`,
  ONCE_REWRITE_TAC [SET_RULE `!s t. s UNION t = s UNION (t DIFF s)`] THEN
  ONCE_REWRITE_TAC [GSYM SUM_SUPPORT] THEN
  REWRITE_TAC [SUPPORT_CLAUSES; SUPPORT_SUPPORT] THEN
  REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
  `!s:int->bool f:int->real. support (+) f s DIFF support (+) f (:int) = {}`
  (fun th -> REWRITE_TAC [th]) THENL [REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM SUPPORT_CLAUSES] THEN 
  SUBGOAL_THEN
    `s SUBSET (:int)` ASSUME_TAC THENL [REWRITE_TAC [SUBSET; IN_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC [SET_RULE `!s t. s SUBSET t ==> s DIFF t = {}`] THEN
  REWRITE_TAC [SUPPORT_CLAUSES]; SET_TAC []]);;

let SUM_SUPERSET_SUPPORT_int = prove
(`!f:int->real s. support (+) f (:int) SUBSET s ==>
  sum s f = sum (support (+) f (:int)) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  TRANS_TAC `sum (support (+) f (:int) UNION 
  (s:int->bool DIFF support (+) f (:int))) f` THENL
    [REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC) THEN
    POP_ASSUM MP_TAC THEN SET_TAC [];
    ONCE_REWRITE_TAC [GSYM SUM_SUPPORT_UNION_int] THEN
    REWRITE_TAC [EQ_REFL]]);;

let SUPPORT_SUBSET_INTSEG = prove
(`!f:int->real a:int b:int.
  support (+) f (:int) SUBSET {i:int | a <= i /\ i <= b}
    ==> sum {i:int | a <= i /\ i <= b} f = sum (:int) f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM SUM_SUPPORT] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC [SET_RULE `!s:A->bool t. s = t <=> (s SUBSET t /\ t SUBSET s)`] THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUPPORT_MONOTONIC THEN
    REWRITE_TAC [SUBSET; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN `!(f:int->real). support (+) f (:int) = 
  support (+) f (support (+) f (:int))` (fun th -> ONCE_REWRITE_TAC [th])
  THENL [REWRITE_TAC [SUPPORT_SUPPORT]; ALL_TAC] THEN
  ASM_SIMP_TAC [SUPPORT_MONOTONIC]);;

(* f:num->real *)

(* basic operation *)

let SUPPORT_SUM_num = prove
(`!f:num->real g:num->real. support (+) (\x. f x + g x) (:num) SUBSET
  ((support (+) f (:num)) UNION (support (+) g (:num)))`,
 REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; SUBSET; UNION] THEN
 (REPEAT GEN_TAC) THEN REWRITE_TAC [SET_RULE `!x:A. x IN {x| P x} <=> P x`]
 THEN DISCH_TAC THEN
 FIRST_X_ASSUM MP_TAC THEN ONCE_REWRITE_TAC 
  [TAUT `!P Q. P ==> Q <=> ~Q ==> ~P`] THEN REAL_ARITH_TAC);;

let SUPPORT_NEG_num = prove
(`!g:num->real. support (+) g (:num) = support (+) (real_neg o g) (:num)`,
 STRIP_TAC THEN REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; o_DEF;
  SET_RULE `!P Q. ({x | P x} = {x | Q x}) <=> 
  ({x | P x} SUBSET {x | Q x} /\ {x | Q x} SUBSET {x | P x})`] THEN
 CONJ_TAC THENL [REWRITE_TAC [SUBSET] THEN
  GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
 REWRITE_TAC [SUBSET] THEN GEN_TAC THEN REWRITE_TAC [IN_ELIM_THM]
 THEN REAL_ARITH_TAC);;

let SUPPORT_SUB_num = prove
(`!f:num->real g:num->real. support (+) (\x. f x - g x) (:num) SUBSET
  ((support (+) f (:num)) UNION (support (+) g (:num)))`,
 REPEAT GEN_TAC THEN REWRITE_TAC [REAL_ARITH `!a:real b. a - b = a + (-- b)`]
 THEN SUBGOAL_THEN 
  `support (+) (g:num->real) (:num) = support (+) (real_neg o g) (:num)` 
  (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [GSYM SUPPORT_NEG_num]; ALL_TAC]
 THEN SUBGOAL_THEN `(\x:num. f x + real_neg (g x)) = (\x. f x + ((--) o g) x)` 
  (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [o_THM]; ALL_TAC] THEN
 REWRITE_TAC [SUPPORT_SUM_num]);;

let FINITE_SUPPORT_SUB_num = prove
(` !(f:num->real) (g:num->real). FINITE (support (+) f (:num)) /\ 
  FINITE (support (+) g (:num)) ==>
  FINITE (support (+) (\x. f x - g x) (:num))`,
 REPEAT STRIP_TAC THEN
 SUBGOAL_THEN `(\x. (f:num->real) x - (g:num->real) x) = (\x. f x + (real_neg o g) x)`
  (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC
  THEN REWRITE_TAC [o_DEF] THEN REAL_ARITH_TAC; ALL_TAC] THEN
 SUBGOAL_THEN `FINITE (support (+) ((--) o g) (:num))` ASSUME_TAC
  THENL [ASM_REWRITE_TAC [GSYM SUPPORT_NEG_num]; ALL_TAC] THEN
 MATCH_MP_TAC FINITE_SUBSET THEN
 EXISTS_TAC `support (+) (f:num->real) (:num) UNION support (+) ((--) o g)(:num)`
 THEN REWRITE_TAC [SUPPORT_SUM_num] THEN MATCH_MP_TAC FINITE_UNION_IMP
 THEN ASM_REWRITE_TAC []);;

(* ingrandire il supporto *)

let SUM_SUPPORT_UNION_num = prove
(`!f:num->real s:num->bool. 
  sum (support (+) f (:num)) f = sum ((support (+) f (:num)) UNION s) f`,
 ONCE_REWRITE_TAC [SET_RULE `!s t. s UNION t = s UNION (t DIFF s)`] THEN
 ONCE_REWRITE_TAC [GSYM SUM_SUPPORT] THEN
 REWRITE_TAC [SUPPORT_CLAUSES; SUPPORT_SUPPORT] THEN
 REPEAT GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
 SUBGOAL_THEN
  `!s:num->bool f:num->real. support (+) f s DIFF support (+) f (:num) = {}`
  (fun th -> REWRITE_TAC [th]) THENL [REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM SUPPORT_CLAUSES] THEN 
  SUBGOAL_THEN
    `s SUBSET (:num)` ASSUME_TAC THENL [REWRITE_TAC [SUBSET; IN_UNIV]; ALL_TAC] THEN
  ASM_SIMP_TAC [SET_RULE `!s t. s SUBSET t ==> s DIFF t = {}`] THEN
  REWRITE_TAC [SUPPORT_CLAUSES]; SET_TAC []]);;

let SUM_SUPERSET_SUPPORT_num = prove
(`!f:num->real s. support (+) f (:num) SUBSET s ==>
  sum s f = sum (support (+) f (:num)) f`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 TRANS_TAC `sum (support (+) f (:num) UNION 
  (s:num->bool DIFF support (+) f (:num))) f` THENL
  [REPEAT (AP_THM_TAC ORELSE AP_TERM_TAC) THEN 
  POP_ASSUM MP_TAC THEN SET_TAC []; ALL_TAC] THEN
 ONCE_REWRITE_TAC [GSYM SUM_SUPPORT_UNION_num] THEN REWRITE_TAC [EQ_REFL]);;

let SUPPORT_SUBSET_NUMSEG = prove
(`!f:num->real n.
  support (+) f (:num) SUBSET (0..n) ==> sum (0..n) f = sum (:num) f`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 ONCE_REWRITE_TAC [GSYM SUM_SUPPORT] THEN
 AP_THM_TAC THEN AP_TERM_TAC THEN
 REWRITE_TAC [SET_RULE `!s:A->bool t. s = t <=> (s SUBSET t /\ t SUBSET s)`]
  THEN CONJ_TAC THENL [MATCH_MP_TAC SUPPORT_MONOTONIC THEN
  REWRITE_TAC [SUBSET; IN_UNIV]; 
  SUBGOAL_THEN `!(f:num->real). support (+) f (:num) = 
  support (+) f (support (+) f (:num))` (fun th -> ONCE_REWRITE_TAC [th])
  THENL [REWRITE_TAC [SUPPORT_SUPPORT]; ALL_TAC] THEN
  ASM_SIMP_TAC [SUPPORT_MONOTONIC]]);;






