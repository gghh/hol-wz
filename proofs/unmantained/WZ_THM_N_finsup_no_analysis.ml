(* -*- holl -*- *)

(* ====================================================================== *)
(* ||                                                                  || *)
(* ||              In this file I prove the WZ theorem.                || *)
(* ||       The sum environment is (:num), the "WZ pair" functions     || *)
(* ||                  have type :num->num->real.                      || *)
(* ||                                                                  || *)
(* ||     This approach turned out to be a dead end road in order      || *)
(* ||    to write a HOL tactic that prove combinatorial identities     || *)
(* ||   using the WZ-method, so I don't mantain this file any more.    || *)
(* ||                                                                  || *)
(* ||     Giovanni Gherdovich, gherdovich@students.math.unifi.it       || *)
(* ||       Universita` degli Studi di Firenze, december 2006          || *)
(* ||                                                                  || *)
(* ====================================================================== *)

needs "finite_support.ml";;

let TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

(* ---------------------------------------------------------------------- *)
(*             This semplifies telescopic sums (by Harrison)              *)
(* ---------------------------------------------------------------------- *)

let SUM_DIFFS = prove
 (`!a m n. m <= n + 1 ==> sum(m..n) (\i. a(i + 1) - a(i)) = a(n + 1) - 
a(m)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG] THENL
   [REWRITE_TAC[ARITH_RULE `m <= 0 + 1 <=> m = 0 \/ m = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ARITH; ADD_CLAUSES; REAL_SUB_REFL];
    SIMP_TAC[ARITH_RULE `m <= SUC n + 1 <=> m <= n + 1 \/ m = SUC n + 
1`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[ADD1] THENL [REAL_ARITH_TAC; ALL_TAC] 
THEN
    REWRITE_TAC[REAL_SUB_REFL; ARITH_RULE `~((n + 1) + 1 <= n + 1)`] 
THEN
    MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ARITH_TAC]);;

(* ---------------------------------------------------------------------- *)
(*       If g makes f telescopic, this theorem links their supports       *)
(* ---------------------------------------------------------------------- *)

let FINITE_SUPPORT_TELESEQ = prove
(`!f:num->real g:num->real a:num. 
  (!n. f n = g (n + 1) - g n) /\ 
  FINITE (support (+) g (:num)) /\
  (!k. a < k ==> f k = &0)
    ==> (!j. a < j ==> g j = &0)`,
 REPEAT STRIP_TAC THEN
(* g is definitively constant *)
 SUBGOAL_THEN `!m:num. (g:num->real) (a+1+m) = g (a+1)` ASSUME_TAC THENL
 [INDUCT_TAC THENL 
  [ARITH_TAC; 
  UNDISCH_TAC `!n. (f:num->real) n = g (n + 1) - g n` THEN
  REWRITE_TAC [REAL_ARITH `!a:real b c. a = b - c <=> b = a + c`] THEN DISCH_TAC
  THEN REWRITE_TAC [GSYM ADD1] THEN 
  REWRITE_TAC [ARITH_RULE `a + 1 + SUC m = (a + 1 + m) + 1`] THEN ASM_REWRITE_TAC []
  THEN SUBGOAL_THEN `(f:num->real) (a + 1 + m) = &0`
  (fun th -> REWRITE_TAC [th])
  THENL [UNDISCH_TAC `!k:num. a < k ==> (f:num->real) k = &0` THEN
  SIMP_TAC [ARITH_RULE `a < a + 1 + m`]; ALL_TAC] THEN REWRITE_TAC [REAL_ADD_LID]
  THEN ASM_REWRITE_TAC [ADD1]]; ALL_TAC] THEN
 SUBGOAL_THEN `j:num = a + 1 + (j - (a + 1))`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [UNDISCH_TAC `a:num < j` THEN
  ARITH_TAC; ALL_TAC] THEN
 ASM_REWRITE_TAC [] THEN UNDISCH_TAC `FINITE (support (+) (g:num->real) (:num))`
 THEN REWRITE_TAC [num_FINITE; IN_SUPPORT; IN_UNIV; NEUTRAL_REAL_ADD]
 THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
 ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
 STRIP_TAC THEN REWRITE_TAC [NOT_FORALL_THM] THEN
 REWRITE_TAC [NOT_IMP] THEN EXISTS_TAC `a + 1 + a'` THEN ASM_REWRITE_TAC []
 THEN ARITH_TAC);;

(* ---------------------------------------------------------------------- *)
(*     If g makes f telescopic and x is out of the support of f, is out   *)
(*      of the support of g supporto di f, x non e` nel supporto di g     *)
(* ---------------------------------------------------------------------- *)

let NOT_IN_SUPP_TELESEQ = prove
(`!f:num->real g:num->real a:num b:num. 
  (!n. f n = g (n + 1) - g n) /\ 
  support (+) f (:num) SUBSET (0..b) /\
  FINITE (support (+) g (:num))
    ==> 
    (!x:num. ~(x IN (0..b)) ==> g x = &0)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 REWRITE_TAC [IN_NUMSEG; LE_0; ARITH_RULE `!s:num t. ~(s <= t) <=> (t < s)`]
 THEN MATCH_MP_TAC FINITE_SUPPORT_TELESEQ THEN
 EXISTS_TAC `f:num->real` THEN
 CONJ_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN
 CONJ_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN
 GEN_TAC THEN UNDISCH_TAC `support (+) (f:num->real) (:num) SUBSET 0..b` THEN
 REWRITE_TAC [SUBSET; IN_SUPPORT; NEUTRAL_REAL_ADD; IN_UNIV;
  IN_NUMSEG; LE_0] THEN
 ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
 REWRITE_TAC [NOT_IMP] THEN STRIP_TAC THEN REWRITE_TAC [NOT_FORALL_THM; NOT_IMP]
 THEN EXISTS_TAC `k:num` THEN
 FIRST_X_ASSUM MP_TAC THEN FIRST_X_ASSUM MP_TAC THEN ARITH_TAC);;

(* ---------------------------------------------------------------------- *)
(*                         This is half the WZ proof                      *)
(* ---------------------------------------------------------------------- *)

let num_FINSUP_SUM_NUM_TELESEQ = prove
(`!(f:num->real) g. 
  FINITE (support (+) f (:num)) /\ 
  f = (\i. g(i + 1) - g(i)) /\
  FINITE (support (+) g (:num))
    ==> sum (:num) f = -- g(0)`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN
 UNDISCH_TAC `FINITE (support (+) (f:num->real) (:num))` THEN
 REWRITE_TAC [num_FINITE] THEN STRIP_TAC THEN
 SUBGOAL_THEN `support (+) (f:num->real) (:num) SUBSET (0..a+1)` ASSUME_TAC
  THENL [REWRITE_TAC [SUBSET; IN_NUMSEG; LE_0] THEN
  ASM_SIMP_TAC [ARITH_RULE `!x:num a. x <= a ==> x <= a + 1`]; ALL_TAC]
 THEN SUBGOAL_THEN `sum (:num) f = sum (0..a+1) f`
  (fun th -> REWRITE_TAC [th]) THENL [MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC SUPPORT_SUBSET_NUMSEG THEN ASM_REWRITE_TAC []; ALL_TAC]
 THEN ASM_REWRITE_TAC [] THEN SUBGOAL_THEN `0 <= (a + 1) + 1` ASSUME_TAC
  THENL [ARITH_TAC; ALL_TAC] THEN
 ASM_SIMP_TAC [SUM_DIFFS] THEN
 REWRITE_TAC [REAL_ARITH `!A:real b. a - b = --b <=> a = &0`] THEN
 SUBGOAL_THEN `~((a+1)+1 IN 0..a+1)` ASSUME_TAC THENL
  [REWRITE_TAC [IN_NUMSEG; LE_0] THEN ARITH_TAC; ALL_TAC]
 THEN POP_ASSUM MP_TAC THEN ABBREV_TAC `h = (a + 1) + 1` THEN
 SPEC_TAC (`h:num`, `h:num`) THEN
 MATCH_MP_TAC NOT_IN_SUPP_TELESEQ THEN EXISTS_TAC `f:num->real`
 THEN CONJ_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC]
 THEN CONJ_TAC THENL [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

(* ---------------------------------------------------------------------- *)
(*                     When a sequence is constant?                       *)
(* ---------------------------------------------------------------------- *)

let SEQ_CONST_TEST = prove
(`!f. (!n. f (SUC n) - f n = real_of_num 0)
    ==> !n. f n = f 0`,
 STRIP_TAC THEN DISCH_TAC THEN
 INDUCT_TAC THENL [REWRITE_TAC [EQ_REFL];
 SUBGOAL_THEN `!n. (f:num->real) (SUC n) = f n` (fun th -> REWRITE_TAC [th])
  THENL [ONCE_REWRITE_TAC [GSYM REAL_SUB_0] THEN ASM_REWRITE_TAC [];
  ASM_REWRITE_TAC []]]);;

(* ---------------------------------------------------------------------- *)
(*                              The WZ Theorem                            *)
(* ---------------------------------------------------------------------- *)

g `!U:num->num->real. 
  (?G:num->num->real.
         (!n. FINITE (support (+) (\k. U n k) (:num))) /\
         (!n. FINITE (support (+) (\k. G n k) (:num))) /\
         (!n k. (U (SUC n) k) - (U n k) = (G n (k + 1)) - (G n k)) /\
	 sum (:num) (\k. U 0 k) = (real_of_num 1) /\
         (!n. G n 0 = real_of_num 0))
  ==> (sum (:num) (\k. U n k) = (real_of_num 1))`;;
e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `&1 = sum (:num) (\k. U 0 k)` (fun th -> REWRITE_TAC [th])
  THENL [MATCH_MP_TAC (EQ_SYM) THEN ASM_REWRITE_TAC []; ALL_TAC]);;
e (SPEC_TAC (`n:num`, `n:num`));;
e (MATCH_MP_TAC SEQ_CONST_TEST);;
e (ONCE_REWRITE_TAC [GSYM SUM_SUPPORT]);;
e (GEN_TAC);;
e (TRANS_TAC `
  sum 
    (support (+) (\k. U (SUC n) k) (:num) UNION 
    support (+) (\k. U n k) (:num)) 
      (\k. U (SUC n) k) -
  sum 
    (support (+) (\k. U n k) (:num) UNION 
    support (+) (\k. U (SUC n) k) (:num)) 
      (\k. U n k)`);;
e (REWRITE_TAC [GSYM SUM_SUPPORT_UNION_num]);;
e (SUBGOAL_THEN `!U:num->num->real.
  (support (+) (\k. U (SUC n) k) (:num) UNION support (+) (\k. U n k) (:num)) = 
  (support (+) (\k. U n k) (:num) UNION support (+) (\k. U (SUC n) k) (:num))`
  (fun th -> REWRITE_TAC [th])  THENL 
  [GEN_TAC THEN REWRITE_TAC [SET_RULE `!s t. s UNION t = t UNION s`]; ALL_TAC]);;
e (SUBGOAL_THEN 
  `FINITE 
  (support (+) (\k. (U:num->num->real) n k) (:num) UNION 
  support (+) (\k. U (SUC n) k) (:num))`
  ASSUME_TAC THENL [ASM_REWRITE_TAC [FINITE_UNION]; ALL_TAC]);;
e (TRANS_TAC `sum
 (support (+) (\k. U n k) (:num) UNION support (+) (\k. U (SUC n) k) (:num))
 (\k. U (SUC n) k - U n k)` THENL [MATCH_MP_TAC (GSYM SUM_SUB) THEN
 ASM_REWRITE_TAC []; ALL_TAC]);;
e (TRANS_TAC `
  sum
    (support (+) (\k. U (SUC n) k - U n k) (:num))
    (\k. U (SUC n) k - U n k)` THENL [MATCH_MP_TAC SUM_SUPERSET_SUPPORT_num THEN
ONCE_REWRITE_TAC [SET_RULE `!s t. s UNION t = t UNION s`] THEN REWRITE_TAC [SUPPORT_SUB_num];
ALL_TAC]);;
e (REWRITE_TAC [SUM_SUPPORT]);;
e (TRANS_TAC `-- (G:num->num->real) n 0`);; 
e (MATCH_MP_TAC num_FINSUP_SUM_NUM_TELESEQ);;
e (CONJ_TAC);;
e (MATCH_MP_TAC FINITE_SUPPORT_SUB_num);;
e (ASM_REWRITE_TAC []);;
e (ASM_REWRITE_TAC []);;
e (ASM_REWRITE_TAC []);;
e (REAL_ARITH_TAC);;
let num_WZ_THM = top_thm();;
