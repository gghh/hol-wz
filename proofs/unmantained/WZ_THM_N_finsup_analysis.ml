(* -*- holl -*- *)

(* ====================================================================== *)
(* ||                                                                  || *)
(* ||              In this file I prove the WZ theorem.                || *)
(* ||       The sum environment is (:num), the "WZ pair" functions     || *)
(* ||                  have type :num->num->real.                      || *)
(* ||                                                                  || *)
(* ||       The involved functions                                     || *)
(* ||       are required to have finite support, but here I use the    || *)
(* ||       same proof strategy of Wilf and Zeilberg: real analysis    || *)
(* ||       and limits. Now I prefer to use better the finite support  || *)
(* ||       hypotesis in order to avoid real analysis, so              || *)
(* ||       I don't mantain this file any more.                        || *)
(* ||                                                                  || *)
(* ||     Giovanni Gherdovich, gherdovich@students.math.unifi.it       || *)
(* ||       Universita` degli Studi di Firenze, december 2006          || *)
(* ||                                                                  || *)
(* ====================================================================== *)

needs "finite_support.ml";;

(* ---------------------------------------------------------------------- *)
(* |                                                                    | *)
           needs "/home/giovanni/hol_light/Examples/analysis.ml";;
(* |                                                                    | *)
(* | When I load this file, I miss a lot of theorems about sum in       | *)
(* | the file iter.ml bacause of a name conflict.                       | *)
(* |                                                                    | *)
            let SUM_SUB = prove
            (`!f g s. FINITE s ==>
            (sum s (\x. f(x) - g(x)) = sum s f - sum s g)`,
            CHEAT_TAC);;
(* |                                                                    | *)
(* | The only way is to use this dirty trick...                         | *)
(* ---------------------------------------------------------------------- *)

let TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

(* ---------------------------------------------------------------------- *)
(*              The link between infinite sums and sum (:num) f           *)
(* ---------------------------------------------------------------------- *)

let FINSUPPORT_SUM_NUM = prove
(`!(f:num->real) s. FINITE (support (+) f (:num)) /\ f sums s
    ==> sum (:num) f = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SER_UNIQ THEN
  EXISTS_TAC `f:num->real` THEN ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC `FINITE (support (+) f (:num))` THEN REWRITE_TAC [num_FINITE]
  THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sum (:num) f = sum (0..a) f` (fun th -> REWRITE_TAC [th])
    THENL [MATCH_MP_TAC (GSYM SUPPORT_SUBSET_NUMSEG) THEN 
    ASM_REWRITE_TAC [SUBSET; IN_NUMSEG; LE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(0..a) = {i | 0 <= i /\ i < 0 + (a + 1)}`
  (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [numseg; LE_0;
    SET_RULE `!s:A->bool t. s = t <=> (s SUBSET t /\ t SUBSET s)`;
    SUBSET; IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC [GSYM PSUM_SUM] THEN MATCH_MP_TAC SER_0 THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [IN_SUPPORT; NEUTRAL_REAL_ADD; IN_UNIV]
  THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `m:num > a` ASSUME_TAC 
    THENL [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [TAUT `!P Q. P ==> Q <=> ~Q ==> ~P`]
  THEN ASM_REWRITE_TAC [ARITH_RULE `!m:num a. ~(m > a) <=> m <= a`]);;

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
    SIMP_TAC[ARITH_RULE `m <= SUC n + 1 <=> m <= n + 1 \/ m = SUC n + 1`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[ADD1] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_REFL; ARITH_RULE `~((n + 1) + 1 <= n + 1)`] THEN
    MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ARITH_TAC]);;

(* ---------------------------------------------------------------------- *)
(*                         This is half the WZ proof                      *)
(* ---------------------------------------------------------------------- *)

let TELESEQ_SUMS_FIRST = prove
(`!f:num->real g. 
  f = (\i. g(i + 1) - g(i)) /\
  g tends_num_real (real_of_num 0)
    ==> f sums (-- g(0))`,
  REWRITE_TAC [sums; PSUM_SUM] THEN
  SUBGOAL_THEN `!f:num->real. (\n. sum {i | 0 <= i /\ i < 0 + n} f) = 
  (\n. if n = 0 then sum {} f else sum (0..n-1) f)`
  (fun th -> REWRITE_TAC [th]) THENL
    [GEN_TAC THEN REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
    ASM_CASES_TAC `x = 0` THENL [ASM_REWRITE_TAC [] THEN AP_THM_TAC
    THEN AP_TERM_TAC THEN REWRITE_TAC [numseg; LE_0;
    SET_RULE `!s:A->bool t. s = t <=> (s SUBSET t /\ t SUBSET s)`;
    SUBSET; IN_ELIM_THM; IN; EMPTY] THEN ARITH_TAC;
    ASM_REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC [numseg; LE_0; 
    SET_RULE `!s:A->bool t. s = t <=> (s SUBSET t /\ t SUBSET s)`;
    SUBSET; IN_ELIM_THM] THEN FIRST_ASSUM MP_TAC THEN ARITH_TAC]; ALL_TAC]
  THEN ONCE_REWRITE_TAC [SEQ_SUC] THEN BETA_TAC THEN
  REWRITE_TAC [NOT_SUC; ARITH_RULE `SUC n - 1 = n`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
  SIMP_TAC [ARITH_RULE `0 <= n + 1`; SUM_DIFFS] THEN
  REWRITE_TAC [REAL_ARITH `!a:real. -- a = &0 - a`] THEN MATCH_MP_TAC SEQ_SUB
  THEN ASM_REWRITE_TAC [SEQ_CONST; GSYM ADD1]);;

let FINSUP_SUM_NUM_TELESEQ = prove
(`!(f:num->real) g. 
  FINITE (support (+) f (:num)) /\ 
  f = (\i. g(i + 1) - g(i)) /\
  g tends_num_real (real_of_num 0)
    ==> sum (:num) f = -- g(0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `f sums -- g(0)` ASSUME_TAC THENL
    [MATCH_MP_TAC TELESEQ_SUMS_FIRST THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  MATCH_MP_TAC FINSUPPORT_SUM_NUM THEN ASM_REWRITE_TAC []);;

(* ---------------------------------------------------------------------- *)
(*          I use the finite support hypotesis just to say that           *)
(*                        zero is the limit point                         *)
(* ---------------------------------------------------------------------- *)

let FINITE_SUPPORT_TENDS_ZERO = prove
(`!(f:num->real). FINITE (support (+) f (:num)) ==> f tends_num_real (&0:real)`,
  GEN_TAC THEN REWRITE_TAC [num_FINITE; support; IN_UNIV;
  NEUTRAL_REAL_ADD; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN REWRITE_TAC [SEQ]
  THEN REPEAT STRIP_TAC THEN EXISTS_TAC `SUC a` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:num->real) n = &0` (fun th -> REWRITE_TAC [th]) THENL
    [FIRST_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [TAUT `!P Q. P ==> Q <=> ~Q ==> ~P`]
    THEN ASM_REWRITE_TAC [ARITH_RULE `~(n >= SUC a) <=> (n <= a)`]; ALL_TAC]
  THEN ASM_REWRITE_TAC [REAL_ARITH `abs (&0 - &0) = &0`]);;

(* ---------------------------------------------------------------------- *)
(*                     When a sequence is constant?                       *)
(* ---------------------------------------------------------------------- *)

let SEQ_CONST_TEST = prove
(`!f. (!n. f (SUC n) - f n = real_of_num 0)
    ==> !n. f n = f 0`,
  STRIP_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THENL [REWRITE_TAC [EQ_REFL];
    SUBGOAL_THEN `!n. (f:num->real) (SUC n) = f n` (fun th -> REWRITE_TAC [th])
      THENL [ONCE_REWRITE_TAC [GSYM REAL_SUB_0] THEN ASM_REWRITE_TAC []; ALL_TAC]
    THEN ASM_REWRITE_TAC []]);;

(* ---------------------------------------------------------------------- *)
(*                              The WZ Theorem                            *)
(* ---------------------------------------------------------------------- *)

g `!U:num->num->real. 
  (?G:num->num->real.
         (!n. FINITE (support (+) (\k. U n k) (:num))) /\
         (!n. (\k. G n k) tends_num_real &0) /\
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
e (SUBGOAL_THEN `
  (support (+) (\k. U (SUC n) k) (:num) UNION support (+) (\k. U n k) (:num)) = 
  (support (+) (\k. U n k) (:num) UNION support (+) (\k. U (SUC n) k) (:num))`
  (fun th -> REWRITE_TAC [th]) THENL 
  [REWRITE_TAC [SET_RULE `!s t. s UNION t = t UNION s`]; ALL_TAC]);;
e (SUBGOAL_THEN 
  `FINITE (support (+) (\k. U n k) (:num) UNION support (+) (\k. U (SUC n) k) (:num))`
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
e (MATCH_MP_TAC FINSUP_SUM_NUM_TELESEQ);;
e (CONJ_TAC);;
e (MATCH_MP_TAC FINITE_SUPPORT_SUB_num);;
e (ASM_REWRITE_TAC []);;
e (ASM_REWRITE_TAC []);;
e (ASM_REWRITE_TAC []);;
e (REAL_ARITH_TAC);;
let lim_WZ_THM_NUM = top_thm();;



