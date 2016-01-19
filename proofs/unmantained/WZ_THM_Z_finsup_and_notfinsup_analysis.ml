(* -*- holl -*- *)

(* ====================================================================== *)
(* ||                                                                  || *)
(* ||              In this file I prove the WZ theorem.                || *)
(* ||            I use exactly the proof strategy by Wilf and          || *)
(* ||            Zeilberg (real analysis and limit), and I do it       || *)
(* ||            in two steps: first, I build up a convergence         || *)
(* ||            definition for sums over the integers, then           || *)
(* ||            I specialize the result to the finite support         || *)
(* ||            case.                                                 || *)
(* ||                                                                  || *)
(* ||            The "WZ pair" functions have type :num->int->real.    || *)
(* ||                                                                  || *)
(* ||               This approach turned out to be a dead              || *)
(* ||            end road in order to write a WZ_TACTIC, so            || *)
(* ||            I don't mantain this file any more.                   || *)
(* ||                                                                  || *)
(* ||     Giovanni Gherdovich, gherdovich@students.math.unifi.it       || *)
(* ||       Universita` degli Studi di Firenze, december 2006          || *)
(* ||                                                                  || *)
(* ====================================================================== *)

needs "finite_support.ml";;
needs "/home/giovanni/hol_light/Examples/analysis.ml";;

(* I cannot invert the order of loading of these files, because
Example/analysis redefines "sum" *)

let TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

(* ---------------------------------------------------------------------- *)
(*                                                                        *)
(*   Now I build the sum environment, copying from Examples/analysis.ml,  *)
(*   line 4151 and following                                              *)
(*                                                                        *)
(* ---------------------------------------------------------------------- *)

parse_as_infix ("zums", (12, "right"));;
parse_as_infix ("tends_num_real", (12, "right"));;

(* ---------------------------------------------------------------------- *)
(*                   Definitions about the sum over Z                     *)
(* ---------------------------------------------------------------------- *)

let zums = new_definition
  `(f:int->real) zums s <=> (\n:num. sum(0..n)(\i. f (int_of_num i)) + 
  sum(1..n)(\i. f (int_neg (int_of_num i)))) tends_num_real s`;;

let zummable = new_definition
  `zummable f <=> ?s. f zums s`;;

let zuminf = new_definition
  `zuminf f = @s. f zums s`;;

(* ---------------------------------------------------------------------- *)
(*                  Useful theorems about the sum over Z                  *)
(* ---------------------------------------------------------------------- *)

let ZUM_ZUMMABLE = prove(
  `!f l. f zums l ==> zummable f`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[zummable] THEN
  EXISTS_TAC `l:real` THEN POP_ASSUM ACCEPT_TAC);;

let ZUMMABLE_ZUM = prove(
  `!f. zummable f ==> f zums (zuminf f)`,
  GEN_TAC THEN REWRITE_TAC[zummable; zuminf] THEN
  DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV ETA_CONV) THEN
  MATCH_ACCEPT_TAC SELECT_AX);;

let ZUM_UNIQ = prove
(`!f x. f zums x ==> (x = zuminf f)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `zummable f` MP_TAC THENL [MATCH_MP_TAC ZUM_ZUMMABLE THEN
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP ZUMMABLE_ZUM) THEN MATCH_MP_TAC SEQ_UNIQ
  THEN EXISTS_TAC `(\n:num. sum(0..n)(\i. f (int_of_num i)) + 
  sum(1..n)(\i. f (int_neg (int_of_num i))))` THEN ASM_REWRITE_TAC [GSYM zums]);;

let Z_SER_UNIQ = prove
(`!f x y. f zums x /\ f zums y ==> (x = y)`, MESON_TAC [ZUM_UNIQ]);;

let Z_SER_SUB = prove
(`!x:int->real x0 y y0. x zums x0 /\ y zums y0 ==> (\n. x(n) - y(n)) zums (x0 - y0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC [zums; SUM_SUB_NUMSEG] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\n. sum (0..n) (\i. x (int_of_num i)) -
                 sum (0..n) (\i. y (int_of_num i)) +
          sum (1..n) (\i. x (-- &i)) - sum (1..n) (\i. y (-- &i))) = 
	  (\n. (\j. sum (0..j) (\i. x (&i)) + sum (1..j) (\i. x (-- &i))) n -
 	  (\j. sum (0..j) (\i. y (&i)) + sum (1..j) (\i. y (-- &i))) n)`
	  (fun th -> PURE_REWRITE_TAC [th]) THENL
    [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [SEQ_SUB]);;

let ZUMINF_SUB = prove
(`!f g. (zummable f /\ zummable g) ==>
    zuminf f - zuminf g = zuminf (\j. f j - g j)`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\n. f n - g n) zums (zuminf f - zuminf g)` ASSUME_TAC THENL
    [ASM_SIMP_TAC [ZUMMABLE_ZUM; Z_SER_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN `zummable (\n. f n - g n)` ASSUME_TAC THENL
    [MATCH_MP_TAC ZUM_ZUMMABLE THEN EXISTS_TAC `zuminf f - zuminf g` THEN
    ASM_REWRITE_TAC []; ALL_TAC] THEN MATCH_MP_TAC ZUM_UNIQ THEN
  ASM_REWRITE_TAC []);;

(* ------------------------------------------------------ *)
(*          Some lemmas to lighten the WZ proof           *)
(* ------------------------------------------------------ *)

let WZ_SEQ_CONST_TEST = prove
(`!f. (!n. f (SUC n) - f n = real_of_num 0)
    ==> ?b:real. !n. f n = b`,
  STRIP_TAC THEN DISCH_TAC THEN EXISTS_TAC `(f:num->real) 0` THEN
  INDUCT_TAC THENL [REWRITE_TAC [EQ_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. (f:num->real) (SUC n) = f n` (fun th -> REWRITE_TAC [th])
    THENL [ONCE_REWRITE_TAC [GSYM REAL_SUB_0] THEN ASM_REWRITE_TAC []; ALL_TAC]
  THEN ASM_REWRITE_TAC []);;

let WZ_lemma1 = prove
(`!U:num->int->real. 
  (!n. zummable (\k. U n k)) /\ (?a:real. !n.(\n. zuminf (\k. U n k)) n = a) 
    ==>  (?a:real. !n. (\k. U n k) zums a)`,
  REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN STRIP_TAC THEN
  REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!n. (\k. U n k) zums zuminf (\k. U 0 k)` ASSUME_TAC THENL
    [INDUCT_TAC THENL
      [ASM_SIMP_TAC [ZUMMABLE_ZUM];
      SUBGOAL_THEN `zuminf (\k:int. U 0 k) = zuminf (\k. U (SUC n) k)`
      (fun th -> REWRITE_TAC [th]) THENL
        [TRANS_TAC `a:real` THENL
          [ASM_REWRITE_TAC [EQ_SYM]; ASM_REWRITE_TAC []]; ALL_TAC] THEN
       ASM_SIMP_TAC [ZUMMABLE_ZUM]];
     ALL_TAC] THEN
  EXISTS_TAC `zuminf (\k:int. U 0 k)` THEN ASM_REWRITE_TAC []);;

let WZ_lemma2 = prove
(`int_neg (int_of_num(SUC (N + M))) + int_of_num 1 = int_neg (int_of_num (N + M))`,
  REWRITE_TAC [ADD1; GSYM INT_OF_NUM_ADD; INT_NEG_ADD] THEN ARITH_TAC);;

let WZ_lemma3 = prove
(`f tends_num_real (real_of_num 0) <=>
  f tends_num_real (real_of_num 0 + real_of_num 0)`,
  REWRITE_TAC [INST [`real_of_num 0`, `x:real`] (SPEC_ALL REAL_ADD_LID)]);;

let WZ_lemma4 = prove
(`f tends_num_real (real_neg (real_of_num 0)) <=> f tends_num_real (real_of_num 0)`,
  REWRITE_TAC [REAL_ARITH `real_neg (real_of_num 0) = real_of_num 0`]);;

(* ---------------------------------------------------------------------- *)
(*                  Theorems about telescopic sums over Z                 *)
(* ---------------------------------------------------------------------- *)

let WZ_TELESEQ1 = prove
(`!f:int->real N M. sum (N..N+M) 
  (\n. f (int_add (int_of_num n) (int_of_num 1)) - f (int_of_num n)) = 
    f (int_of_num (SUC (M + N))) - f (int_of_num N)`,
  GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [ADD_CLAUSES; SUM_SING_NUMSEG; INT_OF_NUM_ADD; ADD1];
  ONCE_REWRITE_TAC [ADD_AC] THEN
  REWRITE_TAC [ADD_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH_RULE `N <= SUC (M + N)`] THEN
  ONCE_REWRITE_TAC [ADD_AC] THEN 
  ASM_REWRITE_TAC [REAL_ARITH `a:real - b = a + (--b)`;
  REAL_ARITH `((a:real) + b) + (c + d) = b + c + a + d`;
  ARITH_RULE `SUC (M + N)  = SUC (N + M)`; REAL_ADD_RINV; REAL_ADD_RID;
  INT_OF_NUM_ADD; ADD1] THEN REAL_ARITH_TAC]);;

let WZ_TELESEQ2 = prove
(`!f:int->real N M. sum (N..N+M) 
  (\n. f (int_add (int_neg (int_of_num n)) (int_of_num 1))
    - f (int_neg (int_of_num n))) = 
  f (int_add (int_neg (int_of_num N)) (int_of_num 1)) 
    - f (int_neg (int_of_num (N+M)))`,
  GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [ADD_CLAUSES; SUM_SING_NUMSEG];
  ONCE_REWRITE_TAC [ADD_AC] THEN
  REWRITE_TAC [ADD_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH_RULE `N <= SUC (M + N)`]
  THEN ONCE_REWRITE_TAC [ADD_AC] THEN ASM_REWRITE_TAC
  [REAL_ARITH `a:real - b = a + (--b)`; WZ_lemma2;
  REAL_ARITH `((a:real) + b) + (c + d) = a + (b + c) + d`;
  REAL_ADD_LINV; REAL_ADD_LID]]);;

let WZ_TELESEQ2_bis = prove
(`!f:int->real. sum (1..n) 
  (\n. f (int_add (int_neg (int_of_num n)) (int_of_num 1))
    - f (int_neg (int_of_num n))) = 
  f (int_of_num 0)  - f (int_neg (int_of_num (n)))`,
  ASM_CASES_TAC `n:num = 0` THENL [GEN_TAC THEN
  ASM_REWRITE_TAC [ARITH_RULE `int_neg(int_of_num 0) = int_of_num 0`;
  REAL_SUB_REFL] THEN MATCH_MP_TAC SUM_TRIV_NUMSEG THEN ARITH_TAC; ALL_TAC]
  THEN GEN_TAC THEN
  SUBGOAL_THEN `n:num = 1 + n - 1` ASSUME_TAC THENL
    [FIRST_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:int->real) (&0) - f (-- &n) = f (&0) - f (-- &(1 + n - 1))`
  (fun th -> REWRITE_TAC[th]) THENL
    [REWRITE_TAC [REAL_ARITH `a:real - b = a - c <=> b = c`] THEN
    (REPEAT AP_TERM_TAC) THEN (FIRST_ASSUM MP_TAC) THEN MESON_TAC []; ALL_TAC]
 THEN REWRITE_TAC [
    GSYM(
        REWRITE_RULE 
    	    [ARITH_RULE `int_neg (int_of_num 1) + int_of_num 1 = int_of_num 0`; 
	     ARITH_RULE `int_neg (int_of_num 0) + int_of_num 1 = int_of_num 1`] 
   	        (GEN `f:int->real` 
		    (INST [`f:int->real`, `f:int->real`; `1`, `N:num`; `n - 1`, `M:num`] 
		        (SPEC_ALL WZ_TELESEQ2))))] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC []);;

(* ---------------------------------------------------------------------- *)
(*                 The WZ proof, from the book "A = B"                    *)
(* ---------------------------------------------------------------------- *)

g `!U:num->int->real. 
  (?G:num->int->real.(!n. zummable (\k. U (SUC n) k)) /\
                     (!n. zummable (\k. U n k)) /\ 
                     (!n. (\i. (G n) (int_of_num i)) tends_num_real (real_of_num 0)) /\
                     (!n. (\i. (G n) (int_neg (int_of_num i))) tends_num_real (real_of_num 0)) /\
                     !n k. (U (SUC n) k) - (U n k) = (G n (int_add k (int_of_num 1))) - (G n k))
  ==> ?a:real. !n. (\k. U n k) zums a`;;
e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC WZ_lemma1);;
e (CONJ_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC]);;
e (MATCH_MP_TAC WZ_SEQ_CONST_TEST);;
e (ASM_SIMP_TAC [ZUMINF_SUB]);;
e (GEN_TAC);;
e (MATCH_MP_TAC (GSYM ZUM_UNIQ));;
e (REWRITE_TAC [zums]);;
e (REWRITE_TAC [
    REWRITE_RULE 
        [ARITH_RULE `0 + n = n`; ARITH_RULE `n + 0 = n`] 
            (GEN `f:int->real` 
                (INST [`f:int->real`, `f:int->real`; `0`, `N:num`; `n:num`, `M:num`] 
                    (SPEC_ALL WZ_TELESEQ1)))]);;
e (REWRITE_TAC [WZ_TELESEQ2_bis; REAL_ARITH `a:real - b = a + (--b)`;
  REAL_ARITH `((a:real) + --b) + b + --c = a + --c`; WZ_lemma3]);;
e (MATCH_MP_TAC SEQ_ADD);;
e (CONJ_TAC THENL [ASM_REWRITE_TAC [GSYM SEQ_SUC];
  ASM_REWRITE_TAC [GSYM WZ_lemma4; GSYM SEQ_NEG]]);;
let WZ_THM = top_thm();;

(* ---------------------------------------------------------------------- *)
(*                  I generalize SEQ_SUC for f:num->real                  *)
(* ---------------------------------------------------------------------- *)

let SAME_BEHAVIOR_bis = prove
(`!(f:num->real) (l:real) (N:num). (\n. f(n + N)) tends_num_real l
  ==> f tends_num_real l`,
 GEN_TAC THEN GEN_TAC THEN
 INDUCT_TAC THENL [REWRITE_TAC [ARITH_RULE `n + 0 = n`; ETA_AX];
  SUBGOAL_THEN `(\n. (f:num->real)(n + SUC N)) = (\n. (\k. f(k + N))(SUC n))`
  (fun th -> PURE_REWRITE_TAC [th]) THENL
  [BETA_TAC THEN REWRITE_TAC [ADD_CLAUSES]; ALL_TAC] THEN
  ASM_REWRITE_TAC [GSYM SEQ_SUC]]);;

(* ---------------------------------------------------------------------- *)
(*         Se f:num->real is definitively constant, has a limit           *)
(* ---------------------------------------------------------------------- *)

let SEQ_DEFINITIVELY_CONST = prove
(`!(f:num->real). (?M a. !n. M <= n ==> f n = a) ==> 
  ?l. f tends_num_real l`,
 REPEAT STRIP_TAC THEN EXISTS_TAC `a:real` THEN
 MATCH_MP_TAC 
  (SPECL [`f:num->real`; `a:real`; `M:num`] SAME_BEHAVIOR_bis) THEN
  SUBGOAL_THEN `(\n. (f:num->real)(n + M)) = (\n. a)` 
  (fun th -> REWRITE_TAC [th]) THENL
  [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
  ASM_SIMP_TAC [ARITH_RULE `!(M:num) x. M <= x + M`]; ALL_TAC] THEN
 REWRITE_TAC [SEQ_CONST]);;

(* ---------------------------------------------------------------------- *)
(*            If f has finite support, his limit is zero                  *)
(* ---------------------------------------------------------------------- *)

let FINITE_SUPPORT_TENDS_ZERO = prove
(`!(f:num->real). FINITE (support (+) f (:num)) ==> f tends_num_real (&0:real)`,
  GEN_TAC THEN
  REWRITE_TAC [num_FINITE; support; IN_UNIV; NEUTRAL_REAL_ADD; IN_ELIM_THM]
  THEN REPEAT STRIP_TAC THEN REWRITE_TAC [SEQ] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `SUC a` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:num->real) n = &0` (fun th -> REWRITE_TAC [th]) THENL
    [FIRST_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [TAUT `!P Q. P ==> Q <=> ~Q ==> ~P`]
    THEN ASM_REWRITE_TAC [ARITH_RULE `~(n >= SUC a) <=> (n <= a)`]; ALL_TAC]
  THEN ASM_REWRITE_TAC [REAL_ARITH `abs (&0 - &0) = &0`]);;

(* ---------------------------------------------------------------------- *)
(*                 If f has finite support, is "zummable"                 *)
(* ---------------------------------------------------------------------- *)

let FINITE_SUPPORT_ZUMMABLE = prove
(`!f:int->real. FINITE (support (+) f (:int)) ==> zummable f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [zummable; zums] THEN
  MATCH_MP_TAC SEQ_DEFINITIVELY_CONST THEN
  SUBGOAL_THEN
  `(\n. sum (0..n) (\i. f (&i:int)) + sum (1..n) (\i. f (-- (&i:int)))) = 
  (\n. f (int_of_num 0) + sum (1..n) (\i. f (int_of_num i)) +
  sum (1..n) (\i. f (-- &i)))`
  (fun th -> PURE_REWRITE_TAC [th]) THENL
    [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC [REAL_ARITH `!(a:real) b c d. a + b = c + d + b 
    <=> a + b = (c + d) + b`] THEN REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
    ONCE_REWRITE_TAC [ARITH_RULE `1 = 0 + 1`] THEN
    MATCH_MP_TAC SUM_CLAUSES_LEFT THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC [GSYM SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN `FINITE (support (+) 
  (\i:num. (f:int->real) (int_of_num i) + f (-- int_of_num i)) (:num))` ASSUME_TAC
    THENL [SUBGOAL_THEN `(\i:num. (f:int->real) (&i) + f (-- &i)) = 
    (\i. f (i) + f (-- i)) o int_of_num` (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [o_DEF]; ALL_TAC] THEN MATCH_MP_TAC FINITE_SUPPORT_COMPOS THEN
    CONJ_TAC THENL 
      [SUBGOAL_THEN `(\i. f i + (f:int->real)(int_neg i)) =
      (\i. f i + (f o int_neg) i)`
      (fun th -> REWRITE_TAC [th]) THENL [REWRITE_TAC [o_DEF]; ALL_TAC]
      THEN MATCH_MP_TAC FINITE_SUPPORT_SUM_INJ THEN ASM_REWRITE_TAC [INJ; IN_UNIV]
      THEN ARITH_TAC; REWRITE_TAC [INJ; IN_UNIV; INT_OF_NUM_EQ]]; ALL_TAC] THEN
  ONCE_REWRITE_TAC [GSYM SUM_SUPPORT] THEN
  SUBGOAL_THEN `?(S:num). !x:num. x IN (support (+) 
  (\i:num. (f:int->real) (&i:int) + f (-- &i)) (:num)) ==> S >= x` ASSUME_TAC THENL
  [ASM_REWRITE_TAC [ARITH_RULE `S:num >= x <=> x <= S`; GSYM num_FINITE]; ALL_TAC]
  THEN FIRST_X_ASSUM MP_TAC THEN REPEAT STRIP_TAC THEN EXISTS_TAC `S:num` THEN
  EXISTS_TAC `(f:int->real) (&0) +
             sum (support (+) (\i. f (&i) + f (-- &i)) (1..S))
             (\i. f (&i) + f (-- &i))` THEN REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(1..n) = (1..S) UNION (S+1..n)` (fun th -> REWRITE_TAC [th]) THENL
    [ASM_CASES_TAC `S = 0` THENL 
      [ASM_REWRITE_TAC [ARITH_RULE `0 + 1 = 1`; NUMSEG_CLAUSES;
      ARITH_RULE `~(1 = 0)`] THEN SET_TAC []; ALL_TAC]
    THEN MATCH_MP_TAC (GSYM NUMSEG_COMBINE_R) THEN ASM_REWRITE_TAC [] THEN
    FIRST_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC [SUPPORT_CLAUSES] THEN
  SUBGOAL_THEN
  `support (+) (\i:num. (f:int->real) (&i) + f (-- &i)) (S + 1..n) = {}`
  (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [support; NEUTRAL_REAL_ADD] THEN
    MATCH_MP_TAC (SET_RULE `(!x:A. ~(P x)) ==> {x | P x} = {}`) THEN
    REWRITE_TAC [TAUT `~(P /\ ~Q) <=> ~Q ==> ~P`] THEN
    GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN support (+) (\i:num. (f:int->real) (&i) + f (-- &i)) (:num)`
    ASSUME_TAC THENL 
      [ASM_REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD; IN_ELIM_THM]; ALL_TAC]
    THEN SUBGOAL_THEN `S:num >= x` ASSUME_TAC THENL [FIRST_X_ASSUM MP_TAC
    THEN ASM_REWRITE_TAC []; ALL_TAC] THEN FIRST_ASSUM MP_TAC THEN
    REWRITE_TAC [IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  SET_TAC []);;

(* ---------------------------------------------------------------------- *)
(*   I need some other lemmas to specify the WZ theorem I've proved to    *)
(*                     the finite support case                            *)
(* ---------------------------------------------------------------------- *)

let WZ_lemma5 = prove
(`(?a:A. !n:num. f n = a) ==> !n. f n = f 0`,
  STRIP_TAC THEN
  INDUCT_TAC THENL [ASM_REWRITE_TAC [];
    TRANS_TAC `a:A` THENL [ASM_REWRITE_TAC []; 
    REWRITE_TAC [EQ_SYM] THEN ASM_REWRITE_TAC []]]);;

let WZ_lemma6 = prove
(`(?a:A. !n:num. f n = a) /\ f 0 = b ==> !n. f n = b`,
  STRIP_TAC THEN GEN_TAC THEN
  TRANS_TAC `(f:num->A) 0` THENL
    [SUBGOAL_THEN `!n:num. (f:num->A) n = f 0` ASSUME_TAC THENL
    [MATCH_MP_TAC WZ_lemma5 THEN EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []; ASM_REWRITE_TAC []]);;

let WZ_lemma7 = prove
(`!f:int->real. zummable f /\ zuminf f = (&1:real)
  ==> f zums (&1:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&1:real) = zuminf f` (fun th -> REWRITE_TAC [th])
  THENL [ASM_REWRITE_TAC [EQ_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC ZUMMABLE_ZUM THEN ASM_REWRITE_TAC []);;

(* ---------------------------------------------------------------------- *)
(*                The WZ theorem with stronger hypotesis:                 *)
(*              first, I ask that the identity holds for a value          *)
(*              then I ask for finite support functions                   *)
(* ---------------------------------------------------------------------- *)

g `!U:num->int->real. 
  (?G:num->int->real.(!n. zummable (\k. U (SUC n) k)) /\
                     (!n. zummable (\k. U n k)) /\ 
                     (!n. (\i. (G n) (int_of_num i)) tends_num_real (real_of_num 0)) /\
                     (!n. (\i. (G n) (int_neg (int_of_num i))) tends_num_real (real_of_num 0)) /\
                  (!n k. (U (SUC n) k) - (U n k) = (G n (int_add k (int_of_num 1))) - (G n k)) /\
		     (\k. U 0 k) zums (real_of_num 1))
  ==> (!n. (\k. U n k) zums (real_of_num 1))`;;

e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `(?a:real. !n:num. (\k:int. U n k) zums a)` ASSUME_TAC THENL
  [MATCH_MP_TAC WZ_THM THEN EXISTS_TAC `G:num->int->real` THEN
  ASM_REWRITE_TAC []; ALL_TAC]);;

e (MATCH_MP_TAC WZ_lemma7);;
e (ASM_REWRITE_TAC []);;
e (SUBGOAL_THEN `!n. zuminf (\k:int. U (n:num) k) = (&1:real)` (fun th -> REWRITE_TAC [th]));;
e (MATCH_MP_TAC WZ_lemma6);;
e (CONJ_TAC THENL
  [FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  STRIP_TAC THEN DISCH_TAC THEN EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC []
  THEN GEN_TAC THEN MATCH_MP_TAC (GSYM ZUM_UNIQ) THEN
  SUBGOAL_THEN `!n:num. (\k:int. U n k) zums a:real` (fun th -> REWRITE_TAC [th])
  THEN ASM_REWRITE_TAC []; MATCH_MP_TAC (GSYM ZUM_UNIQ) THEN ASM_REWRITE_TAC []]);;
let WZ_THM_bis = top_thm();;

g `!U:num->int->real. 
  (?G:num->int->real.(!n. FINITE (support (+) (\k. U n k) (:int))) /\
                     (!n. FINITE (support (+) (\k. G n k) (:int))) /\
                  (!n k. (U (SUC n) k) - (U n k) = (G n (int_add k (int_of_num 1))) - (G n k)) /\
		     (\k. U 0 k) zums (real_of_num 1))
  ==> (!n. (\k. U n k) zums (real_of_num 1))`;;

e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `!n. (\k. (U:num->int->real) n k) zums (real_of_num 1)`
  (fun th -> REWRITE_TAC [th]));;
e (MATCH_MP_TAC WZ_THM_bis);;
e (EXISTS_TAC `G:num->int->real`);;
e (REPEAT CONJ_TAC THENL
  [ASM_SIMP_TAC [FINITE_SUPPORT_ZUMMABLE];
  ASM_SIMP_TAC [FINITE_SUPPORT_ZUMMABLE];
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUPPORT_TENDS_ZERO THEN
    REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC FINITE_SUPPORT_COMPOS THEN
    CONJ_TAC THENL
      [FIRST_X_ASSUM MP_TAC THEN FIRST_X_ASSUM MP_TAC THEN FIRST_ASSUM MP_TAC THEN
      REWRITE_TAC [ETA_AX] THEN MESON_TAC [];
      REWRITE_TAC [INJ; IN_UNIV; INT_OF_NUM_EQ]];
    GEN_TAC THEN MATCH_MP_TAC FINITE_SUPPORT_TENDS_ZERO THEN
      REWRITE_TAC [GSYM o_DEF] THEN MATCH_MP_TAC FINITE_SUPPORT_COMPOS THEN
      CONJ_TAC 
        THENL [FIRST_X_ASSUM MP_TAC THEN FIRST_X_ASSUM MP_TAC
              THEN FIRST_ASSUM MP_TAC THEN REWRITE_TAC [ETA_AX] THEN MESON_TAC [];
              REWRITE_TAC [INJ; IN_UNIV; o_DEF] THEN ARITH_TAC];
  ASM_REWRITE_TAC [];
  ASM_REWRITE_TAC []]);;
let WZ_THM_FINSUPPORT = top_thm();;
