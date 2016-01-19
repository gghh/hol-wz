(* -*-holl-*- *)

(* ====================================================================== *)
(* ||                                                                  || *)
(* ||     In this file I build up binomial coefficients with           || *)
(* ||     both parameters integer number, and the tactics to           || *)
(* ||     semplify them.                                               || *)
(* ||                                                                  || *)
(* ||     Giovanni Gherdovich, gherdovich@students.math.unifi.it       || *)
(* ||       Universita` degli Studi di Firenze, december 2006          || *)
(* ||                                                                  || *)
(* ====================================================================== *)

needs "/home/giovanni/hol_light/Examples/binomial.ml";;
needs "finite_support.ml";;

(* ---------------------------------------------------------------------- *)
(*                        Useful tactics to start                         *)
(* ---------------------------------------------------------------------- *)

let TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

let REAL_FIELD_TAC = CONV_TAC REAL_FIELD;;

(* ---------------------------------------------------------------------- *)
(*         The tactic written by Harrison, that I use in a proof          *)
(* ---------------------------------------------------------------------- *)

let BINOM_TOP_STEP_TAC =
    let lemma = prove
     (`(~(k = n + 1) /\ ~(&n + &1 - &k = &0)) /\
       &(binom(n + 1,k)) = (&n + &1) / (&n + &1 - &k) * &(binom(n,k)) 
\/
       k = n + 1 /\ &(binom(n + 1,k)) = &1`,
      REWRITE_TAC[BINOM_TOP_STEP_REAL] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD] THEN
      REAL_ARITH_TAC) in
    let BINOM_MATCH = PART_MATCH (lhs o rand o lhand) lemma in
    fun (asl,w as gl) ->
      MAP_EVERY (DISJ_CASES_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
                                                  SUBST_ALL_TAC))
                (map BINOM_MATCH (find_terms (can BINOM_MATCH) w)) gl;;

(* ---------------------------------------------------------------------- *)
(*         Some linking lemmas between the various number systems         *)
(* ---------------------------------------------------------------------- *)

let real_num_int = prove
(`!(n:num) (k:int).
  (int_of_num n = k) <=> (real_of_num n = real_of_int k)`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL [DISCH_TAC THEN REWRITE_TAC [GSYM int_of_num_th] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC [];
  DISCH_TAC THEN REWRITE_TAC [int_eq] THEN TRANS_TAC `real_of_num n` THEN
  ASM_REWRITE_TAC [int_of_num_th]]);;

let NUM_OF_INT_ADD = prove
(`!(a:int) (b:int).
  &0 <= a /\ &0 <= b ==>
  num_of_int (a + b) = num_of_int a + num_of_int b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC [GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD]
  THEN SUBGOAL_THEN `&0 <= (a:int) + b` ASSUME_TAC THENL
    [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [INT_OF_NUM_OF_INT]);;

let REAL_OF_NUM_OF_INT = prove
(`!(k:int). (&0:int) <= k ==>
  real_of_int k = real_of_num (num_of_int k)`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC [GSYM real_num_int] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT]);;

(* ---------------------------------------------------------------------- *)
(*                               Definition                               *)
(* ---------------------------------------------------------------------- *)

let z_binom = new_definition
  `z_binom n k = 
    if (&0:int) <= k /\ (&0:int) <= n then 
    int_of_num (binom(num_of_int n,num_of_int k))
    else (&0:int)`;;

(* ---------------------------------------------------------------------- *)
(*                    Useful properties of z-binomials                    *)
(* ---------------------------------------------------------------------- *)

let ZBINOM_EMPTY_SET = prove
(`real_of_int (z_binom (&0:int) k) = 
  if k = int_of_num 0 then (&1:real) else (&0:real)`,
  REWRITE_TAC [z_binom] THEN
  ASM_CASES_TAC `k:int = &0` THENL [ASM_REWRITE_TAC [INT_LE_REFL; BINOM_REFL;
  int_of_num_th]; ALL_TAC] THEN
  ASM_REWRITE_TAC [INT_LE_REFL] THEN
  ASM_CASES_TAC `(&0:int) <= k` THENL [ASM_REWRITE_TAC [int_of_num_th;
  REAL_OF_NUM_EQ; BINOM_EQ_0; GSYM INT_OF_NUM_LT] THEN
  ASM_SIMP_TAC [INT_OF_NUM_OF_INT; INT_LE_REFL] THEN 
  REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC [int_of_num_th]);;

let ZBINOM_LT = prove
(`!n k. n < k ==> z_binom n k = int_of_num 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `int_of_num 0 <= k` THENL [ASM_REWRITE_TAC [z_binom] THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC [INT_OF_NUM_EQ; BINOM_EQ_0;
  GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT]; REWRITE_TAC [EQ_REFL]];
  SUBGOAL_THEN `~(int_of_num 0 <= n)` ASSUME_TAC THENL [
  REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC [z_binom]]);;

let ZBINOM_REFL = prove
(`!n. z_binom n n = if int_of_num 0 <= n then int_of_num 1 else int_of_num 0`,
  GEN_TAC THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC [z_binom; INT_OF_NUM_EQ; BINOM_REFL];
  ASM_REWRITE_TAC [z_binom]]);;

let ZBINOM_EQ_0 = prove
(`!n k. z_binom n k = int_of_num 0 <=>
  (~(int_of_num 0 <= n) \/ ~(int_of_num 0 <= k) \/ n < k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [z_binom] THEN
  COND_CASES_TAC THENL [EQ_TAC THENL [ASM_SIMP_TAC [INT_OF_NUM_EQ; 
  BINOM_EQ_0; GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT]; 
  ASM_SIMP_TAC [INT_OF_NUM_EQ; BINOM_EQ_0; GSYM INT_OF_NUM_LT; 
  INT_OF_NUM_OF_INT]];
  EQ_TAC THENL [FIRST_ASSUM MP_TAC THEN REWRITE_TAC [DE_MORGAN_THM] THEN
  CONV_TAC TAUT; REWRITE_TAC [EQ_REFL]]]);;

let ZBINOM_CHOOSE_0 = prove
(`!n. z_binom n (int_of_num 0) = 
  if int_of_num 0 <= n then int_of_num 1 else int_of_num 0`,
  GEN_TAC THEN
  REWRITE_TAC [z_binom; INT_LE_REFL] THEN
  COND_CASES_TAC THENL [REWRITE_TAC [REAL_OF_NUM_EQ; NUM_OF_INT_OF_NUM; binom];
  REWRITE_TAC []]);;

(* ---------------------------------------------------------------------- *)
(*          Sometimes  Integer binomials has finite support...            *)
(* ---------------------------------------------------------------------- *)

let ZBINOM_SUPPORT_IS_INTSEG = prove
(`(support (+) (\k. real_of_int (z_binom n k)) (:int)) =
  if ~(int_of_num 0 <= n) then {}
  else IMAGE (int_of_num) (0..num_of_int n)`,
    COND_CASES_TAC THENL [ASM_REWRITE_TAC [z_binom; int_of_num_th; support; 
    IN_UNIV; NEUTRAL_REAL_ADD] THEN SET_TAC []; ALL_TAC] THEN
    ASM_REWRITE_TAC [SET_RULE `P = Q <=> (P SUBSET Q /\ Q SUBSET P)`;
    support; NEUTRAL_REAL_ADD; IN_UNIV; SUBSET; IN_ELIM_THM;
    int_of_num_th; REAL_OF_NUM_EQ; z_binom; IMAGE; IN_NUMSEG; LE_0] THEN
    CONJ_TAC THENL
      [GEN_TAC THEN
      ASM_CASES_TAC `int_of_num 0 <= (x:int)` THENL 
      [ASM_SIMP_TAC [int_of_num_th; REAL_OF_NUM_EQ; BINOM_EQ_0;
      GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT] THEN DISCH_TAC THEN
      EXISTS_TAC `num_of_int x`
      THEN ASM_SIMP_TAC [GSYM INT_OF_NUM_LE; INT_OF_NUM_OF_INT] THEN 
      FIRST_ASSUM MP_TAC THEN ARITH_TAC; ASM_REWRITE_TAC [int_of_num_th]];
      GEN_TAC THEN
      ASM_CASES_TAC `int_of_num 0 <= (x:int)` THENL [ASM_SIMP_TAC 
        [int_of_num_th; REAL_OF_NUM_EQ; BINOM_EQ_0; GSYM INT_OF_NUM_LT;
        INT_OF_NUM_OF_INT] THEN STRIP_TAC THEN
        SUBGOAL_THEN `x:int <= n` ASSUME_TAC THENL [ASM_REWRITE_TAC []
          THEN UNDISCH_TAC `x' <= num_of_int n` THEN ONCE_REWRITE_TAC 
          [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN ASM_SIMP_TAC 
          [GSYM INT_OF_NUM_LE; INT_OF_NUM_OF_INT]; ALL_TAC] THEN
        FIRST_X_ASSUM MP_TAC THEN ARITH_TAC; ASM_REWRITE_TAC [int_of_num_th; 
        NOT_EXISTS_THM; DE_MORGAN_THM; num_of_int] THEN SELECT_ELIM_TAC THEN 
        REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC]]);;

let ZBINOM_FINITE_SUPPORT = prove
(`FINITE (support (+) (\k. real_of_int (z_binom n k)) (:int))`,
  REWRITE_TAC [ZBINOM_SUPPORT_IS_INTSEG] THEN
  COND_CASES_TAC THENL [REWRITE_TAC [FINITE_RULES]; 
  MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC [FINITE_NUMSEG]]);;

(* ---------------------------------------------------------------------- *)
(*                     ... and sometimes they don't.                      *)
(* ---------------------------------------------------------------------- *)

let ZBINOM_SUPPORT_HALFLINE = prove
(`support (+) (\i. real_of_int (z_binom (int_of_num 2 * i) i)) (:int) =
  {(x:int) | int_of_num 0 <= x}`,
  REWRITE_TAC [support; NEUTRAL_REAL_ADD; IN_UNIV; FUN_EQ_THM; IN_ELIM_THM]
  THEN GEN_TAC THEN
  ONCE_REWRITE_TAC [REAL_ARITH `!a:real b. a = b <=> b = a`] THEN
  REWRITE_TAC [GSYM real_num_int] THEN
  ONCE_REWRITE_TAC [ARITH_RULE `!a:int b. a = b <=> b = a`] THEN
  REWRITE_TAC [ZBINOM_EQ_0] THEN ARITH_TAC);;

(* ---------------------------------------------------------------------- *)
(*  Theorems for rewriting the binomials. After avery theormes there is   *)
(*                       the corresponding tactic.                        *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(*                                TOP_STEP                                *)
(* ---------------------------------------------------------------------- *)

let ZBINOM_TOP_STEP_REAL = prove
(`!(n:int) (k:int). real_of_int (z_binom (n + int_of_num 1) k) = 
  (if 
     k = n + (int_of_num 1) /\ 
     ~((int_of_num 0) <= n + (int_of_num 1)) 
   then real_of_num 0
   else if  
     k = n + (int_of_num 1) /\ 
     (int_of_num 0) <= n + (int_of_num 1) 
   then real_of_num 1
   else (real_of_int n + real_of_num 1) / (real_of_int n + 
   real_of_num 1 - real_of_int k) * real_of_int (z_binom n k))`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC [z_binom; int_of_num_th]; ALL_TAC]
  THEN COND_CASES_TAC THENL [ASM_REWRITE_TAC [z_binom; int_of_num_th; BINOM_REFL];
  ALL_TAC] THEN ASM_REWRITE_TAC [z_binom] THEN
  COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THENL
      [ASM_SIMP_TAC [ARITH_RULE `int_of_num 0 <= int_of_num 1`; 
      NUM_OF_INT_ADD; NUM_OF_INT_OF_NUM; int_of_num_th] THEN BINOM_TOP_STEP_TAC THEN
      ASM_SIMP_TAC [GSYM REAL_OF_NUM_OF_INT] THEN FIRST_X_ASSUM MP_TAC THEN
      ASM_SIMP_TAC [GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD; INT_OF_NUM_OF_INT] THEN
      DISCH_TAC THEN ASM_MESON_TAC []; ALL_TAC] THEN
    ASM_SIMP_TAC [int_of_num_th; REAL_MUL_RZERO; REAL_OF_NUM_EQ; BINOM_EQ_0;
    GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT] THEN
    REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [int_of_num_th; REAL_ENTIRE] THEN
  COND_CASES_TAC THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; 
  REWRITE_TAC [int_of_num_th]]);;

(* In the following there are less cases than in the previous, but it doesn't
   isolate che case `denominator = zero`, so I don't use it. *)

let ZBINOM_TOP_STEP_REAL_bis = prove
(`!(n:int) (k:int). real_of_int (z_binom (n + int_of_num 1) k) = 
  (if k = n + (int_of_num 1) /\ 
     (int_of_num 0) <= n + (int_of_num 1)
   then real_of_num 1
   else (real_of_int n + real_of_num 1) / (real_of_int n + 
   real_of_num 1 - real_of_int k) * real_of_int (z_binom n k))`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC [ZBINOM_REFL; int_of_num_th]; ALL_TAC] THEN
  REWRITE_TAC [z_binom] THEN
  COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL
      [ASM_SIMP_TAC [NUM_OF_INT_ADD; ARITH_RULE `int_of_num 0 <= int_of_num 1`;
      NUM_OF_INT_OF_NUM; int_of_num_th; BINOM_TOP_STEP_REAL] THEN
      SUBGOAL_THEN `int_of_num 0 <= n + int_of_num 1` ASSUME_TAC
        THENL [FIRST_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `~(k = n + int_of_num 1 /\ int_of_num 0 <= n + int_of_num 1)` THEN
      ASM_REWRITE_TAC [DE_MORGAN_THM] THEN DISCH_TAC THEN
      ASM_SIMP_TAC [GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD; INT_OF_NUM_OF_INT] THEN
      ASM_SIMP_TAC [GSYM REAL_OF_NUM_OF_INT]; ASM_SIMP_TAC 
      [int_of_num_th; REAL_MUL_RZERO; REAL_OF_NUM_EQ; BINOM_EQ_0;
      GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT] THEN
      REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC]; ALL_TAC] THEN
  COND_CASES_TAC THENL [REWRITE_TAC [int_of_num_th] THEN
    MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [REAL_ENTIRE] THEN
    ASM_SIMP_TAC [REAL_OF_NUM_EQ; BINOM_EQ_0; GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT]
    THEN REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC;
    REWRITE_TAC [int_of_num_th; REAL_MUL_RZERO]]);;

let ZBINOM_TOP_STEP_TAC =
let lemma = prove (
 `(~(k = n + int_of_num 1) /\ ~(real_of_int n + real_of_num 1 - real_of_int k = &0))
  /\
    real_of_int (z_binom (n + int_of_num 1) k) = 
  (real_of_int n + real_of_num 1) / (real_of_int n + real_of_num 1 - real_of_int k) * 
    real_of_int (z_binom n k) 
\/
   (k = n + int_of_num 1 /\ ~(int_of_num 0 <= n + int_of_num 1)) 
           /\ real_of_int (z_binom(n + int_of_num 1) k) = real_of_num 0
\/
   (k = n + int_of_num 1 /\ int_of_num 0 <= n + int_of_num 1) 
           /\ real_of_int (z_binom(n + int_of_num 1) k) = real_of_num 1`,
 REWRITE_TAC [ZBINOM_TOP_STEP_REAL] THEN COND_CASES_TAC THENL
  [ASM_REWRITE_TAC []; COND_CASES_TAC THENL
      [ASM_REWRITE_TAC []; REWRITE_TAC [TAUT `!P. F /\ P <=> F`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC []; SUBGOAL_THEN `~(k:int = n + int_of_num 1)` 
                      ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
                      ASM_REWRITE_TAC [REAL_ARITH `!a:real b c. a + b - c = 
                      real_of_num 0 <=> c = a + b`; GSYM int_of_num_th; 
                      GSYM int_add_th; GSYM int_eq]]]]) in
    let ZBINOM_MATCH = PART_MATCH (lhs o rand o lhand) lemma in
    fun (asl,w as gl) ->
      MAP_EVERY (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC)
                                 (DISJ_CASES_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
                                                  SUBST_ALL_TAC)))
                (map ZBINOM_MATCH (find_terms (can ZBINOM_MATCH) w)) gl;;

(* If the variables are universally quantified it works, otherwise it doesn't.
   I need some experiments. *)

(* Now it works
g  `!n k. real_of_int (z_binom ((a + b) + int_of_num 1) k) =
                                  flying_spaghetti_monster`;;
e (REPEAT GEN_TAC);;
e (ZBINOM_TOP_STEP_TAC);;

But here it doesn't

g   `!n k. real_of_int (z_binom ((a + b) + int_of_num 1) k) =
                                   flying_spaghetti_monster`;;
e (ZBINOM_TOP_STEP_TAC);;
*)

(* ---------------------------------------------------------------------- *)
(*                               BOTTOM_STEP                              *)
(* ---------------------------------------------------------------------- *)

(* The same as before: less cases, but I don't isolate the case
   in wich the denominator is zero *)

let ZBINOM_BOTTOM_STEP_bis = prove
(`!n k. real_of_int(z_binom n (k + int_of_num 1)) = 
  if k  = int_neg (int_of_num 1) /\ int_of_num 0 <= n then real_of_num 1
  else (real_of_int n - real_of_int k) / (real_of_int k + real_of_num 1) * 
                       real_of_int (z_binom n k)`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC 
  [ARITH_RULE `int_neg (int_of_num 1) + int_of_num 1 = int_of_num 0`;
  ZBINOM_CHOOSE_0; int_of_num_th]; ALL_TAC] THEN REWRITE_TAC [z_binom] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC [] THEN COND_CASES_TAC THENL 
    [ASM_SIMP_TAC [int_of_num_th; NUM_OF_INT_ADD; ARITH_RULE
    `int_of_num 0 <= int_of_num 1`; NUM_OF_INT_OF_NUM; BINOM_BOTTOM_STEP_REAL;
    REAL_OF_NUM_OF_INT]; REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC]; ALL_TAC]
  THEN COND_CASES_TAC THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC;
    REWRITE_TAC [int_of_num_th; REAL_MUL_RZERO]]);;

let ZBINOM_BOTTOM_STEP = prove
(`!n k. real_of_int(z_binom n (k + int_of_num 1)) = 
  if ~(int_of_num 0 <= n) then real_of_num 0
  else if ~(int_of_num 0 <= k + int_of_num 1) then real_of_num 0
  else if k + int_of_num 1 = int_of_num 0 then real_of_num 1
  else (real_of_int n - real_of_int k) / (real_of_int k + real_of_num 1) * 
                       real_of_int (z_binom n k)`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC [z_binom; int_of_num_th]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC [z_binom; int_of_num_th]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC [z_binom; INT_OF_NUM_LE; LE_REFL;
  NUM_OF_INT_OF_NUM; int_of_num_th; REAL_OF_NUM_EQ; binom]; ALL_TAC] THEN
  ASM_REWRITE_TAC [z_binom; int_of_num_th] THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC [NUM_OF_INT_ADD; 
    ARITH_RULE `int_of_num 0 <= int_of_num 1`;int_of_num_th; NUM_OF_INT_OF_NUM; 
    BINOM_BOTTOM_STEP_REAL; REAL_OF_NUM_OF_INT]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:int) + int_of_num 1 = int_of_num 0` ASSUME_TAC THENL
    [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ASM_MESON_TAC []]);;

let ZBINOM_BOTTOM_STEP_TAC =
let lemma = prove 
(`~(int_of_num 0 <= n) /\ 
            real_of_int(z_binom n (k + int_of_num 1)) = real_of_num 0
\/
   (int_of_num 0 <= n /\ ~(int_of_num 0 <= k + int_of_num 1)) /\
            real_of_int(z_binom n (k + int_of_num 1)) = real_of_num 0
\/
   (int_of_num 0 <= n /\ k + int_of_num 1 = int_of_num 0) /\
            real_of_int(z_binom n (k + int_of_num 1)) = real_of_num 1
\/
   (int_of_num 0 <= n /\ int_of_num 0 <= k /\
         ~(real_of_int k + real_of_num 1 = real_of_num 0)) /\
            real_of_int(z_binom n (k + int_of_num 1)) = 
            (real_of_int n - real_of_int k) / (real_of_int k + real_of_num 1) * 
                       real_of_int (z_binom n k)`,
  REWRITE_TAC [ZBINOM_BOTTOM_STEP] THEN
  COND_CASES_TAC THENL [REWRITE_TAC []; COND_CASES_TAC THENL 
  [REWRITE_TAC []; COND_CASES_TAC THENL 
  [REWRITE_TAC [ARITH_RULE `real_of_num 1 = real_of_num 0 <=> F`];
  REWRITE_TAC [] THEN
  CONJ_TAC THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC;
  ASM_REWRITE_TAC [GSYM int_of_num_th; GSYM int_add_th; GSYM int_eq]]]]]) in
    let ZBINOM_MATCH = PART_MATCH (lhs o rand o lhand) lemma in
    fun (asl,w as gl) ->
      MAP_EVERY (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
                                                  SUBST_ALL_TAC)
                                 (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
                                                  SUBST_ALL_TAC)
                                  (DISJ_CASES_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
                                                  SUBST_ALL_TAC))))
                (map ZBINOM_MATCH (find_terms (can ZBINOM_MATCH) w)) gl;;

(* ---------------------------------------------------------------------- *)
(*                            BOTTOM_BACKSTEP                             *)
(* ---------------------------------------------------------------------- *)

let ZBINOM_BOTTOM_BACKSTEP_REAL_bis = prove
(`!(n:int) (k:int).
  real_of_int (z_binom n (k - int_of_num 1)) = 
   if (k = n + int_of_num 1 /\ int_of_num 0 <= n)
       then real_of_num 1
   else (real_of_int k) / (real_of_int n + real_of_num 1 - real_of_int k) * 
  real_of_int (z_binom n k)`,
(* mi metto nelle condizioni di bottom_step *)
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL [ASM_SIMP_TAC [ARITH_RULE
  `(n + int_of_num 1) - int_of_num 1 = n`; ZBINOM_REFL; int_of_num_th]; ALL_TAC]
  THEN SUBGOAL_THEN `z_binom n k = z_binom n ((k - int_of_num 1) + int_of_num 1)`
  (fun th -> REWRITE_TAC [th]) THENL [REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) 
  THEN ARITH_TAC; ALL_TAC] THEN
  ZBINOM_BOTTOM_STEP_TAC THENL
  [ASM_REWRITE_TAC [REAL_MUL_RZERO; z_binom; int_of_num_th];

  ASM_REWRITE_TAC [REAL_MUL_RZERO; z_binom] THEN
  COND_CASES_TAC THENL [REWRITE_TAC [int_of_num_th; REAL_OF_NUM_EQ; BINOM_EQ_0]
    THEN ASM_SIMP_TAC [GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT] THEN
    REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC [int_of_num_th];

  FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC [
  ARITH_RULE `k - int_of_num 1 + int_of_num 1 = k`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(int_of_num 0 <= k - int_of_num 1)` ASSUME_TAC THENL [
    ASM_REWRITE_TAC [] THEN ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC [z_binom]
  THEN REWRITE_TAC [int_of_num_th] THEN REAL_ARITH_TAC;

  SUBGOAL_THEN `~(real_of_int n + real_of_num 1 - real_of_int k = real_of_num 0)` 
    ASSUME_TAC THENL [SUBGOAL_THEN `~(k = n + int_of_num 1)` ASSUME_TAC THENL 
    [ASM_MESON_TAC []; ALL_TAC] THEN ASM_REWRITE_TAC [REAL_ARITH
    `!a:real b c. a + b - c = real_of_num 0 <=> c = a + b`;
    GSYM int_of_num_th; GSYM int_add_th; GSYM int_eq]; ALL_TAC] THEN
  FIRST_X_ASSUM MP_TAC THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC [int_sub_th; int_of_num_th;
  REAL_ARITH `!a:real. a - real_of_num 1 + real_of_num 1 = a`;
  REAL_ARITH `!a:real b c. a - (b - c) = a + c - b`] THEN REAL_FIELD_TAC]);;

let ZBINOM_BOTTOM_BACKSTEP_REAL = prove
(`!(n:int) (k:int).
  real_of_int (z_binom n (k - int_of_num 1)) = 
  (if (k = n + int_of_num 1 /\ ~(int_of_num 0 <= n))
       then real_of_num 0
   else if (k = n + int_of_num 1 /\ int_of_num 0 <= n)
       then real_of_num 1
   else (real_of_int k) / (real_of_int n + real_of_num 1 - real_of_int k) * 
  real_of_int (z_binom n k))`,
(* mi metto nelle condizioni di bottom_step *)
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC [z_binom; int_of_num_th]; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC [z_binom; 
  ARITH_RULE `!n:int. (n + int_of_num 1) - int_of_num 1 = n`;
  int_of_num_th; BINOM_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `z_binom n k = z_binom n ((k - int_of_num 1) + int_of_num 1)`
  (fun th -> REWRITE_TAC [th]) THENL [REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) 
  THEN ARITH_TAC; ALL_TAC] THEN
  ZBINOM_BOTTOM_STEP_TAC THENL
    [ASM_REWRITE_TAC [REAL_MUL_RZERO; z_binom; int_of_num_th];

    ASM_REWRITE_TAC [REAL_MUL_RZERO; z_binom] THEN
    COND_CASES_TAC THENL [REWRITE_TAC [int_of_num_th; REAL_OF_NUM_EQ; BINOM_EQ_0]
      THEN ASM_SIMP_TAC [GSYM INT_OF_NUM_LT; INT_OF_NUM_OF_INT] THEN
      REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC [int_of_num_th];

    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC [
    ARITH_RULE `k - int_of_num 1 + int_of_num 1 = k`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(int_of_num 0 <= k - int_of_num 1)` ASSUME_TAC THENL [
    ASM_REWRITE_TAC [] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC [z_binom] THEN
    REWRITE_TAC [REAL_MUL_RID; int_of_num_th; REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `~(real_of_int n + real_of_num 1 = real_of_num 0)` ASSUME_TAC THENL
      [UNDISCH_TAC `int_of_num 0 <= n` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM MP_TAC THEN REAL_FIELD_TAC;

    SUBGOAL_THEN `~(real_of_int n + real_of_num 1 - real_of_int k = real_of_num 0)` 
    ASSUME_TAC THENL [SUBGOAL_THEN `~(k = n + int_of_num 1)` ASSUME_TAC THENL 
    [ASM_MESON_TAC []; ALL_TAC] THEN ASM_REWRITE_TAC [REAL_ARITH
    `!a:real b c. a + b - c = real_of_num 0 <=> c = a + b`; GSYM int_of_num_th;
    GSYM int_add_th; GSYM int_eq]; ALL_TAC] THEN
    FIRST_X_ASSUM MP_TAC THEN FIRST_ASSUM MP_TAC THEN
    REWRITE_TAC [int_sub_th; int_of_num_th;
    REAL_ARITH `!a:real. a - real_of_num 1 + real_of_num 1 = a`;
    REAL_ARITH `!a:real b c. a - (b - c) = a + c - b`] THEN REAL_FIELD_TAC]);;


(* -------------------------------------------------- *)
(* -------------------------------------------------- *)
(***
REAL_FIELD_TAC cannot simplify
`~(real_of_int (k - &1) + &1 = &0)
 ==> ~(real_of_int n + &1 - real_of_int k = &0)
 ==> real_of_int (z_binom n (k - &1)) =
     real_of_int k / (real_of_int n + &1 - real_of_int k) *
     (real_of_int n - real_of_int (k - &1)) / (real_of_int (k - &1) + &1) *
     real_of_int (z_binom n (k - &1))`

but it works with
`~(real_of_int k = &0)
 ==> ~(real_of_int n + &1 - real_of_int k = &0)
 ==> real_of_int (z_binom n (k - &1)) =
     real_of_int k / (real_of_int n + &1 - real_of_int k) *
     (real_of_int n + &1 - real_of_int k) / real_of_int k *
     real_of_int (z_binom n (k - &1))`
***)
(* -------------------------------------------------- *)
(* -------------------------------------------------- *)

let ZBINOM_BOTTOM_BACKSTEP_TAC =
let lemma = prove
(`(k = n + int_of_num 1 /\ ~(int_of_num 0 <= n)) /\ 
              real_of_int (z_binom n (k - int_of_num 1)) = real_of_num 0
\/
   (k = n + int_of_num 1 /\ int_of_num 0 <= n) /\ 
              real_of_int (z_binom n (k - int_of_num 1)) = real_of_num 1
\/
   (~(k = n + int_of_num 1) /\ ~(real_of_int n + &1 - real_of_int k = real_of_num 0)) /\
              real_of_int (z_binom n (k - int_of_num 1)) =
              real_of_int k / (real_of_int n + &1 - real_of_int k) *
                    real_of_int (z_binom n k)`,
  REWRITE_TAC [ZBINOM_BOTTOM_BACKSTEP_REAL] THEN 
  COND_CASES_TAC THENL [REWRITE_TAC []; REWRITE_TAC [] THEN
  COND_CASES_TAC THENL [REWRITE_TAC []; REWRITE_TAC [REAL_ARITH `!a:real b c. a + b - c = 
  real_of_num 0 <=> c = a + b`; GSYM int_of_num_th; GSYM int_add_th; GSYM int_eq] THEN
  ASM_MESON_TAC []]]) in
    let ZBINOM_MATCH = PART_MATCH (lhs o rand o lhand) lemma in
    fun (asl,w as gl) ->
      MAP_EVERY (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC)
                                 (DISJ_CASES_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
                                                  SUBST_ALL_TAC)))
                (map ZBINOM_MATCH (find_terms (can ZBINOM_MATCH) w)) gl;;

(* look at this:
# REAL_ARITH `real_of_num 1 / real_of_num 0 * real_of_num 0 = real_of_num 0`;;
val it : thm = |- &1 / &0 * &0 = &0
*)

(* ---------------------------------------------------------------------- *)
(*                              TOP BACKSTEP                              *)
(* ---------------------------------------------------------------------- *)

let ZBINOM_TOP_BACKSTEP = prove
(`!n:int k:int. real_of_int (z_binom (n - int_of_num 1) k) = 
  if ~(n = int_of_num 0)
  then (real_of_int n - real_of_int k)  / real_of_int n *
       real_of_int (z_binom n k)
  else real_of_num 0`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL [ABBREV_TAC `w = z_binom (n - int_of_num 1) k` THEN
    SUBGOAL_THEN `!n k. z_binom n k = z_binom ((n - int_of_num 1) + int_of_num 1) k`
    (fun th -> ONCE_REWRITE_TAC [th]) THENL [REPEAT GEN_TAC THEN 
      REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "w" THEN
    ZBINOM_TOP_STEP_TAC THENL
      [SUBGOAL_THEN `~(real_of_int n = real_of_num 0)` ASSUME_TAC THENL
      [UNDISCH_TAC `~(n = int_of_num 0)` THEN REWRITE_TAC [int_eq; int_of_num_th];
      ALL_TAC] THEN FIRST_X_ASSUM MP_TAC THEN FIRST_X_ASSUM MP_TAC THEN 
      REWRITE_TAC [int_sub_th; int_of_num_th] THEN REAL_FIELD_TAC;

      REWRITE_TAC [REAL_MUL_RZERO] THEN MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC
      [GSYM real_num_int] THEN MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [ZBINOM_EQ_0]
      THEN REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC;

      SUBGOAL_THEN `k:int = n` (fun th -> REWRITE_TAC [th]) THENL
        [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC [REAL_ARITH `!a:real. a - a = real_of_num 0`;
      REAL_ARITH `!a:real. real_of_num 0 / a = real_of_num 0`; REAL_MUL_LZERO]
      THEN MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [GSYM real_num_int] 
      THEN MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [ZBINOM_EQ_0]
      THEN REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [GSYM real_num_int] 
  THEN MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC [ZBINOM_EQ_0]
  THEN REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC);;

(*
# ARITH_RULE `~(int_of_num_0 <= int_of_num 0 - int_of_num 1)`;;
Exception: Failure "linear_ineqs: no contradiction".
*)

let ZBINOM_TOP_BACKSTEP_TAC = 
let lemma = prove
(`(~(n = int_of_num 0) /\ ~(real_of_int n = real_of_num 0)) /\ 
   real_of_int (z_binom (n - int_of_num 1) k) = 
        (real_of_int n - real_of_int k)  / real_of_int n *
        real_of_int (z_binom n k)
\/
   n = int_of_num 0 /\
   real_of_int (z_binom (n - int_of_num 1) k) = real_of_num 0`,
  REWRITE_TAC [ZBINOM_TOP_BACKSTEP] THEN 
  COND_CASES_TAC THENL [ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC [int_eq; int_of_num_th]; 
  ASM_REWRITE_TAC []]) in
    let ZBINOM_MATCH = PART_MATCH (lhs o rand o lhand) lemma in
    fun (asl,w as gl) ->
      MAP_EVERY (DISJ_CASES_THEN (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
                                                  SUBST_ALL_TAC))
                (map ZBINOM_MATCH (find_terms (can ZBINOM_MATCH) w)) gl;;

