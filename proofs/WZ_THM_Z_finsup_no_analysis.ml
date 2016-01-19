(* -*- holl -*- *)

(* ====================================================================== *)
(* ||                                                                  || *)
(* ||              In this file I prove the WZ theorem.                || *)
(* ||       The sum environment is (:int) and the "WZ pair"            || *)
(* ||              functions have type :int->int->real                 || *)
(* ||                                                                  || *)
(* ||     Giovanni Gherdovich, gherdovich@students.math.unifi.it       || *)
(* ||       Universita` degli Studi di Firenze, december 2006          || *)
(* ||                                                                  || *)
(* ====================================================================== *)

needs "finite_support.ml";;
needs "/home/giovanni/hol_light/Multivariate/misc.ml";;

let TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

let REAL_FIELD_TAC = CONV_TAC REAL_FIELD;;

(* ---------------------------------------------------------------------- *)
(*           I need of an "induction theorem" over the integers           *)
(* ---------------------------------------------------------------------- *)

let INT_NUM_LEMMA = prove
(`!(n:int). 
   (~(int_of_num 0 <= n) ==> n = int_neg (int_of_num (num_of_int (int_neg n))))
  /\ ((int_of_num 0 <= n) ==> n = int_of_num (num_of_int n))`,
 GEN_TAC THEN CONJ_TAC THENL [DISCH_TAC THEN
  REWRITE_TAC [ARITH_RULE `!a:int b. a = --b <=> --a = b`] THEN
  MATCH_MP_TAC (GSYM INT_OF_NUM_OF_INT) THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
 MATCH_ACCEPT_TAC (GSYM INT_OF_NUM_OF_INT));;

let SPLIT_INT_CASES = prove
(`!(P:int->bool).
  (!(n:int). P n) <=>
  ((!(h:num). P (int_of_num h)) /\ (!(k:num). P (int_neg (int_of_num k))))`,
 GEN_TAC THEN EQ_TAC THENL [MESON_TAC []; ALL_TAC] THEN
 DISCH_TAC THEN GEN_TAC THEN
 ASM_CASES_TAC `int_of_num 0 <= n` THENL
  [SUBGOAL_THEN `(P:int->bool) n = P (int_of_num (num_of_int n))`
  (fun th -> REWRITE_TAC [th]) THENL [AP_TERM_TAC THEN
  ASM_SIMP_TAC [GSYM INT_OF_NUM_OF_INT]; ALL_TAC] THEN ASM_MESON_TAC []; ALL_TAC]
 THEN SUBGOAL_THEN `(P:int->bool) n = P (int_neg (int_of_num (num_of_int (int_neg n))))`
  (fun th -> REWRITE_TAC [th]) THENL [AP_TERM_TAC THEN ASM_SIMP_TAC [INT_NUM_LEMMA];
  ALL_TAC] THEN ASM_MESON_TAC []);;

let int_INDUCTION = prove
(`!(P:int->bool).
  P (int_of_num 0) /\ (!(n:int). P n ==> P (n + int_of_num 1)) /\
  (!n. P n ==> P (n - int_of_num 1)) ==>
  (!n. P n)`,
 GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [SPLIT_INT_CASES] THEN
 CONJ_TAC THENL [INDUCT_TAC THENL [ASM_REWRITE_TAC [];
  REWRITE_TAC [ADD1; GSYM INT_OF_NUM_ADD] THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
 INDUCT_TAC THENL
  [ASM_REWRITE_TAC [ARITH_RULE `int_neg (int_of_num 0) = int_of_num 0`];
  REWRITE_TAC [ADD1; GSYM INT_OF_NUM_ADD; 
  ARITH_RULE `!a:int b. int_neg (a + b) = int_neg a - b`] THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC []]);;

let int_INDUCTION_BIS = prove
(`!(P:int->bool).
  P (int_of_num 0) /\ (!(n:int). P n <=> P (n + int_of_num 1))
    ==> (!n. P n)`,
  REPEAT STRIP_TAC THEN SPEC_TAC (`n:int`, `n:int`) THEN
  MATCH_MP_TAC int_INDUCTION THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC []; GEN_TAC THEN
    ABBREV_TAC `r = (P:int->bool) (n - int_of_num 1)` THEN
    ONCE_REWRITE_TAC [ARITH_RULE `!a:int. a = (a - int_of_num 1) + int_of_num 1`]
    THEN EXPAND_TAC "r" THEN ASM_MESON_TAC []]);;

let FINITE_SINGLETON = prove
(`!(x:A). FINITE {x}`,
  GEN_TAC THEN ONCE_REWRITE_TAC [FINITE_CASES] THEN
  SUBGOAL_THEN `~({x:A} = {})` (fun th -> REWRITE_TAC [th]) THENL
  [REWRITE_TAC [SET_RULE `!(P:A->bool) (Q:A->bool).
    (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`; DE_MORGAN_THM;
    SUBSET; NOT_IN_EMPTY; NOT_FORALL_THM] THEN EXISTS_TAC `x:A` THEN
    SET_TAC []; ALL_TAC] THEN
  EXISTS_TAC `x:A` THEN EXISTS_TAC `(EMPTY:A->bool)` THEN
  REWRITE_TAC [FINITE_RULES; EQ_REFL]);;

(* ---------------------------------------------------------------------- *)
(*               When a subset of the integers is finite?                 *)
(* ---------------------------------------------------------------------- *)

let FINITE_SYM_INTSEG = prove
(`!n:int. int_of_num 0 <= n ==>
     FINITE {x | int_neg n <= x /\ x <= n}`,
  MATCH_MP_TAC int_INDUCTION_BIS THEN
  REWRITE_TAC [ARITH_RULE `int_neg (int_of_num 0) = int_of_num 0`;
  ARITH_RULE `(int_of_num 0 <= x /\ x <= &0) <=> x = int_of_num 0`;
  SET_RULE `{x | x = a} = {a}`] THEN
  CONJ_TAC THENL [REWRITE_TAC [FINITE_SINGLETON]; ALL_TAC] THEN
  GEN_TAC THEN EQ_TAC THENL
  [STRIP_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `int_of_num 0 <= n` THENL
    [ONCE_REWRITE_TAC [FINITE_CASES] THEN
    SUBGOAL_THEN `~({x | --(n + int_of_num 1) <= x /\ x <= n + int_of_num 1} = {})`
    (fun th -> REWRITE_TAC [th]) THENL
      [REWRITE_TAC [SET_RULE `!(P:A->bool) (Q:A->bool).
      (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`; DE_MORGAN_THM] THEN
      SUBGOAL_THEN
      `~({x | --(n + int_of_num 1) <= x /\ x <= n + int_of_num 1} SUBSET {})`
      (fun th -> REWRITE_TAC [th]) THEN
      REWRITE_TAC [SUBSET; IN_ELIM_THM; EMPTY; NOT_FORALL_THM] THEN
      EXISTS_TAC `int_of_num 0` THEN
      REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `int_neg (n + int_of_num 1)` THEN
    EXISTS_TAC `{x | int_neg n <= x /\ x <= n + int_of_num 1}` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [INSERT; IN_ELIM_THM; SET_RULE `!(P:A->bool) (Q:A->bool).
    (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`; SUBSET] THEN
    REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC [FINITE_CASES] THEN
    SUBGOAL_THEN `~({x | --n <= x /\ x <= n + int_of_num 1} = {})`
    (fun th -> REWRITE_TAC [th]) THENL
      [REWRITE_TAC [SET_RULE `!(P:A->bool) (Q:A->bool).
      (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`; DE_MORGAN_THM] THEN
      SUBGOAL_THEN
      `~({x | --n <= x /\ x <= n + int_of_num 1} SUBSET {})`
      (fun th -> REWRITE_TAC [th]) THEN
      REWRITE_TAC [SUBSET; IN_ELIM_THM; EMPTY; NOT_FORALL_THM] THEN
      EXISTS_TAC `int_of_num 0` THEN
      REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `n + int_of_num 1` THEN
    EXISTS_TAC `{x | int_neg n <= x /\ x <= n}` THEN
    CONJ_TAC THENL
      [REWRITE_TAC [INSERT; IN_ELIM_THM; SET_RULE `!(P:A->bool) (Q:A->bool).
      (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`; SUBSET] THEN
      REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ASM_SIMP_TAC []];
    ALL_TAC] THEN
  SUBGOAL_THEN `n = int_neg (int_of_num 1)` (fun th -> REWRITE_TAC [th])
  THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC [ARITH_RULE `int_neg (int_of_num 1) + int_of_num 1 =
  int_of_num 0`; ARITH_RULE `int_neg (int_of_num 0) = int_of_num 0`;
  ARITH_RULE `int_of_num 0 <= x /\ x <= int_of_num 0 <=> x = int_of_num 0`;
  SET_RULE `{x | x = a} = {a}`; FINITE_SINGLETON]; ALL_TAC] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `{x | int_neg n <= x /\ x <= n} =
  ({x | int_neg (n + &1) <= x /\ x <= n + &1} DELETE
  (int_neg (n + int_of_num 1)))
  DELETE (n + int_of_num 1)` (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [SET_RULE `!(P:A->bool) (Q:A->bool).
    (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`; SUBSET; DELETE; IN_ELIM_THM] THEN
    CONJ_TAC THENL [REPEAT (FIRST_X_ASSUM MP_TAC THEN ARITH_TAC);
    REPEAT (FIRST_X_ASSUM MP_TAC THEN ARITH_TAC)]; ALL_TAC] THEN
  REWRITE_TAC [FINITE_DELETE] THEN
  ASM_CASES_TAC `int_of_num 0 <= n + int_of_num 1` THENL
    [ASM_SIMP_TAC []; REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC]);;

let FINITE_INTSEG = prove
(`!n:int m. FINITE {z | n <= z /\ z <= m}`,
  GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `if m < n 
               then {}
               else if (n <= int_of_num 0 /\ m <= int_of_num 0)
                    then {z | int_neg(int_neg n) <= z /\ z <= (int_neg n)}
                    else if (n <= int_of_num 0 /\ int_of_num 0 <= m)
                         then (if (int_neg n) <= m then {z | (int_neg m) <= z /\ z <= m}
                              else {z | int_neg (int_neg n) <= z /\ z <= (int_neg n)})
                         else {z | (int_neg m) <= z /\ z <= m}` THEN
  CONJ_TAC THENL
    [REPEAT COND_CASES_TAC THENL
    [REWRITE_TAC [FINITE_RULES]; MATCH_MP_TAC FINITE_SYM_INTSEG THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC; MATCH_MP_TAC FINITE_SYM_INTSEG THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    MATCH_MP_TAC FINITE_SYM_INTSEG THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    MATCH_MP_TAC FINITE_SYM_INTSEG THEN REPEAT (FIRST_X_ASSUM MP_TAC)
    THEN ARITH_TAC];
    COND_CASES_TAC THENL
      [REWRITE_TAC [SUBSET; IN_ELIM_THM; EMPTY]
      THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
      COND_CASES_TAC THENL
        [REWRITE_TAC [SUBSET; IN_ELIM_THM]
        THEN REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;
        COND_CASES_TAC THENL
          [COND_CASES_TAC THENL
            [REWRITE_TAC [SUBSET; IN_ELIM_THM]
            THEN REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC];
            REWRITE_TAC [SUBSET; IN_ELIM_THM]
            THEN REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC]]]] THEN
    REWRITE_TAC [SUBSET; IN_ELIM_THM]
    THEN REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC);;

let int_LE_CASES = prove
(`!m:int n. m <= n \/ n <= m`, ARITH_TAC);;

let int_LE_TRANS = prove
( `!m:int n p. m <= n /\ n <= p ==> m <= p`, ARITH_TAC);;

let int_FINITE = prove
(`!s:int->bool. FINITE s <=> ?a. !x. (int_of_num 0 <= a /\
  (x IN s ==> ((int_neg a) <= x /\ x <= a)))`,
  SUBGOAL_THEN `!x:int. int_of_num 0 <= (if &0 <= x then x else --x)` 
  ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN EQ_TAC THENL
    [SPEC_TAC(`s:int->bool`,`s:int->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THENL [EXISTS_TAC `int_of_num 0` THEN ARITH_TAC; ALL_TAC]
    THEN REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `a <= (if int_of_num 0 <= x:int then x else (int_neg x))`
    THENL
      [EXISTS_TAC `if int_of_num 0 <= x:int then x else (int_neg x)` THEN
      GEN_TAC THEN
      ASM_REWRITE_TAC [TAUT `!P Q R. (P \/ Q ==> R) <=> ((P ==> R) /\ (Q ==> R))`]
      THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN SUBGOAL_THEN `(int_neg a) <= x' /\ x' <= a` ASSUME_TAC
      THENL [ASM_SIMP_TAC []; ALL_TAC] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `a:int` THEN GEN_TAC THEN ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC `x' = (x:int)` THENL [REPEAT (POP_ASSUM MP_TAC)
    THEN ARITH_TAC; ASM_REWRITE_TAC []]; ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{(y:int) | (int_neg a) <= y /\ y <= a}` THEN
  REWRITE_TAC [FINITE_INTSEG] THEN
  REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC []);;

(* ---------------------------------------------------------------------- *)
(*    The two following theorems help me to prove that a sequence with    *)
(*                     integer indexes is constant                        *)
(* ---------------------------------------------------------------------- *)

let SEQ_CONST_TEST_int = prove
(`!(f:int->real). (!n. f (n + int_of_num 1) - f n = real_of_num 0)
    ==> !n. f n = f (int_of_num 0)`,
 STRIP_TAC THEN DISCH_TAC THEN MATCH_MP_TAC int_INDUCTION THEN
 REWRITE_TAC [] THEN
 CONJ_TAC THENL [SUBGOAL_THEN `!n:int. (f:int->real) (n + int_of_num 1) = f n`
  (fun th -> REWRITE_TAC [th]) THENL [GEN_TAC THEN POP_ASSUM MP_TAC THEN
   REWRITE_TAC [REAL_ARITH `!a:real b. a - b = real_of_num 0 <=> a = b`] THEN
   DISCH_TAC THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
 SUBGOAL_THEN `!n:int. (f:int->real) (n - int_of_num 1) = f n`
  (fun th -> REWRITE_TAC [th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC EQ_SYM THEN POP_ASSUM MP_TAC THEN
   REWRITE_TAC [REAL_ARITH `!a:real b. a - b = real_of_num 0 <=> a = b`] THEN
   SUBGOAL_THEN `?m:int. n = m + int_of_num 1` ASSUME_TAC THENL
     [EXISTS_TAC `n - int_of_num 1` THEN ARITH_TAC; ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
   GEN_TAC THEN DISCH_TAC THEN
   ASM_REWRITE_TAC [ARITH_RULE `!a:int. (a + int_of_num 1) - int_of_num 1 = a`]
   THEN DISCH_TAC THEN ASM_REWRITE_TAC []]);;

let GENERAL_SEQ_CONST_TEST_int = prove
(`(!n. f (n + int_of_num 1) - f n = real_of_num 0)
    ==> f h = f k`,
  SUBGOAL_THEN `?(g:int->real). !n. f n = g (n - k)` ASSUME_TAC THENL
    [EXISTS_TAC `(\i. (f:int->real) (i + k))` THEN
    BETA_TAC THEN GEN_TAC THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [ARITH_RULE `!a:int. a - a = int_of_num 0`] THEN
  ABBREV_TAC `j = h:int - k` THEN
  SPEC_TAC (`j:int`, `j:int`) THEN MATCH_MP_TAC SEQ_CONST_TEST_int THEN
  SUBGOAL_THEN `!n. (g:int->real) n = f (n + k)` ASSUME_TAC THENL
  [GEN_TAC THEN ASM_SIMP_TAC [] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC]
  THEN POP_ASSUM MP_TAC THEN SIMP_TAC [] THEN DISCH_TAC THEN GEN_TAC
  THEN REWRITE_TAC [ARITH_RULE `(n + int_of_num 1) + k = (n + k) + int_of_num 1`]
  THEN ABBREV_TAC `(q:int) = j' + k` THEN ASM_REWRITE_TAC []);;

(* ---------------------------------------------------------------------- *)
(*              I build up the concept of maximum and minimum             *)
(*                        of a subset of the integers                     *)
(* ---------------------------------------------------------------------- *)

let int_sup = new_definition
  `int_sup S = int_of_real (sup (IMAGE real_of_int S))`;;

let int_inf = new_definition
  `int_inf S = int_of_real (inf (IMAGE real_of_int S))`;;

let INT_INF_FINITE_lemma1 = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ FINITE P ==>
    int_inf P IN P`,
  SUBGOAL_THEN `!x:int. int_of_real (real_of_int x) = x` ASSUME_TAC
    THENL [ONCE_REWRITE_TAC [REAL_ARITH `!a:real. a = a + real_of_num 0`] THEN
    REWRITE_TAC [GSYM int_of_num_th; GSYM int_add] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `int_of_real o real_of_int = (\x. x)`
    ASSUME_TAC THENL
      [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC [o_THM]
      THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC [int_inf] THEN
    SUBGOAL_THEN `~(IMAGE real_of_int P = (EMPTY:real->bool))`
      ASSUME_TAC THENL [ASM_REWRITE_TAC [IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `FINITE (IMAGE real_of_int P)` ASSUME_TAC
      THENL [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC []; ALL_TAC]
    THEN SUBGOAL_THEN `inf (IMAGE real_of_int P) IN (IMAGE real_of_int P)`
      ASSUME_TAC THENL [ASM_SIMP_TAC [INF_FINITE]; ALL_TAC] THEN
    ABBREV_TAC `(i:real) = inf (IMAGE real_of_int P)` THEN
    SUBGOAL_THEN `(P:int->bool) = IMAGE int_of_real (IMAGE real_of_int P)`
    (fun th -> ONCE_REWRITE_TAC [th]) THENL [REWRITE_TAC [GSYM IMAGE_o]
        THEN ASM_REWRITE_TAC [IMAGE] THEN SET_TAC []; ALL_TAC] THEN
    UNDISCH_TAC `i IN IMAGE real_of_int P` THEN
    EXPAND_TAC "i" THEN DISCH_TAC THEN REWRITE_TAC [IN_IMAGE] THEN
    EXISTS_TAC `inf (IMAGE real_of_int P)` THEN
    REWRITE_TAC [] THEN
    EXISTS_TAC `int_inf (IMAGE int_of_real (IMAGE real_of_int P))` THEN
    REWRITE_TAC [int_inf] THEN
    REWRITE_TAC [GSYM IMAGE_o] THEN
    SUBGOAL_THEN `(real_of_int o int_of_real) o real_of_int =
    real_of_int o (int_of_real o real_of_int)` (fun th -> REWRITE_TAC [th])
      THENL [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
      REWRITE_TAC [o_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `!(f:int->real). f o (\(x:int). x) = f`
    (fun th -> REWRITE_TAC [th]) THENL [GEN_TAC THEN
      REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC [o_THM]; ALL_TAC]
    THEN CONJ_TAC THENL [EXPAND_TAC "i" THEN MATCH_MP_TAC EQ_SYM THEN
      REWRITE_TAC [GSYM int_rep; is_int] THEN
      (* this is very wise *)
      POP_ASSUM MP_TAC THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
      THEN GEN_TAC THEN STRIP_TAC THEN
      UNDISCH_TAC `inf (IMAGE real_of_int P) = i` THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [dest_int_rep]; 
    POP_ASSUM MP_TAC THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `inf (IMAGE real_of_int P) = i` THEN ASM_REWRITE_TAC [] ]);;

let INT_SUP_FINITE_lemma1 = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ FINITE P ==>
    int_sup P IN P`,
  SUBGOAL_THEN `!x:int. int_of_real (real_of_int x) = x` ASSUME_TAC
    THENL [ONCE_REWRITE_TAC [REAL_ARITH `!a:real. a = a + real_of_num 0`] THEN
    REWRITE_TAC [GSYM int_of_num_th; GSYM int_add] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `int_of_real o real_of_int = (\x. x)`
    ASSUME_TAC THENL
      [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC [o_THM]
      THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC [int_sup] THEN
  SUBGOAL_THEN `~(IMAGE real_of_int P = (EMPTY:real->bool))`
      ASSUME_TAC THENL [ASM_REWRITE_TAC [IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `FINITE (IMAGE real_of_int P)` ASSUME_TAC
      THENL [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC []; ALL_TAC]
    THEN SUBGOAL_THEN `sup (IMAGE real_of_int P) IN (IMAGE real_of_int P)`
      ASSUME_TAC THENL [ASM_SIMP_TAC [SUP_FINITE]; ALL_TAC] THEN
  ABBREV_TAC `(i:real) = sup (IMAGE real_of_int P)` THEN
    SUBGOAL_THEN `(P:int->bool) = IMAGE int_of_real (IMAGE real_of_int P)`
    (fun th -> ONCE_REWRITE_TAC [th]) THENL [REWRITE_TAC [GSYM IMAGE_o]
        THEN ASM_REWRITE_TAC [IMAGE] THEN SET_TAC []; ALL_TAC] THEN
  UNDISCH_TAC `i IN IMAGE real_of_int P` THEN
    EXPAND_TAC "i" THEN DISCH_TAC THEN REWRITE_TAC [IN_IMAGE] THEN
    EXISTS_TAC `sup (IMAGE real_of_int P)` THEN
    REWRITE_TAC [] THEN
    EXISTS_TAC `int_sup (IMAGE int_of_real (IMAGE real_of_int P))` THEN
    REWRITE_TAC [int_sup] THEN
    REWRITE_TAC [GSYM IMAGE_o] THEN
    SUBGOAL_THEN `(real_of_int o int_of_real) o real_of_int =
    real_of_int o (int_of_real o real_of_int)` (fun th -> REWRITE_TAC [th])
      THENL [REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
      REWRITE_TAC [o_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `!(f:int->real). f o (\(x:int). x) = f`
    (fun th -> REWRITE_TAC [th]) THENL [GEN_TAC THEN
      REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC [o_THM]; ALL_TAC]
    THEN CONJ_TAC THENL [EXPAND_TAC "i" THEN MATCH_MP_TAC EQ_SYM THEN
      REWRITE_TAC [GSYM int_rep; is_int] THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
      THEN GEN_TAC THEN STRIP_TAC THEN
      UNDISCH_TAC `sup (IMAGE real_of_int P) = i` THEN
      ASM_REWRITE_TAC [] THEN DISCH_TAC THEN REWRITE_TAC [dest_int_rep]; 
    POP_ASSUM MP_TAC THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `sup (IMAGE real_of_int P) = i` THEN ASM_REWRITE_TAC [] ]);;

let INT_INF_SUP_FINITE_lemma = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ FINITE P ==>
    int_inf P <= int_sup P`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (IMAGE real_of_int P)` ASSUME_TAC THENL
    [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `~((IMAGE real_of_int P) = (EMPTY:real->bool))` ASSUME_TAC
    THENL [UNDISCH_TAC `~((P:int->bool) = (EMPTY:int->bool))` THEN
    ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
    REWRITE_TAC [TAUT `!P. ~(~P) <=> P`] THEN REWRITE_TAC [IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `sup (IMAGE real_of_int P) IN (IMAGE real_of_int P)`
  ASSUME_TAC THENL [ASM_SIMP_TAC [SUP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `inf (IMAGE real_of_int P) IN (IMAGE real_of_int P)`
  ASSUME_TAC THENL [ASM_SIMP_TAC [INF_FINITE]; ALL_TAC] THEN
  REWRITE_TAC [int_sup; int_le] THEN
  SUBGOAL_THEN `real_of_int (int_of_real (sup (IMAGE real_of_int P))) =
  sup (IMAGE real_of_int P)` (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [GSYM int_rep; is_int] THEN
    UNDISCH_TAC `sup (IMAGE real_of_int P) IN IMAGE real_of_int P`
    THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [dest_int_rep]; ALL_TAC]
  THEN REWRITE_TAC [int_inf] THEN
  SUBGOAL_THEN `real_of_int (int_of_real (inf (IMAGE real_of_int P))) =
  (inf (IMAGE real_of_int P))` (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [GSYM int_rep; is_int] THEN
    UNDISCH_TAC `inf (IMAGE real_of_int P) IN IMAGE real_of_int P`
    THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [dest_int_rep]; ALL_TAC]
  THEN ASM_SIMP_TAC [SUP_FINITE]);;

let INT_INF_FINITE_lemma2 = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ FINITE P ==>
     (!x:int. x IN P ==> int_inf P <= x)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [int_inf]
  THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE (IMAGE real_of_int P)` ASSUME_TAC THENL
    [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `~((IMAGE real_of_int P) = (EMPTY:real->bool))` ASSUME_TAC
    THENL [UNDISCH_TAC `~((P:int->bool) = (EMPTY:int->bool))` THEN
    ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
    REWRITE_TAC [TAUT `!P. ~(~P) <=> P`] THEN REWRITE_TAC [IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `inf (IMAGE real_of_int P) IN (IMAGE real_of_int P)`
  ASSUME_TAC THENL [ASM_SIMP_TAC [INF_FINITE]; ALL_TAC] THEN
  REWRITE_TAC [int_le] THEN
  SUBGOAL_THEN `real_of_int (int_of_real (inf (IMAGE real_of_int P))) =
  (inf (IMAGE real_of_int P))` (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [GSYM int_rep; is_int] THEN
    UNDISCH_TAC `inf (IMAGE real_of_int P) IN IMAGE real_of_int P`
    THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [dest_int_rep]; ALL_TAC]
  THEN SUBGOAL_THEN `real_of_int x IN IMAGE real_of_int P` ASSUME_TAC
    THENL [REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC `x:int` THEN
    ASM_REWRITE_TAC []; ALL_TAC] THEN
  ASM_SIMP_TAC [INF_FINITE]);;

let INT_SUP_FINITE_lemma2 = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ FINITE P ==>
     (!x:int. x IN P ==> x <= int_sup P)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [int_sup]
  THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE (IMAGE real_of_int P)` ASSUME_TAC THENL
    [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `~((IMAGE real_of_int P) = (EMPTY:real->bool))` ASSUME_TAC
    THENL [UNDISCH_TAC `~((P:int->bool) = (EMPTY:int->bool))` THEN
    ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
    REWRITE_TAC [TAUT `!P. ~(~P) <=> P`] THEN REWRITE_TAC [IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `sup (IMAGE real_of_int P) IN (IMAGE real_of_int P)`
  ASSUME_TAC THENL [ASM_SIMP_TAC [SUP_FINITE]; ALL_TAC] THEN
  REWRITE_TAC [int_le] THEN
  SUBGOAL_THEN `real_of_int (int_of_real (sup (IMAGE real_of_int P))) =
  (sup (IMAGE real_of_int P))` (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [GSYM int_rep; is_int] THEN
    UNDISCH_TAC `sup (IMAGE real_of_int P) IN IMAGE real_of_int P`
    THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [dest_int_rep]; ALL_TAC]
  THEN SUBGOAL_THEN `real_of_int x IN IMAGE real_of_int P` ASSUME_TAC
    THENL [REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC `x:int` THEN
    ASM_REWRITE_TAC []; ALL_TAC] THEN
  ASM_SIMP_TAC [SUP_FINITE]);;

let WELL_ORDERED_NUM = prove
(`!(P:num->bool). ~(P = (EMPTY:num->bool)) ==>
    (?a. P a /\ (!b. P b ==> a <= b))`,
  GEN_TAC THEN ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`]
  THEN REWRITE_TAC [TAUT `!P. ~ (~P) <=> P`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((P:num->bool) = (EMPTY:num->bool)) <=>
  (!(n:num). ~(P n))` (fun th -> REWRITE_TAC [th]) THENL [SET_TAC []; ALL_TAC]
  THEN MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~(?a. (P:num->bool) a /\ (!b. (P:num->bool) b ==> a <= b))` THEN
  ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
  REWRITE_TAC [TAUT `!P. ~ (~P) <=> P`] THEN DISCH_TAC THEN EXISTS_TAC `n:num`
  THEN ASM_REWRITE_TAC [] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`]
  THEN ASM_REWRITE_TAC [ARITH_RULE `!(n:num) m. ~(n <= m) <=> m < n`]);;

let int_LEFT_HALFLINE_MAX = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ (?b. !z. z IN P ==> z <= b) ==>
  (?(k:int). P k /\ (!x. P x ==> x <= k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
  `~((((P:int->bool) o (\(g:int). (int_neg g) + b)) o int_of_num) = (EMPTY:num->bool))`
  ASSUME_TAC THENL
    [UNDISCH_TAC `~((P:int->bool) = {})` THEN REWRITE_TAC [EMPTY; FUN_EQ_THM;
    o_THM; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN DISCH_TAC
    THEN EXISTS_TAC `num_of_int ((b:int) - x)` THEN
    UNDISCH_TAC `!z. z IN (P:int->bool) ==> z <= b`
    THEN REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`] THEN DISCH_TAC
    THEN SUBGOAL_THEN `int_of_num 0 <= b - x` ASSUME_TAC THENL
      [REWRITE_TAC [ARITH_RULE `!(a:int) b. int_of_num 0 <= a - b <=> b <= a`]
      THEN ASM_SIMP_TAC []; ALL_TAC] THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT]
    THEN ASM_REWRITE_TAC [ARITH_RULE `int_neg (b - x) + b = x`]; ALL_TAC] THEN
  SUBGOAL_THEN `?(n:num).
    (((P:int->bool) o (\(g:int). (int_neg g) + b)) o int_of_num) n /\
    (!m. (((P:int->bool) o (\(g:int). (int_neg g) + b)) o int_of_num) m ==> n <= m)`
  ASSUME_TAC THENL
    [POP_ASSUM MP_TAC THEN
    ABBREV_TAC `R = (((P:int->bool) o (\(g:int). (int_neg g) + b)) o int_of_num)`
    THEN REWRITE_TAC [WELL_ORDERED_NUM]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC `((\(g:int). (int_neg g) + b) o int_of_num) n` THEN
    REWRITE_TAC [o_THM] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [o_THM]
    THEN SIMP_TAC [] THEN STRIP_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `?(j:num). (x:int) = int_neg (int_of_num j) + b`
    ASSUME_TAC THENL
      [EXISTS_TAC `num_of_int (b - x)` THEN
      SUBGOAL_THEN `int_of_num 0 <= (b:int) - x` ASSUME_TAC THENL
        [UNDISCH_TAC `!(z:int). z IN P ==> z <= b` THEN
        REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`] THEN
        DISCH_TAC THEN REWRITE_TAC [ARITH_RULE
        `!a b. int_of_num 0 <= a - b <=> b <= a`] THEN ASM_SIMP_TAC []; ALL_TAC]
      THEN ASM_SIMP_TAC [INT_OF_NUM_OF_INT] THEN ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ARITH_RULE `!(a:int) b c. -- a + b <= -- c + b <=> c <= a`]
    THEN REWRITE_TAC [INT_OF_NUM_LE] THEN UNDISCH_TAC `(P:int->bool) x` THEN
    ASM_REWRITE_TAC []);;

let SUP_DISCRETE_REAL = prove
(`!(P:int->bool) (f:int->real). ~(P = (EMPTY:int->bool)) /\
  (?b. !z. z IN P ==> z <= b)
  ==> sup (IMAGE real_of_int P) IN (IMAGE real_of_int P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(?(k:int). P k /\ (!x. P x ==> x <= k))` ASSUME_TAC
    THENL [MATCH_MP_TAC int_LEFT_HALFLINE_MAX THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `b:int` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `sup (IMAGE real_of_int P) = real_of_int k` ASSUME_TAC
  THENL [MATCH_MP_TAC REAL_SUP_UNIQUE THEN
  CONJ_TAC THENL [GEN_TAC THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM int_le]
    THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`];
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `real_of_int k` THEN ASM_REWRITE_TAC []
    THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC `k:int` THEN
    ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`]]; ALL_TAC] THEN
  ASM_REWRITE_TAC [IN_IMAGE] THEN
  EXISTS_TAC `k:int` THEN ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`]);;

let SUP_DISCRETE = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ (?b. !z. z IN P ==> z <= b) ==>
  int_sup P IN P`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(?(k:int). P k /\ (!x. P x ==> x <= k))` ASSUME_TAC
    THENL [MATCH_MP_TAC int_LEFT_HALFLINE_MAX THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `b:int` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC
  THEN DISCH_TAC THEN
  SUBGOAL_THEN `int_sup P = k` ASSUME_TAC THENL [REWRITE_TAC [int_sup; int_eq]
    THEN SUBGOAL_THEN `sup (IMAGE real_of_int P) IN IMAGE real_of_int P`
    ASSUME_TAC THENL [MATCH_MP_TAC SUP_DISCRETE_REAL THEN
      ASM_REWRITE_TAC [] THEN EXISTS_TAC `b:int` THEN ASM_REWRITE_TAC []; ALL_TAC]
    THEN SUBGOAL_THEN `real_of_int (int_of_real (sup (IMAGE real_of_int P))) =
    (sup (IMAGE real_of_int P))` (fun th -> REWRITE_TAC [th]) THENL
      [REWRITE_TAC [GSYM int_rep; is_int] THEN
      UNDISCH_TAC `sup (IMAGE real_of_int P) IN IMAGE real_of_int P`
      THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
      THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [dest_int_rep]; ALL_TAC]
    THEN MATCH_MP_TAC REAL_SUP_UNIQUE THEN
    CONJ_TAC THENL [GEN_TAC THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
      THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [GSYM int_le] THEN POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`]; GEN_TAC THEN DISCH_TAC
      THEN EXISTS_TAC `real_of_int k` THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [IN_IMAGE; SET_RULE `!P x. x IN P <=> P x`] THEN
      EXISTS_TAC `k:int` THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
  ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`]);;

let int_RIGHT_HALFLINE_MIN = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ (?b. !z. z IN P ==> b <= z) ==>
  (?(k:int). P k /\ (!x. P x ==> k <= x))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?(Q:int->bool). Q = P o int_neg` ASSUME_TAC THENL
    [EXISTS_TAC `(P:int->bool) o int_neg` THEN REWRITE_TAC []; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC
  THEN DISCH_TAC THEN
  SUBGOAL_THEN `?y. (!z. z IN (Q:int->bool) ==> z <= y)` ASSUME_TAC THENL
    [EXISTS_TAC `int_neg b` THEN GEN_TAC THEN
    ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`; o_THM] THEN
    ONCE_REWRITE_TAC [ARITH_RULE `!(a:int) b. a <= int_neg b <=> b <= int_neg a`]
    THEN UNDISCH_TAC `!(z:int). z IN P ==> b <= z` THEN
    SIMP_TAC [SET_RULE `!P x. x IN P <=> P x`]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC
  THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(Q = (EMPTY:int->bool))` ASSUME_TAC THENL
    [ASM_REWRITE_TAC [] THEN UNDISCH_TAC `~(P = (EMPTY:int->bool))` THEN
    REWRITE_TAC [EMPTY; FUN_EQ_THM; o_THM; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `int_neg x` THEN
    ASM_REWRITE_TAC [ARITH_RULE `!a. int_neg (int_neg a) = a`]; ALL_TAC]
  THEN SUBGOAL_THEN `(?(k:int). Q k /\ (!x. Q x ==> x <= k))` ASSUME_TAC THENL
    [MATCH_MP_TAC int_LEFT_HALFLINE_MAX THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC []; EXISTS_TAC `y:int` THEN ASM_REWRITE_TAC []]; ALL_TAC]
  THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC
  THEN DISCH_TAC THEN EXISTS_TAC `int_neg k` THEN
  CONJ_TAC THENL [POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN
    SIMP_TAC [o_THM]; GEN_TAC THEN POP_ASSUM MP_TAC THEN STRIP_TAC
    THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [LEFT_IMP_FORALL_THM] THEN EXISTS_TAC `int_neg x` THEN
    REWRITE_TAC [o_THM; ARITH_RULE `!a. int_neg (int_neg a) = a`] THEN
    DISCH_TAC THEN
    ONCE_REWRITE_TAC [ARITH_RULE `!(a:int) b. int_neg a <= b <=> int_neg b <= a`]
    THEN ASM_REWRITE_TAC []]);;

let INF_DISCRETE_REAL = prove
(`!(P:int->bool) (f:int->real). ~(P = (EMPTY:int->bool)) /\
  (?b. !z. z IN P ==> b <= z)
  ==> inf (IMAGE real_of_int P) IN (IMAGE real_of_int P)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(?(k:int). P k /\ (!x. P x ==> k <= x))` ASSUME_TAC
    THENL [MATCH_MP_TAC int_RIGHT_HALFLINE_MIN THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `b:int` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `inf (IMAGE real_of_int P) = real_of_int k` ASSUME_TAC
  THENL [MATCH_MP_TAC REAL_INF_UNIQUE THEN
  CONJ_TAC THENL [GEN_TAC THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN REWRITE_TAC [GSYM int_le]
    THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`];
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `real_of_int k` THEN ASM_REWRITE_TAC []
    THEN REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC `k:int` THEN
    ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`]]; ALL_TAC] THEN
  ASM_REWRITE_TAC [IN_IMAGE] THEN
  EXISTS_TAC `k:int` THEN ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`]);;

let INF_DISCRETE = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ (?b. !z. z IN P ==> b <= z) ==>
  int_inf P IN P`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(?(k:int). P k /\ (!x. P x ==> k <= x))` ASSUME_TAC
    THENL [MATCH_MP_TAC int_RIGHT_HALFLINE_MIN THEN ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `b:int` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC
  THEN DISCH_TAC THEN
  SUBGOAL_THEN `int_inf P = k` ASSUME_TAC THENL
    [REWRITE_TAC [int_inf; int_eq]
    THEN SUBGOAL_THEN `inf (IMAGE real_of_int P) IN IMAGE real_of_int P`
    ASSUME_TAC THENL [MATCH_MP_TAC INF_DISCRETE_REAL THEN
      ASM_REWRITE_TAC [] THEN EXISTS_TAC `b:int` THEN ASM_REWRITE_TAC []; ALL_TAC]
    THEN SUBGOAL_THEN `real_of_int (int_of_real (inf (IMAGE real_of_int P))) =
    (inf (IMAGE real_of_int P))` (fun th -> REWRITE_TAC [th]) THENL
      [REWRITE_TAC [GSYM int_rep; is_int] THEN
      UNDISCH_TAC `inf (IMAGE real_of_int P) IN IMAGE real_of_int P`
      THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
      THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [dest_int_rep]; ALL_TAC]
    THEN MATCH_MP_TAC REAL_INF_UNIQUE THEN
    CONJ_TAC THENL [GEN_TAC THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
      THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [GSYM int_le] THEN POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`]; GEN_TAC THEN DISCH_TAC
      THEN EXISTS_TAC `real_of_int k` THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [IN_IMAGE; SET_RULE `!P x. x IN P <=> P x`] THEN
      EXISTS_TAC `k:int` THEN ASM_REWRITE_TAC []]; ALL_TAC] THEN
  ASM_REWRITE_TAC [SET_RULE `!P x. x IN P <=> P x`]);;

let [SUP_lemma1; SUP_lemma2] = map DISCH_ALL
  (CONJUNCTS (UNDISCH (SPEC_ALL SUP)));;
(* HOL complains. Why? *)

let [INF_lemma1; INF_lemma2] = map DISCH_ALL
  (CONJUNCTS (UNDISCH (SPEC_ALL INF)));;

let INTSUP_IS_BIGGER = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ (?h. !z. z IN P ==> z <= h) ==>
  (!x. x IN P ==> x <= int_sup P)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC [int_sup; int_le] THEN
  SUBGOAL_THEN `sup (IMAGE real_of_int P) IN (IMAGE real_of_int P)`
  ASSUME_TAC THENL [MATCH_MP_TAC SUP_DISCRETE_REAL THEN
    ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `real_of_int (int_of_real (sup (IMAGE real_of_int P))) =
  (sup (IMAGE real_of_int P))` (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [GSYM int_rep; is_int] THEN
    UNDISCH_TAC `sup (IMAGE real_of_int P) IN IMAGE real_of_int P`
    THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [dest_int_rep]; ALL_TAC]
  THEN SUBGOAL_THEN `real_of_int x IN IMAGE real_of_int P` ASSUME_TAC THENL
    [REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC `x:int` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN ABBREV_TAC `v = real_of_int x` THEN
  SPEC_TAC (`v:real`, `v:real`) THEN
  MATCH_MP_TAC (GEN `s:real->bool` SUP_lemma1) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC [IMAGE_EQ_EMPTY];
    EXISTS_TAC `real_of_int h` THEN REWRITE_TAC [IN_IMAGE] THEN
    GEN_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN DISCH_TAC
    THEN ASM_REWRITE_TAC [GSYM int_le] THEN ASM_SIMP_TAC []]);;

let INTINF_IS_SMALLER = prove
(`!(P:int->bool). ~(P = (EMPTY:int->bool)) /\ (?h. !z. z IN P ==> h <= z) ==>
  (!x. x IN P ==> int_inf P <= x)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC [int_inf; int_le] THEN
  SUBGOAL_THEN `inf (IMAGE real_of_int P) IN (IMAGE real_of_int P)`
  ASSUME_TAC THENL [MATCH_MP_TAC INF_DISCRETE_REAL THEN
    ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `real_of_int (int_of_real (inf (IMAGE real_of_int P))) =
  (inf (IMAGE real_of_int P))` (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [GSYM int_rep; is_int] THEN
    UNDISCH_TAC `inf (IMAGE real_of_int P) IN IMAGE real_of_int P`
    THEN REWRITE_TAC [IN_IMAGE; LEFT_IMP_EXISTS_THM]
    THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC [dest_int_rep]; ALL_TAC]
  THEN SUBGOAL_THEN `real_of_int x IN IMAGE real_of_int P` ASSUME_TAC THENL
    [REWRITE_TAC [IN_IMAGE] THEN EXISTS_TAC `x:int` THEN ASM_REWRITE_TAC [];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN ABBREV_TAC `v = real_of_int x` THEN
  SPEC_TAC (`v:real`, `v:real`) THEN
  MATCH_MP_TAC (GEN `s:real->bool` INF_lemma1) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN STRIP_TAC THEN STRIP_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC [IMAGE_EQ_EMPTY];
    EXISTS_TAC `real_of_int h` THEN REWRITE_TAC [IN_IMAGE] THEN
    GEN_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN DISCH_TAC
    THEN ASM_REWRITE_TAC [GSYM int_le] THEN ASM_SIMP_TAC []]);;

let int_INFINITE_HALFLINE_1 = prove
(`!(P:int->bool) k. (!x. (P:int->bool) x ==> x <= k) /\ ~(FINITE (P:int->bool))
    ==> (!(w:int). ?q. q < w /\ (P:int->bool) q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(FINITE (P:int->bool))` ASSUME_TAC
  THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
    REWRITE_TAC [TAUT `!P. ~(~P) <=> P`; NOT_FORALL_THM; int_FINITE;
    LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN
    REWRITE_TAC [NOT_EXISTS_THM; DE_MORGAN_THM] THEN STRIP_TAC THEN
    EXISTS_TAC
    `if int_of_num 0 <= w then (if (w <= (k:int)) then k else w)
     else (if (int_of_num 0 <= k) then (if (int_neg w <= k) then k else int_neg w)
                                else int_neg w)` THEN
  COND_CASES_TAC THENL
    [COND_CASES_TAC THENL
        [GEN_TAC THEN CONJ_TAC THENL
          [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
          ALL_TAC] THEN
      DISCH_TAC THEN CONJ_TAC THENL
        [SUBGOAL_THEN `w <= (x:int)` ASSUME_TAC THENL
          [REWRITE_TAC [ARITH_RULE `!(a:int) b. a <= b <=> ~(b < a)`] THEN
          POP_ASSUM MP_TAC THEN REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`] THEN
          ASM_MESON_TAC []; ALL_TAC] THEN REPEAT (POP_ASSUM MP_TAC)
          THEN ARITH_TAC; POP_ASSUM MP_TAC THEN
          REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`] THEN ASM_SIMP_TAC []];
      GEN_TAC THEN ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`] THEN
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC [ARITH_RULE `!(a:int) b. ~(a <= b) <=> b < a`] THEN
      DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:int) <= k` ASSUME_TAC THENL [ASM_SIMP_TAC []; ALL_TAC]
    THEN CONJ_TAC THENL [SUBGOAL_THEN `~((x:int) < w)`
      ASSUME_TAC THENL [ASM_MESON_TAC []; ALL_TAC] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;
      REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC]];
  COND_CASES_TAC THENL
    [COND_CASES_TAC THENL
        [ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [SET_RULE `!P. x IN P <=> P x`]
        THEN GEN_TAC THEN DISCH_TAC THEN
        SUBGOAL_THEN `~((x:int) < w)` ASSUME_TAC THENL
          [ASM_MESON_TAC []; ALL_TAC] THEN
        REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    GEN_TAC THEN CONJ_TAC THENL [REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC]
    THEN DISCH_TAC THEN CONJ_TAC THENL
      [REWRITE_TAC [ARITH_RULE `!(a:int) b. (int_neg (int_neg a) <= b) <=> ~(b < a)`]
      THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`]
      THEN ASM_MESON_TAC []; SUBGOAL_THEN `(x:int) <= k` ASSUME_TAC THENL
        [POP_ASSUM MP_TAC THEN REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`] THEN
        ASM_MESON_TAC []; ALL_TAC] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC];
  GEN_TAC THEN CONJ_TAC THENL
      [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`] THEN
    DISCH_TAC THEN CONJ_TAC THENL
      [ASM_MESON_TAC [ARITH_RULE `!a:int. -- -- a = a`; 
      ARITH_RULE `!(a:int) b. a <= b <=> ~(b < a)`];
      SUBGOAL_THEN `(x:int) <= k` ASSUME_TAC THENL
        [ASM_MESON_TAC []; ALL_TAC] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC]]]);;

let int_INFINITE_HALFLINE_2 = prove
(`!P k.(!x. (P:int->bool) x ==> k <= x) /\ ~(FINITE (P:int->bool))
    ==> (!(w:int). ?q. w < q /\ (P:int->bool) q)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?(Q:int->bool). !x. Q x <=> P (int_neg x)` ASSUME_TAC
    THENL [EXISTS_TAC `(P:int->bool) o int_neg` THEN
    REWRITE_TAC [o_THM; ARITH_RULE `!a:int. int_neg (int_neg a) = a`]; ALL_TAC]
  THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x. (Q:int->bool) x ==> x <= -- k` ASSUME_TAC THENL
    [ASM_REWRITE_TAC [ARITH_RULE `!a:int b. a <= --b <=> b <= --a`] THEN
    GEN_TAC THEN ABBREV_TAC `(y:int) = --x` THEN ASM_REWRITE_TAC []; ALL_TAC]
  THEN SUBGOAL_THEN `~(FINITE (Q:int->bool))` ASSUME_TAC THENL
    [SUBGOAL_THEN `~(FINITE (P:int->bool))` ASSUME_TAC THENL
      [ASM_REWRITE_TAC []; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC
    [GSYM (TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`)] THEN
    SUBGOAL_THEN `(P:int->bool) = IMAGE int_neg (Q:int->bool)`
    (fun th -> REWRITE_TAC [th]) THENL
      [REWRITE_TAC [SET_RULE `!P Q. P = Q <=> (P SUBSET Q /\ Q SUBSET P)`]
      THEN REWRITE_TAC [SUBSET; IMAGE; IN_ELIM_THM] THEN
      CONJ_TAC THENL [GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `int_neg x`
        THEN REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`] THEN
        ASM_REWRITE_TAC [ARITH_RULE `!a:int. int_neg (int_neg a) = a`]
        THEN POP_ASSUM MP_TAC THEN SET_TAC []; GEN_TAC THEN
        REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC [] THEN UNDISCH_TAC `(x':int) IN Q` THEN
        REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`] THEN ASM_MESON_TAC []]; ALL_TAC]
    THEN REWRITE_TAC [FINITE_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!(a:int). ?b. b < a /\ (Q:int->bool) b` ASSUME_TAC
    THENL [MATCH_MP_TAC int_INFINITE_HALFLINE_1 THEN
    EXISTS_TAC `int_neg k` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  GEN_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC [LEFT_IMP_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  EXISTS_TAC `int_neg w` THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `int_neg b`
  THEN ONCE_REWRITE_TAC [ARITH_RULE `!i j. i < int_neg j <=> j < int_neg i`]
  THEN ASM_REWRITE_TAC [] THEN ASM_MESON_TAC []);;

(* ---------------------------------------------------------------------- *)
(*   Now I split a very nice hypotesis in cases, for operative purposes   *)
(* ---------------------------------------------------------------------- *)

let int_CONNECTED = prove
(`!(P:int->bool). (!n m. (n <= m /\ P n /\ P m ==> {x | n <= x /\ x <= m} SUBSET P))
  ==>
    ((?a. ?b. P = {(x:int) | a <= x /\ x <= b} /\ a <= b) \/
    (?c. P = {(x:int) | c <= x}) \/
    (?d. P = {(x:int) | x <= d}) \/
    (!(k:int). P k) \/ (!(k:int). ~(P k)))`,
  GEN_TAC THEN DISCH_TAC THEN
(* the segment or the empty set *)
  ASM_CASES_TAC `FINITE (P:int->bool)` THENL
    [ASM_CASES_TAC `P = (EMPTY:int->bool)` THENL
      [SUBGOAL_THEN `(!(k:int). ~((P:int->bool) k)) <=> (P = (EMPTY:int->bool))`
      (fun th -> REWRITE_TAC [th]) THENL [SET_TAC []; ALL_TAC] THEN
      ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `(?a. ?b. P = {(x:int) | a <= x /\ x <= b} /\ a <= b)`
    (fun th -> REWRITE_TAC [th]) THENL
      [EXISTS_TAC `int_inf P` THEN EXISTS_TAC `int_sup P` THEN
      ASM_SIMP_TAC [INT_INF_SUP_FINITE_lemma] THEN
      REWRITE_TAC [SET_RULE `!P Q. (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`] THEN
      CONJ_TAC THENL
        [REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
        ASM_SIMP_TAC [INT_INF_FINITE_lemma2; INT_SUP_FINITE_lemma2];
        SUBGOAL_THEN `int_inf P <= int_sup P /\ P (int_inf P) /\ P (int_sup P)`
        ASSUME_TAC THENL [ASM_SIMP_TAC [INT_INF_SUP_FINITE_lemma] THEN
          CONJ_TAC THENL [ONCE_REWRITE_TAC [SET_RULE `!P. P x <=> x IN P`] THEN
            ASM_SIMP_TAC [INT_INF_FINITE_lemma1];
            ONCE_REWRITE_TAC [SET_RULE `!P. P x <=> x IN P`] THEN
            ASM_SIMP_TAC [INT_SUP_FINITE_lemma1]]; ALL_TAC] THEN ASM_SIMP_TAC []]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(?c. (P:int->bool) = {x | c <= x}) \/
  (?d. (P:int->bool) = {x | x <= d}) \/
  (!k. (P:int->bool) k)` (fun th -> MESON_TAC [th]) THEN
 (* all the integers *)
  ASM_CASES_TAC `!k. (P:int->bool) k` THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(!x. (P:int->bool) x ==> x <= k) \/
    (!x. (P:int->bool) x ==> k <= x)` ASSUME_TAC THENL
    [UNDISCH_TAC `!n m. n <= m /\ (P:int->bool) n /\ (P:int->bool) m
          ==> {(x:int) | n <= x /\ x <= m} SUBSET P` THEN
    ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
    REWRITE_TAC [DE_MORGAN_THM; NOT_FORALL_THM;
    TAUT `!P Q. ~(P ==> Q) <=> (P /\ ~Q)`] THEN STRIP_TAC THEN
    EXISTS_TAC `x':int` THEN EXISTS_TAC `x:int` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC [] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;
      REWRITE_TAC [SUBSET; IN_ELIM_THM; NOT_FORALL_THM] THEN
      EXISTS_TAC `k:int` THEN REWRITE_TAC [TAUT `!P Q. ~(P ==> Q) <=> (P /\ ~Q)`]
      THEN CONJ_TAC THENL [REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; 
        REWRITE_TAC [SET_RULE `!(P:A->bool) x:A. x IN P <=> P x`] THEN
        ASM_REWRITE_TAC []]]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN STRIP_TAC THENL
(* left halfline *)
    [SUBGOAL_THEN `(?d. (P:int->bool) = {x | x <= d})`
    (fun th -> REWRITE_TAC [th]) THEN
      EXISTS_TAC `int_sup P` THEN
      REWRITE_TAC [SET_RULE `!P Q. (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`] THEN
      CONJ_TAC THENL [REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
        MATCH_MP_TAC INTSUP_IS_BIGGER THEN
        CONJ_TAC THENL [ASM_MESON_TAC [FINITE_RULES]; EXISTS_TAC `k:int`
        THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`]
        THEN MESON_TAC []]; ALL_TAC] THEN REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
      STRUCT_CASES_TAC (SPEC_ALL int_INFINITE_HALFLINE_1) THEN
      POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
(* codificare in modo classico che P e` infinito, ASSUME_TAC.
quindi contronominale sulla connessione *)
      UNDISCH_TAC
        `!(n:int) m. n <= m /\ P n /\ P m ==> {x | n <= x /\ x <= m} SUBSET P` THEN
        ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
        REWRITE_TAC [NOT_FORALL_THM; TAUT `!P Q. ~(P ==> Q) <=> (P /\ ~Q)`]
      THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
      GEN_TAC THEN DISCH_TAC THEN UNDISCH_TAC `!w. ?q. q < w /\ (P:int->bool) q`
      THEN REWRITE_TAC [LEFT_IMP_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
      EXISTS_TAC `x:int` THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `q:int`
      THEN EXISTS_TAC `int_sup P` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
          ONCE_REWRITE_TAC [SET_RULE `!P. P x <=> x IN P`] THEN
          MATCH_MP_TAC SUP_DISCRETE THEN
          CONJ_TAC THENL [POP_ASSUM MP_TAC THEN SET_TAC []; EXISTS_TAC `k:int`
            THEN REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`] THEN ASM_REWRITE_TAC []]];
        REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
        REWRITE_TAC [NOT_FORALL_THM; TAUT `!P Q. ~(P ==> Q) <=> (P /\ ~Q)`] THEN
        EXISTS_TAC `x:int` THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
        ARITH_TAC];
(* right halfline *)
    SUBGOAL_THEN `(?c. (P:int->bool) = {x | c <= x})`
    (fun th -> REWRITE_TAC [th]) THEN
      EXISTS_TAC `int_inf P` THEN
      REWRITE_TAC [SET_RULE `!P Q. (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`] THEN
      CONJ_TAC THENL [REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
        MATCH_MP_TAC INTINF_IS_SMALLER THEN
        CONJ_TAC THENL [ASM_MESON_TAC [FINITE_RULES]; EXISTS_TAC `k:int`
          THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`]
          THEN MESON_TAC []];
        ALL_TAC] THEN REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
      STRUCT_CASES_TAC (SPEC_ALL int_INFINITE_HALFLINE_2) THEN
      POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
      UNDISCH_TAC
        `!(n:int) m. n <= m /\ P n /\ P m ==> {x | n <= x /\ x <= m} SUBSET P` THEN
        ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
        REWRITE_TAC [NOT_FORALL_THM; TAUT `!P Q. ~(P ==> Q) <=> (P /\ ~Q)`]
      THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `!w. ?q. w < q /\ (P:int->bool) q` THEN
      REWRITE_TAC [LEFT_IMP_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
      EXISTS_TAC `x:int` THEN GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `int_inf P`
      THEN EXISTS_TAC `q:int` THEN
      CONJ_TAC THENL
        [ASM_REWRITE_TAC [] THEN CONJ_TAC THENL
          [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
          ONCE_REWRITE_TAC [SET_RULE `!P. P x <=> x IN P`] THEN
          MATCH_MP_TAC INF_DISCRETE THEN
          CONJ_TAC THENL [POP_ASSUM MP_TAC THEN SET_TAC []; EXISTS_TAC `k:int`
            THEN REWRITE_TAC [SET_RULE `!P. x IN P <=> P x`] THEN ASM_REWRITE_TAC []]];
        REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
        REWRITE_TAC [NOT_FORALL_THM; TAUT `!P Q. ~(P ==> Q) <=> (P /\ ~Q)`] THEN
        EXISTS_TAC `x:int` THEN ASM_REWRITE_TAC [] THEN POP_ASSUM MP_TAC THEN
        ARITH_TAC]]);;

(* ---------------------------------------------------------------------- *)
(*              I'm ready to prove a weakened version of the              *)
(*                    test for constant sequences above,                  *)
(*             in order to correct an error of Wilf and Zeilberg          *)
(* ---------------------------------------------------------------------- *)

let SEQ_CONST_WEAK = prove
(`!(P:int->bool) (f:int->real) (n0:int).
    ((!n m. n <= m /\ n IN P /\ m IN P
          ==> {x | n <= x /\ x <= m} SUBSET P) /\
    P n0 /\ 
    (!n. P n ==> f (n + int_of_num 1) - f n = real_of_num 0))
    ==> (!n. P n ==> f n = f n0)`,

  REWRITE_TAC [SET_RULE `!(P:A->bool) x:A. x IN P <=> P x`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRUCT_CASES_TAC ((SPEC_ALL int_CONNECTED))
  THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN STRIP_TAC THENL


  [SUBGOAL_THEN `?(g:int->real). g =
               (\(y:int). if y IN P
                          then (f:int->real) y
                          else (if y < a then (f:int->real) a
                               else f b))` ASSUME_TAC THENL
    [EXISTS_TAC `(\(y:int). if y IN P
               then (f:int->real) y
               else (if y < a then (f:int->real) a
                    else f b))` THEN REWRITE_TAC [EQ_REFL]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. (P:int->bool) n ==> (f:int->real) n = (g:int->real) n`
    ASSUME_TAC THENL [GEN_TAC THEN UNDISCH_TAC `(g:int->real) =
      (\y. if y IN P then f y else if y < a then f a else f b)` THEN
    REWRITE_TAC [SET_RULE `!(P:A->bool) x:A. x IN P <=> P x`] THEN
    SIMP_TAC []; ALL_TAC] THEN POP_ASSUM MP_TAC THEN UNDISCH_TAC `(P:int->bool) n0`
  THEN SIMP_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC
  THEN MATCH_MP_TAC GENERAL_SEQ_CONST_TEST_int THEN GEN_TAC THEN
  ASM_CASES_TAC `(n':int) IN P` THENL
    [ASM_REWRITE_TAC [] THEN
    COND_CASES_TAC THENL
      [COND_CASES_TAC THENL [UNDISCH_TAC `(n':int) IN P` THEN
        ASM_SIMP_TAC [SET_RULE `!(P:A->bool) x:A. x IN P <=> P x`];
        SUBGOAL_THEN `n' + int_of_num 1 = a` (fun th -> REWRITE_TAC [th])
          THENL [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN 
          REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `n' < (a:int)` (fun th -> REWRITE_TAC [th]) THENL
          [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
          REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`]];
      COND_CASES_TAC THENL
      [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC;
      SUBGOAL_THEN `(n':int) = b` (fun th -> REWRITE_TAC [th]) THENL
        [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
        ASM_REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(b:int) IN {(x:int) | a <= x /\ x <= b}`
      (fun th -> REWRITE_TAC [th]) THENL
        [UNDISCH_TAC `(a:int) <= b` THEN
        REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`]]];
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `~((n':int) IN {(x:int) | a <= x /\ x <= b})`
      (fun th -> REWRITE_TAC [th]) THENL
        [SUBGOAL_THEN `{(x:int) | a <= x /\ x <= b} = P` (fun th -> REWRITE_TAC [th])
        THENL [MATCH_MP_TAC EQ_SYM THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
        ASM_MESON_TAC []; ALL_TAC] THEN
    COND_CASES_TAC THENL
      [SUBGOAL_THEN `n' + int_of_num 1 = a` ASSUME_TAC THENL
        [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC [] THEN
        REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(n':int) < a` (fun th -> ASM_REWRITE_TAC [th])
      THENL [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`];
      COND_CASES_TAC THENL
        [SUBGOAL_THEN `(n':int) < a` (fun th -> ASM_REWRITE_TAC [th])
        THENL [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`];
        SUBGOAL_THEN `~((n':int) < a)` (fun th -> ASM_REWRITE_TAC [th]) THENL
          [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC
          THEN ASM_REWRITE_TAC [IN_ELIM_THM] THEN
          UNDISCH_TAC `(a:int) <= b` THEN
          ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`]]]];

  SUBGOAL_THEN `?(g:int->real). g =
               (\(y:int). if y IN P
                          then (f:int->real) y
                          else f c)` ASSUME_TAC THENL
    [EXISTS_TAC `(\(y:int). if y IN P then (f:int->real) y
                          else f c)` THEN REWRITE_TAC [EQ_REFL]; ALL_TAC]
  THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. (P:int->bool) n ==> (f:int->real) n = (g:int->real) n`
    ASSUME_TAC THENL [GEN_TAC THEN UNDISCH_TAC `(g:int->real) =
      (\y. if y IN P then f y else f c)` THEN
    REWRITE_TAC [SET_RULE `!(P:A->bool) x:A. x IN P <=> P x`] THEN
    SIMP_TAC []; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `(P:int->bool) n0` THEN SIMP_TAC [] THEN
  DISCH_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC GENERAL_SEQ_CONST_TEST_int THEN GEN_TAC THEN
  ASM_CASES_TAC `n' IN (P:int->bool)` THENL
    [POP_ASSUM MP_TAC THEN UNDISCH_TAC
    `g = (\y. if y IN P then (f:int->real) y else f c)` THEN SIMP_TAC []
    THEN COND_CASES_TAC THENL [DISCH_TAC THEN REWRITE_TAC
      [SET_RULE `!(P:A->bool) x:A. x IN P <=> P x`] THEN
      UNDISCH_TAC `!n. (P:int->bool) n ==>
      f (n + &1) - (f:int->real) n = &0` THEN SIMP_TAC []; ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c:int) = n'` (fun th -> REWRITE_TAC [th]) THENL
      [POP_ASSUM MP_TAC THEN UNDISCH_TAC `~(n' + &1 IN (P:int->bool))` THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`]; 
  POP_ASSUM MP_TAC THEN UNDISCH_TAC
  `g = (\y. if y IN P then (f:int->real) y else f c)` THEN SIMP_TAC [] THEN
  DISCH_TAC THEN DISCH_TAC THEN COND_CASES_TAC THENL
    [ASM_CASES_TAC `(c:int) = n' + int_of_num 1` THENL
      [ASM_REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`]; 
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC]; 
      REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`]]];

  SUBGOAL_THEN `?(g:int->real). g =
               (\(y:int). if y IN P
                          then (f:int->real) y
                          else f d)` ASSUME_TAC THENL
    [EXISTS_TAC `(\(y:int). if y IN P then (f:int->real) y
                          else f d)` THEN REWRITE_TAC [EQ_REFL]; ALL_TAC]
  THEN POP_ASSUM MP_TAC THEN REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n. (P:int->bool) n ==> (f:int->real) n = (g:int->real) n`
    ASSUME_TAC THENL [GEN_TAC THEN UNDISCH_TAC `(g:int->real) =
      (\y. if y IN P then f y else f d)` THEN
    REWRITE_TAC [SET_RULE `!(P:A->bool) x:A. x IN P <=> P x`] THEN
    SIMP_TAC []; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN UNDISCH_TAC `(P:int->bool) n0` THEN SIMP_TAC [] THEN
  DISCH_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC GENERAL_SEQ_CONST_TEST_int THEN GEN_TAC THEN
  ASM_CASES_TAC `n' IN (P:int->bool)` THENL
    [POP_ASSUM MP_TAC THEN UNDISCH_TAC
    `g = (\y. if y IN P then (f:int->real) y else f d)` THEN SIMP_TAC []
    THEN COND_CASES_TAC THENL [DISCH_TAC THEN REWRITE_TAC
      [SET_RULE `!(P:A->bool) x:A. x IN P <=> P x`] THEN
      UNDISCH_TAC `!n. (P:int->bool) n ==>
      f (n + &1) - (f:int->real) n = &0` THEN SIMP_TAC []; ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(d:int) = n'` (fun th -> REWRITE_TAC [th]) THENL
      [POP_ASSUM MP_TAC THEN UNDISCH_TAC `~(n' + &1 IN (P:int->bool))` THEN
      ASM_REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`];
  POP_ASSUM MP_TAC THEN UNDISCH_TAC
  `g = (\y. if y IN P then (f:int->real) y else f d)` THEN SIMP_TAC [] THEN
  DISCH_TAC THEN DISCH_TAC THEN COND_CASES_TAC THENL
    [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC [REAL_ARITH `!x:real. x - x = real_of_num 0`]];

  UNDISCH_TAC `!n. (P:int->bool) n ==> (f:int->real) (n + &1) - f n = &0` THEN
  ASM_REWRITE_TAC [] THEN DISCH_TAC THEN GEN_TAC THEN
  ASM_SIMP_TAC [GENERAL_SEQ_CONST_TEST_int];

  ASM_REWRITE_TAC []]);;

let NORMALIZE_LEMMA = prove
(`!a. ~(a = real_of_num 0) ==>
  (sum (:int) f = a <=> sum (:int) (\i. (f i) / a) = real_of_num 1)`,
 GEN_TAC THEN DISCH_TAC THEN
 TRANS_TAC `(sum (:int) f) * (real_of_num 1 / a) = a * (real_of_num 1 / a)`
  THENL [POP_ASSUM MP_TAC THEN REAL_FIELD_TAC;
  ASM_SIMP_TAC [REAL_FIELD `~(a = real_of_num 0) ==>
  a * real_of_num 1 / a = real_of_num 1`] THEN REWRITE_TAC [GSYM SUM_RMUL;
  REAL_FIELD `b * real_of_num 1 / a = b / a`]]);;

(* ---------------------------------------------------------------------- *)
(*               This lemma is the core of the next theorem               *)
(* ---------------------------------------------------------------------- *)

let FINITE_SUPPORT_TELESEQ_lemma = prove
(`!f:int->real g:int->real a:int b:int. 
  ((!n. f n = g (n + int_of_num 1) - g n) /\ 
  FINITE (support (+) g (:int)) /\
  (!k. (a < k \/ k < b) ==> f k = real_of_num 0) /\ int_of_num 0 <= m)
     ==>         
    ((g:int->real) (a + int_of_num 1 + m) = g (a + int_of_num 1) /\
    (g:int->real) (b - int_of_num 1 - m) = g (b - int_of_num 1))`,

  REPEAT GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC `int_of_num 0 <= m` THEN
  REWRITE_TAC [ARITH_RULE `(int_of_num 0 <= m) <=>
  (int_of_num 0 < m \/ m = int_of_num 0)`] THEN
  REWRITE_TAC [TAUT `!P Q R. (P \/ Q ==> R) <=> ((P ==> R) /\ (Q ==> R))`] THEN
  CONJ_TAC THENL [DISCH_TAC THEN
    SUBGOAL_THEN `!n. (g:int->real) (n - int_of_num 1) =
    g n - (f:int->real) (n - int_of_num 1)` ASSUME_TAC THENL
      [SUBGOAL_THEN `(!n. (g:int->real) (n - int_of_num 1) =
        g n - (f:int->real) (n - int_of_num 1)) <=>
        (!n. (g:int->real) (n - int_of_num 1) =
        g ((n - int_of_num 1) + int_of_num 1) - (f:int->real) (n - int_of_num 1))`
        (fun th -> REWRITE_TAC [th]) THENL
          [REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN
          REWRITE_TAC [FUN_EQ_THM] THEN GEN_TAC THEN
          (REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)) THEN ARITH_TAC; ALL_TAC] THEN
      GEN_TAC THEN ABBREV_TAC `c:int = n - int_of_num 1` THEN
      REWRITE_TAC [REAL_ARITH `!a:real b c. (a = b - c) <=> b = c + a`] THEN
      ASM_REWRITE_TAC [] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `int_of_num 0 < m` THEN SPEC_TAC (`m:int`, `m:int`) THEN
    MATCH_MP_TAC int_INDUCTION THEN REWRITE_TAC [INT_SUB_RZERO; INT_ADD_RID] THEN
    CONJ_TAC THENL
      [UNDISCH_TAC `!n. (f:int->real) n = g (n + int_of_num 1) - g n` THEN
      REWRITE_TAC [REAL_ARITH `!a:real b c. a = b - c <=> b = a + c`] THEN
      DISCH_TAC THEN
      REWRITE_TAC [ARITH_RULE `!a:int b c d. a + b + c + d = (a + b + c) + d`] THEN
      GEN_TAC THEN DISCH_TAC THEN
      DISCH_TAC THEN CONJ_TAC THENL
        [ASM_REWRITE_TAC [] THEN
        SUBGOAL_THEN `(f:int->real) (a + int_of_num 1 + m) = real_of_num 0`
        (fun th -> REWRITE_TAC [th]) THENL
          [SUBGOAL_THEN `a < (a:int) + int_of_num 1 + m` ASSUME_TAC THENL
            [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC []; ALL_TAC] THEN
        REWRITE_TAC [REAL_ADD_LID] THEN
        ASM_CASES_TAC `int_of_num 0 < m` THENL [ASM_SIMP_TAC []; ALL_TAC] THEN
        SUBGOAL_THEN `m = int_of_num 0` (fun th -> REWRITE_TAC [th]) THENL
          [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC [INT_ADD_RID]; ALL_TAC] THEN
      REWRITE_TAC [ARITH_RULE `!a:int b c d. a - b - (c + d) =
      (a - b - c) - d`] THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN `(f:int->real) (b - int_of_num 1 - m - int_of_num 1) = real_of_num 0`
      (fun th -> REWRITE_TAC [th]) THENL
        [SUBGOAL_THEN `b:int - int_of_num 1 - m - int_of_num 1 < b` ASSUME_TAC
        THENL [UNDISCH_TAC `int_of_num 0 < m + int_of_num 1` THEN ARITH_TAC; ALL_TAC]
        THEN ASM_SIMP_TAC []; ALL_TAC] THEN
      ASM_CASES_TAC `int_of_num 0 < m` THEN
      ASM_SIMP_TAC [REAL_SUB_RZERO] THEN
      REWRITE_TAC [REAL_SUB_RZERO] THEN
      SUBGOAL_THEN `m = int_of_num 0` (fun th -> REWRITE_TAC [th]) THENL
        [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC [INT_SUB_RZERO] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    CONJ_TAC THENL
      [REWRITE_TAC [ARITH_RULE `!a:int b c d. a + b + c - d = (a + b + c) - d`]
      THEN SUBGOAL_THEN `!n. (g:int->real) (n - &1) = g n - (f:int->real) (n - &1)`
      (fun th -> ONCE_REWRITE_TAC [th]) THENL
        [UNDISCH_TAC `!n. (g:int->real) (n - &1) = g n - (f:int->real) (n - &1)` THEN
        REWRITE_TAC []; ALL_TAC] THEN
        ASM_CASES_TAC `int_of_num 0 < m` THENL
          [SUBGOAL_THEN `a < ((a:int) + int_of_num 1 + m) - int_of_num 1` ASSUME_TAC
          THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
          UNDISCH_TAC `!k:int. a < k \/ k < b ==> f k = real_of_num 0` THEN
          UNDISCH_TAC `(a:int) < (a + &1 + m) - &1` THEN
          SIMP_TAC [REAL_SUB_RZERO] THEN REPEAT (DISCH_TAC) THEN ASM_SIMP_TAC [];
          REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC]; ALL_TAC] THEN
    REWRITE_TAC [ARITH_RULE `!a:int b c d. a - b - (c - d) =
    (a - c + d) - b`] THEN
    UNDISCH_TAC `!n:int. (f:int->real) n = (g:int->real) (n + &1) - g n`
    THEN ASM_REWRITE_TAC [] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((b:int) - m + int_of_num 1) - int_of_num 1 < b /\ 
      (b:int) - int_of_num 1 < b` ASSUME_TAC THENL
      [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `!k:int. a < k \/ k < b ==> f k = real_of_num 0`
    THEN SIMP_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN
    REWRITE_TAC [REAL_SUB_RZERO] THEN
    SUBGOAL_THEN `(g:int->real) (b - m + int_of_num 1) = 
    (f:int->real) (b - m) + g (b - m)` (fun th -> REWRITE_TAC [th]) THENL
      [REWRITE_TAC [REAL_ARITH `!a:real b c. a = b + c <=> b = a - c`] THEN
      ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `(b:int) - m < b` ASSUME_TAC THENL
      [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `!k:int. a < k \/ k < b ==> f k = real_of_num 0` THEN
    SIMP_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [REAL_ADD_LID] THEN
    SUBGOAL_THEN `(g:int->real) (b - m) = 
    (f:int->real) (b - m - int_of_num 1) + g (b - m - int_of_num 1)`
    (fun th -> REWRITE_TAC [th]) THENL
      [ABBREV_TAC `v = (b:int) - m - int_of_num 1` THEN
      ONCE_REWRITE_TAC [ARITH_RULE
      `(b:int) - m = (b - m - int_of_num 1) + int_of_num 1`] THEN
      EXPAND_TAC "v" THEN ABBREV_TAC `q = (b:int) - m - int_of_num 1` THEN
      ASM_REWRITE_TAC [REAL_ARITH `!a:real b c. a = b + c <=> b = a - c`]; ALL_TAC]
    THEN SUBGOAL_THEN `(b:int) - m - int_of_num 1 < b` ASSUME_TAC THENL
      [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `!k:int. a < k \/ k < b ==> f k = real_of_num 0` THEN
    SIMP_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [REAL_ADD_LID] THEN
    ONCE_REWRITE_TAC [ARITH_RULE `!a:int b c. a - b - c = a - c - b`] THEN
    ABBREV_TAC `(W:real) = (g:int->real) (b - int_of_num 1 - m)` THEN
    SUBGOAL_THEN `(g:int->real) b = 
    (f:int->real) (b - int_of_num 1) + g (b - int_of_num 1)`
    (fun th -> REWRITE_TAC [th]) THENL
      [ONCE_REWRITE_TAC [REAL_ARITH `!a:real b c. a = b + c <=> c = a - b`] THEN
      UNDISCH_TAC `!n:int. (g:int->real) (n - &1) = g n - f (n - int_of_num 1)`
      THEN SIMP_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `(b:int) - int_of_num 1 < b` ASSUME_TAC THENL
      [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN UNDISCH_TAC `!k:int. a < k \/ k < b ==> f k = real_of_num 0`
    THEN SIMP_TAC [] THEN DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC [REAL_ADD_LID]
    THEN ASM_CASES_TAC `int_of_num 0 < m` THENL [POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `int_of_num 0 < m
      ==> (g:int->real) (a + &1 + m) = g (a + &1) /\ W = g (b - &1)` THEN
    SIMP_TAC []; REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC];
    DISCH_TAC THEN ASM_REWRITE_TAC [INT_ADD_RID; INT_SUB_RZERO]]);;

let [FST_lemma_1;FST_lemma_2] = map DISCH_ALL
  (CONJUNCTS (UNDISCH (SPEC_ALL FINITE_SUPPORT_TELESEQ_lemma)));;

(* ---------------------------------------------------------------------- *)
(*       If g makes f telescopic, this theorem links their supports       *)
(* ---------------------------------------------------------------------- *)

let FINITE_SUPPORT_TELESEQ_int = prove
(`!f:int->real g:int->real a:int b:int. 
  (!n. f n = g (n + int_of_num 1) - g n) /\ 
  FINITE (support (+) g (:int)) /\
  (!k. (a < k \/ k < b) ==> f k = real_of_num 0)
    ==> (!j. (a < j \/ j < b) ==> g j = real_of_num 0)`,
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THENL
    [SUBGOAL_THEN `j:int = a + int_of_num 1 + (j - (a + int_of_num 1))`
    (fun th -> ONCE_REWRITE_TAC [th]) THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `int_of_num 0 <= j - (a + int_of_num 1)` ASSUME_TAC
      THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(g:int->real) (a + int_of_num 1 + j - (a + int_of_num 1)) =
    (g:int->real) (a + int_of_num 1)` (fun th -> REWRITE_TAC [th]) THENL
      [MATCH_MP_TAC FST_lemma_1 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    SUBGOAL_THEN `!m:int. int_of_num 0 <= m ==>
    (g:int->real) (a + int_of_num 1 + m) =  g (a + int_of_num 1)`
    ASSUME_TAC THENL [GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC FST_lemma_1 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
    UNDISCH_TAC `FINITE (support (+) (g:int->real) (:int))` THEN
    REWRITE_TAC [int_FINITE; IN_SUPPORT; IN_UNIV; NEUTRAL_REAL_ADD] THEN
    STRIP_TAC THEN POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
    STRIP_TAC THEN REWRITE_TAC [NOT_FORALL_THM] THEN
    ASM_CASES_TAC `int_of_num 0 <= a'` THENL
      [ASM_REWRITE_TAC [DE_MORGAN_THM; NOT_IMP] THEN
      EXISTS_TAC `if int_of_num 0 < a + int_of_num 1
                 then a + int_of_num 1 + a'
                 else
                   if ((int_neg a') <= a + int_of_num 1 /\
                      a + int_of_num 1 <= int_of_num 0)
                   then a + int_of_num 1 + ((int_of_num 2) * a' + int_of_num 1)
                   else a + int_of_num 1 +
                        (int_neg (int_of_num 2)) * (a + int_of_num 1)` THEN
      ASM_CASES_TAC `int_of_num 0 < a + int_of_num 1` THENL
        [ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [] THEN
        REWRITE_TAC [DE_MORGAN_THM] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC
        THEN ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC `(int_neg a') <= a + int_of_num 1 /\
                      a + int_of_num 1 <= int_of_num 0` THENL
        [ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [ARITH_RULE `!d:int. int_of_num 0 <= d ==>
        int_of_num 0 <= (int_of_num 2) * d + int_of_num 1`] THEN
        REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [ARITH_RULE `!d:int. ~(int_of_num 0 < d) ==>
        int_of_num 0 <= (int_neg (int_of_num 2)) * d`] THEN
        REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC];
        ASM_REWRITE_TAC [DE_MORGAN_THM]]; ALL_TAC] THEN
  SUBGOAL_THEN `j:int = b - int_of_num 1 - (b - int_of_num 1 - j)`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `int_of_num 0 <= b - int_of_num 1 - j` ASSUME_TAC
    THENL [REPEAT (FIRST_X_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(g:int->real) (b - int_of_num 1 - (b - int_of_num 1 - j)) =
  (g:int->real) (b - int_of_num 1)` (fun th -> REWRITE_TAC [th]) THENL
    [MATCH_MP_TAC FST_lemma_2 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `!m:int. int_of_num 0 <= m ==>
  (g:int->real) (b - int_of_num 1 - m) =  g (b - int_of_num 1)`
  ASSUME_TAC THENL [GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC FST_lemma_2 THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  UNDISCH_TAC `FINITE (support (+) (g:int->real) (:int))` THEN
  REWRITE_TAC [int_FINITE; IN_SUPPORT; IN_UNIV; NEUTRAL_REAL_ADD] THEN
  STRIP_TAC THEN POP_ASSUM MP_TAC THEN
  ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
  STRIP_TAC THEN REWRITE_TAC [NOT_FORALL_THM] THEN
  ASM_CASES_TAC `int_of_num 0 <= a'` THENL
    [ASM_REWRITE_TAC [DE_MORGAN_THM; NOT_IMP] THEN
    EXISTS_TAC `if b - int_of_num 1 < int_of_num 0
               then b - int_of_num 1 - a'
               else
                 if (int_of_num 0 <= b - int_of_num 1 /\
                    b - int_of_num 1 <= a')
                 then b - int_of_num 1 - ((int_of_num 2) * a' + int_of_num 1)
                 else b - int_of_num 1 -
                      (int_of_num 2) * (b - int_of_num 1)` THEN
    ASM_CASES_TAC `b - int_of_num 1 < int_of_num 0` THENL
      [ASM_REWRITE_TAC [] THEN ASM_SIMP_TAC [] THEN
      REWRITE_TAC [DE_MORGAN_THM] THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC
      THEN ARITH_TAC; ASM_CASES_TAC `(int_of_num 0 <= b - int_of_num 1 /\
                    b - int_of_num 1 <= a')` THENL
        [ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [ARITH_RULE `!d:int. int_of_num 0 <= d ==>
        int_of_num 0 <= (int_of_num 2) * d + int_of_num 1`] THEN
        REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; ASM_REWRITE_TAC [] THEN
        ASM_SIMP_TAC [ARITH_RULE `!d:int. ~(d < int_of_num 0) ==>
        int_of_num 0 <= (int_of_num 2) * d`] THEN
        REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC]]; ASM_REWRITE_TAC [DE_MORGAN_THM]]);;

(* ---------------------------------------------------------------------- *)
(*                     This simplifies telescopic sums                    *)
(* ---------------------------------------------------------------------- *)

let SUM_DIFFS_lemma = prove 
(`!(a:int->real) n.
  int_of_num 0 <= n + int_of_num 1 ==>
    sum {i:int | int_of_num 0 <= i /\ i <= n} (\i. a(i + int_of_num 1) - a(i)) =
    a(n + int_of_num 1) - a(int_of_num 0)`,
  GEN_TAC THEN MATCH_MP_TAC int_INDUCTION_BIS THEN
  CONJ_TAC THENL
    [REWRITE_TAC [ARITH_RULE 
    `(int_of_num 0 <= i /\ i <= int_of_num 0) <=> i = int_of_num 0`;
    SET_RULE `{x | x = a} = {a}`; SUM_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:int.
  DISJOINT {(i:int) | &0 <= i /\ i <= k} {k + int_of_num 1}`
  ASSUME_TAC THENL [
  REWRITE_TAC [DISJOINT; INTER; IN_ELIM_THM] THEN
    REWRITE_TAC [SET_RULE `!x:A a. x IN {a} <=> x = a`; FINITE_SINGLETON]
    THEN REWRITE_TAC [EXTENSION; EMPTY; IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN EQ_TAC THENL
    [REPEAT DISCH_TAC THEN
    ASM_CASES_TAC `int_of_num 0 <= n + int_of_num 1` THENL
      [SUBGOAL_THEN `{(i:int) | int_of_num 0 <= i /\ i <= n + int_of_num 1} = 
      {(i:int) | int_of_num 0 <= i /\ i <= n} UNION {(i:int) | i = n + int_of_num 1}`
      (fun th -> REWRITE_TAC [th]) THENL
        [REWRITE_TAC [UNION; SET_RULE `!(P:A->bool) (Q:A->bool).
        (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`; IN_ELIM_THM; SUBSET] THEN
        POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC
    `sum {(i:int) | &0 <= i /\ i <= n} (\i. a (i + int_of_num 1) - a i) +
    sum {i | i = n + int_of_num 1} (\i. a (i + int_of_num 1) - a i)`
    THENL [MATCH_MP_TAC SUM_UNION THEN REWRITE_TAC [FINITE_INTSEG] THEN
      REWRITE_TAC [SET_RULE `{x | x = a} = {a}`; FINITE_SINGLETON] THEN
      ASM_REWRITE_TAC []; ALL_TAC] THEN
    ASM_SIMP_TAC [] THEN REWRITE_TAC [SET_RULE `{x | x = a} = {a}`; SUM_SING] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(n:int) + int_of_num 1 = int_neg (int_of_num 1)`
    (fun th -> REWRITE_TAC [th]) THENL
      [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `{i | int_of_num 0 <= i /\ i <= -- &1} = (EMPTY:int->bool)`
    (fun th -> REWRITE_TAC [th]) THENL
      [REWRITE_TAC [EXTENSION; IN_ELIM_THM; EMPTY] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC [ARITH_RULE `!a:int. int_neg a + a = int_of_num 0`;
    REAL_SUB_REFL; SUM_CLAUSES]; ALL_TAC] THEN
  STRIP_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC [REAL_ARITH `(a:real) = b <=> (?c. a + c = b + c)`] THEN
  EXISTS_TAC `sum {i | i = n + int_of_num 1} (\i. a (i + int_of_num 1) - a i)`
  THEN ASM_SIMP_TAC [GSYM SUM_UNION; FINITE_INTSEG; SET_RULE `{x | x = a} = {a}`;
  FINITE_SINGLETON] THEN
  SUBGOAL_THEN `{(i:int) | int_of_num 0 <= i /\ i <= n + int_of_num 1} = 
    {(i:int) | int_of_num 0 <= i /\ i <= n} UNION {n + int_of_num 1}`
    (fun th -> REWRITE_TAC [GSYM th]) THENL
  [REWRITE_TAC [UNION; SET_RULE `!(P:A->bool) (Q:A->bool).
    (P = Q) <=> (P SUBSET Q /\ Q SUBSET P)`; IN_ELIM_THM; SUBSET;
  SET_RULE `!x:A a. x IN {a} <=> x = a`] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC [SUM_SING; REAL_ARITH `!a:real b c. a - b + c - a = c - b`] THEN 
  ASM_CASES_TAC `int_of_num 0 <= (n + int_of_num 1) + &1` THENL [ASM_SIMP_TAC [];
    REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC]);;

let SUM_DIFFS = prove
(`!(a:int->real) n:int m:int.
    m <= n + int_of_num 1 ==>
    sum {i:int | m <= i /\ i <= n} (\i. a(i + int_of_num 1) - a(i)) =
    a(n + int_of_num 1) - a(m)`,
(REPEAT GEN_TAC) THEN DISCH_TAC THEN
TRANS_TAC `sum {k | int_of_num 0 <= k /\ k <= n - m}
   (\(i:int). a ((i + m) + int_of_num 1) - a (i + m))` THENL
  [SUBGOAL_THEN `{(i:int) | m <= i /\ i <= n} =
    IMAGE (\(x:int). x + m) {k | int_of_num 0 <= k /\ k <= n - m}`
    (fun th -> REWRITE_TAC [th]) THENL
    [REWRITE_TAC [IMAGE; EXTENSION; IN_ELIM_THM] THEN
    GEN_TAC THEN EQ_TAC THENL [DISCH_TAC THEN EXISTS_TAC `(x:int) - m` THEN
    REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; STRIP_TAC THEN
    REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC]; ALL_TAC] THEN
    TRANS_TAC `sum {k | int_of_num 0 <= k /\ k <= n - m}
    ((\i. a (i + int_of_num 1) - a i) o (\x. x + m))` THENL
      [MATCH_MP_TAC SUM_IMAGE THEN REWRITE_TAC [IN_ELIM_THM]
      THEN ARITH_TAC; REWRITE_TAC [o_DEF]]; ALL_TAC] THEN
    SUBGOAL_THEN `int_of_num 0 <= (n - m) + int_of_num 1` ASSUME_TAC
    THENL [REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC `sum {k | int_of_num 0 <= k /\ k <= n - m}
    (\i. (a o (\x. x + m)) (i + int_of_num 1) - (a o (\x. x + m)) i)`
    THENL [AP_TERM_TAC THEN REWRITE_TAC [FUN_EQ_THM; o_THM] THEN
      GEN_TAC THEN REWRITE_TAC [REAL_ARITH `!a:real b c. a - b = c - b <=> a = c`]
      THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC [SUM_DIFFS_lemma] THEN REWRITE_TAC [o_THM] THEN
    REWRITE_TAC [INT_ADD_LID; REAL_ARITH `!a:real b c. a - b = c - b <=> a = c`]
    THEN AP_TERM_TAC THEN ARITH_TAC);;

(* ---------------------------------------------------------------------- *)
(*     If g makes f telescopic and x is out of the support of f, is out   *)
(*      of the support of g supporto di f, x non e` nel supporto di g     *)
(* ---------------------------------------------------------------------- *)

let NOT_IN_SUPP_TELESEQ_int = prove
(`!f:int->real g:int->real a:int b:int. 
  (!n. f n = g (n + int_of_num 1) - g n) /\ 
  support (+) f (:int) SUBSET {(z:int) | n <= z /\ z <= m} /\
  FINITE (support (+) g (:int))
    ==> 
    (!x:int. ~(x IN {(z:int) | n <= z /\ z <= m}) ==> g x = real_of_num 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC [IN_ELIM_THM;
  ARITH_RULE `!s:int t. ~(s <= t) <=> (t < s)`; DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC [TAUT `!P Q. P \/ Q <=> Q \/ P`] THEN
  MATCH_MP_TAC FINITE_SUPPORT_TELESEQ_int THEN EXISTS_TAC `f:int->real`
  THEN CONJ_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC]
  THEN CONJ_TAC THENL [ASM_REWRITE_TAC []; ALL_TAC] THEN GEN_TAC THEN
  UNDISCH_TAC `support (+) (f:int->real) (:int)
    SUBSET {(z:int) | n <= z /\ z <= m}` THEN
  REWRITE_TAC [SUBSET; IN_SUPPORT; NEUTRAL_REAL_ADD; IN_UNIV;
  IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC [TAUT `!P Q. (P ==> Q) <=> (~Q ==> ~P)`] THEN
  REWRITE_TAC [NOT_IMP] THEN
  DISCH_TAC THEN REWRITE_TAC [NOT_FORALL_THM; NOT_IMP] THEN
  EXISTS_TAC `k:int` THEN ASM_REWRITE_TAC [] THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

(* ---------------------------------------------------------------------- *)
(*                         This is half the WZ proof                      *)
(* ---------------------------------------------------------------------- *)

let FINSUP_SUM_Z_TELESEQ = prove
(`!(f:int->real) g. 
  FINITE (support (+) f (:int)) /\ 
  f = (\i. g(i + int_of_num 1) - g(i)) /\
  FINITE (support (+) g (:int))
    ==> sum (:int) f = real_of_num 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `FINITE (support (+) (f:int->real) (:int))` THEN
  REWRITE_TAC [int_FINITE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `support (+) (f:int->real) (:int)
  SUBSET {(z:int) | (int_neg a) <= z /\ z <= a}` ASSUME_TAC THENL
    [REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `sum (:int) f =
  sum {(z:int) | (int_neg a) - int_of_num 1 <= z /\ z <= a + int_of_num 1} f`
  (fun th -> REWRITE_TAC [th]) THENL
    [MATCH_MP_TAC EQ_SYM THEN SUBGOAL_THEN `support (+) (f:int->real) (:int)
    SUBSET {(z:int) | (int_neg a) - int_of_num 1 <= z /\
    z <= a + int_of_num 1}` (fun th -> SIMP_TAC [th; SUPPORT_SUBSET_INTSEG])
    THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{z | int_neg a <= z /\ z <= a}` THEN
    ASM_REWRITE_TAC [] THEN REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `int_neg a - int_of_num 1 <= (a + &1) + int_of_num 1`
  ASSUME_TAC THENL [REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC [SUM_DIFFS] THEN
  SUBGOAL_THEN `~(((a + int_of_num 1) + int_of_num 1) IN
    {z | int_neg a <= z /\ z <= a})`
  ASSUME_TAC THENL [REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((int_neg a - int_of_num 1) IN {z | int_neg a <= z /\ z <= a})`
  ASSUME_TAC THENL [REWRITE_TAC [SUBSET; IN_ELIM_THM] THEN
  ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(g:int->real) ((a + int_of_num 1) + &1) = real_of_num 0`
  (fun th -> REWRITE_TAC [th]) THENL
    [UNDISCH_TAC `~((a + &1) + int_of_num 1 IN {z | --a <= z /\ z <= a})` THEN
    ABBREV_TAC `s = (a + int_of_num 1) + int_of_num 1` THEN
    SPEC_TAC (`s:int`, `s:int`) THEN MATCH_MP_TAC NOT_IN_SUPP_TELESEQ_int THEN
    EXISTS_TAC `f:int->real` THEN ASM_REWRITE_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `(g:int->real) (int_neg a - &1) = real_of_num 0`
  (fun th -> REWRITE_TAC [th]) THENL
    [UNDISCH_TAC `~(int_neg a - int_of_num 1 IN {z | --a <= z /\ z <= a})` THEN
    ABBREV_TAC `r = int_neg a - int_of_num 1` THEN SPEC_TAC (`r:int`, `r:int`)
    THEN MATCH_MP_TAC NOT_IN_SUPP_TELESEQ_int THEN EXISTS_TAC `f:int->real`
    THEN ASM_REWRITE_TAC []; ALL_TAC] THEN REAL_ARITH_TAC);;

(* ====================================================================== *)
(* ||                                                                  || *)    
(* ||                         The WZ theorem                           || *)     
(* ||                                                                  || *)
(* ====================================================================== *)

g `!U:int->int->real r:int->real.
  ((!(n:int) m. (n <= m /\
                 n IN (support (+) (\i. r i) (:int)) /\
                 m IN (support (+) (\i. r i) (:int))) ==>
                    {x | n <= x /\ x <= m} SUBSET (support (+) (\i. r i) (:int))) /\
   (?G:int->int->real. !n.
         (FINITE (support (+) (\k. (U n k)/(r n)) (:int))) /\
         (FINITE (support (+) (\k. G n k) (:int))) /\
         (~(r n = real_of_num 0) ==> (!k. (U (n + int_of_num 1) k)/(r (n + int_of_num 1)) - (U n k)/(r n) = (G n (k + int_of_num 1)) - (G n k)))) /\
   (!n. r n = real_of_num 0 ==> (sum (:int) (\k. U n k) = r n)) /\
	 (?m:int. (sum (:int) (\k. U m k) =  r m) /\ ~(r m = real_of_num 0)))
  ==> (sum (:int) (\k. U n k) = r n)`;;

(* -------------------------------------------------- *)
(*            The trivial case:  r(n) = 0             *)
(* -------------------------------------------------- *)

e (REPEAT STRIP_TAC);;
e (ASM_CASES_TAC `(r:int->real) n = real_of_num 0` THENL
  [POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC []; ALL_TAC]);;
e (ASM_SIMP_TAC [NORMALIZE_LEMMA]);;

(* -------------------------------------------------- *)
(*        There is a sequence wich is constant.       *)
(*       I can use the weakened test I've proved      *)
(* -------------------------------------------------- *)

e (SUBGOAL_THEN
  `real_of_num 1 = sum (:int) (\k. (U:int->int->real) m k / (r:int->real) m)`
  (fun th -> REWRITE_TAC [th]) THENL [MATCH_MP_TAC EQ_SYM THEN
  TRANS_TAC `sum (:int) (\k. (U:int->int->real) m k) / (r:int->real) m` THENL
  [TRANS_TAC
  `sum (:int) (\k. (U:int->int->real) m k * (real_of_num 1 / (r:int->real) m))`
  THENL [REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC) THEN REWRITE_TAC [FUN_EQ_THM]
  THEN GEN_TAC THEN UNDISCH_TAC `~((r:int->real) m = real_of_num 0)`
  THEN REAL_FIELD_TAC; REWRITE_TAC [SUM_RMUL] THEN
  UNDISCH_TAC `~((r:int->real) m = real_of_num 0)` THEN REAL_FIELD_TAC]; ALL_TAC]
  THEN ASM_SIMP_TAC [REAL_FIELD `!a:real b. ~(a = real_of_num 0) ==>
  (b / a = real_of_num 1 <=> b = a)`]; ALL_TAC]);;

e (SUBGOAL_THEN `!h:int. sum (:int) (\i. (U:int->int->real) h i / (r:int->real) h) =
  (\y:int. sum (:int) (\i. (U:int->int->real) y i / (r:int->real) y)) h`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [BETA_TAC THEN REWRITE_TAC []; ALL_TAC]);;

e (POP_ASSUM MP_TAC);;
e (SPEC_TAC (`n:int`, `n:int`));;

e (MATCH_MP_TAC SEQ_CONST_WEAK);;
e (CONJ_TAC THENL
  [SUBGOAL_THEN `(\(n:int). ~((r:int->real) n = real_of_num 0)) =
    support (+) (\i. (r:int->real) i) (:int)` (fun th -> REWRITE_TAC [th])
      THENL [REWRITE_TAC [support; IN_UNIV; NEUTRAL_REAL_ADD] THEN SET_TAC [];
      ALL_TAC] THEN ASM_REWRITE_TAC []; ALL_TAC]);;
e (ASM_REWRITE_TAC []);;
e (GEN_TAC THEN DISCH_TAC);; 

(* -------------------------------------------------- *)
(*         Now the game is merging the sums           *)
(* -------------------------------------------------- *)

e (ONCE_REWRITE_TAC [GSYM SUM_SUPPORT]);;

e (TRANS_TAC `
  sum 
    ((support (+) (\k. U (n + int_of_num 1) k / r (n + &1)) (:int)) UNION 
    (support (+) (\k. U n k / r n) (:int))) 
      (\k. U (n + int_of_num 1) k / r (n + int_of_num 1)) -
  sum 
    ((support (+) (\k. U n k / r n) (:int)) UNION
     (support (+) (\k. U (n + int_of_num 1) k / r (n + &1)) (:int)))
      (\k. (U:int->int->real) n k / r n)` THENL
    [REWRITE_TAC [GSYM SUM_SUPPORT_UNION_int]; ALL_TAC]);;

e (SUBGOAL_THEN `!U:int->int->real.
  (support (+) (\k. U (n + int_of_num 1) k / r (n + int_of_num 1)) (:int) UNION
  support (+) (\k. U n k / r n) (:int)) =
  support (+) (\k. U n k / r n) (:int) UNION
  support (+) (\k. U (n + &1) k / r (n + &1)) (:int)`
  (fun th -> REWRITE_TAC [th])  THENL 
  [GEN_TAC THEN REWRITE_TAC [SET_RULE `!s t. s UNION t = t UNION s`]; ALL_TAC]);;
e (SUBGOAL_THEN 
  `FINITE 
  (support (+) (\k. U n k / r n) (:int) UNION
  support (+) (\k. U (n + int_of_num 1) k / r (n + &1)) (:int))`
  ASSUME_TAC THENL [ASM_REWRITE_TAC [FINITE_UNION]; ALL_TAC]);;

e (TRANS_TAC `sum
 (support (+) (\k. (U:int->int->real) n k / r n) (:int) UNION
  support (+) (\k. (U:int->int->real) (n + int_of_num 1) k / r (n + &1)) (:int))
 (\k. U (n + &1) k / (r:int->real) (n + &1) - U n k / r n)` THENL
  [MATCH_MP_TAC (GSYM SUM_SUB) THEN ASM_REWRITE_TAC []; ALL_TAC]);;

e (TRANS_TAC `
  sum
    (support (+) (\k. (U:int->int->real) (n + &1) k / r (n + &1) -
      U n k / (r:int->real) n) (:int))
        (\k. (U:int->int->real) (n + &1) k / r (n + &1) -
          U n k / (r:int->real) n)` THENL
     [MATCH_MP_TAC SUM_SUPERSET_SUPPORT_int THEN
     ONCE_REWRITE_TAC [SET_RULE `!s t. s UNION t = t UNION s`]
     THEN REWRITE_TAC [SUPPORT_SUB_int]; ALL_TAC]);;
e (REWRITE_TAC [SUM_SUPPORT]);;
e (MATCH_MP_TAC FINSUP_SUM_Z_TELESEQ);;
e (EXISTS_TAC `(\k. (G:int->int->real) n k)` THEN BETA_TAC);;
e (CONJ_TAC THENL [MATCH_MP_TAC FINITE_SUPPORT_SUB_int THEN
    ASM_REWRITE_TAC []; ALL_TAC]);;
e (ASM_REWRITE_TAC []);;
e (ASM_SIMP_TAC []);;
let int_WZ_THM = top_thm();;
