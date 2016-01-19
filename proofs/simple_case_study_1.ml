(* -*- holl -*- *)

needs "z_binomial_int.ml";;
needs "WZ_THM_Z_finsup_no_analysis.ml";;

let TRANS_TAC tm =
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC tm THEN CONJ_TAC;;

let ZBINOM_TOP_STEP_STEP_TAC = ZBINOM_TOP_STEP_TAC THEN ZBINOM_TOP_STEP_TAC;;

(* -binomial(n,k-1)/(2*2^n) *)

(* ============================================================ *)
(* ||                                                        || *)
(* ||          Affronto \sum_k \binom{n}{k} = 2^n            || *)
(* ||                                                        || *)
(* ============================================================ *)

g `sum(:int)(\k. (\n k. real_of_int (z_binom n k)) n k) =
  (\j. if int_of_num 0 <= j then (real_of_num 2) pow (num_of_int j)
       else real_of_num 0) n` ;;  

(* questo problema e` introdotto dal fatto che n e` un intero,
vedi http://www.firenzebeagle.com/WZmethod/complicazioni.html *)

e (ASM_CASES_TAC `int_of_num 0 <= n`);;

e (BETA_TAC THEN ASM_REWRITE_TAC []);;

(* adesso devo astrarre di nuovo *)

e (SUBGOAL_THEN `sum (:int) (\k. real_of_int (z_binom n k)) =
  sum (:int) (\k. (\n k. real_of_int (z_binom n k)) n k)`
  (fun th -> PURE_REWRITE_TAC [th]) THENL [REWRITE_TAC []; ALL_TAC]);;

e (SUBGOAL_THEN `real_of_num 2 pow (num_of_int n) =
  (\n. real_of_num 2 pow (num_of_int n)) n`
  (fun th -> ONCE_REWRITE_TAC [th]) THENL [REWRITE_TAC []; ALL_TAC]);;

(* ok ci siamo *)

e (MATCH_MP_TAC int_WZ_THM);;
e (REPEAT STRIP_TAC);;

(* questa e` l'ipotesi dimenticata da Wilf e Zeilberg. Ci penso dopo *)
r 1;;

e (EXISTS_TAC `(\n k.  
  real_neg ((real_of_int (z_binom n (k - int_of_num 1)))) / (real_of_num 2 *
  (real_of_num 2 pow (num_of_int n))))`);;  

e (BETA_TAC);;

e (GEN_TAC);;
e (REPEAT CONJ_TAC);;
r 2;;

(* ahia: c'era un !n davanti, quindi la variabile ha cambiato nome
e non posso piu` sfruttare le ipotesi (e num_of_int puo` anche non esistere).
occorre definire pow: real->int->real, e dimostrare una valanga di teoremi...
*)
