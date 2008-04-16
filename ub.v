(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import digits.
Require Export lb.


(** We define a function [lb] that returns the #<em>#upper bound#</em># of the
interval obtained by applying the initial segment of length [n] of
[alpha] to the base interval #&#91;#-1,+1#&#93;#.*)

Fixpoint ub (alpha:Reals) (n:nat) {struct n} : Q :=
  match n with
  |   0 => 1 (* this is because of base interval *)
  | S p => let (d,alpha'):= alpha in let q := ub alpha' p in
           as_Moebius_Q d q
  end.

Lemma ub_S_n:forall n alpha, ub alpha (S n) = as_Moebius_Q (hd alpha) (ub (tl alpha) n).
Proof.
 intros n [d alpha']; trivial.
Defined.

Lemma ub_is_in_base_interval:forall k alpha,  - Qone <= ub alpha k /\ ub alpha k <= Qone.
Proof.
 intro k; induction k; intro alpha.
 (* 0 *)
 split; unfold ub; natq_one; try rewrite <- Z_to_Qopp; apply Z_to_Qle; auto with zarith.
 (* S k *)
 destruct alpha as [[ | | ] alpha']; generalize (IHk alpha'); clear IHk;
 rewrite ub_S_n; unfold hd, tl; set (u':=ub alpha' k); intros [IHk_1 IHk_2].


  (* L *)
  (* TP: Zero <= u'+ 1 *)
  assert (H_u'_one_nonneg: Zero <= u'+1).
  stepr (u'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; auto. 
  (* TP: Zero < u'+3 *)
  assert (H_u'_three_pos: Zero < u'+3).
  apply Qle_lt_trans with (u'+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= 2*u'+ 2 *)
  assert (H_2u'_two_nonneg: Zero <= 2*u'+2).
  stepr (2*(u'+1)); [|qZ_numerals; ring]; apply Qle_mult_nonneg_nonneg; auto.
  (* TP: Zero <= u'+ 2 *)
  assert (H_u'_two_nonneg: Zero <= u'+2).
  apply Qle_trans with (u'+1); auto;
  apply Qle_plus_plus; try apply Qle_reflexive; apply Z_to_Qle; apply inj_le; auto.

  rewrite as_Moebius_Q_L; trivial; natZ_numerals.

  split; apply Qmult_resp_Qle_pos_r with (u'+3); auto.
   stepr (u'-1).
    apply Qle_Zero_Qminus;
    stepr (2*u'+2); auto; qnat_S 2; qnat_S 1; qnat_one; ring.
    generalize (u'-1) (u'+3) H_u'_three_pos; intros; field; auto.
  
   stepl (u'-1).
    apply Qle_Zero_Qminus;
    stepr 4; auto; qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.
    generalize (u'-1) (u'+3) H_u'_three_pos; intros; field; auto.
  
  (* R *)
  (* TP: Zero <= -u'+ 1 *)
  assert (H_min_u'_one_nonneg: Zero <= -u'+1).
  stepr (1-u'); try ring; apply Qle_Qminus_Zero; auto. 
  (* TP: Zero < -u'+3 *)
  assert (H_min_u'_three_pos: Zero < -u'+3).
  apply Qle_lt_trans with ((-u')+1); auto.
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= 2*(-u')+ 2 *)
  assert (H_2_min_u'_two_nonneg: Zero <= 2*(-u')+2).
  stepr (2*(-u'+1)); [|qZ_numerals; ring]; apply Qle_mult_nonneg_nonneg; auto.

  rewrite as_Moebius_Q_R; trivial; natZ_numerals.
  
  split; apply Qmult_resp_Qle_pos_r with (-u'+3); auto.
   stepr (u'+1).
    apply Qle_Zero_Qminus;
    stepr 4; auto; qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.
    generalize (u'+1) (-u'+3) H_min_u'_three_pos; intros; field; auto.

   stepl (u'+1).
    apply Qle_Zero_Qminus;
    stepr (2*(-u')+2); auto; qnat_S 2; qnat_S 1; qnat_one; ring.
    generalize (u'+1) (-u'+3) H_min_u'_three_pos; intros; field; auto.

  (* M *)
  rewrite as_Moebius_Q_M; natZ_numerals.

  split; apply Qmult_resp_Qle_pos_r with 3; auto;
  [ stepr u' | stepl u'].
  apply Qle_trans with (-Qone); auto; apply Qlt_le_weak; apply Qlt_Zero_Qminus; stepr 2; auto.  
  generalize u'; intro; field; auto.
  apply Qle_trans with Qone; auto; apply Qlt_le_weak; apply Qlt_Zero_Qminus; stepr 2; auto.  
  generalize u'; intro; field; auto.
Defined.

Lemma ub_is_in_base_interval_low:forall k alpha, - Qone <= ub alpha k.
Proof.
 intros k alpha; elim (ub_is_in_base_interval k alpha); trivial.
Defined.

Lemma ub_is_in_base_interval_up:forall k alpha, ub alpha k <= Qone.
Proof.
 intros k alpha; elim (ub_is_in_base_interval k alpha); trivial.
Defined.

(** This is similar to Lemma 5.7.2.i in the thesis. *)
Lemma thesis_5_7_2i_u:forall k alpha,  ~(ub alpha k = 1) -> ub alpha k <= k/(k+2).
Proof.
 intro k; induction k; intros alpha H_nonzero.

  (* 0 *)
  apply False_ind; apply H_nonzero; trivial.
  (* S k *)
  rewrite ub_S_n.
  rewrite ub_S_n in H_nonzero.
  (* TP: Zero < k + Qone *) 
  assert (H_k_one_pos: Zero < k + Qone ).
  natq_S k; natq_zero; apply Z_to_Qlt; apply inj_lt; apply lt_O_Sn.
  (* TP: O <= k  *) 
  assert (H_k_nonneg:  0 <= k).
  apply Z_to_Qle; apply inj_le; auto with arith.
  (* TP: Qone <= 2 * k + 3*)
  assert (H_2k_3_nonneg:  Qone <= 2 * k + 3).
  apply Qle_Zero_Qminus; stepr (2*(k+1));
  [ apply Qle_mult_nonneg_nonneg; auto
  | qnat_S 2; qnat_S 1; qnat_one; ring
  ].

  destruct alpha as [[ | | ] alpha']; unfold hd,tl; unfold hd,tl in H_nonzero; qnat_one; qnat_S k;   set (u':=ub alpha' k).
   (* L *)
   (* TP: Zero <= u'+ 1 *)
   assert (H_u'_one_nonneg: Zero <= u'+1).
   stepr (u'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_low. 
   (* TP: Zero < u'+3 *)
   assert (H_u'_three_pos: Zero < u'+3).
   apply Qle_lt_trans with (u'+1); auto;
   apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.


   rewrite as_Moebius_Q_L; trivial; natZ_numerals.

   apply Qmult_Qdiv_pos_Qle; auto.
   apply Qle_Zero_Qminus.
   stepr (2*((2*k+3)-u')).
   apply Qle_mult_nonneg_nonneg; auto.
   apply Qle_Qminus_Zero.
   apply Qle_trans with Qone; auto; subst u'; apply ub_is_in_base_interval_up.
   qnat_S 2; qnat_S 1; qnat_one; ring.

   (* R *)
   case (Q_eq_dec u' 1); intro H_u'.
   fold u' in H_nonzero.
    (* u' = 1 *)
    apply False_ind; apply H_nonzero; rewrite H_u'; rewrite as_Moebius_Q_R; qZ_numerals; auto.
    (* u' <> 1 *)
    generalize (IHk alpha' H_u'); fold u'; clear IHk; intro IHk.
    (* TP: Zero <= -u'+ 1 *)
    assert (H_min_u'_one_nonneg: Zero <= -u'+1).
    stepr (1-u'); try ring; apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_up.
    (* TP: Zero < -u'+3 *)
    assert (H_min_u'_three_pos: Zero < -u'+3).
    apply Qle_lt_trans with ((-u')+1); auto;
    apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
 
    rewrite as_Moebius_Q_R; trivial; natZ_numerals.

    apply Qmult_Qdiv_pos_Qle; auto;
    apply Qle_Zero_Qminus;
    stepr (2*(k-u'*(k+2))).
     apply Qle_mult_nonneg_nonneg; auto.
     apply Qle_Qminus_Zero.
     apply Qmult_resp_Qle_pos_r with (Qinv (k+2)); auto.
      rewrite <- Qmult_assoc; rewrite Qmult_Qinv_r; auto.
     stepl u'; trivial; try ring.

     qnat_S 2; qnat_S 1; qnat_one; ring.
 
   (* M *)
   generalize H_nonzero; clear H_nonzero; repeat rewrite as_Moebius_Q_M; natZ_numerals; intros H_nonzero;
   fold u' in H_nonzero.
   
   apply Qle_trans with (1/3).
    apply Qmult_Qdiv_pos_Qle; auto;
    apply Qle_Zero_Qminus;
    stepr (3*(1-u')).
     apply Qle_mult_nonneg_nonneg; auto;
     apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_up.
     qnat_S 2; qnat_S 1; qnat_one; ring.
    
    apply Qmult_Qdiv_pos_Qle; auto;
    apply Qle_Zero_Qminus.
    stepr (2*k).
     apply Qle_mult_nonneg_nonneg; auto;
     apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_up.
     qnat_S 2; qnat_S 1; qnat_one; ring.
Defined.
    
Lemma thesis_5_7_2ii_u:forall (k:nat) alpha,  (1-k)/(1+k) <= ub alpha k.
Proof.
 intro k; induction k; intros alpha.
  (* 0 *)
  simpl; apply Qle_reflexive.
  (* S k *)
  (* TP: O <= k  *) 
  assert (H_k_nonneg:  0 <= k).
  apply Z_to_Qle; apply inj_le; auto with arith.
  (* TP: Zero < 1 + k *) 
  assert (H_k_one_pos: Zero < 1 + k ).
  rewrite Qplus_sym; natq_zero; qnat_one; natq_S k; natq_S (S k); auto.
  (* TP: Zero < k + 2 *) 
  assert (H_k_two_pos: Zero < k + 2 ).
  natq_zero; qnat_S 1; qnat_one; rewrite Qplus_assoc; natq_S k; natq_S (S k); auto.

  rewrite ub_S_n.
  destruct alpha as [d alpha'].
  destruct d; unfold hd,tl;
  generalize (IHk alpha'); clear IHk; intros IHk;
  set (u':=ub alpha' k);
  fold u' in IHk.
   (* L *)
   (* TP: Zero <= u'+ 1 *)
   assert (H_u'_one_nonneg: Zero <= u'+1).
   stepr (u'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; unfold u'; apply ub_is_in_base_interval_low. 
   (* TP: Zero < u'+3 *)
   assert (H_u'_three_pos: Zero < u'+3).
   apply Qle_lt_trans with (u'+1); auto;
   apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
   
   rewrite as_Moebius_Q_L; trivial; natZ_numerals;
   apply Qmult_Qdiv_pos_Qle; auto;
   apply Qle_Zero_Qminus;
   stepr (2*(u'*(1+k)-(1-k))).
    apply Qle_mult_nonneg_nonneg; auto;
    apply Qle_Qminus_Zero;
    apply Qmult_resp_Qle_pos_r with (Qinv (1+k)); auto;
    stepr u'; auto; rewrite <- Qmult_assoc; rewrite Qmult_Qinv_r; auto; ring.
    qnat_S k; qnat_S 2; qnat_S 1; qnat_one; ring.

   (* R *)
   (* TP: Zero <= -u'+ 1 *)
   assert (H_min_u'_one_nonneg: Zero <= -u'+1).
   stepr (1-u'); try ring; apply Qle_Qminus_Zero; unfold u'; apply ub_is_in_base_interval_up.
   (* TP: Zero < -u'+3 *)
   assert (H_min_u'_three_pos: Zero < -u'+3).
   apply Qle_lt_trans with ((-u')+1); auto;
   apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
   (* TP: Zero <= u'+ 1 *)
   assert (H_u'_one_nonneg: Zero <= u'+1).
   stepr (u'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; unfold u'; apply ub_is_in_base_interval_low. 

   rewrite as_Moebius_Q_R; trivial; natZ_numerals;
   apply Qmult_Qdiv_pos_Qle; auto;
   apply Qle_Zero_Qminus;
   stepr (2*(u'+1+2*k)).
    apply Qle_mult_nonneg_nonneg; auto;
    apply Qle_plus_pos_pos; auto.
    qnat_S k; qnat_S 2; qnat_S 1; qnat_one; ring.

   (* M *)
   generalize IHk; clear IHk; subst u'.
   destruct k; rewrite as_Moebius_Q_M; natZ_numerals; intro IHk.
   (* k := 0 *)
   unfold ub; stepl Zero; auto.
   (* k := S k *)
   set (u':=ub alpha' (S k));
   fold u' in IHk.
   (* TP: O <= k  *) 
   assert (H_pk_nonneg:  0 <= k).
   apply Z_to_Qle; apply inj_le; auto with arith.
   (* TP: Zero <= u'+ 1 *)
   assert (H_u'_one_nonneg: Zero <= u'+1).
   stepr (u'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; unfold u'; apply ub_is_in_base_interval_low. 
   (* TP: Zero <= u'+ 3 *)
   assert (H_u'_two_nonneg: Zero <= u'+3).
   apply Qle_trans with (u'+1); auto;
   apply Qle_plus_plus; try apply Qle_reflexive; apply Z_to_Qle; apply inj_le; auto.

   apply Qmult_Qdiv_pos_Qle; auto;
   apply Qle_Zero_Qminus.
   stepr (k*(u'+3)+3*(u'+1)).
    apply Qle_plus_pos_pos; apply Qle_mult_nonneg_nonneg; auto.
       
    qnat_S (S k); qnat_S k; qnat_S 2; qnat_S 1; qnat_one;
    [ ring | natq_S k; natq_S (S k); auto].
Defined.


Lemma ub_nonincreasing_step:forall k alpha, ub alpha (S k) <= ub alpha k.
Proof.
 intro k; induction k.
 (* 0 *)
 intro alpha; stepr Qone; trivial; apply ub_is_in_base_interval_up.
 (* S k *)
 intros [d alpha'].
 rewrite ub_S_n;
 rewrite (ub_S_n k (Cons d alpha')); unfold hd, tl.
 destruct d as [ | | ]; set (u':=ub alpha' (S k)); set (u'':=ub alpha' k); 
 generalize (IHk alpha'); clear IHk; intros IHk; fold u' u'' in IHk.

  (* L *)
  (* TP: Zero <= u'+ 1 *)
  assert (H_u'_one_nonneg: Zero <= u'+1).
  stepr (u'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_low. 
  (* TP: Zero < u'+3 *)
  assert (H_u'_three_pos: Zero < u'+3).
  apply Qle_lt_trans with (u'+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= u''+ 1 *)
  assert (H_u''_one_nonneg: Zero <= u''+1).
  stepr (u''-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst u''; apply ub_is_in_base_interval_low. 
  (* TP: Zero < u''+3 *)
  assert (H_u''_three_pos: Zero < u''+3).
  apply Qle_lt_trans with (u''+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.

  repeat rewrite as_Moebius_Q_L; trivial; natZ_numerals.
  (* NB: conjug_Q_L is nondecreasing for -3<= x*)
  apply Qmult_Qdiv_pos_Qle; auto.
  apply Qle_Zero_Qminus.
  stepr (4*(u''-u')).
   apply Qle_mult_nonneg_nonneg; auto.
   apply Qle_Qminus_Zero; assumption.
   qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.

  (* R *)
  (* TP: Zero <= -u'+ 1 *)
  assert (H_min_u'_one_nonneg: Zero <= -u'+1).
  stepr (1-u'); try ring; apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_up.
  (* TP: Zero < -u'+3 *)
  assert (H_min_u'_three_pos: Zero < -u'+3).
  apply Qle_lt_trans with ((-u')+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= -u'''+ 1 *)
  assert (H_min_u''_one_nonneg: Zero <= -u''+1).
  stepr (1-u''); try ring; apply Qle_Qminus_Zero; subst u''; apply ub_is_in_base_interval_up.
  (* TP: Zero < -u''+3 *)
  assert (H_min_u''_three_pos: Zero < -u''+3).
  apply Qle_lt_trans with ((-u'')+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.

  repeat rewrite as_Moebius_Q_R; trivial; natZ_numerals;
  (* NB: conjug_Q_R is nondecreasing for x<=3*)
  apply Qmult_Qdiv_pos_Qle; auto.
  apply Qle_Zero_Qminus.
  stepr (4*(u''-u')).
   apply Qle_mult_nonneg_nonneg; auto.
   apply Qle_Qminus_Zero; assumption.
   qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.

  (* M *)
  do 2 rewrite as_Moebius_Q_M; natZ_numerals;
  (* NB: conjug_Q_M is nondecreasing*)
  apply Qmult_Qdiv_pos_Qle; auto.
  apply Qle_Zero_Qminus.
  stepr (3*(u''-u')).
   apply Qle_mult_nonneg_nonneg; auto.
   apply Qle_Qminus_Zero; assumption.
   qnat_S 2; qnat_S 1; qnat_one; ring.
Defined.

Lemma ub_nonincreasing_steps:forall n k alpha, ub alpha (k+n) <= ub alpha n.
Proof.
 intros [|n] k. 
  (* n:=0 *)
  intros; replace (k+0)%nat with k; trivial; apply ub_is_in_base_interval_up.
  (* n:=S n*)
  induction k.
   (* k:=0 *)
   intro alpha; apply Qle_reflexive. 
   (* k:=S k *)
   replace (S k +S n)%nat with (S (k+S n))%nat; trivial;
   intros [d alpha'];
   rewrite ub_S_n; rewrite (ub_S_n n (Cons d alpha')); unfold hd, tl;
   destruct d.
    apply as_Moebius_Q_L_nondecreasing;
    [ apply ub_is_in_base_interval_low
    | apply ub_is_in_base_interval_up
    | apply Qle_trans with (ub alpha' (S n)); trivial; apply ub_nonincreasing_step].
    apply as_Moebius_Q_R_nondecreasing;
    [ apply ub_is_in_base_interval_low
    | apply ub_is_in_base_interval_up
    | apply Qle_trans with (ub alpha' (S n)); trivial; apply ub_nonincreasing_step].
    apply as_Moebius_Q_M_nondecreasing;
    [ apply ub_is_in_base_interval_low
    | apply ub_is_in_base_interval_up
    | apply Qle_trans with (ub alpha' (S n)); trivial; apply ub_nonincreasing_step].
Defined.

Lemma ub_nonincreasing:forall m n alpha, (m<=n)%nat -> ub alpha n <= ub alpha m.
Proof.
 intros m n alpha Hmn.
 replace n with ((n-m)+m)%nat; try omega; apply ub_nonincreasing_steps.
Defined.


Lemma lb_lt_ub_pointwise:forall k alpha, lb alpha k < ub alpha k.
Proof.
 intros k;
 induction k.
 (* 0 *)
 intro alpha.
 unfold ub,lb.
 apply Qlt_Zero_Qminus; stepr 2; auto. 

 (* S k *)
 intros [[ | | ] alpha'];
 generalize (IHk alpha'); clear IHk; 
 rewrite ub_S_n; rewrite lb_S_n; unfold hd,tl;
 set (u':=ub alpha' k); set (l':=lb alpha' k); intro IHk.
 (* L *)
  (* TP: Zero < u'- l' *)
  assert (H_u'l': Zero < u'- l'); [apply Qlt_Qminus_Zero; assumption |].
  (* TP: Zero <= u'+ 1 *)
  assert (H_u'_one_nonneg: Zero <= u'+1).
  stepr (u'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_low. 
  (* TP: Zero < u'+3 *)
  assert (H_u'_three_pos: Zero < u'+3).
  apply Qle_lt_trans with (u'+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= l'+ 1 *)
  assert (H_l'_one_nonneg: Zero <= l'+1).
  stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_low. 
  (* TP: Zero < l'+3 *)
  assert (H_l'_three_pos: Zero < l'+3).
  apply Qle_lt_trans with (l'+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
 

  repeat rewrite as_Moebius_Q_L; trivial; natZ_numerals.

  apply Qmult_Qdiv_pos; auto;
  apply Qlt_Zero_Qminus;
  stepr (4*(u'-l')); auto; qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.
 (* R *)
  (* TP: Zero < u'- l' *)
  assert (H_u'l': Zero < u'- l'); [apply Qlt_Qminus_Zero; assumption |].
  (* TP: Zero <= -u'+ 1 *)
  assert (H_min_u'_one_nonneg: Zero <= -u'+1).
  stepr (1-u'); try ring; apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_up.
  (* TP: Zero < -u'+3 *)
  assert (H_min_u'_three_pos: Zero < -u'+3).
  apply Qle_lt_trans with ((-u')+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= -l'+ 1 *)
  assert (H_min_l'_one_nonneg: Zero <= -l'+1).
  stepr (1-l'); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_up.
  (* TP: Zero < -l'+3 *)
  assert (H_min_l'_three_pos: Zero < -l'+3).
  apply Qle_lt_trans with ((-l')+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
 
  repeat rewrite as_Moebius_Q_R; trivial; natZ_numerals. 

  apply Qmult_Qdiv_pos; auto;
  apply Qlt_Zero_Qminus;
  stepr (4*(u'-l')); auto; qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.
 (* M *)
 repeat rewrite as_Moebius_Q_M; trivial; natZ_numerals. 
 unfold Qdiv; apply Qlt_reg_mult_pos_r; auto.
Defined.

Lemma lb_leq_ub_pointwise:forall k alpha, lb alpha k <= ub alpha k.
Proof.
 intros k alpha; apply Qlt_le_weak; apply lb_lt_ub_pointwise.
Defined.

Lemma lb_lt_ub:forall n k alpha, lb alpha n < ub alpha k.
Proof.
 intros n k alpha.
 case (le_lt_dec n k); intro H_nk.
  apply Qle_lt_trans with (lb alpha k).
   apply lb_nondecreasing; trivial.
   apply lb_lt_ub_pointwise.
  apply Qlt_le_trans with (ub alpha n).
   apply lb_lt_ub_pointwise.
   apply ub_nonincreasing; apply lt_le_weak; trivial.
Defined.
 

(** This is similar to Corollary 5.7.9 in the thesis. *)
Lemma thesis_5_7_9:forall k alpha, (ub alpha k) - (lb alpha k) <= 2/(k+1).
Proof.
 intros k;
 induction k.
 (* 0 *)
 intro alpha.
 unfold ub,lb.
 stepl 2; auto; stepr 2; auto; apply Qle_reflexive.

 (* S k *)
 (* TP: O <= k  *) 
 assert (H_k_nonneg:  0 <= k).
 apply Z_to_Qle; apply inj_le; auto with arith.
 (* TP: Zero < k + 1 *) 
 assert (H_k_one_pos: Zero < k + 1); [natq_zero; qnat_one; natq_S k; natq_S (S k); auto|].
 (* TP: Zero < k + 2 *) 
 assert (H_k_two_pos: Zero < k + 2 );[natq_zero; qnat_S 1; qnat_one; rewrite Qplus_assoc; natq_S k; natq_S (S k); auto|].
 (* TP: Zero < k + 3 *) 
 assert (H_k_three_pos: Zero < k + 3 );
 [natq_zero; qnat_S 2; qnat_S 1; qnat_one; rewrite Qplus_assoc; natq_S k; natq_S (S k); auto|].
 (* TP: Zero < 2 / (k + 1) *)
 assert (H_k_two_div_k_one_pos: Zero < 2 /(k + 1));[unfold Qdiv; auto|].

 intros [[ | | ] alpha'];
 generalize (IHk alpha'); clear IHk; 
 rewrite ub_S_n; rewrite lb_S_n; unfold hd,tl;
 set (u'':=ub alpha' k); set (l'':=lb alpha' k);
 qnat_one; qnat_S k;  intro IHk.
  (* L *)
  (* TP: Zero <= u''+ 1 *)
  assert (H_u''_one_nonneg: Zero <= u''+1);
  [ stepr (u''-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst u''; apply ub_is_in_base_interval_low|]. 
  (* TP: Zero < u''+3 *)
  assert (H_u''_three_pos: Zero < u''+3);
  [ apply Qle_lt_trans with (u''+1); auto; apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|].
  (* TP: Zero <= l''+ 1 *)
  assert (H_l''_one_nonneg: Zero <= l''+1);
  [ stepr (l''-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst l''; apply lb_is_in_base_interval_low|].
  (* TP: Zero < l''+3 *)
  assert (H_l''_three_pos: Zero < l''+3);
  [apply Qle_lt_trans with (l''+1); auto; apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|].

  repeat rewrite as_Moebius_Q_L; trivial; natZ_numerals.

  rewrite Qminus_Qdiv; auto;
  case (Q_eq_dec l'' (Qopp 1)); intro H_l''.
   (* l'' = -1 *)
   rewrite H_l''; rewrite H_l'' in IHk.
   (* TP : Zero <= 2 - (u'' * k + u'' + k + 1) *)
   assert (IHk_usable:Zero <= 2 - (u'' * k + u'' + k + 1)).
   apply Qle_Qminus_Zero;
   apply Qmult_resp_Qle_pos_r with ((k+Qone)^); auto;
   stepl (u''-(- Qone)); auto;
   qnat_one; generalize u''; intro x; field; auto.

   apply Qmult_Qdiv_pos_Qle; auto;
   apply Qle_Zero_Qminus.
   stepr (4*(2-(u''*k+u''+k+1))).
    apply Qle_mult_nonneg_nonneg; auto.
    qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.
   (* l'' <> -1 *)
   set (Psi_l :=fun x=> (2/(x+3))).
   (* TP:  Zero < Psi_l u'' *)
   assert (H_Psi_u''_pos:Zero < Psi_l u'');
   [ unfold Psi_l; unfold Qdiv; apply Qlt_mult_pos_pos; auto; apply Qinv_pos; auto|].
   (* TP:  Zero < Psi_l l'' *)
   assert (H_Psi_l''_pos:Zero < Psi_l l'');
   [ unfold Psi_l; unfold Qdiv; apply Qlt_mult_pos_pos; auto; apply Qinv_pos; auto|].

   apply Qlt_le_weak; 
   apply Qle_lt_trans with (2/(k+3)).
    apply Qle_trans with ((2/(k+Qone))*((Psi_l u'')*(Psi_l l''))).
     stepl ((u'' - l'')*((Psi_l u'')*(Psi_l l''))).
      apply Qle_reg_mult_r; auto.
      unfold Psi_l; qnat_S 2; qnat_S 1; qnat_one;
      generalize u'' l'' H_u''_three_pos H_l''_three_pos; intros x y Hx Hy; field; repeat apply Qmult_resp_nonzero; auto.
     stepr ((2/(k + Qone))*(((k+Qone)/(k+2))*((k+2)/(k+3)))).
      apply Qle_reg_mult_l; auto.
      (* TP: Psi_l is nonincreasing in [-1,1] *)
      assert (H_Psi_l_nonincreasing:forall x y, (Qopp Qone) <=x -> x<=y -> Psi_l y <= Psi_l x).
       intros x y Hx_nonneg Hx_le_y;
       unfold Psi_l;
       apply Qmult_Qdiv_pos_Qle;
       match goal with | [ |- _ < ?X1 + _ ] => apply Qlt_le_trans with 2; auto; apply Qle_Zero_Qminus;
	                                       stepr (X1- (Qopp Qone)); 
                                               [apply Qle_Qminus_Zero | qnat_S 2; qnat_S 1; qnat_one; ring]; 
					       auto; apply Qle_trans with x; auto
                       | [ |- _] =>  idtac end;
       apply Qle_Zero_Qminus;
       stepr (2*(y-x)); [apply Qle_mult_nonneg_nonneg; auto; apply Qle_Qminus_Zero; trivial | qnat_S 1; qnat_one; ring].
      (* TP: Psi_l ((1-k)/(1+k)) = (k+1)/(k+2) *)
      assert (H_Psi_l_1_min_k_1_plus_k:Psi_l ((1-k)/(1+k))= (k +1) / (k + 2)).
       unfold Psi_l;
       rewrite Qdiv_Qplus_Qmult; auto;
       rewrite Qdiv_Qdiv_Qmult_denominator; auto; 
         [ apply Qmult_Qdiv | stepl (2*(k+2))]; auto; 
         [ stepl (2*(k+2)) | | ]; auto;  qnat_S 2; qnat_S 1; qnat_one; ring.  
      (* TP:  -1 <= (1-k)/(1+k) *)
      assert (H__1_min_k_1_plus_k_ge_min_one:Qopp Qone <= (1-k)/(1+k)).
       apply Qle_Zero_Qminus; rewrite Qdiv_Qminus_Qmult; auto; unfold Qdiv; apply Qle_mult_nonneg_nonneg; auto;
       stepr 2; auto; qnat_S 1; qnat_one; ring.
      (* TP: Psi_l (-k/(k+2)) = (k+2)/(k+3) *)
      assert (H_Psi_l_min_k_k_two:Psi_l (-k/(k+2)) = (k+2)/(k+3)).
       unfold Psi_l;
       rewrite Qdiv_Qplus_Qmult; auto;
       rewrite Qdiv_Qdiv_Qmult_denominator; auto; 
         [ apply Qmult_Qdiv | stepl (2*(k+3))]; auto; 
         [ stepl (2*(k+3)) | | ]; auto;  qnat_S 2; qnat_S 1; qnat_one; ring.  
      (* TP:  -1 <= (-k)/(k+2) *)
      assert (H_min_k_k_two_ge_min_one:Qopp Qone <= (-k)/(k+2)).
       apply Qle_Zero_Qminus; rewrite Qdiv_Qminus_Qmult; auto; unfold Qdiv; apply Qle_mult_nonneg_nonneg; auto;
       stepr 2; auto; qnat_S 1; qnat_one; ring.
       
      apply Qmult_Qle_compat;
      [ natq_one; rewrite <- H_Psi_l_1_min_k_1_plus_k; apply H_Psi_l_nonincreasing; auto; subst u''; apply thesis_5_7_2ii_u
      | rewrite <- H_Psi_l_min_k_k_two; apply H_Psi_l_nonincreasing; auto; subst l''; apply thesis_5_7_2i_l; auto
      | unfold Psi_l; auto
      | unfold Psi_l; auto
      ].

     natq_one; generalize (k+1) (k+2) (k+3) H_k_one_pos H_k_two_pos H_k_three_pos; 
     qnat_S 1; qnat_one;  generalize (Qone+Qone); intros;  field; auto.

    apply Qmult_Qdiv_pos; auto; apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.       

  (* R *)
  (* TP: Zero <= -u''+ 1 *)
  assert (H_min_u''_one_nonneg: Zero <= -u''+1);
  [stepr (1-u''); try ring; apply Qle_Qminus_Zero; subst u''; apply ub_is_in_base_interval_up|].
  (* TP: Zero < -u''+3 *)
  assert (H_min_u''_three_pos: Zero < -u''+3);
  [ apply Qle_lt_trans with ((-u'')+1); auto;apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|].
  (* TP: Zero <= -l''+ 1 *)
  assert (H_min_l''_one_nonneg: Zero <= -l''+1);
  [stepr (1-l''); try ring; apply Qle_Qminus_Zero; subst l''; apply lb_is_in_base_interval_up|].
  (* TP: Zero < -l''+3 *)
  assert (H_min_l''_three_pos: Zero < -l''+3);
  [ apply Qle_lt_trans with ((-l'')+1); auto;
    apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|].

  repeat rewrite as_Moebius_Q_R; trivial; natZ_numerals.

  rewrite Qminus_Qdiv; auto;
  case (Q_eq_dec u'' 1); intro H_u''.
   (* u'' = 1 *)
   rewrite H_u''; rewrite H_u'' in IHk.
   (* TP : Zero <= 2 - (l'' * k + l'' + k + 1) *)
   assert (IHk_usable:Zero<=2-(k+1-l''*k-l'')).
   apply Qle_Qminus_Zero;
   apply Qmult_resp_Qle_pos_r with ((k+Qone)^); auto;
   stepl (Qone - l''); auto;
   qnat_one; generalize l''; intro x; field; auto.

   apply Qmult_Qdiv_pos_Qle; auto;
   apply Qle_Zero_Qminus.
   stepr (4*(2-(k+1-l''*k-l''))).
    apply Qle_mult_nonneg_nonneg; auto.
    qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.

   (* u'' <> -1 *)
   set (Psi_r :=fun x=> (2/(-x+3))).
   (* TP:  Zero < Psi_r l'' *)
   assert (H_Psi_l''_pos:Zero < Psi_r l'');
   [ unfold Psi_r; unfold Qdiv; apply Qlt_mult_pos_pos; auto; apply Qinv_pos; auto|].
   (* TP:  Zero < Psi_r u'' *)
   assert (H_Psi_u''_pos:Zero < Psi_r u'');
   [ unfold Psi_r; unfold Qdiv; apply Qlt_mult_pos_pos; auto; apply Qinv_pos; auto|].

   apply Qlt_le_weak; 
   apply Qle_lt_trans with (2/(k+3)).
    apply Qle_trans with ((2/(k+Qone))*((Psi_r l'')*(Psi_r u''))).
     stepl ((u'' - l'')*((Psi_r l'')*(Psi_r u''))).
      apply Qle_reg_mult_r; auto.
      unfold Psi_r; qnat_S 2; qnat_S 1; qnat_one; generalize l'' u'' H_min_l''_three_pos H_min_u''_three_pos; 
         intros x y Hx Hy; field; repeat apply Qmult_resp_nonzero; auto.
     stepr ((2/(k + Qone))*(((k+Qone)/(k+2))*((k+2)/(k+3)))).
      apply Qle_reg_mult_l; auto.
      (* TP: Psi_r is nondecreasing in [-1,1] *)
      assert (H_Psi_r_nondecreasing:forall x y, y <= Qone -> x<=y -> Psi_r x <= Psi_r y).
       intros x y Hx_nonneg Hx_le_y;
       unfold Psi_r;
       apply Qmult_Qdiv_pos_Qle;
       match goal with | [ |- _ < Qopp ?X1 + _ ] => apply Qlt_le_trans with 2; auto; apply Qle_Zero_Qminus;
	                                       stepr (Qone - X1); 
                                               [apply Qle_Qminus_Zero | qnat_S 2; qnat_S 1; qnat_one; ring]; 
					       auto; apply Qle_trans with y; auto
                       | [ |- _] =>  idtac end;
       apply Qle_Zero_Qminus;
       stepr (2*(y-x)); [apply Qle_mult_nonneg_nonneg; auto; apply Qle_Qminus_Zero; trivial | qnat_S 1; qnat_one; ring].
      (* TP: Psi_r ((k-1)/(k+1)) = (k+1)/(k+2) *)
      assert (H_Psi_r_k_min_1_k_plus_1:Psi_r ((k-1)/(k+1))=(k+1)/(k+2)).
       unfold Psi_r;
       rewrite <- Qdiv_Qopp_numerator; auto;
       rewrite Qdiv_Qplus_Qmult; auto;
       rewrite Qdiv_Qdiv_Qmult_denominator; auto;
         [ apply Qmult_Qdiv | stepl (2*(k+2))]; auto; 
         [ stepl (2*(k+2)) | | ]; auto;  qnat_S 2; qnat_S 1; qnat_one; ring.  
      (* TP:  (k-1)/(k+1) <= 1 *)
      assert (H_k_min_1_k_plus_1_le_one: (k-1)/(k+1) <= Qone).
       apply Qle_Zero_Qminus; rewrite Qminus_Qdiv_Qmult; auto; unfold Qdiv; apply Qle_mult_nonneg_nonneg; auto;
       stepr 2; auto; qnat_S 1; qnat_one; ring.
      (* TP: Psi_r (k/(k+2)) = (k+2)/(k+3) *)
      assert (H_Psi_r_k_k_two:Psi_r (k/(k+2))=(k+2)/(k+3)).
       unfold Psi_r;
       rewrite <- Qdiv_Qopp_numerator; auto;
       rewrite Qdiv_Qplus_Qmult; auto;
       rewrite Qdiv_Qdiv_Qmult_denominator; auto; 
         [ apply Qmult_Qdiv | stepl (2*(k+3))]; auto; 
         [ stepl (2*(k+3)) | | ]; auto;  qnat_S 2; qnat_S 1; qnat_one; ring.  
      (* TP:  k/(k+2) <= 1 *)
      assert (H_k_k_two_le_one: k/(k+2)<=Qone).
       apply Qle_Zero_Qminus; rewrite Qminus_Qdiv_Qmult; auto; unfold Qdiv; apply Qle_mult_nonneg_nonneg; auto;
       stepr 2; auto; qnat_S 1; qnat_one; ring.
       
      apply Qmult_Qle_compat;
      [ natq_one; rewrite <- H_Psi_r_k_min_1_k_plus_1; apply H_Psi_r_nondecreasing; auto; subst l''; apply thesis_5_7_2ii_l
      | rewrite <- H_Psi_r_k_k_two; apply H_Psi_r_nondecreasing; auto; subst u''; apply thesis_5_7_2i_u; auto
      | unfold Psi_r; auto 
      | unfold Psi_r; auto
      ].

     natq_one; generalize (k+1) (k+2) (k+3) H_k_one_pos H_k_two_pos H_k_three_pos; 
     qnat_S 1; qnat_one;  generalize (Qone+Qone); intros;  field; auto.

    apply Qmult_Qdiv_pos; auto; apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.       
  (* M *)
  (* TP: Zero<=2*k+1 *)
  assert (H_2k_1_pos:  Zero<2*k+1);
  [apply Qle_lt_trans with (2*k); auto; apply Qlt_Zero_Qminus; stepr 1; auto; qnat_S 1; qnat_one; ring|].

  repeat rewrite as_Moebius_Q_M; trivial; natZ_numerals.

  apply Qlt_le_weak; 
  apply Qle_lt_trans with ((2/(k+1))/3).
   stepl ((u''-l'')/3).
    unfold Qdiv; apply Qle_reg_mult_r; auto.
    generalize u'' l''; intros x y; field; auto.
   rewrite Qdiv_Qdiv_Qmult_numerator; auto;
   apply Qmult_Qdiv_pos; auto;
   apply Qlt_Zero_Qminus;
   stepr (2*(2*k+1)); auto;
   qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.
Defined.
