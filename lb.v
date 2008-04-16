(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import digits.


Close Scope Z_scope.

(** We define a function [lb] that returns the #<em>#upper bound#</em># of the
interval obtained by applying the initial segment of length [n] of
[alpha] to the base interval #&#91;#-1,+1#&#93;#.*)

Fixpoint lb (alpha:Reals) (n:nat) {struct n} : Q :=
  match n with
  |   O => (Qopp 1) (* this is because of base interval, and that d(-1)=-1 *)
  | S p => let (d,alpha'):= alpha in let q := lb alpha' p in
           as_Moebius_Q d q
  end.

Lemma lb_S_n:forall n alpha, lb alpha (S n) = as_Moebius_Q (hd alpha) (lb (tl alpha) n).
Proof.
 intros n [d alpha']; trivial.
Defined.

Lemma lb_is_in_base_interval:forall k alpha,  - Qone <= lb alpha k /\ lb alpha k <= Qone.
Proof.
 intro k; induction k; intro alpha.
 (* 0 *)
 split; unfold lb; natq_one; try rewrite <- Z_to_Qopp; apply Z_to_Qle; auto with zarith.
 (* S k *)
 destruct alpha as [[ | | ] alpha']; generalize (IHk alpha'); clear IHk;
 rewrite lb_S_n; unfold hd, tl; set (l':=lb alpha' k); intros [IHk_1 IHk_2].


  (* L *)
  (* TP: Zero <= l'+ 1 *)
  assert (H_l'_one_nonneg: Zero <= l'+1).
  stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; auto. 
  (* TP: Zero < l'+3 *)
  assert (H_l'_three_pos: Zero < l'+3).
  apply Qle_lt_trans with (l'+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= 2*l'+ 2 *)
  assert (H_2l'_two_nonneg: Zero <= 2*l'+2).
  stepr (2*(l'+1)); [|qZ_numerals; ring]; apply Qle_mult_nonneg_nonneg; auto.
  (* TP: Zero <= l'+ 2 *)
  assert (H_l'_two_nonneg: Zero <= l'+2).
  apply Qle_trans with (l'+1); auto;
  apply Qle_plus_plus; try apply Qle_reflexive; apply Z_to_Qle; apply inj_le; auto.

  rewrite as_Moebius_Q_L; trivial; natZ_numerals.

  split; apply Qmult_resp_Qle_pos_r with (l'+3); auto.
   stepr (l'-1).
    apply Qle_Zero_Qminus;
    stepr (2*l'+2); auto; qnat_S 2; qnat_S 1; qnat_one; ring.
    generalize (l'-1) (l'+3) H_l'_three_pos; intros; field; auto.
  
   stepl (l'-1).
    apply Qle_Zero_Qminus;
    stepr 4; auto; qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.
    generalize (l'-1) (l'+3) H_l'_three_pos; intros; field; auto.
  
  (* R *)
  (* TP: Zero <= -l'+ 1 *)
  assert (H_min_l'_one_nonneg: Zero <= -l'+1).
  stepr (1-l'); try ring; apply Qle_Qminus_Zero; auto. 
  (* TP: Zero < -l'+3 *)
  assert (H_min_l'_three_pos: Zero < -l'+3).
  apply Qle_lt_trans with ((-l')+1); auto.
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= 2*(-l')+ 2 *)
  assert (H_2_min_l'_two_nonneg: Zero <= 2*(-l')+2).
  stepr (2*(-l'+1)); [|qZ_numerals; ring]; apply Qle_mult_nonneg_nonneg; auto.

  rewrite as_Moebius_Q_R; trivial; natZ_numerals.
  
  split; apply Qmult_resp_Qle_pos_r with (-l'+3); auto.
   stepr (l'+1).
    apply Qle_Zero_Qminus;
    stepr 4; auto; qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.
    generalize (l'+1) (-l'+3) H_min_l'_three_pos; intros; field; auto.

   stepl (l'+1).
    apply Qle_Zero_Qminus;
    stepr (2*(-l')+2); auto; qnat_S 2; qnat_S 1; qnat_one; ring.
    generalize (l'+1) (-l'+3) H_min_l'_three_pos; intros; field; auto.

  (* M *)
  rewrite as_Moebius_Q_M; natZ_numerals.

  split; apply Qmult_resp_Qle_pos_r with 3; auto;
  [ stepr l' | stepl l'].
  apply Qle_trans with (-Qone); auto; apply Qlt_le_weak; apply Qlt_Zero_Qminus; stepr 2; auto.  
  generalize l'; intro; field; auto.
  apply Qle_trans with Qone; auto; apply Qlt_le_weak; apply Qlt_Zero_Qminus; stepr 2; auto.  
  generalize l'; intro; field; auto.
Defined.


Lemma lb_is_in_base_interval_low:forall k alpha, - Qone <= lb alpha k.
Proof.
 intros k alpha; elim (lb_is_in_base_interval k alpha); trivial.
Defined.

Lemma lb_is_in_base_interval_up:forall k alpha, lb alpha k <= Qone.
Proof.
 intros k alpha; elim (lb_is_in_base_interval k alpha); trivial.
Defined.

(** This is similar to Lemma 5.7.2.i in the thesis. *)
Lemma thesis_5_7_2i_l:forall (k:nat) alpha, ~(lb alpha k = Qopp 1) -> (-k)/(k+2) <= lb alpha k.
Proof.
 intro k; induction k; intros alpha H_nonzero.

  (* 0 *)
  apply False_ind; apply H_nonzero; trivial.
  (* S k *)
  rewrite lb_S_n;
  rewrite lb_S_n in H_nonzero.
  (* TP: Zero < k + Qone *) 
  assert (H_k_one_pos: Zero < k + Qone ).
  natq_S k; natq_zero; apply Z_to_Qlt; apply inj_lt; apply lt_O_Sn.
  (* TP: Zero < k + 2 *) 
  assert (H_k_two_pos: Zero < k + 2 ).
  stepr ((k+Qone)+Qone);
  [ natq_S k; natq_S (S k); natq_zero; auto
  | qnat_S 1; qnat_one; ring].
  (* TP: O <= k  *) 
  assert (H_k_nonneg:  0 <= k).
  apply Z_to_Qle; apply inj_le; auto with arith.
  (* TP: Qone <= 2 * k + 3*)
  assert (H_2k_3_nonneg:  Qone <= 2 * k + 3).
  apply Qle_Zero_Qminus; stepr (2*(k+1));
  [ apply Qle_mult_nonneg_nonneg; auto
  | qnat_S 2; qnat_S 1; qnat_one; ring
  ].

  destruct alpha as [[ | | ] alpha']; unfold hd,tl; unfold hd,tl in H_nonzero; qnat_one; qnat_S k; set (l':=lb alpha' k).
   (* L *)
   fold l' in H_nonzero.
   case (Q_eq_dec l' (Qopp 1)); intro H_l'.
    (* l' = -1 *)
    apply False_ind; apply H_nonzero; rewrite H_l'; rewrite as_Moebius_Q_L; qZ_numerals; auto.
    (* l' <> -1 *)
    generalize (IHk alpha' H_l'); fold l'; clear IHk; intro IHk.
    (* TP: Zero <= l'+ 1 *)
    assert (H_l'_one_nonneg: Zero <= l'+1).
    stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero;  unfold l'; apply lb_is_in_base_interval_low. 
    (* TP: Zero < l'+3 *)
    assert (H_l'_three_pos: Zero < l'+3).
    apply Qle_lt_trans with (l'+1); auto;
    apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
 
    generalize H_nonzero; clear H_nonzero; rewrite as_Moebius_Q_L; trivial; natZ_numerals; intros H_nonzero.

    apply Qmult_Qdiv_pos_Qle; auto;
    apply Qle_Zero_Qminus;
    stepr (2*(l'*(k+2)-(-k))).
     apply Qle_mult_nonneg_nonneg; auto;
     apply Qle_Qminus_Zero;
     apply Qmult_resp_Qle_pos_r with (Qinv (k+2)).
      apply Qinv_pos; auto.
      rewrite <- Qmult_assoc; rewrite Qmult_Qinv_r; auto.
      stepr l'; trivial; try ring.

     qnat_S 2; qnat_S 1; qnat_one; ring.

   (* R *)
    (* TP: Zero <= -l'+ 1 *)
    assert (H_min_l'_one_nonneg: Zero <= -l'+1).
    stepr (1-l'); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_up.
    (* TP: Zero < -l'+3 *)
    assert (H_min_l'_three_pos: Zero < -l'+3).
    apply Qle_lt_trans with ((-l')+1); auto;
    apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
    (* TP: Zero <= l'+ 1 *)
    assert (H_l'_one_nonneg: Zero <= l'+1).
    stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_low. 
    (* TP: Zero <= l'+3 *)
    assert (H_l'_three_pos: Zero <= l'+3).
    apply Qlt_le_weak; apply Qle_lt_trans with (l'+1); auto;
    apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.

    rewrite as_Moebius_Q_R; trivial; natZ_numerals.

 
    apply Qmult_Qdiv_pos_Qle; auto;
    apply Qle_Zero_Qminus;
    stepr (2*((l'+3)+2*k)).
     apply Qle_mult_nonneg_nonneg; auto.

     qnat_S 2; qnat_S 1; qnat_one; ring.

   (* M *)
   rewrite as_Moebius_Q_M; natZ_numerals;
    (* TP: Zero <= l'+ 1 *)
    assert (H_l'_one_nonneg: Zero <= l'+1).
    stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_low. 
   
   apply Qle_trans with ((-Qone)/3).
    apply Qmult_Qdiv_pos_Qle; auto;
    apply Qle_Zero_Qminus;
    stepr (2*k); auto; qnat_S 2; qnat_S 1; qnat_one; ring.

    apply Qmult_Qdiv_pos_Qle; auto;
    apply Qle_Zero_Qminus;
    stepr (3*(l'+1)).
     apply Qle_mult_nonneg_nonneg; auto.
     qnat_S 2; qnat_S 1; qnat_one; ring.
Defined.


Lemma thesis_5_7_2ii_l:forall (k:nat) alpha, lb alpha k <= (k-1)/(k+1).
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

  rewrite lb_S_n;
  destruct alpha as [d alpha'];
  destruct d; unfold hd,tl;
  generalize (IHk alpha'); clear IHk; intros IHk;
  qnat_one; qnat_S k; set (l':=lb alpha' k);
  fold l' in IHk.
   (* L *)
   (* TP: Zero <= -l'+ 1 *)
   assert (H_min_l'_one_nonneg: Zero <= -l'+1).
   stepr (1-l'); try ring; apply Qle_Qminus_Zero; unfold l'; apply lb_is_in_base_interval_up.
   (* TP: Zero <= l'+ 1 *)
   assert (H_l'_one_nonneg: Zero <= l'+1).
   stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; unfold l'; apply lb_is_in_base_interval_low. 
   (* TP: Zero < l'+3 *)
   assert (H_l'_three_pos: Zero < l'+3).
   apply Qle_lt_trans with (l'+1); auto;
   apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
   
   rewrite as_Moebius_Q_L; trivial; natZ_numerals.

   apply Qmult_Qdiv_pos_Qle; auto;
   apply Qle_Zero_Qminus;
   stepr (2*((-l'+1)+2*k)).
    apply Qle_mult_nonneg_nonneg; auto;
    apply Qle_plus_pos_pos; auto.  

    qnat_S 2; qnat_S 1; qnat_one; ring.

   (* R *)
   (* TP: Zero <= -l'+ 1 *)
   assert (H_min_l'_one_nonneg: Zero <= -l'+1).
   stepr (1-l'); try ring; apply Qle_Qminus_Zero; unfold l'; apply lb_is_in_base_interval_up.
   (* TP: Zero < -l'+3 *)
   assert (H_min_l'_three_pos: Zero < -l'+3).
   apply Qle_lt_trans with ((-l')+1); auto;
   apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
   (* TP: Zero <= l'+ 1 *)
   assert (H_l'_one_nonneg: Zero <= l'+1).
   stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; unfold l'; apply lb_is_in_base_interval_low. 

   rewrite as_Moebius_Q_R; trivial; natZ_numerals.

   apply Qmult_Qdiv_pos_Qle; auto;
   apply Qle_Zero_Qminus;
   stepr (2*((k-1)-l'*(k+1))).
    apply Qle_mult_nonneg_nonneg; auto;
    apply Qle_Qminus_Zero;
    apply Qmult_resp_Qle_pos_r with (Qinv (k+1)).
      apply Qinv_pos; auto.
      rewrite <- Qmult_assoc; rewrite Qmult_Qinv_r; auto;
      stepl l'; trivial; try ring.

    qnat_S k; qnat_S 2; qnat_S 1; qnat_one; ring.

   (* M *)
   generalize IHk; clear IHk; subst l'.
      destruct k; rewrite as_Moebius_Q_M; natZ_numerals; intro IHk.
   (* k := 0 *)
   unfold lb; stepr Zero; auto.
   (* k := S k *)
   set (l':=lb alpha' (S k));
   fold l' in IHk.
   (* TP: O <= k  *) 
   assert (H_pk_nonneg:  0 <= k).
   apply Z_to_Qle; apply inj_le; auto with arith.
   (* TP: Zero <= -l'+ 1 *)
   assert (H_min_l'_one_nonneg: Zero <= -l'+1).
   stepr (1-l'); try ring; apply Qle_Qminus_Zero; unfold l'; apply lb_is_in_base_interval_up.
   (* TP: Zero < -l'+3 *)
   assert (H_min_l'_three_pos: Zero <= -l'+3).
   apply Qle_trans with (-l'+1); auto;
   apply Qle_plus_plus; try apply Qle_reflexive; apply Z_to_Qle; apply inj_le; auto.

   apply Qmult_Qdiv_pos_Qle; auto;
   apply Qle_Zero_Qminus.
   stepr (k*(-l'+3)+3*(-l'+1)).
    apply Qle_plus_pos_pos; apply Qle_mult_nonneg_nonneg; auto.
       
    qnat_S (S k); qnat_S k; qnat_S 2; qnat_S 1; qnat_one;
    [ ring | natq_S k; natq_S (S k); auto].
Defined.


Lemma lb_nondecreasing_step:forall k alpha, lb alpha k <= lb alpha (S k).
Proof.
 intro k; induction k.
 (* 0 *)
 intro alpha; stepl (Qopp 1); trivial; apply lb_is_in_base_interval_low.
 (* S n *)
 intros [d alpha'];
 rewrite lb_S_n;
 rewrite (lb_S_n (S k) (Cons d alpha')); unfold hd, tl.
 destruct d as [ | | ]; set (l':=lb alpha' (S k)); set (l'':=lb alpha' k); 
 generalize (IHk alpha'); clear IHk; intros IHk; fold l' l'' in IHk.

  (* L *)
  (* TP: Zero <= l'+ 1 *)
  assert (H_l'_one_nonneg: Zero <= l'+1).
  stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_low. 
  (* TP: Zero < l'+3 *)
  assert (H_l'_three_pos: Zero < l'+3).
  apply Qle_lt_trans with (l'+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= l''+ 1 *)
  assert (H_l''_one_nonneg: Zero <= l''+1).
  stepr (l''-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst l''; apply lb_is_in_base_interval_low. 
  (* TP: Zero < l''+3 *)
  assert (H_l''_three_pos: Zero < l''+3).
  apply Qle_lt_trans with (l''+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.

  repeat rewrite as_Moebius_Q_L; trivial; natZ_numerals.
  (* NB: conjug_Q_L is nondecreasing for -3<= x*)
  apply Qmult_Qdiv_pos_Qle; auto.
  apply Qle_Zero_Qminus.
  stepr (4*(l'-l'')).
   apply Qle_mult_nonneg_nonneg; auto.
   apply Qle_Qminus_Zero; assumption.
   qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.

  (* R *)
  (* TP: Zero <= -l'+ 1 *)
  assert (H_min_l'_one_nonneg: Zero <= -l'+1).
  stepr (1-l'); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_up.
  (* TP: Zero < -l'+3 *)
  assert (H_min_l'_three_pos: Zero < -l'+3).
  apply Qle_lt_trans with ((-l')+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.
  (* TP: Zero <= -l'''+ 1 *)
  assert (H_min_l''_one_nonneg: Zero <= -l''+1).
  stepr (1-l''); try ring; apply Qle_Qminus_Zero; subst l''; apply lb_is_in_base_interval_up.
  (* TP: Zero < -l''+3 *)
  assert (H_min_l''_three_pos: Zero < -l''+3).
  apply Qle_lt_trans with ((-l'')+1); auto;
  apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring.

  repeat rewrite as_Moebius_Q_R; trivial; natZ_numerals.
  (* NB: conjug_Q_R is nondecreasing for x<=3*)
  apply Qmult_Qdiv_pos_Qle; auto.
  apply Qle_Zero_Qminus.
  stepr (4*(l'-l'')).
   apply Qle_mult_nonneg_nonneg; auto.
   apply Qle_Qminus_Zero; assumption.
   qnat_S 3; qnat_S 2; qnat_S 1; qnat_one; ring.

  (* M *)
  do 2 rewrite as_Moebius_Q_M; natZ_numerals.
  (* NB: conjug_Q_M is nondecreasing*)
  apply Qmult_Qdiv_pos_Qle; auto.
  apply Qle_Zero_Qminus.
  stepr (3*(l'-l'')).
   apply Qle_mult_nonneg_nonneg; auto.
   apply Qle_Qminus_Zero; assumption.
   qnat_S 2; qnat_S 1; qnat_one; ring.
Defined.


Lemma lb_nondecreasing_steps:forall n k alpha, lb alpha n <= lb alpha (k+n).
Proof.
 intros [|n] k. 
  (* n:=0 *)
  intros; replace (k+0)%nat with k; trivial; apply lb_is_in_base_interval_low.
  (* n:=S n*)
  induction k.
   (* k:=0 *)
   intro alpha; apply Qle_reflexive. 
   (* k:=S k *)
   replace (S k +S n)%nat with (S (k+S n))%nat; trivial;
   intros [d alpha'];
   rewrite (lb_S_n n (Cons d alpha')); rewrite lb_S_n;  unfold hd, tl.
   destruct d.
    apply as_Moebius_Q_L_nondecreasing;
    [ apply lb_is_in_base_interval_low
    | apply lb_is_in_base_interval_up
    | apply Qle_trans with (lb alpha' (S n)); trivial; apply lb_nondecreasing_step].
    apply as_Moebius_Q_R_nondecreasing;
    [ apply lb_is_in_base_interval_low
    | apply lb_is_in_base_interval_up
    | apply Qle_trans with (lb alpha' (S n)); trivial; apply lb_nondecreasing_step].
    apply as_Moebius_Q_M_nondecreasing;
    [ apply lb_is_in_base_interval_low
    | apply lb_is_in_base_interval_up
    | apply Qle_trans with (lb alpha' (S n)); trivial; apply lb_nondecreasing_step].
Defined.

Lemma lb_nondecreasing:forall m n alpha, (m<=n)%nat -> lb alpha m <= lb alpha n.
Proof.
 intros m n alpha Hmn.
 replace n with ((n-m)+m)%nat; try omega; apply lb_nondecreasing_steps.
Defined.
