(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)

Require Import digits.
Require Import Raxioms.
Require Import RIneq.
Require Import R_addenda.
Require Import Fourier_solvable_ineqs.
Require Import Bounded_M.

Open Scope Z_scope.
Open Scope Q_scope.

Lemma Incl_M_L_unfolded_auxiliary_51: forall (a b c d:Q), 0 < d - c  -> 
                (d-c)*((d - c) * (-1 / 2 - 1 / 2)) <= (d-c)*((b - a) * ((2 + 1) / 2 - 1 / 2)) ->
                 -1 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (-1/2 - 1/2) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace ((2+1)/2 - 1/2) with Qone; [|qZ_numerals; field; auto];
 intros H_mult;
 apply Qmult_pos_Qle_Qdiv; trivial;
 ring_exact_Q H_mult.
Qed.

Lemma Incl_M_L_unfolded_auxiliary_52: forall (a b c d:Q), d - c<0  -> 
                (d-c)*((d - c) * (-1 / 2 - 1 / 2)) <= (d-c)*((b - a) * ((2 + 1) / 2 - 1 / 2)) ->
                 -1 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (-1/2 - 1/2) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace ((2+1)/2 - 1/2) with Qone; [|qZ_numerals; field; auto];
 intros H_mult;
 apply Qmult_neg_Qle_Qdiv; trivial;
 ring_exact_Q H_mult.
Qed.

Lemma Incl_M_L_unfolded_auxiliary_5: forall (a b c d:Q), d - c<>0  -> 
                (d-c)*((d - c) * (-1 / 2 - 1 / 2)) <= (d-c)*((b - a) * ((2 + 1) / 2 - 1 / 2)) ->
                 -1 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc.
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_L_unfolded_auxiliary_52
  | apply Incl_M_L_unfolded_auxiliary_51
  ]; assumption.
Qed.

Lemma Incl_M_L_unfolded_auxiliary_61: forall (a b c d:Q), 0 < d + c  -> 
                    (d+c)*((a+b)*(1/2+(2+1)/2))<=(d+c)*((c+d)*(1/2+-1/2))->
                    (a + b) / (c + d) <= 0.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (1/2 + (2+1)/2) with (Qone +Qone); [|qZ_numerals; field; auto];
 replace (1/2 + -1/2) with Zero; [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:Zero<c+d);[ring_exact_Q Hdc|];
 apply Qmult_resp_Qle_pos_l with 2; auto;
 rewrite Qdiv_Qmult_numerator_l; auto;
 apply Qmult_pos_Qdiv_Qle; trivial; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_L_unfolded_auxiliary_62: forall (a b c d:Q), d+c<0  -> 
                    (d+c)*((a+b)*(1/2+(2+1)/2))<=(d+c)*((c+d)*(1/2+-1/2))->
                    (a + b) / (c + d) <= 0.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (1/2 + (2+1)/2) with (Qone +Qone); [|qZ_numerals; field; auto];
 replace (1/2 + -1/2) with Zero; [|qZ_numerals; field; auto];
 repeat rewrite Qmult_zero_right;
 intros H_mult;
 assert (Hcd:c+d<Zero);[ring_exact_Q Hdc|];
 apply Qle_Qdiv_nonneg_neg; trivial;
 apply Qmult_resp_Qle_pos_l with 2; auto; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_L_unfolded_auxiliary_6: forall (a b c d:Q), d+c<>0  -> 
                    (d+c)*((a+b)*(1/2+(2+1)/2))<=(d+c)*((c+d)*(1/2+-1/2))->
                    (a + b) / (c + d) <= 0.
Proof.
 intros a b c d Hdc.
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_L_unfolded_auxiliary_62
  | apply Incl_M_L_unfolded_auxiliary_61
  ]; assumption.
Qed.

Lemma Incl_M_L_unfolded_auxiliary_71: forall (a b c d:Q), 0<d+c -> 
                     (d+c)*((c+d)*(-1/2-1/2))<=(d+c)*((a+b)*((2+1)/2-1/2)) ->
                    -1 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (-1/2 - 1/2) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace ((2+1)/2 - 1/2) with Qone; [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:Zero<c+d);[ring_exact_Q Hdc|];
 apply Qmult_pos_Qle_Qdiv; trivial; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_L_unfolded_auxiliary_72: forall (a b c d:Q), d+c<0 -> 
                     (d+c)*((c+d)*(-1/2-1/2))<=(d+c)*((a+b)*((2+1)/2-1/2)) ->
                    -1 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (-1/2 - 1/2) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace ((2+1)/2 - 1/2) with Qone; [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:c+d<Zero);[ring_exact_Q Hdc|];
 apply Qmult_neg_Qle_Qdiv; trivial; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_L_unfolded_auxiliary_7: forall (a b c d:Q), d+c  <> 0 -> 
                     (d+c)*((c+d)*(-1/2-1/2))<=(d+c)*((a+b)*((2+1)/2-1/2)) ->
                    -1 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc.
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_L_unfolded_auxiliary_72
  | apply Incl_M_L_unfolded_auxiliary_71
  ]; assumption.
Qed.

Lemma Incl_M_L_unfolded_auxiliary_81: forall (a b c d:Q), 0<d-c -> 
             (d-c)*((b-a)*(1/2+(2+1)/2))<=(d-c)*((d-c)*(1/2+-1/2)) ->
                 (b - a) / (d - c)<=0.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (1/2 + (2+1)/2) with (Qone +Qone); [|qZ_numerals; field; auto];
 replace (1/2 + -1/2) with Zero; [|qZ_numerals; field; auto];
 repeat rewrite Qmult_zero_right;
 intros H_mult;
 apply Qle_Qdiv_nonpos_pos; trivial;
 apply Qmult_resp_Qle_pos_l with 2; auto; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_L_unfolded_auxiliary_82: forall (a b c d:Q), d-c<0 -> 
             (d-c)*((b-a)*(1/2+(2+1)/2))<=(d-c)*((d-c)*(1/2+-1/2)) ->
                 (b - a) / (d - c)<=0.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (1/2 + (2+1)/2) with (Qone +Qone); [|qZ_numerals; field; auto];
 replace (1/2 + -1/2) with Zero; [|qZ_numerals; field; auto];
 repeat rewrite Qmult_zero_right;
 intros H_mult;
 apply Qmult_resp_Qle_pos_l with 2; auto;
 rewrite Qdiv_Qmult_numerator_l; auto;
 apply Qmult_neg_Qdiv_Qle; trivial; ring_exact_Q H_mult. 
Qed.


Lemma Incl_M_L_unfolded_auxiliary_8: forall (a b c d:Q), d - c <> 0 -> 
             (d-c)*((b-a)*(1/2+(2+1)/2))<=(d-c)*((d-c)*(1/2+-1/2)) ->
                 (b - a) / (d - c)<=0.
Proof.
 intros a b c d Hdc.
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_L_unfolded_auxiliary_82
  | apply Incl_M_L_unfolded_auxiliary_81
  ]; assumption.
Qed.

Lemma Incl_M_R_unfolded_auxiliary_51: forall (a b c d:Q), 0 < d - c  -> 
             (d-c)*((d-c)*(1/2-1/2))<=(d-c)*((b-a)*((2+1)/2- -1/2))->
                 0 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (1/2 - 1/2) with Zero; [|qZ_numerals; field; auto];
 replace ((2+1)/2- -1/2) with (Qone+Qone); [|qZ_numerals; field; auto];
 rewrite Qmult_zero_right;
 intros H_mult;
 apply Qmult_resp_Qle_pos_l with 2; auto;
 rewrite Qdiv_Qmult_numerator_l; auto;
 apply Qmult_pos_Qle_Qdiv; trivial;
 ring_exact_Q H_mult.
Qed.

Lemma Incl_M_R_unfolded_auxiliary_52:  forall (a b c d:Q), d-c<0  -> 
             (d-c)*((d-c)*(1/2-1/2))<=(d-c)*((b-a)*((2+1)/2- -1/2))->
                 0 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (1/2 - 1/2) with Zero; [|qZ_numerals; field; auto];
 replace ((2+1)/2- -1/2) with (Qone+Qone); [|qZ_numerals; field; auto];
 rewrite Qmult_zero_right;
 intros H_mult;
 apply Qmult_resp_Qle_pos_l with 2; auto;
 rewrite Qdiv_Qmult_numerator_l; auto;
 apply Qmult_neg_Qle_Qdiv; trivial;
 ring_exact_Q H_mult.
Qed.

Lemma Incl_M_R_unfolded_auxiliary_5: forall (a b c d:Q), d - c<>0  -> 
             (d-c)*((d-c)*(1/2-1/2))<=(d-c)*((b-a)*((2+1)/2- -1/2))->
                 0 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc;
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_R_unfolded_auxiliary_52
  | apply Incl_M_R_unfolded_auxiliary_51
  ]; assumption.
Qed.


Lemma Incl_M_R_unfolded_auxiliary_61: forall (a b c d:Q), 0 < d + c  -> 
                     (d+c)*((a+b)*(-1/2+(2+1)/2))<=(d+c)*((c+d)*(1/2+1/2))->
                    (a + b) / (c + d) <= 1.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (-1/2 + (2+1)/2) with Qone; [|qZ_numerals; field; auto];
 replace (1/2 + 1/2) with Qone; [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:Zero<c+d);[ring_exact_Q Hdc|];
 apply Qmult_pos_Qdiv_Qle; trivial; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_R_unfolded_auxiliary_62: forall (a b c d:Q), d+c<0  -> 
                     (d+c)*((a+b)*(-1/2+(2+1)/2))<=(d+c)*((c+d)*(1/2+1/2))->
                    (a + b) / (c + d) <= 1.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (-1/2 + (2+1)/2) with Qone; [|qZ_numerals; field; auto];
 replace (1/2 + 1/2) with Qone; [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:c+d<Zero);[ring_exact_Q Hdc|];
 apply Qmult_neg_Qdiv_Qle; trivial; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_R_unfolded_auxiliary_6: forall (a b c d:Q), d+c<>0  -> 
                     (d+c)*((a+b)*(-1/2+(2+1)/2))<=(d+c)*((c+d)*(1/2+1/2))->
                    (a + b) / (c + d) <= 1.
Proof.
 intros a b c d Hdc;
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_R_unfolded_auxiliary_62
  | apply Incl_M_R_unfolded_auxiliary_61
  ]; assumption.
Qed.

Lemma Incl_M_R_unfolded_auxiliary_71: forall (a b c d:Q), 0<d+c -> 
                     (d+c)*((c+d)*(1 / 2 - 1 / 2))<=(d+c)*((a+b)*((2 + 1) / 2 - -1 / 2)) ->
                    0 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (1/2 - 1/2) with Zero; [|qZ_numerals; field; auto];
 replace ((2+1)/2 - -1/2) with (Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:Zero<c+d);[ring_exact_Q Hdc|];
 apply Qmult_resp_Qle_pos_l with 2; auto;
 rewrite Qdiv_Qmult_numerator_l; auto;
 apply Qmult_pos_Qle_Qdiv; trivial;
 ring_exact_Q H_mult.
Qed.

Lemma Incl_M_R_unfolded_auxiliary_72: forall (a b c d:Q), d+c<0 -> 
                     (d+c)*((c+d)*(1 / 2 - 1 / 2))<=(d+c)*((a+b)*((2 + 1) / 2 - -1 / 2)) ->
                    0 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (1/2 - 1/2) with Zero; [|qZ_numerals; field; auto];
 replace ((2+1)/2 - -1/2) with (Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:c+d<Zero);[ring_exact_Q Hdc|];
 apply Qmult_resp_Qle_pos_l with 2; auto;
 rewrite Qdiv_Qmult_numerator_l; auto;
 apply Qmult_neg_Qle_Qdiv; trivial;
 ring_exact_Q H_mult.
Qed.

Lemma Incl_M_R_unfolded_auxiliary_7: forall (a b c d:Q), d+c<>0 -> 
                     (d+c)*((c+d)*(1 / 2 - 1 / 2))<=(d+c)*((a+b)*((2 + 1) / 2 - -1 / 2)) ->
                    0 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc;
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_R_unfolded_auxiliary_72
  | apply Incl_M_R_unfolded_auxiliary_71
  ]; assumption.
Qed.

Lemma Incl_M_R_unfolded_auxiliary_81: forall (a b c d:Q), 0<d-c -> 
             (d-c)*((b-a)*(-1 / 2 + (2 + 1) / 2))<=(d-c)*((d-c)*(1 / 2 + 1 / 2)) ->
                 (b - a) / (d - c)<=1.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (-1/2 + (2+1)/2) with Qone; [|qZ_numerals; field; auto];
 replace (1/2 + 1/2) with Qone; [|qZ_numerals; field; auto];
 intros H_mult;
 apply Qmult_pos_Qdiv_Qle; trivial;
 ring_exact_Q H_mult.
Qed.

Lemma Incl_M_R_unfolded_auxiliary_82: forall (a b c d:Q), d-c<0 -> 
             (d-c)*((b-a)*(-1 / 2 + (2 + 1) / 2))<=(d-c)*((d-c)*(1 / 2 + 1 / 2)) ->
                 (b - a) / (d - c)<=1.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (-1/2 + (2+1)/2) with Qone; [|qZ_numerals; field; auto];
 replace (1/2 + 1/2) with Qone; [|qZ_numerals; field; auto];
 intros H_mult;
 apply Qmult_neg_Qdiv_Qle; trivial;
 ring_exact_Q H_mult.
Qed.

Lemma Incl_M_R_unfolded_auxiliary_8: forall (a b c d:Q), d-c<>0 -> 
             (d-c)*((b-a)*(-1 / 2 + (2 + 1) / 2))<=(d-c)*((d-c)*(1 / 2 + 1 / 2)) ->
                 (b - a) / (d - c)<=1.
Proof.
 intros a b c d Hdc;
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_R_unfolded_auxiliary_82
  | apply Incl_M_R_unfolded_auxiliary_81
  ]; assumption.
Qed.

Lemma Incl_M_M_unfolded_auxiliary_51: forall (a b c d:Q), 0 < d - c  -> 
             (d-c)*((d-c)*(0/1-1/1))<=(d-c)*((b-a)*((2+1)/1- 0/1))->
                 (-1)/3 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (0/1 - 1/1) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace ((2+1)/1 - 0/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 apply Qmult_Qdiv_pos_Qle; auto; 
 ring_exact_Q H_mult.
Qed.

Lemma Incl_M_M_unfolded_auxiliary_52: forall (a b c d:Q), d - c<0  -> 
             (d-c)*((d-c)*(0/1-1/1))<=(d-c)*((b-a)*((2+1)/1- 0/1))->
                 (-1)/3 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (0/1 - 1/1) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace ((2+1)/1 - 0/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 apply Qmult_Qdiv_pos_neg_Qle; auto;
 ring_exact_Q H_mult.
Qed.


Lemma Incl_M_M_unfolded_auxiliary_5: forall (a b c d:Q), d - c<>0  -> 
             (d-c)*((d-c)*(0/1-1/1))<=(d-c)*((b-a)*((2+1)/1- 0/1))->
                 (-1)/3 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc;
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_M_unfolded_auxiliary_52
  | apply Incl_M_M_unfolded_auxiliary_51
  ]; assumption.
Qed.


Lemma Incl_M_M_unfolded_auxiliary_61: forall (a b c d:Q), 0 < d + c  -> 
             (d+c)*((a+b)*(0 / 1 + (2 + 1) / 1))<=(d+c)*((c+d)*(1 / 1 + 0 / 1))->
                    (a + b) / (c + d) <= 1/3.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (1/1 + 0/1) with Qone; [|qZ_numerals; field; auto];
 replace (0/1 + (2+1)/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:Zero<c+d);[ring_exact_Q Hdc|];
 apply Qmult_Qdiv_pos_Qle; auto; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_M_unfolded_auxiliary_62: forall (a b c d:Q), d + c<0  -> 
             (d+c)*((a+b)*(0 / 1 + (2 + 1) / 1))<=(d+c)*((c+d)*(1 / 1 + 0 / 1))->
                    (a + b) / (c + d) <= 1/3.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (1/1 + 0/1) with Qone; [|qZ_numerals; field; auto];
 replace (0/1 + (2+1)/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:c+d<Zero);[ring_exact_Q Hdc|].
 apply Qmult_Qdiv_neg_pos_Qle; auto; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_M_unfolded_auxiliary_6: forall (a b c d:Q), d + c<>0  -> 
             (d+c)*((a+b)*(0 / 1 + (2 + 1) / 1))<=(d+c)*((c+d)*(1 / 1 + 0 / 1))->
                    (a + b) / (c + d) <= 1/3.
Proof.
 intros a b c d Hdc;
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_M_unfolded_auxiliary_62
  | apply Incl_M_M_unfolded_auxiliary_61
  ]; assumption.
Qed.


Lemma Incl_M_M_unfolded_auxiliary_71: forall (a b c d:Q), 0<d+c -> 
                     (d+c)*((c+d)*(0 / 1 - 1 / 1))<=(d+c)*((a+b)*((2 + 1) / 1 - 0 / 1)) ->
                    (-1)/3 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (0/1 - 1/1) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace ((2+1)/1 - 0/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:Zero<c+d);[ring_exact_Q Hdc|];
 apply Qmult_Qdiv_pos_Qle; auto; ring_exact_Q H_mult. 
Qed.


Lemma Incl_M_M_unfolded_auxiliary_72: forall (a b c d:Q), d+c<0 -> 
                     (d+c)*((c+d)*(0 / 1 - 1 / 1))<=(d+c)*((a+b)*((2 + 1) / 1 - 0 / 1)) ->
                    (-1)/3 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (0/1 - 1/1) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace ((2+1)/1 - 0/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 assert (Hcd:c+d<Zero);[ring_exact_Q Hdc|];
 apply Qmult_Qdiv_pos_neg_Qle; auto; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_M_unfolded_auxiliary_7: forall (a b c d:Q), d+c<>0 -> 
                     (d+c)*((c+d)*(0 / 1 - 1 / 1))<=(d+c)*((a+b)*((2 + 1) / 1 - 0 / 1)) ->
                    (-1)/3 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc;
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_M_unfolded_auxiliary_72
  | apply Incl_M_M_unfolded_auxiliary_71
  ]; assumption.
Qed.


Lemma Incl_M_M_unfolded_auxiliary_81: forall (a b c d:Q), 0<d-c -> 
             (d-c)*((b-a)*(0 / 1 + (2 + 1) / 1))<=(d-c)*((d-c)*(1 / 1 + 0 / 1)) ->
                 (b - a) / (d - c)<=1/3.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_pos_l _ _ _ Hdc H0); clear H0;
 replace (1/1 + 0/1) with Qone; [|qZ_numerals; field; auto];
 replace (0/1 + (2+1)/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 apply Qmult_Qdiv_pos_Qle; auto; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_M_unfolded_auxiliary_82: forall (a b c d:Q), d-c<0 -> 
             (d-c)*((b-a)*(0 / 1 + (2 + 1) / 1))<=(d-c)*((d-c)*(1 / 1 + 0 / 1)) ->
                 (b - a) / (d - c)<=1/3.
Proof.
 intros a b c d Hdc H0;
 generalize (Qmult_resp_Qle_neg_l _ _ _ Hdc H0); clear H0;
 replace (1/1 + 0/1) with Qone; [|qZ_numerals; field; auto];
 replace (0/1 + (2+1)/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 intros H_mult;
 apply Qmult_Qdiv_neg_pos_Qle; auto; ring_exact_Q H_mult. 
Qed.

Lemma Incl_M_M_unfolded_auxiliary_8: forall (a b c d:Q), d-c<>0 -> 
             (d-c)*((b-a)*(0 / 1 + (2 + 1) / 1))<=(d-c)*((d-c)*(1 / 1 + 0 / 1)) ->
                 (b - a) / (d - c)<=1/3.
Proof.
 intros a b c d Hdc;
 destruct (not_Qeq_inf _ _ Hdc);
  [ apply Incl_M_M_unfolded_auxiliary_82
  | apply Incl_M_M_unfolded_auxiliary_81
  ]; assumption.
Qed.

Lemma Incl_M_L_unfolded:forall mu r, (-1<=r<=1)%R->Incl_M mu LL -> (-1<=as_Moebius mu r<=0)%R. 
Proof.
 intros ((a,b),(c,d)) r H_r; unfold as_Moebius, Incl_M, map_digits, fst, snd;
 intros [H_vanish [H1 [H2 [H3 H4]]]];
 generalize (Bounded_M_d_minus_c_nonzero _ _ _ _ H_vanish); intro H_cd1;
 generalize (Bounded_M_c_plus_d_nonzero _ _ _ _ H_vanish); intro H_cd2;
 assert (Hdc:d + c <> Zero);[ring_exact_Q H_cd2|].

 destruct (Qle_dec_weak Zero (a*d-b*c)) as [H_det|H_det];
 split.
  apply Rle_trans with ((b-a)/(d-c))%R.
   rationalify_R; apply Incl_M_L_unfolded_auxiliary_5; trivial. 
   stepl ((a*(-1)+b)/(c*(-1)+d))%R.
    apply (det_nonneg_nondecreasing _ _ _ _ (-1)%R r H_vanish H_det min_one_is_in_base_interval H_r (proj1 H_r)).
    apply (f_equal2 Rdiv); ring...
  apply Rle_trans with ((a+b)/(c+d))%R.
   stepr ((a*1+b)/(c*1+d))%R.
    apply (det_nonneg_nondecreasing _ _ _ _ r (1)%R H_vanish H_det H_r one_is_in_base_interval (proj2 H_r)).
    apply (f_equal2 Rdiv); ring.
   rationalify_R; apply Incl_M_L_unfolded_auxiliary_6; trivial...  
  apply Rle_trans with ((a+b)/(c+d))%R.
   rationalify_R; apply Incl_M_L_unfolded_auxiliary_7; trivial. 
   stepl ((a*1+b)/(c*1+d))%R.
    apply (det_nonpos_nonincreasing _ _ _ _ r (1)%R H_vanish H_det H_r one_is_in_base_interval (proj2 H_r)).
    apply (f_equal2 Rdiv); ring...
  apply Rle_trans with ((b-a)/(d-c))%R.
   stepr ((a*(-1)+b)/(c*(-1)+d))%R.
    apply (det_nonpos_nonincreasing _ _ _ _ (-1)%R r H_vanish H_det min_one_is_in_base_interval H_r (proj1 H_r)).
    apply (f_equal2 Rdiv); ring.
   rationalify_R; apply Incl_M_L_unfolded_auxiliary_8; trivial... 
Qed.

Lemma Incl_M_R_unfolded:forall mu r, (-1<=r<=1)%R->Incl_M mu RR -> (0<=as_Moebius mu r<=1)%R. 
Proof.
 intros ((a,b),(c,d)) r H_r; unfold as_Moebius, Incl_M, map_digits, fst, snd;
 intros [H_vanish [H1 [H2 [H3 H4]]]];
 generalize (Bounded_M_d_minus_c_nonzero _ _ _ _ H_vanish); intro H_cd1;
 generalize (Bounded_M_c_plus_d_nonzero _ _ _ _ H_vanish); intro H_cd2;
 assert (Hdc:d + c <> Zero);[ring_exact_Q H_cd2|].

 destruct (Qle_dec_weak Zero (a*d-b*c)) as [H_det|H_det];
 split.
  apply Rle_trans with ((b-a)/(d-c))%R.
   rationalify_R; apply Incl_M_R_unfolded_auxiliary_5; trivial. 
   stepl ((a*(-1)+b)/(c*(-1)+d))%R.
    apply (det_nonneg_nondecreasing _ _ _ _ (-1)%R r H_vanish H_det min_one_is_in_base_interval H_r (proj1 H_r)).
    apply (f_equal2 Rdiv); ring...
  apply Rle_trans with ((a+b)/(c+d))%R.
   stepr ((a*1+b)/(c*1+d))%R.
    apply (det_nonneg_nondecreasing _ _ _ _ r (1)%R H_vanish H_det H_r one_is_in_base_interval (proj2 H_r)).
    apply (f_equal2 Rdiv); ring.
   rationalify_R; apply Incl_M_R_unfolded_auxiliary_6; trivial...
  apply Rle_trans with ((a+b)/(c+d))%R.
   rationalify_R; apply Incl_M_R_unfolded_auxiliary_7; trivial. 
   stepl ((a*1+b)/(c*1+d))%R.
    apply (det_nonpos_nonincreasing _ _ _ _ r (1)%R H_vanish H_det H_r one_is_in_base_interval (proj2 H_r)).
    apply (f_equal2 Rdiv); ring...
  apply Rle_trans with ((b-a)/(d-c))%R.
   stepr ((a*(-1)+b)/(c*(-1)+d))%R.
    apply (det_nonpos_nonincreasing _ _ _ _ (-1)%R r H_vanish H_det min_one_is_in_base_interval H_r (proj1 H_r)).
    apply (f_equal2 Rdiv); ring.
   rationalify_R; apply Incl_M_R_unfolded_auxiliary_8; trivial. 
Qed.

Lemma Incl_M_M_unfolded:forall mu r, (-1<=r<=1)%R->Incl_M mu MM -> (-1/3<=as_Moebius mu r<=1/3)%R. 
Proof.
 intros ((a,b),(c,d)) r H_r; unfold as_Moebius, Incl_M, map_digits, fst, snd;
 intros [H_vanish [H1 [H2 [H3 H4]]]];
 generalize (Bounded_M_d_minus_c_nonzero _ _ _ _ H_vanish); intro H_cd1;
 generalize (Bounded_M_c_plus_d_nonzero _ _ _ _ H_vanish); intro H_cd2;
 assert (Hdc:d + c <> Zero);[ring_exact_Q H_cd2|].

 destruct (Qle_dec_weak Zero (a*d-b*c)) as [H_det|H_det];
 split.
  apply Rle_trans with ((b-a)/(d-c))%R.
   rationalify_R; apply Incl_M_M_unfolded_auxiliary_5; trivial. 
   stepl ((a*(-1)+b)/(c*(-1)+d))%R.
    apply (det_nonneg_nondecreasing _ _ _ _ (-1)%R r H_vanish H_det min_one_is_in_base_interval H_r (proj1 H_r)).
    apply (f_equal2 Rdiv); ring...
  apply Rle_trans with ((a+b)/(c+d))%R.
   stepr ((a*1+b)/(c*1+d))%R.
    apply (det_nonneg_nondecreasing _ _ _ _ r (1)%R H_vanish H_det H_r one_is_in_base_interval (proj2 H_r)).
    apply (f_equal2 Rdiv); ring.
   rationalify_R; apply Incl_M_M_unfolded_auxiliary_6; trivial. 
  apply Rle_trans with ((a+b)/(c+d))%R.
   rationalify_R; apply Incl_M_M_unfolded_auxiliary_7; trivial. 
   stepl ((a*1+b)/(c*1+d))%R.
    apply (det_nonpos_nonincreasing _ _ _ _ r (1)%R H_vanish H_det H_r one_is_in_base_interval (proj2 H_r)).
    apply (f_equal2 Rdiv); ring...
  apply Rle_trans with ((b-a)/(d-c))%R.
   stepr ((a*(-1)+b)/(c*(-1)+d))%R.
    apply (det_nonpos_nonincreasing _ _ _ _ (-1)%R r H_vanish H_det min_one_is_in_base_interval H_r (proj1 H_r)).
    apply (f_equal2 Rdiv); ring.
   rationalify_R; apply Incl_M_M_unfolded_auxiliary_8; trivial...
Qed.

Lemma  Incl_M_L_folded: forall mu, (forall r, (-1 <= r <= 1)%R -> denom_nonvanishing_M mu r) -> (*Is_refining_M mu ->*) 
     (forall r, (-1 <= r <= 1)%R -> (-1 <= as_Moebius mu r <= 0)%R) -> Incl_M mu LL.
Proof.
 intros ((a,b),(c,d)) H_denom H_mu.
 unfold denom_nonvanishing_M in H_denom; simpl in H_denom.
 unfold as_Moebius in H_mu; simpl in H_mu.
 assert (H_dcmin:d-c <>Zero);
 [apply Q_to_R_Qneq; realify_Q; stepl (c*(-1)+d)%R; [|ring]; apply (H_denom (-1)%R min_one_is_in_base_interval)|].
 assert (H_dc:d+c <>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*1+d)%R; [|ring]; apply (H_denom (1)%R one_is_in_base_interval)|].
 assert (Hd: d<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*0+d)%R; [|ring]; apply H_denom; split; Fourier.fourier|].
 unfold Incl_M, Bounded_M, map_digits, fst, snd; qZ_numerals; repeat split. 
  (* Bounded_M *)
  clear H_mu.
  destruct (Q_zerop c) as [Hc|Hc].
   subst c; destruct (not_Qeq_inf _ _ Hd) as [Hd_sg|Hd_sg].
    right; auto.
    left; auto.
   destruct (Q_le_lt_dec (-Qone) (- (d/c))) as [Hdc_min|Hdc_min].
    destruct (Q_le_lt_dec (- (d/c)) (Qone)) as [Hdc_|Hdc_].
     apply False_ind; apply (H_denom (-(d/c))%R);
      [ revert Hc; realify_Q_assumptions; intros _ _ _ H1 H2 H3; revert H2 H1; realify_Q_goal; tauto
      | try field; rationalify_R_goal; apply Q_to_R_not_eq; assumption
      ]...
     destruct (not_Qeq_inf _ _ Hc) as [Hc_sg|Hc_sg].
      (* c<0 *)
      left; split.
       apply Qlt_Qdiv_denom_neg_neg with c; trivial; 
       stepl (Qone-(-(d/c))); [| field; auto];  apply Qlt_Qminus_Zero_neg; assumption. 
       apply Qlt_Qdiv_denom_neg_neg with c; trivial;
       stepl ((-Qone)-(-(d/c))); [| field; auto]; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with Qone; auto.
      (* 0<c *)
      right; split.
       apply Qlt_Qdiv_denom_pos_neg with c; trivial; 
       stepl (Qone-(-(d/c))); [| field; auto];  apply Qlt_Qminus_Zero_neg; assumption. 
       apply Qlt_Qdiv_denom_pos_neg with c; trivial;
       stepl ((-Qone)-(-(d/c))); [| field; auto]; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with Qone; auto...
     destruct (not_Qeq_inf _ _ Hc) as [Hc_sg|Hc_sg].
      (* c<0 *)
      right; split.
       apply Qlt_pos_Qopp; apply Qlt_Qdiv_denom_neg_neg with c; trivial;
       stepl ((-(d/c))-(Qone)); [| field; auto];  apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with (-Qone); auto.
       apply Qlt_pos_Qopp; apply Qlt_Qdiv_denom_neg_neg with c; trivial;
       stepl ((-(d/c))-(-Qone)); [| field; auto]; apply Qlt_Qminus_Zero_neg; assumption. 
      (* 0<c *)
      left; split.
       apply Qlt_neg_Qopp; apply Qlt_Qdiv_denom_pos_neg with c; trivial.
       stepl ((-(d/c))-(Qone)); [| field; auto]; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with (-Qone); auto.
       apply Qlt_neg_Qopp; apply Qlt_Qdiv_denom_pos_neg with c; trivial;
       stepl ((-(d/c))-(-Qone)); [| field; auto]; apply Qlt_Qminus_Zero_neg; assumption. 
  (* Refining 1 *)
  destruct (not_Qeq_inf _ _ H_dcmin) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_minsig.
   (* d-c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite Rmult_comm; apply Rdiv_Rmult_pos_neg_Rle'; auto; try Fourier.fourier;
   stepl (-1)%R; [|field]; stepr ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj1 (H_mu (-1)%R min_one_is_in_base_interval)).
   (* 0<d-c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite (Rmult_comm (b+ -a)%R); apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepl (-1)%R; [|field]; stepr ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj1 (H_mu (-1)%R min_one_is_in_base_interval)).
  (* Refining 2 *)
  destruct (not_Qeq_inf _ _ H_dcmin) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_minsig.
   (* d-c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite (Rmult_comm (b+ -a)%R); apply Rdiv_Rmult_neg_pos_Rle'; auto; try Fourier.fourier;
   stepr R0; [|field]; stepl ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj2 (H_mu (-1)%R min_one_is_in_base_interval)).
   (* 0<d-c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite Rmult_comm; apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepr R0; [|field]; stepl ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj2 (H_mu (-1)%R min_one_is_in_base_interval)).
  (* Refining 3 *)
  destruct (not_Qeq_inf _ _ H_dc) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_sig.
   (* d+c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_pos_neg_Rle'; auto; try Fourier.fourier;
   stepl (-1)%R; [|field]; stepr ((a * 1 + b) / (c * 1 + d))%R; [|field; auto; stepl (d+c)%R; trivial; ring];
   exact (proj1 (H_mu (1)%R one_is_in_base_interval)).
   (* 0<d+c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepl (-1)%R; [|field]; stepr ((a * 1 + b) / (c * 1 + d))%R; [|field; auto;stepl (d+c)%R; trivial; ring];
   exact (proj1 (H_mu (1)%R one_is_in_base_interval)).
  (* Refining 4 *)
  destruct (not_Qeq_inf _ _ H_dc) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_sig.
   (* d+c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_neg_pos_Rle'; auto; try Fourier.fourier.
   stepr R0; [|field]; stepl ((a * 1 + b) / (c * 1 + d))%R; [|field; auto; stepl (d+c)%R; trivial; ring];
   exact (proj2 (H_mu (1)%R one_is_in_base_interval)).
   (* 0<d+c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepr R0; [|field]; stepl ((a * 1 + b) / (c * 1 + d))%R; [|field; auto;stepl (d+c)%R; trivial; ring];
   exact (proj2 (H_mu (1)%R one_is_in_base_interval)).
Qed.

Lemma  Incl_M_R_folded: forall mu, (forall r, (-1 <= r <= 1)%R -> denom_nonvanishing_M mu r) ->
     (forall r, (-1 <= r <= 1)%R -> (0 <= as_Moebius mu r <= 1)%R) -> Incl_M mu RR.
Proof.
 intros ((a,b),(c,d)) H_denom H_mu.
 unfold denom_nonvanishing_M in H_denom; simpl in H_denom.
 unfold as_Moebius in H_mu; simpl in H_mu.
 assert (H_dcmin:d-c <>Zero);
 [apply Q_to_R_Qneq; realify_Q; stepl (c*(-1)+d)%R; [|ring]; apply (H_denom (-1)%R min_one_is_in_base_interval)|].
 assert (H_dc:d+c <>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*1+d)%R; [|ring]; apply (H_denom (1)%R one_is_in_base_interval)|].
 assert (Hd: d<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*0+d)%R; [|ring]; apply H_denom; split; Fourier.fourier|].
 unfold Incl_M, Bounded_M, map_digits, fst, snd; qZ_numerals; repeat split. 
  (* Bounded_M *)
  clear H_mu.
  destruct (Q_zerop c) as [Hc|Hc].
   subst c; destruct (not_Qeq_inf _ _ Hd) as [Hd_sg|Hd_sg].
    right; auto.
    left; auto.
   destruct (Q_le_lt_dec (-Qone) (- (d/c))) as [Hdc_min|Hdc_min].
    destruct (Q_le_lt_dec (- (d/c)) (Qone)) as [Hdc_|Hdc_].
     apply False_ind; apply (H_denom (-(d/c))%R);
      [ revert Hc; realify_Q_assumptions; intros _ _ _ H1 H2 H3; revert H2 H1; realify_Q_goal; tauto
      | try field; rationalify_R_goal; apply Q_to_R_not_eq; assumption
      ]...
     destruct (not_Qeq_inf _ _ Hc) as [Hc_sg|Hc_sg].
      (* c<0 *)
      left; split.
       apply Qlt_Qdiv_denom_neg_neg with c; trivial; 
       stepl (Qone-(-(d/c))); [| field; auto];  apply Qlt_Qminus_Zero_neg; assumption. 
       apply Qlt_Qdiv_denom_neg_neg with c; trivial;
       stepl ((-Qone)-(-(d/c))); [| field; auto]; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with Qone; auto.
      (* 0<c *)
      right; split.
       apply Qlt_Qdiv_denom_pos_neg with c; trivial; 
       stepl (Qone-(-(d/c))); [| field; auto];  apply Qlt_Qminus_Zero_neg; assumption. 
       apply Qlt_Qdiv_denom_pos_neg with c; trivial;
       stepl ((-Qone)-(-(d/c))); [| field; auto]; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with Qone; auto...
     destruct (not_Qeq_inf _ _ Hc) as [Hc_sg|Hc_sg].
      (* c<0 *)
      right; split.
       apply Qlt_pos_Qopp; apply Qlt_Qdiv_denom_neg_neg with c; trivial;
       stepl ((-(d/c))-(Qone)); [| field; auto];  apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with (-Qone); auto.
       apply Qlt_pos_Qopp; apply Qlt_Qdiv_denom_neg_neg with c; trivial;
       stepl ((-(d/c))-(-Qone)); [| field; auto]; apply Qlt_Qminus_Zero_neg; assumption. 
      (* 0<c *)
      left; split.
       apply Qlt_neg_Qopp; apply Qlt_Qdiv_denom_pos_neg with c; trivial.
       stepl ((-(d/c))-(Qone)); [| field; auto]; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with (-Qone); auto.
       apply Qlt_neg_Qopp; apply Qlt_Qdiv_denom_pos_neg with c; trivial;
       stepl ((-(d/c))-(-Qone)); [| field; auto]; apply Qlt_Qminus_Zero_neg; assumption. 
  (* Refining 1 *)
  destruct (not_Qeq_inf _ _ H_dcmin) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_minsig.
   (* d-c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite Rmult_comm; apply Rdiv_Rmult_pos_neg_Rle'; auto; try Fourier.fourier;
   stepl R0; [|field]; stepr ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj1 (H_mu (-1)%R min_one_is_in_base_interval)).
   (* 0<d-c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite (Rmult_comm (b+ -a)%R); apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepl R0; [|field]; stepr ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj1 (H_mu (-1)%R min_one_is_in_base_interval)).
  (* Refining 2 *)
  destruct (not_Qeq_inf _ _ H_dcmin) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_minsig.
   (* d-c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite (Rmult_comm (b+ -a)%R); apply Rdiv_Rmult_neg_pos_Rle'; auto; try Fourier.fourier;
   stepr R1; [|field]; stepl ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj2 (H_mu (-1)%R min_one_is_in_base_interval)).
   (* 0<d-c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite Rmult_comm; apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepr R1; [|field]; stepl ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj2 (H_mu (-1)%R min_one_is_in_base_interval)).
  (* Refining 3 *)
  destruct (not_Qeq_inf _ _ H_dc) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_sig.
   (* d+c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_pos_neg_Rle'; auto; try Fourier.fourier;
   stepl R0; [|field]; stepr ((a * 1 + b) / (c * 1 + d))%R; [|field; auto; stepl (d+c)%R; trivial; ring];
   exact (proj1 (H_mu (1)%R one_is_in_base_interval)).
   (* 0<d+c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepl R0; [|field]; stepr ((a * 1 + b) / (c * 1 + d))%R; [|field; auto;stepl (d+c)%R; trivial; ring];
   exact (proj1 (H_mu (1)%R one_is_in_base_interval)).
  (* Refining 4 *)
  destruct (not_Qeq_inf _ _ H_dc) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_sig.
   (* d+c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_neg_pos_Rle'; auto; try Fourier.fourier.
   stepr R1; [|field]; stepl ((a * 1 + b) / (c * 1 + d))%R; [|field; auto; stepl (d+c)%R; trivial; ring];
   exact (proj2 (H_mu (1)%R one_is_in_base_interval)).
   (* 0<d+c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepr R1; [|field]; stepl ((a * 1 + b) / (c * 1 + d))%R; [|field; auto;stepl (d+c)%R; trivial; ring];
   exact (proj2 (H_mu (1)%R one_is_in_base_interval)).
Qed.


Lemma  Incl_M_M_folded: forall mu, (forall r, (-1 <= r <= 1)%R -> denom_nonvanishing_M mu r) ->
     (forall r, (-1 <= r <= 1)%R -> ((-1/3) <= as_Moebius mu r <= 1/3)%R) -> Incl_M mu MM.
Proof.
 intros ((a,b),(c,d)) H_denom H_mu.
 unfold denom_nonvanishing_M in H_denom; simpl in H_denom.
 unfold as_Moebius in H_mu; simpl in H_mu.
 assert (H_dcmin:d-c <>Zero);
 [apply Q_to_R_Qneq; realify_Q; stepl (c*(-1)+d)%R; [|ring]; apply (H_denom (-1)%R min_one_is_in_base_interval)|].
 assert (H_dc:d+c <>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*1+d)%R; [|ring]; apply (H_denom (1)%R one_is_in_base_interval)|].
 assert (Hd: d<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*0+d)%R; [|ring]; apply H_denom; split; Fourier.fourier|].
 unfold Incl_M, Bounded_M, map_digits, fst, snd; qZ_numerals; repeat split. 
  (* Bounded_M *)
  clear H_mu.
  destruct (Q_zerop c) as [Hc|Hc].
   subst c; destruct (not_Qeq_inf _ _ Hd) as [Hd_sg|Hd_sg].
    right; split; stepl d; trivial; ring.    
    left; split; stepr d; trivial; ring.
   destruct (Q_le_lt_dec (-Qone) (- (d/c))) as [Hdc_min|Hdc_min].
    destruct (Q_le_lt_dec (- (d/c)) (Qone)) as [Hdc_|Hdc_].
     apply False_ind; apply (H_denom (-(d/c))%R);
      [ revert Hc; realify_Q_assumptions; intros _ _ _ H1 H2 H3; revert H2 H1; realify_Q_goal; tauto
      | try field; rationalify_R_goal; apply Q_to_R_not_eq; assumption
      ]...
     destruct (not_Qeq_inf _ _ Hc) as [Hc_sg|Hc_sg].
      (* c<0 *)
      left; split.
       apply Qlt_Qdiv_denom_neg_neg with c; trivial; 
       stepl (Qone-(-(d/c))); [| field; auto];  apply Qlt_Qminus_Zero_neg; assumption. 
       apply Qlt_Qdiv_denom_neg_neg with c; trivial;
       stepl ((-Qone)-(-(d/c))); [| field; auto]; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with Qone; auto.
      (* 0<c *)
      right; split.
       apply Qlt_Qdiv_denom_pos_neg with c; trivial; 
       stepl (Qone-(-(d/c))); [| field; auto];  apply Qlt_Qminus_Zero_neg; assumption. 
       apply Qlt_Qdiv_denom_pos_neg with c; trivial;
       stepl ((-Qone)-(-(d/c))); [| field; auto]; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with Qone; auto...
     destruct (not_Qeq_inf _ _ Hc) as [Hc_sg|Hc_sg].
      (* c<0 *)
      right; split.
       apply Qlt_pos_Qopp; apply Qlt_Qdiv_denom_neg_neg with c; trivial;
       stepl ((-(d/c))-(Qone)); [| field; auto];  apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with (-Qone); auto.
       apply Qlt_pos_Qopp; apply Qlt_Qdiv_denom_neg_neg with c; trivial;
       stepl ((-(d/c))-(-Qone)); [| field; auto]; apply Qlt_Qminus_Zero_neg; assumption. 
      (* 0<c *)
      left; split.
       apply Qlt_neg_Qopp; apply Qlt_Qdiv_denom_pos_neg with c; trivial.
       stepl ((-(d/c))-(Qone)); [| field; auto]; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with (-Qone); auto.
       apply Qlt_neg_Qopp; apply Qlt_Qdiv_denom_pos_neg with c; trivial;
       stepl ((-(d/c))-(-Qone)); [| field; auto]; apply Qlt_Qminus_Zero_neg; assumption. 
  (* Refining 1 *)
  destruct (not_Qeq_inf _ _ H_dcmin) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_minsig.
   (* d-c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite Rmult_comm; apply Rdiv_Rmult_pos_neg_Rle'; auto; try Fourier.fourier;
   stepl ((-1)/3)%R; [|field]; stepr ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj1 (H_mu (-1)%R min_one_is_in_base_interval)).
   (* 0<d-c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite (Rmult_comm (b+ -a)%R); apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepl ((-1)/3)%R; [|field]; stepr ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj1 (H_mu (-1)%R min_one_is_in_base_interval)).
  (* Refining 2 *)
  destruct (not_Qeq_inf _ _ H_dcmin) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_minsig.
   (* d-c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite (Rmult_comm (b+ -a)%R); apply Rdiv_Rmult_neg_pos_Rle'; auto; try Fourier.fourier;
   stepr (1/3)%R; [|field]; stepl ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj2 (H_mu (-1)%R min_one_is_in_base_interval)).
   (* 0<d-c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite Rmult_comm; apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepr (1/3)%R; [|field]; stepl ((a * (-1) + b) / (c * (-1) + d))%R; [|field; auto];
   exact (proj2 (H_mu (-1)%R min_one_is_in_base_interval)).
  (* Refining 3 *)
  destruct (not_Qeq_inf _ _ H_dc) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_sig.
   (* d+c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_pos_neg_Rle'; auto; try Fourier.fourier;
   stepl ((-1)/3)%R; [|field]; stepr ((a * 1 + b) / (c * 1 + d))%R; [|field; auto; stepl (d+c)%R; trivial; ring];
   exact (proj1 (H_mu (1)%R one_is_in_base_interval)).
   (* 0<d+c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepl ((-1)/3)%R; [|field]; stepr ((a * 1 + b) / (c * 1 + d))%R; [|field; auto;stepl (d+c)%R; trivial; ring];
   exact (proj1 (H_mu (1)%R one_is_in_base_interval)).
  (* Refining 4 *)
  destruct (not_Qeq_inf _ _ H_dc) as [H_|H_]; apply Q_to_R_Qle; realify_Q; auto; intros H_dcmin H_dc Hd H_dc_sig.
   (* d+c < 0 *) 
   apply Rmult_le_compat_neg_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_neg_pos_Rle'; auto; try Fourier.fourier.
   stepr (1/3)%R; [|field]; stepl ((a * 1 + b) / (c * 1 + d))%R; [|field; auto; stepl (d+c)%R; trivial; ring];
   exact (proj2 (H_mu (1)%R one_is_in_base_interval)).
   (* 0<d+c *) 
   apply Rmult_le_compat_l; [Fourier.fourier|];
   rewrite (Rmult_comm (a+b)%R); apply Rdiv_Rmult_pos_pos_Rle';  auto; try Fourier.fourier;
   stepr (1/3)%R; [|field]; stepl ((a * 1 + b) / (c * 1 + d))%R; [|field; auto;stepl (d+c)%R; trivial; ring];
   exact (proj2 (H_mu (1)%R one_is_in_base_interval)).
Qed.

Close Scope Q_scope.
Close Scope Z_scope.
