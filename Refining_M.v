(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)

Require Import digits.
Require Import R_addenda.
Require Import Fourier_solvable_ineqs.
Require Import Fourier.
Require Import Bounded_M.

Open Scope Q_scope.

Lemma Bounded_M_auxiliary_5: forall c d r, Zero <= d + c -> Zero <= d - c ->(-1<=r<=1)%R->(0<=c*r+d)%R.
Proof.
 intros c d r H1 H2 Hr.
 (* TP : Zero<=d *)
 assert (Hd: Zero<=d);
 [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepl Zero; auto; stepr ((d+c)+(d-c)); auto; ring|].

 destruct (Qtrichotomy_inf Zero c) as [[Hc|Hc]|Hc]; realify_Q.
   intros; apply Bounded_M_pos_auxiliary_3; trivial.
   intros Hc _ _ Hd; rewrite <- Hc; stepr d; trivial; ring.
   intros; apply Bounded_M_pos_auxiliary_4; trivial.
Qed.

Lemma Bounded_M_auxiliary_6: forall c d r, d + c<=Zero -> d - c<=Zero ->(-1<=r<=1)%R->(c*r+d<=0)%R.
Proof.
 intros c d r H1 H2 Hr.
 (* TP : d<=Zero *)
 assert (Hd: d<=Zero);
 [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepr Zero; auto; stepl ((d+c)+(d-c)); auto; ring|].

 destruct (Qtrichotomy_inf Zero c) as [[Hc|Hc]|Hc]; realify_Q.
   intros; apply Bounded_M_neg_auxiliary_3; trivial.
   intros Hc _ _ Hd; rewrite <- Hc; stepl d; trivial; ring.
   intros; apply Bounded_M_neg_auxiliary_4; trivial.
Qed.


Lemma Is_refining_M_auxiliary_1: forall (a b c d:Q), Zero <= a + b + c + d -> Zero <= a - b - c + d -> 
                                                     Zero <= - a - b + c + d -> Zero <= - a + b - c + d -> 
         Zero<=d/\Zero<=d-c/\Zero<=d+c/\Zero<=d-b/\Zero<=d+b/\Zero<=d-a/\Zero<=d+a.
Proof.
 let 
 t_local:= apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepl Zero; auto
 in
 ( intros a b c d H1 H2 H3 H4; repeat split;
 [ apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone+Qone); auto; stepl Zero; auto; 
   stepr ((a + b + c + d)+(- a - b + c + d)+(a - b - c + d)+(- a + b - c + d))
 | t_local; stepr ((a - b - c + d)+(- a + b - c + d))
 | t_local; stepr ((a + b + c + d)+(- a - b + c + d))
 | t_local; stepr ((a - b - c + d)+(- a - b + c + d))
 | t_local; stepr ((a + b + c + d)+(- a + b - c + d))
 | t_local; stepr ((- a - b + c + d)+(- a + b - c + d))
 | t_local; stepr ((a + b + c + d)+(a - b - c + d))
 ]; 
 auto; ring).
Qed.

Lemma Is_refining_M_auxiliary_2: forall (a b c d:Q), a + b + c + d <= Zero -> a - b - c + d <= Zero -> 
                                                     - a - b + c + d <= Zero -> - a + b - c + d <= Zero -> 
                 d<=Zero/\d-c<=Zero/\d+c<=Zero/\d-b<=Zero/\d+b<=Zero/\d-a<=Zero/\d+a<=Zero.
Proof.
 let 
 t_local:= apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepr Zero; auto
 in
 ( intros a b c d H1 H2 H3 H4; repeat split;
 [ apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone+Qone); auto; stepr Zero; auto; 
   stepl ((a + b + c + d)+(- a - b + c + d)+(a - b - c + d)+(- a + b - c + d))
 | t_local; stepl ((a - b - c + d)+(- a + b - c + d))
 | t_local; stepl ((a + b + c + d)+(- a - b + c + d))
 | t_local; stepl ((a - b - c + d)+(- a - b + c + d))
 | t_local; stepl ((a + b + c + d)+(- a + b - c + d))
 | t_local; stepl ((- a - b + c + d)+(- a + b - c + d))
 | t_local; stepl ((a + b + c + d)+(a - b - c + d))
 ]; 
 auto; ring).
Qed.


Lemma Is_refining_M_d_minusplus_c_sign_dec: forall a b c d, Is_refining_M ((a,b),(c,d))-> 
              (Qle Zero (Qplus (Qplus (Qplus a b) c) d) /\ Qle Zero (Qplus (Qminus (Qminus a b) c) d) /\
               Qle Zero (Qplus (Qplus (Qminus (Qopp a) b) c) d) /\ Qle Zero (Qplus (Qminus (Qplus (Qopp a) b) c) d) /\ 
               Qlt Zero (Qminus d c)/\Qlt Zero (Qplus d c)/\Qlt Zero d) \/
              (Qle (Qplus (Qplus (Qplus a b) c) d) Zero /\ Qle (Qplus (Qminus (Qminus a b) c) d) Zero /\
	       Qle (Qplus (Qplus (Qminus (Qopp a) b) c) d) Zero /\ Qle (Qplus (Qminus (Qplus (Qopp a) b) c) d) Zero /\
               Qlt (Qminus d c) Zero/\Qlt (Qplus d c) Zero/\Qlt d Zero).
Proof.
 intros a b c d [[[H0 H0']|[H0 H0']] [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]]; unfold fst, snd in H0, H0', H1, H2, H3, H4;
 first [generalize (Bounded_M_auxiliary_1 _ _ H0 H0')|generalize (Bounded_M_auxiliary_2 _ _ H0 H0')] ;intros Hd; 
 tauto ||
 first [decompose record (Is_refining_M_auxiliary_1 _ _ _ _ H1 H2 H3 H4)
       |decompose record (Is_refining_M_auxiliary_2 _ _ _ _ H1 H2 H3 H4)]; contradiction.
Qed.

Close Scope Q_scope.

Lemma Is_refining_M_denom_nonvanishing_M:forall mu r, Is_refining_M mu -> ((-1)<=r<=1)%R -> denom_nonvanishing_M mu r.
Proof.
 intros ((a,b),(c,d)) r H_refining Hr; 
 generalize (Is_refining_M_d_minusplus_c_sign_dec _ _ _ _ H_refining); clear H_refining.
 intros [[_[_[_[_[H1 [H2 H3]]]]]]|[_[_[_[_[H1 [H2 H3]]]]]]]; red; simpl; realify_Q; intros H1 H2 H3;
 destruct (Qtrichotomy_inf Zero c) as [[Hc|Hc]|Hc]; realify_Q; intros Hc.
  apply Rlt_not_eq'; apply Bounded_M_pos_auxiliary_1; trivial...
  rewrite <- Hc; stepl d; auto; ring... 
  apply Rlt_not_eq'; apply Bounded_M_pos_auxiliary_2; trivial...
  apply Rlt_not_eq; apply Bounded_M_neg_auxiliary_1; trivial...
  rewrite <- Hc; stepl d; auto; ring...
  apply Rlt_not_eq; apply Bounded_M_neg_auxiliary_2; trivial...
Qed.

Lemma Is_refining_M_property:forall mu r, ((-1)<=r<=1)%R->Is_refining_M mu -> ((-1)<=as_Moebius mu r<=1)%R.
Proof.
 intros ((a,b),(c,d)) r Hr H_refining; 
 generalize (Is_refining_M_denom_nonvanishing_M _ _ H_refining Hr). 
 unfold denom_nonvanishing_M, as_Moebius, fst, snd.
 destruct (Is_refining_M_d_minusplus_c_sign_dec _ _ _ _ H_refining) 
     as [[H1 [H2 [H3 [H4 [H7 [H5 H6]]]]]]|[H1 [H2 [H3 [H4 [H7 [H5 H6]]]]]]];
 [ generalize (Is_refining_M_auxiliary_1 _ _ _ _ H1 H2 H3 H4)
 | generalize (Is_refining_M_auxiliary_2 _ _ _ _ H1 H2 H3 H4)
 ];
 intros [H12 [H13 [H14 [H8 [H9 [H10 H11]]]]]];
 realify_Q; intros H1 H2 H3 H4 H7 H5 H6 H12 H13 H14 H8 H9 H10 H11 H_denom. 
  (* everything is positive *)
   (* TP: 0 < c*r+d *)
   assert (H_crd:0<c*r+d);
   [ destruct (Qtrichotomy_inf Zero c) as [[Hc|Hc]|Hc]; realify_Q; intros Hc;
     [ (* 0<c *) apply Bounded_M_pos_auxiliary_1; trivial
     | (* c=0 *) rewrite <- Hc; stepr d; auto; ring
     | (* c<0 *) apply Bounded_M_pos_auxiliary_2; trivial]
   |].

  split. 

   (* lower bound *)
   destruct (Qtrichotomy_inf Zero (Qplus c a)) as [[Hca|Hca]|Hca]; realify_Q; intros Hca;
   (stepl (-1/1); [|field; auto]); apply Rmult_Rdiv_pos_Rle; auto; apply Rle_zero_Rminus; (stepr ((c+a)*r+(d+b)); [|ring]).
    (* 0<c+a *)
    apply Bounded_M_pos_auxiliary_3; trivial; ring_exact_R H4.
    (* c+a=0 *)
    rewrite <- Hca; stepr (d+b); auto; ring.
    (* 0<c+a *)
    apply Bounded_M_pos_auxiliary_4; trivial; ring_exact_R H1...
   (* upper bound *)
   destruct (Qtrichotomy_inf Zero (Qminus c a)) as [[Hca|Hca]|Hca]; realify_Q; intros Hca;
   (stepr (1/1); [|field; auto]); apply Rmult_Rdiv_pos_Rle; auto; apply Rle_zero_Rminus; (stepr ((c-a)*r+(d-b)); [|ring]).
    (* 0<c+a *)
    apply Bounded_M_pos_auxiliary_3; trivial; ring_exact_R H2.
    (* c+a=0 *)
    rewrite <- Hca; stepr (d-b); auto; ring.
    (* 0<c+a *)
    apply Bounded_M_pos_auxiliary_4; trivial; ring_exact_R H3...
  (* everything is negative *)
   (* TP: c*r+d < 0 *)
   assert (H_crd:c*r+d<0);
   [ destruct (Qtrichotomy_inf Zero c) as [[Hc|Hc]|Hc]; realify_Q; intros Hc;
     [ (* 0<c *) apply Bounded_M_neg_auxiliary_1; trivial
     | (* c=0 *) rewrite <- Hc; stepl d; auto; ring
     | (* c<0 *) apply Bounded_M_neg_auxiliary_2; trivial]
   |].

  split. 

   (* lower bound *)
   destruct (Qtrichotomy_inf Zero (Qplus c a)) as [[Hca|Hca]|Hca]; realify_Q; intros Hca;
   (stepl (1/(-1)); [|field; auto]); apply Rmult_Rdiv_neg_Rle; auto; apply Rminus_le; (stepl ((c+a)*r+(d+b)); [|ring]).
    (* 0<c+a *)
    apply Bounded_M_neg_auxiliary_3; trivial; ring_exact_R H1.
    (* c+a=0 *)
    rewrite <- Hca; stepl (d+b); auto; ring.
    (* 0<c+a *)
    apply Bounded_M_neg_auxiliary_4; trivial; ring_exact_R H4...
   (* upper bound *)
   destruct (Qtrichotomy_inf Zero (Qminus c a)) as [[Hca|Hca]|Hca]; realify_Q; intros Hca;
   (stepr (-1/-1); [|field; auto]); apply Rmult_Rdiv_neg_Rle; auto; apply Rminus_le; (stepl ((c-a)*r+(d-b)); [|ring]).
    (* 0<c+a *)
    apply Bounded_M_neg_auxiliary_3; trivial; ring_exact_R H3.
    (* c+a=0 *)
    rewrite <- Hca; stepl (d-b); auto; ring.
    (* 0<c+a *)
    apply Bounded_M_neg_auxiliary_4; trivial; ring_exact_R H2...
Qed.

Lemma denom_nonvanishing_M_product:forall mu mu' r,Is_refining_M mu ->((-1)<=as_Moebius mu' r<=1)%R->
                denom_nonvanishing_M mu' r-> denom_nonvanishing_M (product mu mu') r.
Proof.
 intros ((a,b),(c,d)) ((a',b'),(c',d')) r.
 unfold as_Moebius, denom_nonvanishing_M, product, fst, snd.
 intros  H_refining Hr H_denom.
 repeat rewrite Q_to_Rplus; repeat rewrite Q_to_Rmult.
 stepl (c*(a'*r+b')+d*(c'*r+d')); [|ring].
 apply Rlinear_non_zero_2; auto. 
 apply (Is_refining_M_denom_nonvanishing_M _ _ H_refining Hr).
Qed.
 
Lemma as_Moebius_product : forall mu mu' r, denom_nonvanishing_M mu' r -> ((-1)<=as_Moebius mu' r<=1)%R -> 
                     Is_refining_M mu ->  as_Moebius (product mu mu') r = as_Moebius mu (as_Moebius mu' r).
Proof.
 intros ((a,b),(c,d)) ((a',b'),(c',d')) r H_denom H_mu'_r H_refining.
 generalize (denom_nonvanishing_M_product _ _ _ H_refining H_mu'_r H_denom).
 generalize H_denom; clear H_denom.
 unfold as_Moebius, denom_nonvanishing_M, product, fst, snd. 
 realify_Q.
 intros H_denom H_denom_prod.
 repeat rewrite Rdiv_Rmult_numerator; trivial.
 repeat rewrite Rdiv_Rplus_Rmult; trivial.
 rewrite Rdiv_Rdiv_simplify; trivial. 
  apply (f_equal2 Rdiv); ring.
  stepl ((c * a' + d * c') * r + (c * b' + d * d')); trivial; ring.
Qed.


Open Scope Z_scope.
Open Scope Q_scope.

Lemma Incl_M_absorbs_Is_refining_M_L:forall mu, Incl_M mu LL -> Is_refining_M (product inv_LL mu).
Proof.
 intros ((a,b),(c,d));
 unfold Incl_M, Is_refining_M, Bounded_M, product, inv_digit, map_digits, inv_LL, fst, snd.
 replace ((-1)/2 - 1/2) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace (1/2 + 3/2) with (Qone +Qone); [|qZ_numerals; field; auto];
 replace (3/2 - 1/2) with Qone; [|qZ_numerals; field; auto];
 replace (1/2 + -1/2) with Zero; [|qZ_numerals; field; auto];
 repeat rewrite Qmult_one_right;
 intros [[[H1 H2]|[H1 H2]] [H3 [H4 [H5 H6]]]]. 

  (* Zero < d-c,d+c *)
  generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H5); generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H6);
  generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H3); generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H4); clear H3 H4 H5 H6;
  repeat rewrite Qmult_zero_right;
  intros H3 H4 H5 H6; 
  split; left; repeat split.
   (* TP: boundedness *)
   stepr ((1/2)*((d+c)-(a+b))); [|qZ_numerals; field; auto];
    apply Qlt_mult_pos_pos; auto; apply Qlt_Qminus_Zero; apply Qle_lt_trans with Zero; trivial;
    apply Qmult_resp_Qle_pos_r with (Qone+Qone);  auto.
   stepr ((1/2)*((d-c)-(b-a))); [|qZ_numerals; field; auto];
    apply Qlt_mult_pos_pos; auto; apply Qlt_Qminus_Zero; apply Qle_lt_trans with Zero; trivial; 
    apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto.
   (* TP: refining *)
   stepr ((c+d)+(a+b)); [|qZ_numerals; field; auto];
    stepl ((c+d)+(c + d)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto.
   stepr (Zero-((b-a)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero; trivial.
   stepr (Zero-((a+b)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero; trivial.
   stepr ((d-c)+(b-a)); [|qZ_numerals; field; auto];
    stepl ((d-c)+(d-c)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto.
  (* d-c,d+c < Zero *)
  generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H5); generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H6);
  generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H3); generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H4); clear H3 H4 H5 H6;
  repeat rewrite Qmult_zero_right;
  intros H3 H4 H5 H6; 
  split; right; repeat split.
   (* TP: boundedness *)
   stepl (((d+c)-(a+b))*(1/2)); [|qZ_numerals; field; auto];
    apply Qlt_mult_neg_pos; auto; apply Qlt_Qminus_Zero_neg; apply Qlt_le_trans with Zero; trivial;
    apply Qmult_resp_Qle_pos_r with (Qone+Qone);  auto.
   stepl (((d-c)-(b-a))*(1/2)); [|qZ_numerals; field; auto];
    apply Qlt_mult_neg_pos; auto; apply Qlt_Qminus_Zero_neg; apply Qlt_le_trans with Zero; trivial; 
    apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto.
   (* TP: refining *)
   stepl ((c+d)+(a+b)); [|qZ_numerals; field; auto];
    stepr ((c+d)+(c + d)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto.
   stepl (Zero-((b-a)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero_neg; trivial.
   stepl (Zero-((a+b)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero_neg; trivial.
   stepl ((d-c)+(b-a)); [|qZ_numerals; field; auto];
    stepr ((d-c)+(d-c)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto.
Qed.

Lemma Incl_M_absorbs_Is_refining_M_R:forall mu, Incl_M mu RR -> Is_refining_M (product inv_RR mu).
Proof.
 intros ((a,b),(c,d));
 unfold Incl_M, Is_refining_M, Bounded_M, product, inv_digit, map_digits, inv_RR, fst, snd.
 replace (1/2 - 1/2) with Zero; [|qZ_numerals; field; auto];
 replace (-1/2 + 3/2) with Qone; [|qZ_numerals; field; auto];
 replace (3/2 - -1/2) with (Qone +Qone); [|qZ_numerals; field; auto];
 replace (1/2 + 1/2) with Qone; [|qZ_numerals; field; auto];
 repeat rewrite Qmult_one_right;
 intros [[[H1 H2]|[H1 H2]] [H3 [H4 [H5 H6]]]]. 
  (* Zero < d-c,d+c *)
  generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H5); generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H6);
  generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H3); generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H4); clear H3 H4 H5 H6;
  repeat rewrite Qmult_zero_right;
  intros H3 H4 H5 H6; 
  split; left; repeat split.
   (* TP: boundedness *)
   stepr ((1/2)*((d+c)+(a+b))); [|qZ_numerals; field; auto];
   apply Qlt_mult_pos_pos; auto; apply Qlt_le_reg_pos; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto.
   stepr ((1/2)*((d-c)+(b-a))); [|qZ_numerals; field; auto];
   apply Qlt_mult_pos_pos; auto; apply Qlt_le_reg_pos; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto.
   (* TP: refining *)
   stepr ((a+b)*(Qone+Qone)); trivial; qZ_numerals; field; auto.
   stepr ((d-c)-(b-a)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero; trivial.
   stepr ((c+d)-(a+b)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero; trivial.
   stepr ((b-a)*(Qone+Qone)); trivial; qZ_numerals; field; auto.
  (* d-c,d+c < Zero *)
  generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H5); generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H6);
  generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H3); generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H4); clear H3 H4 H5 H6;
  repeat rewrite Qmult_zero_right;
  intros H3 H4 H5 H6; 
  split; right; repeat split.
   (* TP: boundedness *)
   stepl (((d+c)+(a+b))*(1/2)); [|qZ_numerals; field; auto];
   apply Qlt_mult_neg_pos; auto; apply Qlt_le_reg_neg; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto.
   stepl (((d-c)+(b-a))*(1/2)); [|qZ_numerals; field; auto];
   apply Qlt_mult_neg_pos; auto; apply Qlt_le_reg_neg; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto.
   (* TP: refining *)
   stepl ((a+b)*(Qone+Qone)); trivial; qZ_numerals; field; auto.
   stepl ((d-c)-(b-a)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero_neg; trivial.
   stepl ((c+d)-(a+b)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero_neg; trivial.
   stepl ((b-a)*(Qone+Qone)); trivial; qZ_numerals; field; auto.
Qed.

Lemma Incl_M_absorbs_Is_refining_M_M:forall mu, Incl_M mu MM -> Is_refining_M (product inv_MM mu).
Proof.
 intros ((a,b),(c,d));
 unfold Incl_M, Is_refining_M, Bounded_M, product, inv_digit, map_digits, inv_MM, fst, snd.
 replace (0/1 - 1/1) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace (1/1 + 0/1) with Qone; [|qZ_numerals; field; auto];
 replace (3/1 - 0/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 replace (0/1 + 3/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 repeat rewrite Qmult_one_right;
 intros [[[H1 H2]|[H1 H2]] [H3 [H4 [H5 H6]]]]. 
  (* Zero < d-c,d+c *)
  generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H5); generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H6);
  generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H3); generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H4); clear H3 H4 H5 H6;
  intros H3 H4 H5 H6; 
  split; left; repeat split.
   (* TP: boundedness *)
   stepr ((1/3)*(d+c)); [|qZ_numerals; field; auto]; apply Qlt_mult_pos_pos; auto.
   stepr ((1/3)*(d-c)); [|qZ_numerals; field; auto]; apply Qlt_mult_pos_pos; auto.
   (* TP: refining *)
   stepr ((a+b)+(1/3)*(d+c)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial; 
    stepr (((a+b)*(Qone+Qone+Qone))-((c + d)*-Qone)); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial.
   stepr ((a-b)+(1/3)*(d-c)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial;
    stepr ((d-c)-((b-a)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial.
   stepr ((1/3)*(c+d)-(a+b)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial;
    stepr ((c+d)-((a+b)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial.
   stepr ((1/3)*(d-c)+(b-a)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial;
    stepr (((b-a)*(Qone+Qone+Qone))-((d-c)*-Qone)); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial.
  (* d-c,d+c < Zero *)
  generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H5); generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H6);
  generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H3); generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H4); clear H3 H4 H5 H6;
  intros H3 H4 H5 H6; 
  split; right; repeat split.
   (* TP: boundedness *)
   stepl ((d+c)*(1/3)); [|qZ_numerals; field; auto]; apply Qlt_mult_neg_pos; auto.
   stepl ((d-c)*(1/3)); [|qZ_numerals; field; auto]; apply Qlt_mult_neg_pos; auto.
   (* TP: refining *)
   stepl ((a+b)+(1/3)*(d+c)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial; 
    stepl (((a+b)*(Qone+Qone+Qone))-((c + d)*-Qone)); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial.
   stepl ((a-b)+(1/3)*(d-c)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial;
    stepl ((d-c)-((b-a)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial.
   stepl ((1/3)*(c+d)-(a+b)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial;
    stepl ((c+d)-((a+b)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial.
   stepl ((1/3)*(d-c)+(b-a)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial;
    stepl (((b-a)*(Qone+Qone+Qone))-((d-c)*-Qone)); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial.
Qed.

Lemma Incl_M_absorbs_Is_refining_M:forall mu d, Incl_M mu d -> Is_refining_M (product (inv_digit d) mu).
Proof.
 intros mu [ | | ] H_Incl; unfold inv_digit;
 [ apply Incl_M_absorbs_Is_refining_M_L
 | apply Incl_M_absorbs_Is_refining_M_R
 | apply Incl_M_absorbs_Is_refining_M_M
 ]; assumption.
Qed.

Close Scope Q_scope.
Close Scope Z_scope.

Lemma denom_nonvanishing_M_product_inv_L: forall mu r, denom_nonvanishing_M mu r -> ((-1) <= as_Moebius mu r <= 0)%R ->
                                                       denom_nonvanishing_M (product inv_LL mu) r.
Proof. 
 intros ((a,b),(c,d)) r.
 unfold product, as_Moebius, denom_nonvanishing_M, inv_LL, fst, snd.
 intros H_denom [Hr1 Hr2].
 destruct (Q_eq_dec c a) as [Hca|Hca].
  (* a=c *)
  destruct (Q_eq_dec d b) as [Hbd|Hbd].
   (* d=b *)
   apply False_ind; subst c d; apply (Rlt_irrefl 1); apply Rle_lt_trans with 0; trivial; 
   stepl ((a * r + b)/(a * r + b)); trivial; field; trivial.
   (* d<>b *)
   subst c; stepl ((1%Z/2%Z)*(d-b)).
    apply Rmult_resp_nonzero; realify_Q; auto; apply Rminus_eq_contra; apply Q_to_R_not_eq; trivial. 
    realify_Q_goal; auto; change (IZR (Zneg xH)) with (- IZR (Zpos xH))%R; field; auto.
  (* c<>a *)
  realify_Q; auto.
  intros Hca.
  generalize (Rminus_eq_contra _ _ Hca); clear Hca; intro Hca.
  change (IZR 1) with 1; change (IZR (-1)) with (-1); change (IZR 2) with 2.
  stepl (1/2*((c-a)*r+(d-b))); [|field; auto].
  apply Rmult_resp_nonzero; auto.
  apply Rlinear_non_zero_3; trivial.
  intro H_false.
  apply (Rlt_irrefl 1).
  apply Rle_lt_trans with 0; trivial.
  stepl ((a * r + b)/(c * r + d)); trivial. 
  subst r. 
  repeat rewrite Rdiv_Rmult_numerator; trivial.
  repeat rewrite Rdiv_Rplus_Rmult; trivial.
  assert (H_linear:c * - (d - b) + (c - a) * d<>0);[rewrite (Rmult_comm (c-a) d); apply Rlinear_non_zero_2; trivial|].
  rewrite Rdiv_Rdiv_simplify; trivial.
  apply Req_Rdiv_Rone; trivial; ring.
Qed.

Lemma denom_nonvanishing_M_product_inv_R: forall mu r, denom_nonvanishing_M mu r -> (0 <= as_Moebius mu r <= 1)%R ->
                                                       denom_nonvanishing_M (product inv_RR mu) r.
Proof. 
 intros ((a,b),(c,d)) r.
 unfold product, as_Moebius, denom_nonvanishing_M, inv_RR, fst, snd.
 intros H_denom [Hr1 Hr2].
 destruct (Q_eq_dec c (Qopp a)) as [Hca|Hca].
  (* -a=c *)
  destruct (Q_eq_dec d (Qopp b)) as [Hbd|Hbd].
   (* -d=b *)
   apply False_ind; subst c d; apply (Rlt_irrefl (-1)); apply Rlt_le_trans with 0; trivial;
    stepr ((a * r + b)/((-a)%Q * r + (-b)%Q)); trivial; generalize H_denom; clear H_denom; realify_Q;
    intros H_denom; field; trivial.
   (* -d<>b *)
   subst c; stepl ((1%Z/2%Z)*(d+b)).
    apply Rmult_resp_nonzero; realify_Q; auto; intros Hbd; stepl (d-(-b)); [|ring]; apply Rminus_eq_contra; trivial.
    realify_Q; auto; intros Hdb; field; auto.
  (* -c<>a *)
  realify_Q; auto; intros Hca.
  assert (Hca': c + a <> 0); [stepl (c-(-a));[|ring]; apply Rminus_eq_contra; assumption|].
  change (IZR 1) with 1; change (IZR (-1)) with (-1); change (IZR 2) with 2.
  stepl (1/2*((c+a)*r+(d+b))); [|field; auto].
  apply Rmult_resp_nonzero; auto.
  apply Rlinear_non_zero_3; trivial.
  intro H_false.
  apply (Rlt_irrefl (-1)).
  apply Rlt_le_trans with 0; trivial.
  stepr ((a * r + b)/(c * r + d)); trivial. 
  subst r. 
  repeat rewrite Rdiv_Rmult_numerator; trivial.
  repeat rewrite Rdiv_Rplus_Rmult; trivial.
  assert (H_linear:c * - (d + b) + (c + a) * d<>0);[rewrite (Rmult_comm (c+a) d); apply Rlinear_non_zero_2; trivial|].
  rewrite Rdiv_Rdiv_simplify; trivial.
  apply Req_Ropp_Rdiv_minus_Rone; trivial; ring.
Qed.

Lemma denom_nonvanishing_M_product_inv_M: forall mu r, denom_nonvanishing_M mu r -> ((-1/3) <= as_Moebius mu r <= 1/3)%R ->
                                                       denom_nonvanishing_M (product inv_MM mu) r.
Proof. 
 intros ((a,b),(c,d)) r;
 unfold product, as_Moebius, denom_nonvanishing_M, inv_MM, fst, snd;
 intros H_denom [Hr1 Hr2];
 realify_Q; auto; simpl;
 stepl (1/3*(c*r+d)); auto;
 field; repeat apply Rmult_resp_nonzero; auto; stepl 3; auto; ring.
Qed.

Lemma Is_refining_M_L:Is_refining_M (LL:Matrix). 
Proof.
 unfold map_digits, Is_refining_M, Bounded_M, fst, snd; split; left; repeat split; auto.
Qed.
 
Lemma Is_refining_M_R:Is_refining_M (RR:Matrix). 
Proof.
 unfold map_digits, Is_refining_M, Bounded_M, fst, snd; split; left; repeat split; auto.
Qed.

Lemma Is_refining_M_M:Is_refining_M (MM:Matrix). 
Proof.
 unfold map_digits, Is_refining_M, Bounded_M, fst, snd; split; left; repeat split; auto.
Qed.

Lemma as_Moebius_L: forall mu r, denom_nonvanishing_M mu r -> ((-1)<=as_Moebius mu r<=1)%R-> 
                                 as_Moebius (product LL mu) r= (((as_Moebius mu r)-1)/((as_Moebius mu r)+3))%R.
Proof.
 intros ((a,b),(c,d)) r H_denom H_r.
 generalize (denom_nonvanishing_M_product _ _ _ Is_refining_M_L H_r H_denom); generalize H_denom H_r; clear H_denom H_r.
 unfold product, as_Moebius, denom_nonvanishing_M, map_digits, fst, snd.
 realify_Q ;auto; simpl.
 replace (2+1) with 3; [|ring].
 intros H_denom Hr H_denom_product.
 assert (H_denom': a*r+b+(c*r+d)*3<>0);
  [apply Rmult_reg_nonzero_l with (1/2); stepl ((1/2*a+3/2*c)*r+(1/2*b+3/2*d)); trivial; field; auto|].
 rewrite Rdiv_Rminus_Rmult; trivial.
 rewrite Rdiv_Rplus_Rmult; trivial.
 rewrite Rdiv_Rdiv_simplify; trivial.
 transitivity (((a * r + b - (c * r + d) * 1)*(1/2))/((a * r + b + (c * r + d) * 3)*(1/2))).
  apply (f_equal2 Rdiv); field; auto.
  apply Rdiv_Rmult_simplify; auto.
Qed.

Lemma as_Moebius_R: forall mu r, denom_nonvanishing_M mu r -> ((-1)<=as_Moebius mu r<=1)%R-> 
                                 as_Moebius (product RR mu) r= (((as_Moebius mu r)+1)/((-as_Moebius mu r)+3))%R.
Proof.
 intros ((a,b),(c,d)) r H_denom H_r.
 generalize (denom_nonvanishing_M_product _ _ _ Is_refining_M_R H_r H_denom); generalize H_denom H_r; clear H_denom H_r.
 unfold product, as_Moebius, denom_nonvanishing_M, map_digits, fst, snd.
 realify_Q ;auto; simpl.
 replace (2+1) with 3; [|ring].
 intros H_denom Hr H_denom_product.
 assert (H_denom': -(a*r+b)+(c*r+d)*3<>0);
  [apply Rmult_reg_nonzero_l with (1/2); stepl ((-1/2*a+3/2*c)*r+(-1/2*b+3/2*d)); trivial; field; auto|].
 rewrite <- Rdiv_Ropp_numerator; trivial.
 repeat rewrite Rdiv_Rplus_Rmult; trivial.
 rewrite Rdiv_Rdiv_simplify; trivial.
 transitivity (((a * r + b + (c * r + d) * 1)*(1/2))/((-(a * r + b) + (c * r + d) * 3)*(1/2))).
  apply (f_equal2 Rdiv); field; auto.
  apply Rdiv_Rmult_simplify; auto.
Qed.

Lemma as_Moebius_M: forall mu r, denom_nonvanishing_M mu r -> ((-1)<=as_Moebius mu r<=1)%R-> 
                                 as_Moebius (product MM mu) r= ((as_Moebius mu r)/3)%R.
Proof.
 intros ((a,b),(c,d)) r H_denom H_r.
 generalize (denom_nonvanishing_M_product _ _ _ Is_refining_M_M H_r H_denom); generalize H_denom H_r; clear H_denom H_r.
 unfold product, as_Moebius, denom_nonvanishing_M, map_digits, fst, snd.
 realify_Q ;auto; simpl.
 replace (2+1) with 3; [|ring].
 intros H_denom Hr H_denom_product.
 rewrite Rdiv_Rdiv_Rmult_numerator; auto.
 apply (f_equal2 Rdiv); field; auto.
Qed.

Lemma as_Moebius_inv_L: forall mu r, denom_nonvanishing_M mu r -> ((-1) <= as_Moebius mu r <= 0)%R -> as_Moebius (product inv_LL mu) r = ((3 * as_Moebius mu r + 1) / (- as_Moebius mu r + 1))%R.
Proof.
 intros ((a,b),(c,d)) r H_denom H_r;
 generalize (denom_nonvanishing_M_product_inv_L _ _ H_denom H_r); generalize H_denom H_r; clear H_denom H_r;
 unfold product, as_Moebius, denom_nonvanishing_M, inv_LL, fst, snd;
 realify_Q ;auto; simpl;
 replace (2+1) with 3; [|ring];
 intros H_denom Hr H_denom_product.
 assert (H_denom':    - (a * r + b) + (c * r + d) * 1 <> 0);
 [apply Rmult_reg_nonzero_l with (1/2); stepl ((-1/2*a+1/2*c)*r+(-1/2*b+1/2*d)); trivial; field; auto|].
 rewrite <- Rdiv_Ropp_numerator; trivial.
 rewrite Rdiv_Rmult_numerator; trivial.
 repeat rewrite Rdiv_Rplus_Rmult; trivial.
 rewrite Rdiv_Rdiv_simplify; trivial.
 transitivity (((3 * (a * r + b) + (c * r + d) * 1)*(1/2))/((- (a * r + b) + (c * r + d) * 1)*(1/2))).
  apply (f_equal2 Rdiv); field; auto.
  apply Rdiv_Rmult_simplify; auto.
Qed.

Lemma as_Moebius_inv_R: forall mu r, denom_nonvanishing_M mu r -> (0 <= as_Moebius mu r <= 1)%R -> as_Moebius (product inv_RR mu) r = ((3 * as_Moebius mu r - 1) / (as_Moebius mu r + 1))%R.
Proof.
 intros ((a,b),(c,d)) r H_denom H_r;
 generalize (denom_nonvanishing_M_product_inv_R _ _ H_denom H_r); generalize H_denom H_r; clear H_denom H_r;
 unfold product, as_Moebius, denom_nonvanishing_M, inv_RR, fst, snd;
 realify_Q ;auto; simpl;
 replace (2+1) with 3; [|ring];
 intros H_denom Hr H_denom_product.
 assert (H_denom':    (a * r + b) + (c * r + d) * 1 <> 0);
 [apply Rmult_reg_nonzero_l with (1/2); stepl ((1/2*a+1/2*c)*r+(1/2*b+1/2*d)); trivial; field; auto|].
 rewrite Rdiv_Rmult_numerator; trivial.
 repeat rewrite Rdiv_Rplus_Rmult; trivial.
 rewrite Rdiv_Rminus_Rmult; trivial.
 rewrite Rdiv_Rdiv_simplify; trivial.
 transitivity (((3 * (a * r + b) - (c * r + d) * 1)*(1/2))/(((a * r + b) + (c * r + d) * 1)*(1/2))).
  apply (f_equal2 Rdiv); field; auto.
  apply Rdiv_Rmult_simplify; auto.
Qed.

Lemma as_Moebius_inv_M: forall mu r, denom_nonvanishing_M mu r -> ((-1/3) <= as_Moebius mu r <= 1/3)%R -> as_Moebius (product inv_MM mu) r = (3 * as_Moebius mu r)%R.
Proof.
 intros ((a,b),(c,d)) r H_denom H_r;
 generalize (denom_nonvanishing_M_product_inv_M _ _ H_denom H_r); generalize H_denom H_r; clear H_denom H_r;
 unfold product, as_Moebius, denom_nonvanishing_M, inv_MM, fst, snd;
 realify_Q ;auto; simpl;
 replace (2+1) with 3; [|ring];
 intros H_denom Hr H_denom_product.
 rewrite Rdiv_Rmult_numerator; trivial.
 rewrite (Rmult_comm 3); rewrite <- Rdiv_Rdiv_Rmult_denominator; auto.
 apply (f_equal2 Rdiv); field; auto.
Qed.

Lemma as_Moebius_L_min_one: as_Moebius LL (-1)%R = (-1)%R.
Proof.
 unfold as_Moebius, map_digits, fst, snd;
 realify_Q; auto; simpl; replace (2+1) with 3; [|ring]; replace (1 / 2 * -1 + 3 / 2) with 1; field; auto.
Qed.

Lemma as_Moebius_R_min_one: as_Moebius RR (-1)%R = (0)%R.
Proof.
 unfold as_Moebius, map_digits, fst, snd;
 realify_Q; auto; simpl; replace (2+1) with 3; [|ring]; replace (-1 / 2 * -1 + 3 / 2) with 2; field; auto.
Qed.

Lemma as_Moebius_M_min_one: as_Moebius MM (-1)%R = (-1/3)%R.
Proof.
 unfold as_Moebius, map_digits, fst, snd;
 realify_Q; auto; simpl; replace (2+1) with 3; [|ring]; replace (0/1 * -1 + 3 / 1) with 3; field; auto.
Qed.

Lemma as_Moebius_L_one: as_Moebius LL (1)%R = (0)%R.
Proof.
 unfold as_Moebius, map_digits, fst, snd;
 realify_Q; auto; simpl; replace (2+1) with 3; [|ring]; replace (1 / 2 * 1 + 3 / 2) with 2; field; auto.
Qed.

Lemma as_Moebius_R_one: as_Moebius RR (1)%R = (1)%R.
Proof.
 unfold as_Moebius, map_digits, fst, snd;
 realify_Q; auto; simpl; replace (2+1) with 3; [|ring]; replace (-1 / 2 * 1 + 3 / 2) with 1; field; auto.
Qed.

Lemma as_Moebius_M_one: as_Moebius MM (1)%R = (1/3)%R.
Proof.
 unfold as_Moebius, map_digits, fst, snd;
 realify_Q; auto; simpl; replace (2+1) with 3; [|ring]; replace (0/1 * 1 + 3 / 1) with 3; field; auto.
Qed.

Lemma as_Moebius_endpoints_digits_base_l: forall d:Digit, ((-1)%R<=as_Moebius d (-1)%R)%R.
Proof.
 intros [ | | ];
 [ rewrite as_Moebius_L_min_one
 | rewrite as_Moebius_R_min_one
 | rewrite as_Moebius_M_min_one
 ]; fourier.
Qed.

Lemma as_Moebius_endpoints_digits_base_r: forall d:Digit, (as_Moebius d 1%R<=1)%R.
Proof.
 intros [ | | ];
 [ rewrite as_Moebius_L_one
 | rewrite as_Moebius_R_one
 | rewrite as_Moebius_M_one
 ]; fourier.
Qed.

Open Scope Z_scope.
Open Scope Q_scope.

Lemma Is_refining_M_property_fold:  forall mu, (forall r, (-1 <= r <= 1)%R -> denom_nonvanishing_M mu r)->
  (forall (r : R),(-1 <= r <= 1)%R -> (-1<=as_Moebius mu r<=1)%R) ->  Is_refining_M mu.
Proof.
 intros ((a,b),(c,d)) H_denom H_mu.
 unfold denom_nonvanishing_M in H_denom; simpl in H_denom.
 unfold as_Moebius in H_mu; simpl in H_mu.
 assert (H_dcmin:d-c <>Zero);
 [apply Q_to_R_Qneq; realify_Q; stepl (c*(-1)+d)%R; [|ring]; apply (H_denom (-1)%R min_one_is_in_base_interval)|].
 assert (H_dc:d+c <>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*1+d)%R; [|ring]; apply (H_denom (1)%R one_is_in_base_interval)|].
 assert (Hd: d<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*0+d)%R; [|ring]; apply H_denom; split; fourier|].
 split; [ apply denom_nonvanishing_M_Bounded_M; assumption|].
 simpl.
 destruct (denom_nonvanishing_M_Bounded_M ((a,b),(c,d)) H_denom) as [[H1 H2]|[H1 H2]]; simpl in H1, H2.
  (* Zero < d + c /\ Zero < d - c *)
  left; repeat split.
   (* 1 *)
   apply Qle_Qdiv_denom_pos_nonneg with (d+c); trivial;
   assert (Hcd:c*Qone+d <> Zero);[stepl (d+c); trivial; ring|];
   stepr (((a*Qone + b)/(c*Qone + d)) - (-  Qone)); [|field; auto];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal; trivial;
   apply (proj1 (H_mu (1)%R one_is_in_base_interval)).
   (* 2 *)
   apply Qle_Qdiv_denom_pos_nonneg with (d-c); trivial;
   assert (Hcd:c*(-Qone)+d <> Zero);[stepl (d-c); trivial; ring|];
   stepr (Qone -((a*(-Qone) + b)/(c*(-Qone) + d))); [|field; auto];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal; trivial;
   apply (proj2 (H_mu (-1)%R min_one_is_in_base_interval)).
   (* 3 *)
   apply Qle_Qdiv_denom_pos_nonneg with (d+c); trivial;
   assert (Hcd:c*Qone+d <> Zero);[stepl (d+c); trivial; ring|];
   stepr (Qone-((a*Qone + b)/(c*Qone + d))); [|field; auto];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal; trivial;
   apply (proj2 (H_mu (1)%R one_is_in_base_interval)).
   (* 4 *)
   apply Qle_Qdiv_denom_pos_nonneg with (d-c); trivial;
   assert (Hcd:c*(-Qone)+d <> Zero);[stepl (d-c); trivial; ring|];
   stepr (((a*(-Qone) + b)/(c*(-Qone) + d))-(-Qone)); [|field; auto];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal; trivial;
   apply (proj1 (H_mu (-1)%R min_one_is_in_base_interval)).
  (* d + c < Zero /\ d - c , Zero *)
  right; repeat split.
   (* 1 *)
   apply Qle_Qdiv_denom_neg_nonneg with (d+c); trivial;
   assert (Hcd:c*Qone+d <> Zero);[stepl (d+c); trivial; ring|];
   stepr (((a*Qone + b)/(c*Qone + d)) - (-  Qone)); [|field; auto];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal; trivial;
   apply (proj1 (H_mu (1)%R one_is_in_base_interval)).
   (* 2 *)
   apply Qle_Qdiv_denom_neg_nonneg with (d-c); trivial;
   assert (Hcd:c*(-Qone)+d <> Zero);[stepl (d-c); trivial; ring|];
   stepr (Qone -((a*(-Qone) + b)/(c*(-Qone) + d))); [|field; auto];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal; trivial;
   apply (proj2 (H_mu (-1)%R min_one_is_in_base_interval)).
   (* 3 *)
   apply Qle_Qdiv_denom_neg_nonneg with (d+c); trivial;
   assert (Hcd:c*Qone+d <> Zero);[stepl (d+c); trivial; ring|];
   stepr (Qone-((a*Qone + b)/(c*Qone + d))); [|field; auto];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal; trivial;
   apply (proj2 (H_mu (1)%R one_is_in_base_interval)).
   (* 4 *)
   apply Qle_Qdiv_denom_neg_nonneg with (d-c); trivial;
   assert (Hcd:c*(-Qone)+d <> Zero);[stepl (d-c); trivial; ring|];
   stepr (((a*(-Qone) + b)/(c*(-Qone) + d))-(-Qone)); [|field; auto];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal; trivial;
   apply (proj1 (H_mu (-1)%R min_one_is_in_base_interval)).
Qed.

Lemma Is_refining_M_product: forall mu mu', Is_refining_M mu -> Is_refining_M mu' -> Is_refining_M (product mu mu').
Proof.
 intros ((a,b),(c,d)) ((a',b'),(c',d')) H_mu H_mu'.
 apply Is_refining_M_property_fold; intros r Ht.
  apply denom_nonvanishing_M_product; trivial;
  [ apply Is_refining_M_property
  | apply Is_refining_M_denom_nonvanishing_M
  ]; trivial.

  rewrite as_Moebius_product; trivial;
  repeat apply Is_refining_M_property; trivial;
  apply Is_refining_M_denom_nonvanishing_M; trivial.
Qed.

Lemma Is_refining_M_product_hd:forall mu alpha, Is_refining_M mu -> Is_refining_M (product mu (map_digits (hd alpha))).
Proof.
 intros mu [[ | | ] alpha] H_mu;
 unfold hd; apply Is_refining_M_product; trivial;
 [apply Is_refining_M_L|apply Is_refining_M_R|apply Is_refining_M_M].
Qed.

Lemma det_nonneg_refining_endpoints:forall a b c d, Is_refining_M ((a,b),(c,d)) -> Zero <= a*d-b*c  -> 
       as_Moebius_Q ((a,b),(c,d)) (-Qone)<=as_Moebius_Q ((a,b),(c,d)) Qone.
Proof.
 intros a b c d [H_bounded _] H_det.
 unfold as_Moebius_Q; simpl.
 generalize (det_nonneg_nondecreasing _ _ _ _ (-1) 1 H_bounded H_det min_one_is_in_base_interval one_is_in_base_interval
 one_is_in_base_interval_subproof).
 let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in rationalify_R_goal; 
 [ intro H_Rle; apply Q_to_R_Qle; assumption 
 | stepl (d-c); try ring; t_local 
 | stepl (d+c); try ring;t_local
 ].
Qed.

Lemma det_nonpos_refining_endpoints:forall a b c d, Is_refining_M ((a,b),(c,d)) -> a*d-b*c<= Zero  -> 
       as_Moebius_Q ((a,b),(c,d)) Qone<=as_Moebius_Q ((a,b),(c,d)) (-Qone).
Proof.
 intros a b c d [H_bounded _] H_det.
 unfold as_Moebius_Q; simpl.
 generalize (det_nonpos_nonincreasing _ _ _ _ (-1) 1 H_bounded H_det min_one_is_in_base_interval one_is_in_base_interval
 one_is_in_base_interval_subproof).
 let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in rationalify_R_goal; 
 [ intro H_Rle; apply Q_to_R_Qle; assumption 
 | stepl (d-c); try ring; t_local 
 | stepl (d+c); try ring;t_local
 ].
Qed.

Lemma as_Moebius_Q_product: forall mu mu' (q:Q),
  denom_nonvanishing_M mu' q -> -1 <= as_Moebius_Q mu' q -> as_Moebius_Q mu' q <= 1 -> Is_refining_M mu ->
    as_Moebius_Q (product mu mu') q = as_Moebius_Q mu (as_Moebius_Q mu' q).
Proof.
 intros mu mu' q H_denom.
 qZ_numerals.
 intros H_l H_r H_refining.
 apply Q_to_R_Qeq.
 realify_Q.
 intros H_l H_r.
 assert (H1: denom_nonvanishing_M mu (as_Moebius mu' q));
  [apply Is_refining_M_denom_nonvanishing_M; trivial; revert H_l H_r; rewrite Q_to_R_as_Moebius; auto|].
 assert (H2: denom_nonvanishing_M (product mu mu') q);
  [apply denom_nonvanishing_M_product; trivial;revert H_l H_r; rewrite Q_to_R_as_Moebius; auto|].
 revert H_l H_r; repeat rewrite Q_to_R_as_Moebius; trivial.
 intros H_l H_r.
 apply as_Moebius_product; auto. 
Qed.

Lemma Is_refining_M_product_init_pure:forall alpha n, Is_refining_M (product_init_pure alpha n).
Proof.
 intros alpha n; revert alpha; induction n; intros [d alpha]; unfold product_init_pure.
  (* O *)
  simpl; apply Is_refining_M_idM.
  (* S n *)
  rewrite Streams_addenda.take_S_n;
  rewrite (Streams_addenda.fold_right_cons _ _ product).
  apply Is_refining_M_product.
   simpl; destruct d; [apply Is_refining_M_L|apply Is_refining_M_R|apply Is_refining_M_M].
   unfold map_reals; rewrite Streams_addenda.map_unfolded; simpl; apply (IHn alpha).
Qed.

Close Scope Q_scope.
Close Scope Z_scope.