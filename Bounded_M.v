(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import digits.
Require Import Raxioms.
Require Import RIneq.
Require Import R_addenda.
Require Import Fourier_solvable_ineqs.

(** Properties of the predicate [Bounded_M]. *)

Lemma Bounded_M_auxiliary_1: forall (c d:Q), Zero <  d+c -> Zero < d-c -> Zero < d.
Proof.
 intros c d H1 H2; apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepl Zero; auto; stepr ((d+c)+(d-c)); auto ;ring.
Qed.

Lemma Bounded_M_auxiliary_2: forall (c d:Q), d+c<Zero -> d-c<Zero -> d<Zero.
Proof.
 intros c d H1 H2; apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepr Zero; auto; stepl ((d+c)+(d-c)); auto ;ring.
Qed.

Lemma Bounded_M_auxiliary_3: forall (c d:Q), Zero<=d+c -> Zero <= d-c -> Zero <= d.
Proof.
 intros c d H1 H2; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepl Zero; auto; stepr ((d+c)+(d-c)); auto ;ring.
Qed.

Lemma Bounded_M_auxiliary_4: forall (c d:Q), d+c<=Zero -> d-c<=Zero -> d<=Zero.
Proof.
 intros c d H1 H2; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepr Zero; auto; stepl ((d+c)+(d-c)); auto ;ring.
Qed.

Lemma Bounded_M_d_minus_c_nonzero: forall a b c d, Bounded_M ((a,b),(c,d)) -> d-c<> Zero.
Proof.
 intros a b c d [[H1 H2]|[H1 H2]]; unfold fst, snd in H1; unfold fst, snd in H2; auto; apply sym_not_eq; auto.
Qed.

Lemma Bounded_M_c_plus_d_nonzero: forall a b c d, Bounded_M ((a,b),(c,d)) -> c+d<> Zero.
Proof.
 intros a b c d [[H1 H2]|[H1 H2]]; unfold fst, snd in H1; unfold fst, snd in H2; (stepl (d+c); [|ring]);
 auto; apply sym_not_eq; auto.
Qed.

Lemma Bounded_M_nonzero: forall a b c d, Bounded_M ((a,b),(c,d)) -> d<> Zero.
Proof.
 intros a b c d [[H1 H2]|[H1 H2]] H3; unfold fst, snd in H1; unfold fst, snd in H2;
  generalize H1 H2; clear H1 H2; rewrite H3; unfold Qminus; repeat rewrite Qplus_zero_left;
  intros H1 H2; apply Qlt_irreflexive with Zero; apply Qlt_transitive with c; trivial; apply Qlt_opp;
  [ stepl Zero | stepr Zero]; trivial; ring.
Qed.
  
Lemma Bounded_M_pos: forall a b c d r, Bounded_M ((a,b),(c,d))-> Zero<d ->(-1<=r<=1)%R->(0<c*r+d)%R.
Proof.
 intros a b c d r [[H1 H2]|[H1 H2]] Hd Hr; unfold fst, snd in H1; unfold fst, snd in H2.

 destruct (Qtrichotomy_inf Zero c) as [[Hc|Hc]|Hc]. 
  generalize (Q_to_Rlt _ _ H2) (Q_to_Rlt _ _ Hc) Hr; clear H1 H2 Hc Hr;
  rewrite Q_to_R_Zero; try rewrite Q_to_Rplus; try rewrite Q_to_Rminus; 
  intros; apply Bounded_M_pos_auxiliary_1; trivial...
  rewrite <- Hc; generalize (Q_to_Rlt _ _ Hd); clear Hd; rewrite Q_to_R_Zero; intro Hd; stepr d; trivial; ring...
  generalize (Q_to_Rlt _ _ H1) (Q_to_Rlt _ _ Hc) Hr; clear H1 H2 Hc Hr;
  rewrite Q_to_R_Zero; try rewrite Q_to_Rplus; try rewrite Q_to_Rminus; 
  intros; apply Bounded_M_pos_auxiliary_2; trivial...
 
 apply False_ind; apply Qlt_irreflexive with Zero; apply Qlt_transitive with (d+d); auto; stepl ((d+c)+(d-c)); auto; ring.
Qed.

Lemma Bounded_M_neg: forall a b c d r, Bounded_M ((a,b),(c,d))-> d<Zero ->(-1<=r<=1)%R->(c*r+d<0)%R.
Proof.
 intros a b c d r [[H1 H2]|[H1 H2]] Hd Hr; unfold fst, snd in H1; unfold fst, snd in H2.

 apply False_ind; apply Qlt_irreflexive with Zero; apply Qlt_transitive with (d+d); auto; stepr ((d+c)+(d-c)); auto; ring.

 destruct (Qtrichotomy_inf Zero c) as [[Hc|Hc]|Hc]. 

  generalize (Q_to_Rlt _ _ H1) (Q_to_Rlt _ _ Hc) Hr; clear H1 H2 Hc Hr;
  rewrite Q_to_R_Zero; try rewrite Q_to_Rplus; try rewrite Q_to_Rminus. 
  intros; apply Bounded_M_neg_auxiliary_1; trivial...
  rewrite <- Hc; generalize (Q_to_Rlt _ _ Hd); clear Hd; rewrite Q_to_R_Zero; intro Hd; stepl d; trivial; ring...
  generalize (Q_to_Rlt _ _ H2) (Q_to_Rlt _ _ Hc) Hr; clear H1 H2 Hc Hr;
  rewrite Q_to_R_Zero; try rewrite Q_to_Rplus; try rewrite Q_to_Rminus; 
  intros; apply Bounded_M_neg_auxiliary_2; trivial...
Qed.

Lemma Bounded_M_nonzero_denum: forall a b c d r, Bounded_M ((a,b),(c,d))->(-1<=r<=1)%R->(c*r+d<>0)%R.
Proof.
 intros a b c d r H_vanish Hr;
 destruct (Qtrichotomy_inf Zero d) as [[Hd|Hd]|Hd];
  [ apply Rlt_not_eq'; apply Bounded_M_pos with a b; trivial
  | intros _; apply (Bounded_M_nonzero a b c d); auto
  | apply Rlt_not_eq; apply Bounded_M_neg with a b; trivial].
Qed.

Lemma Bounded_M_twice_pos:forall a b c d x y, Bounded_M ((a,b),(c,d))->(-1<=x<=1)%R->(-1<=y<=1)%R->
                                 (0<(c*y+d)*(c*x+d))%R.
Proof.
 intros a b c d x y H_vanish Hx Hy. 
 destruct (Qtrichotomy_inf Zero d) as [[Hd|Hd]|Hd].
  apply Rlt_mult_pos_pos; apply Bounded_M_pos with a b; trivial.
  apply False_ind; apply (Bounded_M_nonzero a b c d); auto.
  apply Rlt_mult_neg_neg; apply Bounded_M_neg with a b; trivial.
Qed. 

Lemma det_nonneg_nondecreasing:forall a b c d x y, Bounded_M ((a,b),(c,d)) -> Zero <= a*d-b*c -> 
               (-1<=x<=1)%R -> (-1<=y<=1)%R -> (x<=y)%R -> ((a*x+b)/(c*x+d) <= (a*y+b)/(c*y+d))%R.
Proof.
 intros a b c d x y H_vanish H_det Hx Hy Hxy;
 generalize (Bounded_M_nonzero_denum _ _ _ _ _ H_vanish Hx);
 generalize (Bounded_M_nonzero_denum _ _ _ _ _ H_vanish Hy);
 generalize (Bounded_M_twice_pos _ _ _ _ _ _ H_vanish Hx Hy);
 generalize (Q_to_Rle _ _ H_det); rewrite Q_to_R_Zero; rewrite Q_to_Rminus; repeat rewrite Q_to_Rmult; 
 clear H_det; intros H_det H_cxyd H_cyd H_cxd;
 apply Rle_zero_Rminus;
 rewrite (distance_Moebius a b _ _ _ _ H_cyd H_cxd);
 unfold Rdiv; apply Fourier_util.Rle_mult_inv_pos; auto;
 apply Rmult_le_pos; trivial; apply Rle_Rminus_zero; trivial.
Qed.

Lemma det_nonpos_nonincreasing:forall a b c d x y, Bounded_M ((a,b),(c,d)) -> a*d-b*c <= Zero -> 
               (-1<=x<=1)%R -> (-1<=y<=1)%R -> (x<=y)%R -> ((a*y+b)/(c*y+d)<=(a*x+b)/(c*x+d))%R.
Proof.
 intros a b c d x y H_vanish H_det Hx Hy Hxy;
 generalize (Bounded_M_nonzero_denum _ _ _ _ _ H_vanish Hx);
 generalize (Bounded_M_nonzero_denum _ _ _ _ _ H_vanish Hy);
 generalize (Bounded_M_twice_pos _ _ _ _ _ _ H_vanish Hy Hx);
 generalize (Q_to_Rle _ _ H_det); rewrite Q_to_R_Zero; rewrite Q_to_Rminus; repeat rewrite Q_to_Rmult; 
 clear H_det; intros H_det H_cxyd H_cyd H_cxd;
 apply Rle_zero_Rminus;
 rewrite (distance_Moebius a b _ _ _ _ H_cxd H_cyd);
 unfold Rdiv; apply Fourier_util.Rle_mult_inv_pos; auto;
 apply Rle_mult_nonpos_nonpos; trivial; apply Rle_minus; trivial.
Qed.

Lemma Bounded_M_denom_nonvanishing_M:forall mu, Bounded_M mu -> (forall r, (-1 <= r <= 1)%R -> denom_nonvanishing_M mu r).
Proof.
 intros ((a,b),(c,d)) H_bounded r Hr; red; simpl; apply Bounded_M_nonzero_denum with a b; assumption.
Qed.

Lemma denom_nonvanishing_M_Bounded_M:forall mu, (forall r, (-1 <= r <= 1)%R -> denom_nonvanishing_M mu r) -> Bounded_M mu.
Proof.
 intros ((a,b),(c,d)) H_denom.
 unfold denom_nonvanishing_M in H_denom; simpl in H_denom.
 assert (H_dcmin:d-c <>Zero);
 [apply Q_to_R_Qneq; realify_Q; stepl (c*(-1)+d)%R; [|ring]; apply (H_denom (-1)%R min_one_is_in_base_interval)|].
 assert (H_dc:d+c <>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*1+d)%R; [|ring]; apply (H_denom (1)%R one_is_in_base_interval)|].
 assert (Hd: d<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (c*0+d)%R; [|ring]; apply H_denom; split; Fourier.fourier|].
 unfold Incl_M, Bounded_M, map_digits, fst, snd.  
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
Qed.

Lemma maximum_eta_discriminant_nondecreasing: forall a b c d x, c<=Zero -> Bounded_M ((a,b),(c,d)) ->
      -Qone<= x -> x <=Qone -> as_Moebius_Q  ((0/1,1/1),(c,d)) x <= Qone/(c+d).
Proof.
 intros a b c d x Hc H_bounded Hx_l Hx_r.
 assert (Hdc:=Bounded_M_c_plus_d_nonzero _ _ _ _ H_bounded).
 assert (Hx_lr:(-1<= x <= 1 )%R); [realify_Q; intros; split; trivial|].
 generalize ((Bounded_M_denom_nonvanishing_M _ H_bounded) x Hx_lr).
 unfold denom_nonvanishing_M, as_Moebius_Q, fst, snd; rationalify_R_goal; intros Hcxd.
 qZ_numerals.
 stepl (Qone/(c*x+d)); [|field; split; auto; apply Q_to_R_Qneq; assumption].
 apply Q_to_R_Qle.
 assert (Hcxd':=Q_to_R_Qneq _ _ Hcxd).
 clear Hcxd.
 realify_Q_goal; trivial. 
 realify_Q.
 intros H1 H2 H3 H4 H5.
 apply Rle_zero_Rminus. 
 stepr (((1-x)*(-c))/((c*1+d)*(c*x+d)))%R; [|field; split; auto].
  unfold Rdiv; repeat apply Rle_mult_nonneg_nonneg; try Fourier.fourier;
  apply Rlt_le; apply Rinv_pos; apply (Bounded_M_twice_pos _ _ _ _ x R1 H_bounded); auto; apply one_is_in_base_interval.
Qed.


Lemma maximum_eta_discriminant_nonincreasing: forall a b c d x, Zero<=c -> Bounded_M ((a,b),(c,d)) ->
      -Qone<= x -> x <=Qone -> as_Moebius_Q  ((0/1,1/1),(c,d)) x <= Qone/(d-c).
Proof.
 intros a b c d x Hc H_bounded Hx_l Hx_r.
 assert (Hdc:=Bounded_M_d_minus_c_nonzero _ _ _ _ H_bounded).
 assert (Hx_lr:(-1<= x <= 1 )%R); [realify_Q; intros; split; trivial|].
 generalize ((Bounded_M_denom_nonvanishing_M _ H_bounded) x Hx_lr); 
 unfold denom_nonvanishing_M, as_Moebius_Q, fst, snd; rationalify_R_goal; intros Hcxd.
 qZ_numerals.
 stepl (Qone/(c*x+d)); [|field; split; auto; apply Q_to_R_Qneq; assumption].
 apply Q_to_R_Qle.
 assert (Hcxd':=Q_to_R_Qneq _ _ Hcxd).
 clear Hcxd.
 realify_Q_goal; trivial. 
 realify_Q.
 intros H1 H2 H3 H4 H5.
 apply Rle_zero_Rminus. 
 stepr (((x+1)*c)/((c*(-1)+d)*(c*x+d)))%R; [|field; split; auto].
  unfold Rdiv; repeat simple apply Rle_mult_nonneg_nonneg; try Fourier.fourier;
  apply Rlt_le; apply Rinv_pos;
  apply (Bounded_M_twice_pos _ _ _ _ x (-1)%R H_bounded); auto; apply min_one_is_in_base_interval.
Qed.

Lemma minimum_eta_discriminant_nondecreasing: forall a b c d x, c<=Zero -> Bounded_M ((a,b),(c,d)) ->
      -Qone<= x -> x <=Qone -> Qone/(d-c) <= as_Moebius_Q  ((0/1,1/1),(c,d)) x.
Proof.
 intros a b c d x Hc H_bounded Hx_l Hx_r.
 assert (Hdc:=Bounded_M_d_minus_c_nonzero _ _ _ _ H_bounded).
 assert (Hx_lr:(-1<= x <= 1 )%R); [realify_Q; intros; split; trivial|].
 generalize ((Bounded_M_denom_nonvanishing_M _ H_bounded) x Hx_lr); 
 unfold denom_nonvanishing_M, as_Moebius_Q, fst, snd; rationalify_R_goal; intros Hcxd.
 qZ_numerals.
 stepr (Qone/(c*x+d)); [|field; split; auto; apply Q_to_R_Qneq; assumption].
 apply Q_to_R_Qle.
 assert (Hcxd':=Q_to_R_Qneq _ _ Hcxd).
 clear Hcxd.
 realify_Q_goal; trivial. 
 realify_Q.
 intros H1 H2 H3 H4 H5.
 apply Rle_zero_Rminus. 
 stepr (((x+1)*(-c))/((c*(-1)+d)*(c*x+d)))%R; [|field; split; auto].
  unfold Rdiv; repeat apply Rle_mult_nonneg_nonneg; try Fourier.fourier;
  apply Rlt_le; apply Rinv_pos;
  apply (Bounded_M_twice_pos _ _ _ _ x (-1)%R H_bounded); auto; apply min_one_is_in_base_interval.
Qed.

Lemma minimum_eta_discriminant_nonincreasing: forall a b c d x, Zero<=c -> Bounded_M ((a,b),(c,d)) ->
      -Qone<= x -> x <=Qone -> Qone/(c+d) <= as_Moebius_Q  ((0/1,1/1),(c,d)) x.
Proof.
 intros a b c d x Hc H_bounded Hx_l Hx_r.
 assert (Hdc:=Bounded_M_c_plus_d_nonzero _ _ _ _ H_bounded).
 assert (Hx_lr:(-1<= x <= 1 )%R); [realify_Q; intros; split; trivial|].
 generalize ((Bounded_M_denom_nonvanishing_M _ H_bounded) x Hx_lr); 
 unfold denom_nonvanishing_M, as_Moebius_Q, fst, snd; rationalify_R_goal; intros Hcxd.
 qZ_numerals.
 stepr (Qone/(c*x+d)); [|field; split; auto; apply Q_to_R_Qneq; assumption].
 apply Q_to_R_Qle.
 assert (Hcxd':=Q_to_R_Qneq _ _ Hcxd).
 clear Hcxd.
 realify_Q_goal; trivial. 
 realify_Q.
 intros H1 H2 H3 H4 H5.
 apply Rle_zero_Rminus. 
 stepr (((1-x)*c)/((c*1+d)*(c*x+d)))%R; [|field; split; auto].
  unfold Rdiv; repeat simple apply Rle_mult_nonneg_nonneg; try Fourier.fourier;
  apply Rlt_le; apply Rinv_pos; apply (Bounded_M_twice_pos _ _ _ _ x R1 H_bounded); auto; apply one_is_in_base_interval.
Qed.

Lemma maximum_eta_discriminant_base_interval: forall a b c d x, Bounded_M ((a,b),(c,d)) -> -Qone<= x -> x <=Qone ->
                         Qabs (as_Moebius_Q  ((0/1,1/1),(c,d)) x) <= Qmax (Qabs(Qone/(c+d))) (Qabs (Qone/(d-c))).
Proof.
 intros a b c d x H_bounded Hx_l Hx_r.
 assert (Hdc_min:=Bounded_M_d_minus_c_nonzero _ _ _ _ H_bounded).
 assert (Hdc:=Bounded_M_c_plus_d_nonzero _ _ _ _ H_bounded).
 assert (Hx_lr:(-1<= x <= 1 )%R); [realify_Q; intros; split; trivial|].
 generalize ((Bounded_M_denom_nonvanishing_M _  H_bounded) x Hx_lr).  
 unfold denom_nonvanishing_M, fst, snd; rationalify_R_goal; intros Hcxd.
 destruct (Qle_dec_weak c Zero) as [Hc|Hc].
 (* c<=Zero, eta nondecreasing *)
  destruct (Q_le_lt_dec Zero (as_Moebius_Q (0 / 1, 1 / 1, (c, d)) x)) as [H_eta|H_eta].
   (* Zero <= eta(x) *)
   rewrite (Qabs_eq _ H_eta).
   apply Qle_trans with (Qabs (Qone / (c + d))).
    apply Qle_trans with (Qone/(c+d)).
     apply maximum_eta_discriminant_nondecreasing with a b; trivial.
     apply Qle_Qabs.
    apply Qle_max_l.     
   (* eta(x)<Zero *)
   rewrite (Qabs_non_eq_neg _ H_eta).
   apply Qle_trans with (Qabs (Qone / (d-c))).
    apply Qle_trans with (Qopp (Qone/(d-c))).
     apply Qopp_Qle; apply minimum_eta_discriminant_nondecreasing with a b; trivial.
     apply Qle_Qabs_Qopp.
    apply Qle_max_r.
 (* Zero<=c, eta nonincreasing *)
  destruct (Q_le_lt_dec Zero (as_Moebius_Q (0 / 1, 1 / 1, (c, d)) x)) as [H_eta|H_eta].
   (* Zero <= eta(x) *)
   rewrite (Qabs_eq _ H_eta).
   apply Qle_trans with (Qabs (Qone / (d-c))).
    apply Qle_trans with (Qone/(d-c)).
     apply maximum_eta_discriminant_nonincreasing with a b; trivial.
     apply Qle_Qabs.
    apply Qle_max_r.
   (* eta(x)<Zero *)
   rewrite (Qabs_non_eq_neg _ H_eta).
   apply Qle_trans with (Qabs (Qone / (c + d))).
    apply Qle_trans with (Qopp(Qone/(c+d))).
     apply Qopp_Qle; apply minimum_eta_discriminant_nonincreasing with a b; trivial.
     apply Qle_Qabs_Qopp.
    apply Qle_max_l.
Qed.

