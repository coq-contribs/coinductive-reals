(************************************************************************)
(* Copyright 2007 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import Reals.
Require Import R_addenda.
Require Import Fourier_solvable_ineqs.
Require Import Fourier.
Require Import digits.
Require Import ub.
Require Import LNP_Digit.
Require Import Refining_T.
Require Import Incl_T.
Import Refining_M.
Import Bounded_M.
Import Bounded_T.
Require Import quadratic.
Require Import qcorrectness.
Require Import productivity_M.

(** * Obtaining the productivity predicate for the refining tensors. *)


Open Scope Z_scope.
Open Scope Q_scope.


Lemma thesis_5_6_20:forall xi H_refining, 
 diameter2 xi H_refining (-Qone) (-Qone) Qone Qone min_one_is_in_base_interval_Q min_one_is_in_base_interval_Q  
                                               one_is_in_base_interval_Q one_is_in_base_interval_Q < redundancy -> 
                     {d:Digit| Incl_T xi d}.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) H_refining.
 assert (H_bounded:=proj1 H_refining).
 assert (H_denom:forall r1 r2,(-1<=r1<=1)%R->(-1<=r2<=1)%R->denom_nonvanishing_T (a,b,(c,d),(e,f,(g,h))) r1 r2);
  [intros r1 r2 Hr1 Hr2; apply Is_refining_T_denom_nonvanishing_T; trivial|].
 unfold diameter2,redundancy.
 set (xi_ll:= as_Tensor_Q (((a,b),(c,d)),((e,f),(g,h))) (-Qone) (-Qone)); 
 set (xi_lr:= as_Tensor_Q (((a,b),(c,d)),((e,f),(g,h))) (-Qone) Qone);
 set (xi_rl:= as_Tensor_Q (((a,b),(c,d)),((e,f),(g,h))) Qone (-Qone)); 
 set (xi_rr:= as_Tensor_Q (((a,b),(c,d)),((e,f),(g,h))) Qone Qone). 
 set (M:=Qmax4 xi_ll xi_lr xi_rl xi_rr).
 set (m:=Qmin4 xi_ll xi_lr xi_rl xi_rr).
 intros H_diam.
 destruct (Q_le_lt_dec M Zero) as [H_M|H_M].
  (* Qmax .... <=0 *) 
  exists LL.
  apply Incl_T_L_folded; trivial; intros r1 r2 Hr1 Hr2; split. 
   elim (Is_refining_T_property _ _ _ Hr1 Hr2 H_refining); trivial.
   apply Rle_trans with M; [ | realify_Q; auto];
    exact (proj2 (denom_nonvanishing_T_within_diameter2 _ H_denom _ _ Hr1 Hr2)).  
  (* 0<Qmax .... *) 
  destruct (Q_le_lt_dec Zero m) as [H_m|H_m].
   (* 0<=Qmin .... *) 
   exists RR.
   apply Incl_T_R_folded; trivial; intros r1 r2 Hr1 Hr2; split. 
    apply Rle_trans with m; [ realify_Q; auto| ];
     exact (proj1 (denom_nonvanishing_T_within_diameter2 _ H_denom _ _ Hr1 Hr2)).  
    elim (Is_refining_T_property _ _ _ Hr1 Hr2 H_refining); trivial.
   (* Qmin ....<Zero *) 
    exists MM.
    apply Incl_T_M_folded; trivial; intros r1 r2 Hr1 Hr2; split. 
     apply Rle_trans with m.
      generalize (Q_to_Rlt _ _ H_M);
      assert (H_diam':(M-m<1/3)%R);
      [ generalize (Q_to_Rlt _ _ H_diam); rationalify_R_goal
      | realify_Q_goal; intros H_M'; fourier
      ]...
      exact (proj1 (denom_nonvanishing_T_within_diameter2 _ H_denom _ _ Hr1 Hr2))...  
     apply Rle_trans with M.
      exact (proj2 (denom_nonvanishing_T_within_diameter2 _ H_denom _ _ Hr1 Hr2))...  
      generalize (Q_to_Rlt _ _ H_m);
      assert (H_diam':(M-m<1/3)%R);
      [ generalize (Q_to_Rlt _ _ H_diam); rationalify_R_goal
      | realify_Q_goal; intros H_M'; fourier
      ]...
Qed.

Lemma diameter2_product:forall xi mu_l mu_r H_xi H_prod (H_l:Is_refining_M mu_l) (H_r:Is_refining_M mu_r) Hll Hrl Hlr Hrr, 
        diameter2 (right_product (left_product xi mu_l) mu_r) H_prod (-Qone) (-Qone) Qone Qone 
                   min_one_is_in_base_interval_Q min_one_is_in_base_interval_Q  
                   one_is_in_base_interval_Q one_is_in_base_interval_Q = 
        diameter2 xi H_xi (as_Moebius_Q mu_l (-Qone)) (as_Moebius_Q mu_r (-Qone)) 
                          (as_Moebius_Q mu_l Qone) (as_Moebius_Q mu_r Qone) Hll Hrl Hlr Hrr.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) ((A,B),(C,D)) ((A',B'),(C',D')) H_xi H_prod H_l H_r Hll Hrl Hlr Hrr.
 assert (H_mul_bound:=proj1 H_l); assert (H_mur_bound:=proj1 H_r);
 generalize (proj1 H_prod).
 unfold diameter2, left_product, right_product,  as_Tensor_Q, as_Moebius_Q, fst, snd.
 intros H_pbounded.
 assert (HCD:=Bounded_M_c_plus_d_nonzero _ _ _ _ H_mul_bound).
 assert (HCDm:=Bounded_M_d_minus_c_nonzero _ _ _ _ H_mul_bound).
 assert (HC'D':=Bounded_M_c_plus_d_nonzero _ _ _ _ H_mur_bound).
 assert (HC'D'm:=Bounded_M_d_minus_c_nonzero _ _ _ _ H_mur_bound).
 assert (H1p:=Bounded_T_e_mf_mg_h_nonzero _ _ _ _ _ _ _ _ H_pbounded);
 assert (H2p:=Bounded_T_me_mf_g_h_nonzero _ _ _ _ _ _ _ _ H_pbounded);
 assert (H3p:=Bounded_T_me_f_mg_h_nonzero _ _ _ _ _ _ _ _ H_pbounded);
 assert (H4p:=Bounded_T_e_f_g_h_nonzero _ _ _ _ _ _ _ _ H_pbounded).
 apply (f_equal2 Qminus); [ apply (f_equal4 Qmax4)|apply (f_equal4 Qmin4)].
  abstract (field; repeat split; [ring_exact_Q HC'D'm|ring_exact_Q HCDm|ring_exact_Q H1p]).
  abstract (field; repeat split; [ring_exact_Q HC'D'|ring_exact_Q HCDm|ring_exact_Q H2p]).
  abstract (field; repeat split; [ring_exact_Q HC'D'm|ring_exact_Q HCD|ring_exact_Q H3p]).
  abstract (field; repeat split; [ring_exact_Q HC'D'|ring_exact_Q HCD|ring_exact_Q H4p]).
  abstract (field; repeat split; [ring_exact_Q HC'D'm|ring_exact_Q HCDm|ring_exact_Q H1p]).
  abstract (field; repeat split; [ring_exact_Q HC'D'|ring_exact_Q HCDm|ring_exact_Q H2p]).
  abstract (field; repeat split; [ring_exact_Q HC'D'm|ring_exact_Q HCD|ring_exact_Q H3p]).
  abstract (field; repeat split; [ring_exact_Q HC'D'|ring_exact_Q HCD|ring_exact_Q H4p]).
Qed.


Lemma upper_bound_Tensor_Moebius_Q_l_eta_discriminant: forall xi (H_xi:Is_refining_T xi), 
   { Y:Q | Zero < Y /\ (forall x y1 y2, 
  -Qone<=x/\x<=Qone -> -Qone<=y1/\y1<=Qone -> -Qone<=y2/\y2<=Qone ->  
       Qabs(as_Moebius_Q  (eta_discriminant (Tensor_Moebius_Q_l xi x)) y1)
        *Qabs(as_Moebius_Q  (eta_discriminant (Tensor_Moebius_Q_l xi x)) y2)<= Y)}.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) H_xi.
 assert (H_bounded:=proj1 H_xi);
 assert (H1:=Bounded_T_e_mf_mg_h_nonzero _ _ _ _ _ _ _ _ H_bounded);
 assert (H2:=Bounded_T_me_mf_g_h_nonzero _ _ _ _ _ _ _ _ H_bounded);
 assert (H3:=Bounded_T_me_f_mg_h_nonzero _ _ _ _ _ _ _ _ H_bounded);
 assert (H4:=Bounded_T_e_f_g_h_nonzero _ _ _ _ _ _ _ _ H_bounded).
 unfold Determinant, Tensor_Moebius_Q_l, eta_discriminant, as_Moebius_Q, fst, snd.
 set (Y:=Qmax4 (Qabs (Qone/(e+f+g+h))) (Qabs (Qone/(-e-f+g+h))) (Qabs (Qone/(-e+f-g+h))) (Qabs (Qone/(e-f-g+h)))).
 exists (Y*Y); split; subst Y.
  apply Qmult_mult_pos; apply Qlt_not_eq; apply Qmax4_Qlt_upper_bound; apply Qabs_nonzero_pos; 
  apply Qinv_resp_nonzero_Qdiv; [ring_exact_Q H4|ring_exact_Q H2|ring_exact_Q H3|ring_exact_Q H1].
 
  intros x y1 y2 Hx Hy1 Hy2.
  assert (Hx_lr:(-1<= x <= 1 )%R); [destruct Hx; realify_Q; intros; split; trivial|].
  assert (H_bx:=Bounded_T_M_l _ _ _ _ _ _ _ _ H_bounded x Hx).
  assert (H_b1:=Bounded_T_M_3 _ _ _ _ _ _ _ _ H_bounded).
  assert (H_b2:=Bounded_T_M_4 _ _ _ _ _ _ _ _ H_bounded).
  assert (H_dx1:e*x+g+(f*x+h)<>Zero);
  [generalize (Bounded_M_nonzero_denum _ _ _ _ x H_b1 Hx_lr); rationalify_R_goal; 
   intros H_tmp; assert (H_:=Q_to_R_Qneq _ _ H_tmp); ring_exact_Q H_|].
  assert (H_dx2:f*x+h-(e*x+g)<>Zero);
  [generalize (Bounded_M_nonzero_denum _ _ _ _ x H_b2 Hx_lr); rationalify_R_goal; 
   intros H_tmp; assert (H_:=Q_to_R_Qneq _ _ H_tmp); ring_exact_Q H_|].

  apply Qmult_Qle_compat; try apply Qabs_nonneg;
  apply Qle_trans with (Qmax (Qabs (Qone / (e * x + g + (f * x + h)))) (Qabs (Qone / (f * x + h - (e * x + g)))));
  [ stepl  (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (e * x + g, f * x + h)) y1)); trivial;
    apply (maximum_eta_discriminant_base_interval _ _ _ _ y1 H_bx (proj1 Hy1) (proj2 Hy1))
  |
  | stepl  (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (e * x + g, f * x + h)) y2)); trivial;
    apply (maximum_eta_discriminant_base_interval _ _ _ _ y2 H_bx (proj1 Hy2) (proj2 Hy2))
  |
  ].

   apply Qmax_lub.
    apply Qle_trans with (Qmax (Qabs (Qone / (e + f + (g + h)))) (Qabs (Qone / (g + h - (e + f))))). 
     stepl (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (e + f, g + h)) x)).
      apply (maximum_eta_discriminant_base_interval (a+b) (c+d) (e+f) (g+h) x H_b1 (proj1 Hx) (proj2 Hx)).
      unfold as_Moebius_Q, fst, snd; apply (f_equal Qabs); qZ_numerals; field; split; auto.
      apply Qmax_lub.
       stepl (Qabs (Qone / (e + f + g + h)));[apply Qle_Qmax4_1|apply (f_equal Qabs); field; ring_exact_Q H4].
       stepl (Qabs (Qone / (- e - f + g + h)));[apply Qle_Qmax4_2|apply (f_equal Qabs); field; ring_exact_Q H2].
    apply Qle_trans with (Qmax (Qabs (Qone / (- e + f + (- g + h)))) (Qabs (Qone / (- g + h - (- e + f))))).
     stepl (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (-e + f, -g + h)) x)).
      apply (maximum_eta_discriminant_base_interval (-a+b) (-c+d) (-e+f) (-g+h) x H_b2 (proj1 Hx) (proj2 Hx)).
      unfold as_Moebius_Q, fst, snd; apply (f_equal Qabs); qZ_numerals; field; split; auto.
      apply Qmax_lub.
       stepl (Qabs (Qone / (-e + f - g + h)));[apply Qle_Qmax4_3|apply (f_equal Qabs); field; ring_exact_Q H3].
       stepl (Qabs (Qone / (e - f - g + h)));[apply Qle_Qmax4_4|apply (f_equal Qabs); field; ring_exact_Q H1].
   (* copy of the above piece *)
   apply Qmax_lub.
    apply Qle_trans with (Qmax (Qabs (Qone / (e + f + (g + h)))) (Qabs (Qone / (g + h - (e + f))))). 
     stepl (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (e + f, g + h)) x)).
      apply (maximum_eta_discriminant_base_interval (a+b) (c+d) (e+f) (g+h) x H_b1 (proj1 Hx) (proj2 Hx)).
      unfold as_Moebius_Q, fst, snd; apply (f_equal Qabs); qZ_numerals; field; split; auto.
      apply Qmax_lub.
       stepl (Qabs (Qone / (e + f + g + h)));[apply Qle_Qmax4_1|apply (f_equal Qabs); field; ring_exact_Q H4].
       stepl (Qabs (Qone / (- e - f + g + h)));[apply Qle_Qmax4_2|apply (f_equal Qabs); field; ring_exact_Q H2].
    apply Qle_trans with (Qmax (Qabs (Qone / (- e + f + (- g + h)))) (Qabs (Qone / (- g + h - (- e + f))))).
     stepl (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (-e + f, -g + h)) x)).
      apply (maximum_eta_discriminant_base_interval (-a+b) (-c+d) (-e+f) (-g+h) x H_b2 (proj1 Hx) (proj2 Hx)).
      unfold as_Moebius_Q, fst, snd; apply (f_equal Qabs); qZ_numerals; field; split; auto.
      apply Qmax_lub.
       stepl (Qabs (Qone / (-e + f - g + h)));[apply Qle_Qmax4_3|apply (f_equal Qabs); field; ring_exact_Q H3].
       stepl (Qabs (Qone / (e - f - g + h)));[apply Qle_Qmax4_4|apply (f_equal Qabs); field; ring_exact_Q H1].
Qed.

Lemma upper_bound_Tensor_Moebius_Q_r_eta_discriminant: forall xi (H_xi:Is_refining_T xi), 
   { Y:Q | Zero < Y /\ (forall x1 x2 y, 
  -Qone<=x1/\x1<=Qone -> -Qone<=x2/\x2<=Qone -> -Qone<=y/\y<=Qone ->  
       Qabs(as_Moebius_Q  (eta_discriminant (Tensor_Moebius_Q_r xi y)) x1)
        *Qabs(as_Moebius_Q  (eta_discriminant (Tensor_Moebius_Q_r xi y)) x2)<= Y)}.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) H_xi.
 assert (H_bounded:=proj1 H_xi);
 assert (H1:=Bounded_T_e_mf_mg_h_nonzero _ _ _ _ _ _ _ _ H_bounded);
 assert (H2:=Bounded_T_me_mf_g_h_nonzero _ _ _ _ _ _ _ _ H_bounded);
 assert (H3:=Bounded_T_me_f_mg_h_nonzero _ _ _ _ _ _ _ _ H_bounded);
 assert (H4:=Bounded_T_e_f_g_h_nonzero _ _ _ _ _ _ _ _ H_bounded).
 unfold Determinant, Tensor_Moebius_Q_r, eta_discriminant, as_Moebius_Q, fst, snd.
 set (Y:=Qmax4 (Qabs (Qone/(e+f+g+h))) (Qabs (Qone/(-e-f+g+h))) (Qabs (Qone/(-e+f-g+h))) (Qabs (Qone/(e-f-g+h)))).
 exists (Y*Y); split; subst Y.
  apply Qmult_mult_pos; apply Qlt_not_eq; apply Qmax4_Qlt_upper_bound; apply Qabs_nonzero_pos; 
  apply Qinv_resp_nonzero_Qdiv; [ring_exact_Q H4|ring_exact_Q H2|ring_exact_Q H3|ring_exact_Q H1].
 
  intros x1 x2 y Hx1 Hx2 Hy.
  assert (Hy_lr:(-1<= y <= 1 )%R); [destruct Hy; realify_Q; intros; split; trivial|].
  assert (H_by:=Bounded_T_M_r _ _ _ _ _ _ _ _ H_bounded y Hy).
  assert (H_b1:=Bounded_T_M_2 _ _ _ _ _ _ _ _ H_bounded).
  assert (H_b2:=Bounded_T_M_1 _ _ _ _ _ _ _ _ H_bounded).
  assert (H_b2':Bounded_M (-a+c,-b+d,(-e+g,-f+h)));
  [ replace (-a+c) with (c-a); [|ring]; replace (-b+d) with (d-b); [|ring]; 
    replace (-e+g) with (g-e); [|ring]; replace (-f+h) with (h-f); [|ring]; assumption|].
  assert (H_dy1:e*y+f+(g*y+h)<>Zero);
  [generalize (Bounded_M_nonzero_denum _ _ _ _ y H_b1 Hy_lr); rationalify_R_goal;
   intros H_tmp; assert (H_:=Q_to_R_Qneq _ _ H_tmp); ring_exact_Q H_|].
  assert (H_dy2:g*y+h-(e*y+f)<>Zero);
  [generalize (Bounded_M_nonzero_denum _ _ _ _ y H_b2 Hy_lr); rationalify_R_goal; 
   intros H_tmp; assert (H_:=Q_to_R_Qneq _ _ H_tmp); ring_exact_Q H_|].

  apply Qmult_Qle_compat; try apply Qabs_nonneg;
  apply Qle_trans with (Qmax (Qabs (Qone / (e * y + f + (g * y + h)))) (Qabs (Qone / (g * y + h - (e * y + f)))));
  [  stepl  (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (e * y + f, g * y + h)) x1)); trivial;
    apply (maximum_eta_discriminant_base_interval _ _ _ _ x1 H_by (proj1 Hx1) (proj2 Hx1))
  |
  | stepl  (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (e * y + f, g * y + h)) x2)); trivial;
    apply (maximum_eta_discriminant_base_interval _ _ _ _ x2 H_by (proj1 Hx2) (proj2 Hx2))
  |
  ].

   apply Qmax_lub.
    apply Qle_trans with (Qmax (Qabs (Qone / (e + g + (f + h)))) (Qabs (Qone / (f + h - (e + g))))). 
     stepl (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (e + g, f + h)) y)).
      apply (maximum_eta_discriminant_base_interval (a+c) (b+d) (e+g) (f+h) y H_b1 (proj1 Hy) (proj2 Hy)).
      unfold as_Moebius_Q, fst, snd; apply (f_equal Qabs); qZ_numerals; field; split; auto.
      apply Qmax_lub.
       stepl (Qabs (Qone / (e + f + g + h)));[apply Qle_Qmax4_1|apply (f_equal Qabs); field; ring_exact_Q H4].
       stepl (Qabs (Qone / (- e + f - g + h)));[apply Qle_Qmax4_3|apply (f_equal Qabs); field; ring_exact_Q H3].
    apply Qle_trans with (Qmax (Qabs (Qone / (- e + g + (- f + h)))) (Qabs (Qone / (- f + h - (- e + g))))).
     stepl (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (-e + g, -f + h)) y)).
      apply (maximum_eta_discriminant_base_interval (-a+c) (-b+d) (-e+g) (-f+h) y H_b2' (proj1 Hy) (proj2 Hy)).
      unfold as_Moebius_Q, fst, snd; apply (f_equal Qabs); qZ_numerals; field; split; auto.
      apply Qmax_lub.
       stepl (Qabs (Qone / (-e - f +g + h)));[apply Qle_Qmax4_2|apply (f_equal Qabs); field; ring_exact_Q H2].
       stepl (Qabs (Qone / (e - f - g + h)));[apply Qle_Qmax4_4|apply (f_equal Qabs); field; ring_exact_Q H1].
   (* copy of the above piece *)
   apply Qmax_lub.
    apply Qle_trans with (Qmax (Qabs (Qone / (e + g + (f + h)))) (Qabs (Qone / (f + h - (e + g))))). 
     stepl (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (e + g, f + h)) y)).
      apply (maximum_eta_discriminant_base_interval (a+c) (b+d) (e+g) (f+h) y H_b1 (proj1 Hy) (proj2 Hy)).
      unfold as_Moebius_Q, fst, snd; apply (f_equal Qabs); qZ_numerals; field; split; auto.
      apply Qmax_lub.
       stepl (Qabs (Qone / (e + f + g + h)));[apply Qle_Qmax4_1|apply (f_equal Qabs); field; ring_exact_Q H4].
       stepl (Qabs (Qone / (- e + f - g + h)));[apply Qle_Qmax4_3|apply (f_equal Qabs); field; ring_exact_Q H3].
    apply Qle_trans with (Qmax (Qabs (Qone / (- e + g + (- f + h)))) (Qabs (Qone / (- f + h - (- e + g))))).
     stepl (Qabs (as_Moebius_Q (0 / 1, 1 / 1, (-e + g, -f + h)) y)).
      apply (maximum_eta_discriminant_base_interval (-a+c) (-b+d) (-e+g) (-f+h) y H_b2' (proj1 Hy) (proj2 Hy)).
      unfold as_Moebius_Q, fst, snd; apply (f_equal Qabs); qZ_numerals; field; split; auto.
      apply Qmax_lub.
       stepl (Qabs (Qone / (-e - f +g + h)));[apply Qle_Qmax4_2|apply (f_equal Qabs); field; ring_exact_Q H2].
       stepl (Qabs (Qone / (e - f - g + h)));[apply Qle_Qmax4_4|apply (f_equal Qabs); field; ring_exact_Q H1].
Qed.

Lemma upper_bound_Tensor_Moebius_Q_l_determinant:  forall xi (H_xi:Is_refining_T xi),
  { W : Q | Zero < W /\ forall  x, -Qone<=x/\x<=Qone -> Qabs (Determinant (Tensor_Moebius_Q_l xi x))< W }.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) H_xi.
 unfold Determinant, Tensor_Moebius_Q_l, fst, snd.
 set (W1 := Qmax4 ((Qabs (a*f)) + Qabs (a*h+f*c) + c*h) (-(Qabs (a*f)) + -Qabs (a*h+f*c) + c*h) 
                  (-(Qabs (b*e)) + -Qabs (b*g+e*d) + d*g) ((Qabs (b*e)) + Qabs (b*g+e*d) + d*g)).
 set (W2 := Qmin4 ((Qabs (a*f)) + Qabs (a*h+f*c) + c*h) (-(Qabs (a*f)) + -Qabs (a*h+f*c) + c*h) 
                  (-(Qabs (b*e)) + -Qabs (b*g+e*d) + d*g) ((Qabs (b*e)) + Qabs (b*g+e*d) + d*g)).
 exists ((W1-W2)+Qone); split.
  apply Qle_lt_reg_pos; auto; apply Qle_Qminus_Zero; subst W1 W2; apply Qmin4_Qmax4_Qle.
  intros x [Hxl Hxu].
  apply Qle_lt_trans with (W1-W2); [|apply Qlt_Zero_Qminus; stepr Qone; auto; ring].
  apply Qabs_Qminus_bound; unfold W1,W2.
   apply Qle_trans with (- Qabs (a*f) + -Qabs (a*h+f*c) + c*h); 
   [apply Qle_Qmin4_2| apply (lower_bound_affine_base_interval_twice a c f h); assumption].
   apply Qle_trans with ( Qabs (a*f) + Qabs (a*h+f*c) + c*h); 
   [apply (upper_bound_affine_base_interval_twice a c f h); assumption|apply Qle_Qmax4_1].
   apply Qle_trans with (-(Qabs (b*e)) + -Qabs (b*g+e*d) + d*g); 
   [apply Qle_Qmin4_3| apply (lower_bound_affine_base_interval_twice b d e g); assumption].
   apply Qle_trans with ((Qabs (b*e)) + Qabs (b*g+e*d) + d*g); 
   [apply (upper_bound_affine_base_interval_twice b d e g); assumption|apply Qle_Qmax4_4].
Qed.

Lemma upper_bound_Tensor_Moebius_Q_r_determinant:  forall xi (H_xi:Is_refining_T xi),
  { W : Q | Zero < W /\ forall  y, -Qone<=y/\y<=Qone -> Qabs (Determinant (Tensor_Moebius_Q_r xi y))< W }.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) H_xi.
 unfold Determinant, Tensor_Moebius_Q_r, fst, snd.
 set (W1 := Qmax4 ((Qabs (a*g)) + Qabs (a*h+g*b) + b*h) (-(Qabs (a*g)) + -Qabs (a*h+g*b) + b*h) 
                  (-(Qabs (c*e)) + -Qabs (c*f+e*d) + d*f) ((Qabs (c*e)) + Qabs (c*f+e*d) + d*f)).
 set (W2 := Qmin4  ((Qabs (a*g)) + Qabs (a*h+g*b) + b*h) (-(Qabs (a*g)) + -Qabs (a*h+g*b) + b*h) 
                  (-(Qabs (c*e)) + -Qabs (c*f+e*d) + d*f) ((Qabs (c*e)) + Qabs (c*f+e*d) + d*f)).
 exists ((W1-W2)+Qone); split.
  apply Qle_lt_reg_pos; auto; apply Qle_Qminus_Zero; subst W1 W2; apply Qmin4_Qmax4_Qle.
  intros y [Hyl Hyu].
  apply Qle_lt_trans with (W1-W2); [|apply Qlt_Zero_Qminus; stepr Qone; auto; ring].
  apply Qabs_Qminus_bound; unfold W1,W2.
   apply Qle_trans with (-(Qabs (a*g)) + -Qabs (a*h+g*b) + b*h);
   [apply Qle_Qmin4_2| apply (lower_bound_affine_base_interval_twice a b g h); assumption].
   apply Qle_trans with ((Qabs (a*g)) + Qabs (a*h+g*b) + b*h);
   [apply (upper_bound_affine_base_interval_twice a b g h); assumption|apply Qle_Qmax4_1].
   apply Qle_trans with (-(Qabs (c*e)) + -Qabs (c*f+e*d) + d*f);
   [apply Qle_Qmin4_3| apply (lower_bound_affine_base_interval_twice c d e f); assumption].
   apply Qle_trans with ((Qabs (c*e)) + Qabs (c*f+e*d) + d*f);
   [apply (upper_bound_affine_base_interval_twice c d e f); assumption|apply Qle_Qmax4_4].
Qed.

Lemma upper_bound_Tensor_Moebius_Q_l_relative: forall xi (H_xi:Is_refining_T xi) x y1 y2, 
  -Qone<=x/\x<=Qone -> -Qone<=y1/\y1<=Qone -> -Qone<=y2/\y2<=Qone ->  
     Qabs ((as_Tensor_Q xi x y1)-(as_Tensor_Q xi x y2)) =
       (Qabs (Determinant (Tensor_Moebius_Q_l xi x))) * (Qabs (y1-y2)) *
       (Qabs(as_Moebius_Q  (eta_discriminant (Tensor_Moebius_Q_l xi x)) y1)
        *Qabs(as_Moebius_Q  (eta_discriminant (Tensor_Moebius_Q_l xi x)) y2)).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) [H_bound _] x y1 y2 [Hxl Hxu] [Hy1l Hy1u] [Hy2l Hy2u];
 assert (H_denom1:e * x * y1 + f * x + g * y1 + h <> Zero);
 [apply Q_to_R_Qneq; realify_Q; intros; apply Bounded_T_nonzero_denum with a b c d; trivial; split; trivial|];
 assert (H_denom2:e * x * y2 + f * x + g * y2 + h <> Zero);
 [apply Q_to_R_Qneq; realify_Q; intros; apply Bounded_T_nonzero_denum with a b c d; trivial; split; trivial|];
 unfold as_Tensor_Q, Tensor_Moebius_Q_l, as_Moebius_Q, eta_discriminant, Determinant, fst, snd;
 qZ_numerals; repeat rewrite <- Qabs_Qmult; repeat rewrite Qminus_Qdiv; trivial; apply (f_equal Qabs);
 field; repeat split; auto; [ring_exact_Q H_denom2|ring_exact_Q H_denom1].
Qed.

Lemma upper_bound_Tensor_Moebius_Q_r_relative: forall xi (H_xi:Is_refining_T xi) x1 x2 y, 
  -Qone<=x1/\x1<=Qone -> -Qone<=x2/\x2<=Qone -> -Qone<=y/\y<=Qone ->  
     Qabs ((as_Tensor_Q xi x1 y)-(as_Tensor_Q xi x2 y)) =
       (Qabs (Determinant (Tensor_Moebius_Q_r xi y))) * (Qabs (x1-x2)) *
       (Qabs(as_Moebius_Q  (eta_discriminant (Tensor_Moebius_Q_r xi y)) x1)
        *Qabs(as_Moebius_Q  (eta_discriminant (Tensor_Moebius_Q_r xi y)) x2)).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) [H_bound _] x1 x2 y [Hx1l Hx1u] [Hx2l Hx2u] [Hyl Hyu];
 assert (H_denom1:e * x1 * y + f * x1 + g * y + h <> Zero);
 [apply Q_to_R_Qneq; realify_Q; intros; apply Bounded_T_nonzero_denum with a b c d; trivial; split; trivial|];
 assert (H_denom2:e * x2 * y + f * x2 + g * y + h <> Zero);
 [apply Q_to_R_Qneq; realify_Q; intros; apply Bounded_T_nonzero_denum with a b c d; trivial; split; trivial|];
 unfold as_Tensor_Q, Tensor_Moebius_Q_r, as_Moebius_Q, eta_discriminant, Determinant, fst, snd;
 qZ_numerals; repeat rewrite <- Qabs_Qmult; repeat rewrite Qminus_Qdiv; trivial; apply (f_equal Qabs);
 field; repeat split; auto; [ring_exact_Q H_denom2|ring_exact_Q H_denom1].
Qed.

Lemma upper_bound_Tensor_Moebius_Q_l:forall xi (H_xi:Is_refining_T xi),
   {q | Zero < q /\ (forall x y1 y2 (Hx:-Qone<=x/\x<=Qone) (Hy1:-Qone<=y1/\y1<=Qone)(Hy2:-Qone<=y2/\y2<=Qone), 
     Zero < Qabs (y1-y2) -> 
     Qabs ((as_Tensor_Q xi x y1)-(as_Tensor_Q xi x y2)) < q*(Qabs (y1-y2)))}.
Proof.
 intros xi H_xi.
 destruct (upper_bound_Tensor_Moebius_Q_l_eta_discriminant xi H_xi) as [Y [H_Y1 H_Y2]].
 destruct (upper_bound_Tensor_Moebius_Q_l_determinant xi H_xi) as [W [H_W1 H_W2]].
 exists (Y*W); split; auto.
 intros x y1 y2 Hx Hy1 Hy2 Hy12.
 rewrite (upper_bound_Tensor_Moebius_Q_l_relative xi H_xi _ _ _ Hx Hy1 Hy2).
 stepr ((Qabs (y1-y2)) *(W* Y)); [|ring].
 stepl (Qabs (y1 - y2) * ( Qabs (Determinant (Tensor_Moebius_Q_l xi x)) * 
   (Qabs (as_Moebius_Q (eta_discriminant (Tensor_Moebius_Q_l xi x)) y1) * 
    Qabs (as_Moebius_Q (eta_discriminant (Tensor_Moebius_Q_l xi x)) y2)))); [|ring].
 apply Qlt_reg_mult_pos_l; trivial.
 apply Qmult_Qlt_Qle_nonneg_pos_compat; trivial.
  apply H_W2; assumption.
  apply H_Y2; assumption.
  apply Qabs_nonneg.
Qed.

Lemma upper_bound_Tensor_Moebius_Q_r:forall xi (H_xi:Is_refining_T xi),
   {q | Zero < q /\ (forall x1 x2 y (Hx1:-Qone<=x1/\x1<=Qone) (Hx2:-Qone<=x2/\x2<=Qone) (Hy:-Qone<=y/\y<=Qone), 
     Zero < Qabs (x1-x2) ->
     Qabs ((as_Tensor_Q xi x1 y)-(as_Tensor_Q xi x2 y)) < q*(Qabs (x1-x2)))}.
Proof.
 intros xi H_xi.
 destruct (upper_bound_Tensor_Moebius_Q_r_eta_discriminant xi H_xi) as [Y [H_Y1 H_Y2]].
 destruct (upper_bound_Tensor_Moebius_Q_r_determinant xi H_xi) as [W [H_W1 H_W2]].
 exists (Y*W); split; auto.
 intros x1 x2 y Hx1 Hx2 Hy Hx12.
 rewrite (upper_bound_Tensor_Moebius_Q_r_relative xi H_xi _ _ _ Hx1 Hx2 Hy).
 stepr ((Qabs (x1-x2)) *(W* Y)); [|ring].
 stepl (Qabs (x1 - x2) * ( Qabs (Determinant (Tensor_Moebius_Q_r xi y)) * 
   (Qabs (as_Moebius_Q (eta_discriminant (Tensor_Moebius_Q_r xi y)) x1) * 
    Qabs (as_Moebius_Q (eta_discriminant (Tensor_Moebius_Q_r xi y)) x2)))); [|ring].
 apply Qlt_reg_mult_pos_l; trivial.
 apply Qmult_Qlt_Qle_nonneg_pos_compat; trivial.
  apply H_W2; assumption.
  apply H_Y2; assumption.
  apply Qabs_nonneg.
Qed.

Lemma upper_bound_diameter2:forall (eps:Q) xi (H_xi:Is_refining_T xi) (H_eps:Zero < eps),
   { theta1:Q & {theta2 | Zero<theta1/\Zero<theta2/\ (forall  x1 y1 x2 y2 
     (Hx1:-Qone<=x1/\x1<=Qone) (Hy1:-Qone<=y1/\y1<=Qone) (Hx2:-Qone<=x2/\x2<=Qone) (Hy2:-Qone<=y2/\y2<=Qone), 
     Qabs (x1-x2)<theta1 -> Qabs (y1-y2)<theta2 -> Qabs ((as_Tensor_Q xi x1 y1)-(as_Tensor_Q xi x2 y2)) < eps)}}.
Proof.
 intros eps xi H_xi H_eps.
 destruct (upper_bound_Tensor_Moebius_Q_l _ H_xi) as [Kl [HKl_1 HKl_2]].
 destruct (upper_bound_Tensor_Moebius_Q_r _ H_xi) as [Kr [HKr_1 HKr_2]].
 exists (eps/(2*Kr)); exists (eps/(2*Kl)); repeat split;
 [ qZ_numerals; unfold Qdiv; auto
 | qZ_numerals; unfold Qdiv; auto
 | ].
 intros x1 y1 x2 y2 Hx1 Hy1 Hx2 Hy2 Hx1x2 Hy1y2.
 stepl (Qabs ((as_Tensor_Q xi x1 y1 - as_Tensor_Q xi x2 y1)+(as_Tensor_Q xi x2 y1 - as_Tensor_Q xi x2 y2)));
 [|apply (f_equal Qabs); ring].
 apply Qle_lt_trans with ((Qabs (as_Tensor_Q xi x1 y1 - as_Tensor_Q xi x2 y1))
                          +(Qabs (as_Tensor_Q xi x2 y1 - as_Tensor_Q xi x2 y2))); [apply Qabs_triangle|]. 
 stepr ((eps/2)*Qone+(eps/2)*Qone); [|qZ_numerals; field; auto].
 destruct (Qle_lt_eq_dec _ _ (Qabs_nonneg (x1-x2))) as [Habsx|Habsx];
 destruct (Qle_lt_eq_dec _ _ (Qabs_nonneg (y1-y2))) as [Habsy|Habsy].
  apply Qlt_plus_plus;
  [ apply Qlt_transitive with  (Kr * Qabs (x1 - x2)); [apply (HKr_2 x1 x2 y1); assumption|]
  | apply Qlt_transitive with  (Kl * Qabs (y1 - y2)); [apply (HKl_2 x2 y1 y2); assumption|]
  ]; rewrite Qmult_sym; apply Qdiv_Qmult_pos; auto; rewrite Qdiv_Qdiv_Qmult_numerator; auto;
  [ stepl (Qabs (x1 - x2)) | stepl (Qabs (y1 - y2))]; trivial; field; auto... 

  apply Qlt_plus_plus;
  [ apply Qlt_transitive with  (Kr * Qabs (x1 - x2)); [apply (HKr_2 x1 x2 y1); assumption|];
    rewrite Qmult_sym; apply Qdiv_Qmult_pos; auto; rewrite Qdiv_Qdiv_Qmult_numerator; auto;
    stepl (Qabs (x1 - x2)); trivial; field; auto
  | stepl Zero; 
    [ qZ_numerals; unfold Qdiv; auto
    | rewrite (Qabs_Qminus_Zero_eq _ _ (sym_eq Habsy)); symmetry; apply Qabs_Zero_Qminus_eq; reflexivity
    ]
  ]...
   
  apply Qlt_plus_plus;
  [ stepl Zero; 
    [ qZ_numerals; unfold Qdiv; auto
    | rewrite (Qabs_Qminus_Zero_eq _ _ (sym_eq Habsx)); symmetry; apply Qabs_Zero_Qminus_eq; reflexivity
    ]
  | apply Qlt_transitive with  (Kl * Qabs (y1 - y2)); [apply (HKl_2 x2 y1 y2); assumption|];
    rewrite Qmult_sym; apply Qdiv_Qmult_pos; auto; rewrite Qdiv_Qdiv_Qmult_numerator; auto;
    stepl (Qabs (y1 - y2)); trivial; field; auto
  ]...

  apply Qlt_plus_plus;
  [ stepl Zero; 
    [ qZ_numerals; unfold Qdiv; auto
    | rewrite (Qabs_Qminus_Zero_eq _ _ (sym_eq Habsx)); symmetry; apply Qabs_Zero_Qminus_eq; reflexivity
    ]
  | stepl Zero; 
    [ qZ_numerals; unfold Qdiv; auto
    | rewrite (Qabs_Qminus_Zero_eq _ _ (sym_eq Habsy)); symmetry; apply Qabs_Zero_Qminus_eq; reflexivity
    ]
  ]...
Qed.

(* I_1=[x_1,x_2], I_2=[y_1,y_2] *)
Lemma thesis_5_6_19:forall (eps:Q)  xi H_xi, Zero < eps ->
  { theta1:Q & {theta2 | Zero<theta1/\Zero<theta2/\ (forall x1 y1 x2 y2 (Hx1:-Qone<=x1/\x1<=Qone) (Hy1:-Qone<=y1/\y1<=Qone)
   (Hx2:-Qone<=x2/\x2<=Qone) (Hy2:-Qone<=y2/\y2<=Qone), 
    Qabs (x1-x2)<theta1 -> Qabs (y1-y2)<theta2 ->diameter2 xi H_xi x1 y1 x2 y2 Hx1 Hy1 Hx2 Hy2 < eps) }}.
Proof.
 intros eps xi H_xi H_eps.
 destruct (upper_bound_diameter2 eps xi H_xi H_eps) as [theta1 [theta2 [H_theta1 [H_theta2 H_theta]]]].
 exists theta1; exists theta2; repeat split; trivial.
 intros x1 y1 x2 y2 Hx1 Hy1 Hx2 Hy2 H_x1y1 H_x2y2.
 unfold diameter2.
 assert (H_x1x1:Qabs (x1 - x1) < theta1); [stepl (Qabs Zero); trivial; apply (f_equal Qabs); ring|].
 assert (H_y1y1:Qabs (y1 - y1) < theta2); [stepl (Qabs Zero); trivial; apply (f_equal Qabs); ring|].
 assert (H_x2x2:Qabs (x2 - x2) < theta1); [stepl (Qabs Zero); trivial; apply (f_equal Qabs); ring|].
 assert (H_y2y2:Qabs (y2 - y2) < theta2); [stepl (Qabs Zero); trivial; apply (f_equal Qabs); ring|].
 assert (H_x2x1:Qabs (x2 - x1) < theta1); [rewrite Qabs_Qminus_sym; trivial|].
 assert (H_y2y1:Qabs (y2 - y1) < theta2); [rewrite Qabs_Qminus_sym; trivial|].
 set (xi_ll:= as_Tensor_Q xi x1 y1); set (xi_lr:= as_Tensor_Q xi x1 y2);
 set (xi_rl:= as_Tensor_Q xi x2 y1); set (xi_rr:= as_Tensor_Q xi x2 y2). 
 destruct (Qmax4_informative xi_ll xi_lr xi_rl xi_rr) as [[[Hmax|Hmax]|Hmax]|Hmax];
 destruct (Qmin4_informative xi_ll xi_lr xi_rl xi_rr) as [[[Hmin|Hmin]|Hmin]|Hmin]; 
 rewrite Hmax; rewrite Hmin; unfold xi_ll, xi_lr, xi_rl, xi_rr;
 match goal with 
 | |- as_Tensor_Q xi ?X1 ?Y1 - as_Tensor_Q xi ?X2 ?Y2 < eps  =>  
  apply Qle_lt_trans with (Qabs (as_Tensor_Q xi X1 Y1 - as_Tensor_Q xi X2 Y2)); 
  [apply Qle_Qabs| apply (H_theta X1 Y1 X2 Y2)]; trivial
 end.
Qed.

Theorem thesis_5_6_10':forall xi alpha beta, Is_refining_T xi->{n:nat & {d| Incl_T (product_init_zip xi alpha beta n) d}}. 
Proof.
 intros xi alpha beta H_refining.
 destruct (thesis_5_6_19 redundancy xi H_refining redundancy_pos) as [theta1 [theta2 [H1 [H2 H_theta]]]].
 set (q1:=(2/theta1)).
 set (q2:=(2/theta2)).
 destruct (Q_Archimedean_nat_inf q1) as [n1 Hn1].
 destruct (Q_Archimedean_nat_inf q2) as [n2 Hn2].
 set (n:=Max.max n1 n2).
 assert (Hnn1:=Max.le_max_l n1 n2: (n1<=n)%nat).
 assert (Hnn2:=Max.le_max_r n1 n2: (n2<=n)%nat).
 assert (H_mu_l:=Is_refining_M_product_init_pure alpha n).
 assert (H_mu_r:=Is_refining_M_product_init_pure beta n).
 assert (H_prod:=Is_refining_T_left_right_product _ _ _ H_refining H_mu_l H_mu_r).
 exists n.
 generalize (ub_is_in_base_interval n alpha).
 generalize (lb_is_in_base_interval n alpha).
 generalize (ub_is_in_base_interval n beta).
 generalize (lb_is_in_base_interval n beta).
 set (u1:=ub alpha n).
 set (l1:=lb alpha n).
 set (u2:=ub beta n).
 set (l2:=lb beta n).
 intros H_l2 H_u2 H_l1 H_u1.
 assert (H_ul1':Qabs (u1 - l1) < theta1).
  unfold u1,l1; rewrite Qabs_eq_pos; [|apply Qlt_Qminus_Zero; apply lb_lt_ub_pointwise];
  apply Qle_lt_trans with (2%nat / (n + 1%nat)); [apply thesis_5_7_9|];
  stepl (2/(n + 1%nat)); trivial; apply Qle_lt_trans with (2/(n1 + 1%nat)).
   let t_local:=natq_zero; apply Z_to_Qlt; apply inj_lt; auto with arith in
   apply Qmult_Qdiv_pos_Qle; [natq_S n; t_local|natq_S n1; t_local| ];
   apply Qle_Zero_Qminus; qnat_S n; qnat_S n1; stepr (2*(n-n1)); [|ring];
   apply Qle_mult_nonneg_nonneg; auto; apply Qle_Qminus_Zero; apply Z_to_Qle; apply inj_le; trivial.
   revert Hn1; unfold q1; intros Hn1; apply Qmult_pos_Qdiv_Qlt;
   [| rewrite Qmult_sym; stepl (2*Qone); [|ring]; apply Qdiv_Qmult_pos; auto;
      stepr (n1 + 1%nat); [|field; auto]; apply Qle_lt_trans with n1; trivial
   ]; natq_S n1; natq_zero; apply Z_to_Qlt; apply inj_lt; auto with arith. 
 assert (H_ul1:Qabs (l1 - u1) < theta1);[rewrite Qabs_Qopp; stepl (Qabs (u1-l1)); trivial; apply (f_equal Qabs); ring|].
 assert (H_ul2':Qabs (u2 - l2) < theta2).
  unfold u2,l2; rewrite Qabs_eq_pos; [|apply Qlt_Qminus_Zero; apply lb_lt_ub_pointwise];
  apply Qle_lt_trans with (2%nat / (n + 1%nat)); [apply thesis_5_7_9|];
  stepl (2/(n + 1%nat)); trivial; apply Qle_lt_trans with (2/(n2 + 1%nat)).
   let t_local:=natq_zero; apply Z_to_Qlt; apply inj_lt; auto with arith in
   apply Qmult_Qdiv_pos_Qle; [natq_S n; t_local|natq_S n2; t_local| ];
   apply Qle_Zero_Qminus; qnat_S n; qnat_S n1; stepr (2*(n-n2)); [|ring];
   apply Qle_mult_nonneg_nonneg; auto; apply Qle_Qminus_Zero; apply Z_to_Qle; apply inj_le; trivial.
   revert Hn2; unfold q1; intros Hn2; apply Qmult_pos_Qdiv_Qlt;
   [| rewrite Qmult_sym; stepl (2*Qone); [|ring]; apply Qdiv_Qmult_pos; auto;
      stepr (n2 + 1%nat); [|field; auto]; apply Qle_lt_trans with n2; trivial
   ]; natq_S n2; natq_zero; apply Z_to_Qlt; apply inj_lt; auto with arith.
 assert (H_ul2:Qabs (l2 - u2) < theta2);[rewrite Qabs_Qopp; stepl (Qabs (u2-l2)); trivial; apply (f_equal Qabs); ring|].

 generalize (H_theta l1 l2 u1 u2 H_l1 H_l2 H_u1 H_u2 H_ul1 H_ul2).
 revert H_l2 H_u2 H_l1 H_u1; unfold u1,l1,u2,l2; 
 repeat rewrite <- product_init_pure_ub; repeat rewrite <- product_init_pure_lb; intros H_l2 H_u2 H_l1 H_u1.
 rewrite <- (diameter2_product _ _ _ H_refining H_prod H_mu_l H_mu_r H_l1 H_l2 H_u1 H_u2).
 intros H_diam.
 destruct (thesis_5_6_20 _ _ H_diam) as [d Hd].
 exists d.
 rewrite product_init_zip_product_init_pure; assumption.
Qed.

Close Scope Z_scope.
Close Scope Q_scope.


Lemma semantic_modulus_q: forall xi alpha beta, Is_refining_T xi -> 
  {n:nat & { d | Incl_T (product_init_zip xi alpha beta n) d /\
                      (forall m d', (m<n)%nat ->~Incl_T (product_init_zip xi alpha beta m) d') } }.
Proof.
 intros xi alpha beta H_r.
 apply LNP_sigS_nat_Digit.
  intros n d; apply Incl_T_dec_D.
  apply thesis_5_6_10'; assumption.
Qed.

Lemma semantic_modulus_q_S_product:forall n n' xi alpha beta (H_r:Is_refining_T xi) H_r', 
   let smodu':=semantic_modulus_q (right_product (left_product xi (map_digits (hd alpha))) (map_digits (hd beta))) 
                                  (tl alpha) (tl beta) H_r' in
    let smodu:=semantic_modulus_q xi alpha beta H_r in
      (0 < n)%nat -> n' = projT1 smodu' -> n = projT1 smodu -> n =  S n'.
Proof.
 destruct n; intros n' xi alpha beta H_r H_r' smodu' smodu Hn_pos Hn' Hn; [inversion  Hn_pos |].
 set (d:=(proj1_sig (projT2 smodu)));
 set (d':=(proj1_sig (projT2 smodu')));
 assert (Hd:d=(proj1_sig (projT2 smodu))); trivial;
 assert (Hd':d'=(proj1_sig (projT2 smodu'))); trivial;
 destruct (proj2_sig (projT2 smodu)) as [H1 H3];
 destruct (proj2_sig (projT2 smodu')) as [H1' H3'].
 rewrite_all <- Hd; rewrite_all <- Hd'; rewrite_all <- Hn; rewrite_all <- Hn'.
 apply eq_S.
 destruct (lt_eq_lt_dec n n') as [[Hnn'|Hnn']|Hnn']; trivial.
  generalize (H3' n d Hnn');
  rewrite_all (product_init_zip_folds xi alpha beta n);
  contradiction...
  generalize (lt_n_S _ _ Hnn'); intros Hnn'_S;
  generalize (H3 (S n') d' Hnn'_S);
  rewrite (product_init_zip_folds xi alpha beta n');
  contradiction...
Qed.

Lemma Is_refining_T_emits_q_pointwise: forall n xi alpha beta H_r, 
    let smodu:=semantic_modulus_q xi alpha beta H_r in
       n = projT1 smodu ->  emits_q xi alpha beta.
Proof.
 induction n;
 intros xi alpha beta H_r smodu Hn;
 set (n':=projS1 smodu);
 set (d:=(proj1_sig (projT2 smodu)));
 assert (Hn':n'=(projT1 smodu)); trivial;
 assert (Hd:d=(proj1_sig (projT2 smodu))); trivial;
 destruct (proj2_sig (projT2 smodu)) as [H1 H3].
 (* O *)
  simpl in H1.
  case (Incl_T_dec_D xi LL); intros t_l.
   constructor 1; trivial.
   case (Incl_T_dec_D xi RR); intros t_r.
    constructor 2; trivial.
    case (Incl_T_dec_D xi MM); intros t_m.
     constructor 3; trivial.
     rewrite_all <- Hd; rewrite_all <- Hn'; rewrite_all <- Hn; destruct d; contradiction.
 (* S n *)
 rewrite_all <- Hd; rewrite_all <- Hn.
 generalize (H3 O LL (lt_O_Sn _));  generalize (H3 O RR (lt_O_Sn _));  generalize (H3 O MM (lt_O_Sn _)).
 simpl; intros t_m t_r t_l.
 constructor 4; trivial.
 apply (IHn (right_product (left_product xi (hd alpha)) (hd beta)) (tl alpha) (tl beta)
            (Is_refining_T_product_hd _ _ _ H_r)).
 apply eq_add_S.
 apply (semantic_modulus_q_S_product (S n) 
          (projT1 (semantic_modulus_q (right_product (left_product xi (hd alpha)) (hd beta)) (tl alpha) (tl beta)
                                      (Is_refining_T_product_hd _ _ _ H_r)))
          xi alpha beta H_r (Is_refining_T_product_hd _ _ _ H_r)); trivial.
  apply lt_O_Sn.
Qed.

Lemma Is_refining_T_emits_q: forall xi alpha beta, Is_refining_T xi -> emits_q xi alpha beta.
Proof.
 intros xi alpha beta H_r.
 set (smodu:=semantic_modulus_q xi alpha beta H_r).
 set (n:=projS1 smodu).
 assert (Hn:n=(projT1 smodu)); trivial.
 apply Is_refining_T_emits_q_pointwise with n H_r; trivial.
Qed.

Lemma Is_refining_T_depth_q:forall n xi alpha beta (H_r:Is_refining_T xi), 
   let smodu:=semantic_modulus_q xi alpha beta H_r in
     n= projS1 smodu ->  depth_q xi alpha beta (Is_refining_T_emits_q xi alpha beta H_r) = n.
Proof.
 induction n; intros xi alpha beta H_r smodu Hn;
 set (d:=(proj1_sig (projT2 smodu)));
 assert (Hd':d=(proj1_sig (projT2 smodu))); trivial;
 destruct (proj2_sig (projT2 smodu)) as [H1 H3].
  (* 0 *)
  revert H1; rewrite <- Hd'; rewrite <- Hn; intros H1.
  case (Incl_T_dec_D xi LL); intros t_l.
   apply depth_q_L; trivial.
   case (Incl_T_dec_D xi RR); intros t_r.
    apply depth_q_R; trivial.
    case (Incl_T_dec_D xi MM); intros t_m.
     apply depth_q_M; trivial.
     destruct d; contradiction.
  (* S n *)
  generalize H1 (H3 O); clear H1 H3; rewrite <- Hd'; rewrite <- Hn; intros H1 H3.
  case (Incl_T_dec_D xi LL); intros t_l.
   rewrite depth_q_L; trivial; generalize (H3 LL (lt_O_Sn _)); simpl; intros H4; contradiction. 
   case (Incl_T_dec_D xi RR); intros t_r.
    rewrite depth_q_R; trivial; generalize (H3 RR (lt_O_Sn _)); simpl; intros H4; contradiction. 
    case (Incl_T_dec_D xi MM); intros t_m.
     rewrite depth_q_M; trivial; generalize (H3 MM (lt_O_Sn _)); simpl; intros H4; contradiction. 

     set (smodu':=semantic_modulus_q (right_product (left_product xi (map_digits (hd alpha))) (map_digits (hd beta)))
                                     (tl alpha) (tl beta) (Is_refining_T_product_hd _ _ _ H_r)).
     generalize (semantic_modulus_q_S_product  (S n) (projT1 smodu') _ alpha beta H_r(Is_refining_T_product_hd _ _ _ H_r)).
     intros H_Sn.
     rewrite (depth_q_absorbs _ _ _ (Is_refining_T_emits_q xi alpha beta H_r) t_l t_r t_m
                 (Is_refining_T_emits_q _ (tl alpha) (tl beta) (Is_refining_T_product_hd xi alpha beta H_r))).
     apply eq_S.
     apply IHn.
     rewrite (eq_add_S _ _ (H_Sn (lt_O_Sn _) (refl_equal _) Hn)); trivial.
Qed.

Lemma Is_refining_T_modulus_q:forall xi alpha beta (H_r:Is_refining_T xi), 
  let modu:=modulus_q xi alpha beta (Is_refining_T_emits_q xi alpha beta H_r) in
   let xi' := fstT (sndT modu) in 
      Is_refining_T xi'.
Proof.
 intros xi alpha beta H_r.
 set (smodu:=semantic_modulus_q xi alpha beta H_r).
 set (n:=projS1 smodu).
 set (d':=(proj1_sig (projT2 smodu))).
 assert (Hn:n=(projT1 smodu)); trivial.
 assert (Hd':d'=(proj1_sig (projT2 smodu))); trivial.
 assert (H_depth: depth_q xi alpha beta (Is_refining_T_emits_q xi alpha beta H_r) = n);[apply (Is_refining_T_depth_q n _ alpha beta H_r Hn)|].
 destruct (depth_q_modulus_q xi alpha beta (Is_refining_T_emits_q xi alpha beta H_r) n (Is_refining_T_depth_q n _ _ _ _ Hn)) as [d Hd].
 destruct (proj2_sig (projS2 smodu)) as [H_Incl _].
 rewrite Hd; simpl.
 apply Incl_T_absorbs_Is_refining_T.
 destruct (depth_q_Incl_T_inf_strong_general _ _ _ (Is_refining_T_emits_q xi alpha beta H_r) n H_depth) as [d'' [Hd''1 Hd''2]].
 revert Hd''2.
 rewrite Hd; simpl.
 intros Hd''2. 
 subst d''.
 assumption.
Qed.

Lemma Is_refining_T_step_productive_q: forall n xi alpha beta, Is_refining_T xi -> step_productive_q n xi alpha beta.
Proof.
 induction n;
 intros xi alpha beta H_refining.
 (* 0 *) constructor; apply Is_refining_T_emits_q; trivial.
 (* S *) apply (step_productive_q_S n _ _ _ (Is_refining_T_emits_q _ alpha beta H_refining)).
 apply IHn.
 apply (Is_refining_T_modulus_q _ alpha beta H_refining).
Qed.

Lemma Is_refining_T_productive_q: forall xi alpha beta, Is_refining_T xi -> productive_q xi alpha beta.
Proof.
 intros xi alpha beta H_refining.
 constructor; intros n; apply Is_refining_T_step_productive_q; trivial.
Qed. 
