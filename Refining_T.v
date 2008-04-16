(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import digits.
Require Import Refining_M.
Require Import Bounded_T.
Require Import R_addenda.
Require Import Fourier_solvable_ineqs.
Require Import Fourier.

(** Properties of the predicate [Refining_M]. *)

Open Scope Q_scope.

Lemma Bounded_T_auxiliary_5:forall e f g h x y, 
Zero <= e + f + g + h -> Zero <= e - f - g + h -> Zero <= - e - f + g + h -> Zero <= - e + f - g + h  ->
                                        (-1<=x<=1)%R->(-1<=y<=1)%R->(0<=e*x*y+f*x+g*y+h)%R.
Proof.
 intros e f g h x y H1 H2 H3 H4 Hx Hy.
  (* TP: Zero <= h-f *)
  assert (H_hf1:Zero<=h-f);
  [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepl Zero; auto; stepr ((e-f-g+h)+(-e-f+g+h)); auto; ring|].
  (* TP: Zero <= h+f *)
  assert (H_hf2:Zero<=h+f); 
  [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepl Zero; auto; stepr ((e+f+g+h)+(-e+f-g+h)); auto; ring|].
  (* TP: Zero <= h-g *)
  assert (H_hg1:Zero<=h-g); 
  [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepl Zero; auto; stepr ((e-f-g+h)+(-e+f-g+h)); auto; ring|].
  assert (H_hg2:Zero<=h+g); 
  [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepl Zero; auto; stepr ((e+f+g+h)+(-e-f+g+h)); auto; ring|].
  stepr ((e*y+f)*x+ (g*y+h))%R; [|ring].

  destruct (Rtrichotomy_inf 0 (e*y+f)) as [[Hef|Hef]|Hef]. 
   (* 0<ey+f *)
   apply Bounded_M_pos_auxiliary_3; trivial;
   stepr (Qminus g e * y + Qminus h f)%R; [|realify_Q_goal; ring];
    apply Bounded_M_auxiliary_5; trivial; [ring_exact_Q H3|ring_exact_Q H2].
   (* ey+f=0 *)
   rewrite <- Hef; stepr (g*y+h)%R; [|ring]; apply Bounded_M_auxiliary_5; assumption.
   (* ey+f<0 *)
   apply Bounded_M_pos_auxiliary_4; trivial;
   stepr (Qplus g e * y + Qplus h f)%R; [|realify_Q_goal; ring].
    apply Bounded_M_auxiliary_5; trivial; [ring_exact_Q H1|ring_exact_Q H4].
Qed.

Lemma Bounded_T_auxiliary_6:forall e f g h x y,
 e + f + g + h<=Zero ->  e - f - g + h<=Zero ->  - e - f + g + h<=Zero ->  - e + f - g + h<=Zero  ->
                                        (-1<=x<=1)%R->(-1<=y<=1)%R->(e*x*y+f*x+g*y+h<=0)%R.
Proof.
 intros e f g h x y H1 H2 H3 H4 Hx Hy.
  (* TP: h-f <= Zero *)
  assert (H_hf1:h-f<=Zero); 
  [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepr Zero; auto; stepl ((e-f-g+h)+(-e-f+g+h)); auto; ring|].
  (* TP: h+f <= Zero *)
  assert (H_hf2:h+f<=Zero); 
  [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepr Zero; auto; stepl ((e+f+g+h)+(-e+f-g+h)); auto; ring|].
  (* TP: h-g <= Zero *)
  assert (H_hg1:h-g<=Zero); 
  [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepr Zero; auto; stepl ((e-f-g+h)+(-e+f-g+h)); auto; ring|].
  (* TP: h+g < Zero *)
  assert (H_hg2:h+g<=Zero); 
  [apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepr Zero; auto; stepl ((e+f+g+h)+(-e-f+g+h)); auto; ring|].
  stepl ((e*y+f)*x+ (g*y+h))%R; [|ring].

  destruct (Rtrichotomy_inf 0 (e*y+f)) as [[Hef|Hef]|Hef]. 
   (* 0<ey+f *)
   apply Bounded_M_neg_auxiliary_3; trivial;
   stepl (Qplus g e * y + Qplus h f)%R; [|realify_Q_goal; ring];
    apply Bounded_M_auxiliary_6; trivial; [ring_exact_Q H1|ring_exact_Q H4].
   (* ey+f=0 *)
   rewrite <- Hef; stepl (g*y+h)%R; [|ring]; apply Bounded_M_auxiliary_6; assumption.
   (* ey+f<0 *)
   apply Bounded_M_neg_auxiliary_4; trivial;
   stepl (Qminus g e * y + Qminus h f)%R; [|realify_Q_goal; ring];
    apply Bounded_M_auxiliary_6; trivial; [ring_exact_Q H3|ring_exact_Q H2].
Qed.

Lemma Is_refining_T_auxiliary_1: forall (a b c d e f g h:Q),
 Zero <= a + b + c + d + e + f + g + h -> Zero <= - a - b - c - d + e + f + g + h ->
 Zero <= a - b - c + d + e - f - g + h -> Zero <= - a + b + c - d + e - f - g + h ->
 Zero <= - a - b + c + d - e - f + g + h -> Zero <= a + b - c - d - e - f + g + h ->
 Zero <= - a + b - c + d - e + f - g + h -> Zero <= a - b + c - d - e + f - g + h ->
         Zero<=h/\ Zero<=e+f+g+h /\ Zero<=e-f-g+h /\ Zero<=-e-f+g+h /\ Zero<=-e+f-g+h.
Proof.
 let 
 t_local:= apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepl Zero; auto
 in
 ( 
 intros a b c d e f g h H1 H2 H3 H4 H5 H6 H7 H8; repeat split;
 [ apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone+Qone+Qone+Qone+Qone+Qone); auto; stepl Zero; auto;
   stepr ((a + b + c + d + e + f + g + h)+( - a - b - c - d + e + f + g + h)+(a - b - c + d + e - f - g + h)+
           (- a + b + c - d + e - f - g + h)+(- a - b + c + d - e - f + g + h)+(a + b - c - d - e - f + g + h)+
           (- a + b - c + d - e + f - g + h)+(a - b + c - d - e + f - g + h));
   repeat first [apply Qle_plus_pos_pos; trivial]; ring
 | t_local
 | t_local
 | t_local
 | t_local
 ]; idtac).
 stepr ((a + b + c + d + e + f + g + h)+(- a - b - c - d + e + f + g + h)); auto; ring.
 stepr ((a - b - c + d + e - f - g + h)+(- a + b + c - d + e - f - g + h)); auto; ring.
 stepr ((a + b - c - d - e - f + g + h)+(- a - b + c + d - e - f + g + h)); auto; ring.
 stepr ((-a + b - c + d - e + f - g + h)+(a - b + c - d - e + f - g + h)); auto; ring.
Qed.

Lemma Is_refining_T_auxiliary_2: forall (a b c d e f g h:Q),
  a + b + c + d + e + f + g + h<=Zero ->  - a - b - c - d + e + f + g + h<=Zero ->
  a - b - c + d + e - f - g + h<=Zero ->  - a + b + c - d + e - f - g + h<=Zero ->
  - a - b + c + d - e - f + g + h<=Zero ->  a + b - c - d - e - f + g + h<=Zero ->
  - a + b - c + d - e + f - g + h<=Zero ->  a - b + c - d - e + f - g + h<=Zero ->
         h<=Zero/\ e+f+g+h<=Zero/\ e-f-g+h<=Zero /\ -e-f+g+h<=Zero /\ -e+f-g+h<=Zero.
Proof.
 let 
 t_local:= apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto; stepr Zero; auto
 in
 ( 
 intros a b c d e f g h H1 H2 H3 H4 H5 H6 H7 H8; repeat split;
 [ apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone+Qone+Qone+Qone+Qone+Qone); auto; stepr Zero; auto;
   stepl ((a + b + c + d + e + f + g + h)+( - a - b - c - d + e + f + g + h)+(a - b - c + d + e - f - g + h)+
           (- a + b + c - d + e - f - g + h)+(- a - b + c + d - e - f + g + h)+(a + b - c - d - e - f + g + h)+
           (- a + b - c + d - e + f - g + h)+(a - b + c - d - e + f - g + h));
   repeat first [apply Qle_plus_neg_neg; trivial]; ring
 | t_local
 | t_local
 | t_local
 | t_local
 ]; idtac).
 stepl ((a + b + c + d + e + f + g + h)+(- a - b - c - d + e + f + g + h)); auto; ring.
 stepl ((a - b - c + d + e - f - g + h)+(- a + b + c - d + e - f - g + h)); auto; ring.
 stepl ((a + b - c - d - e - f + g + h)+(- a - b + c + d - e - f + g + h)); auto; ring.
 stepl ((-a + b - c + d - e + f - g + h)+(a - b + c - d - e + f - g + h)); auto; ring.
Qed.

Lemma Is_refining_T_h_minusplus_efg_sign_dec: forall a b c d e f g h, Is_refining_T (((a,b),(c,d)),((e,f),(g,h)))-> 
 Zero <= a + b + c + d + e + f + g + h /\ Zero <= - a - b - c - d + e + f + g + h /\
 Zero <= a - b - c + d + e - f - g + h /\ Zero <= - a + b + c - d + e - f - g + h /\
 Zero <= - a - b + c + d - e - f + g + h /\ Zero <= a + b - c - d - e - f + g + h /\
 Zero <= - a + b - c + d - e + f - g + h /\ Zero <= a - b + c - d - e + f - g + h /\
 Zero<e+f+g+h /\ Zero<e-f-g+h /\ Zero< -e-f+g+h /\ Zero< -e+f-g+h /\ Zero<h \/
 a + b + c + d + e + f + g + h <= Zero /\ - a - b - c - d + e + f + g + h <= Zero /\
 a - b - c + d + e - f - g + h <= Zero /\ - a + b + c - d + e - f - g + h <= Zero /\
 - a - b + c + d - e - f + g + h <= Zero /\ a + b - c - d - e - f + g + h <= Zero /\
 - a + b - c + d - e + f - g + h <= Zero /\ a - b + c - d - e + f - g + h <= Zero /\ 
 e+f+g+h<Zero /\ e-f-g+h<Zero /\ -e-f+g+h<Zero /\ -e+f-g+h<Zero /\ h<Zero.
Proof.
 intros a b c d e f g h [[[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]] 
                         [[H5[H6[H7[H8[H9[H10[H11 H12]]]]]]]|[H5[H6[H7[H8[H9[H10[H11 H12]]]]]]]]];
 unfold fst, snd in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12.
  generalize (Bounded_T_auxiliary_1 _ _ _ _ H1 H2 H3 H4); intros Hh; tauto.
  decompose record (Is_refining_T_auxiliary_2  _ _ _ _ _ _ _ _ H5 H6 H7 H8 H9 H10 H11 H12); contradiction.
  decompose record (Is_refining_T_auxiliary_1  _ _ _ _ _ _ _ _ H5 H6 H7 H8 H9 H10 H11 H12); contradiction.
  generalize (Bounded_T_auxiliary_2 _ _ _ _ H1 H2 H3 H4); intros Hh; tauto.
Qed.

Close Scope Q_scope.

Lemma Is_refining_T_denom_nonvanishing_T:forall xi r1 r2, Is_refining_T xi -> ((-1)<=r1<=1)%R ->((-1)<=r2<=1)%R ->
                 denom_nonvanishing_T xi r1 r2.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) r1 r2 H_refining H_r1 H_r2;
 generalize (Is_refining_T_h_minusplus_efg_sign_dec _ _ _ _ _ _ _ _ H_refining);
 generalize H_refining; clear H_refining;
 intros [H_bounded _] [[_[_[_[_[_[_[_[_[H1 [H2 [H3 [H4 H5]]]]]]]]]]]]|[_[_[_[_[_[_[_[_[H1 [H2 [H3 [H4 H5]]]]]]]]]]]]];
 red; simpl.
  apply Rlt_not_eq'; apply (Bounded_T_pos _ _ _ _ _ _ _ _ _ _ H_bounded H5 H_r1 H_r2). 
  apply Rlt_not_eq; apply (Bounded_T_neg _ _ _ _ _ _ _ _ _ _ H_bounded H5 H_r1 H_r2). 
Qed.

Lemma Is_refining_T_property:forall xi r1 r2, ((-1)<=r1<=1)%R->((-1)<=r2<=1)%R->Is_refining_T xi-> 
          ((-1)<=as_Tensor xi r1 r2<=1)%R.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) r1 r2 H_r1 H_r2 H_refining.
 generalize (Is_refining_T_denom_nonvanishing_T _ _ _ H_refining H_r1 H_r2). 
 generalize H_refining; intros [H_bounded _].
 unfold denom_nonvanishing_T, as_Tensor, fst, snd.
 destruct (Is_refining_T_h_minusplus_efg_sign_dec _ _ _ _ _ _ _ _ H_refining)
     as [[H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]]]|
         [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [H11 [H12 H13]]]]]]]]]]]]];
 [ generalize (Is_refining_T_auxiliary_1 _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7 H8)
 | generalize (Is_refining_T_auxiliary_2 _ _ _ _ _ _ _ _ H1 H2 H3 H4 H5 H6 H7 H8)
 ];
 intros [H14 [H15 [H16 [H17 H18]]]] H_denom.
  (* everything is positive *)
   (* TP: 0 < e*r1*r2+f*r1+g*r2+h *)
   assert (H_crd:0<e*r1*r2+f*r1+g*r2+h); [apply Bounded_T_pos with a b c d; trivial|].

   split. 

    (* lower bound *)
    stepl (-1/1); [|field; auto]; apply Rmult_Rdiv_pos_Rle; auto; apply Rle_zero_Rminus;
    stepr ((Qplus e a)*r1*r2+(Qplus f b)*r1+(Qplus g c)*r2+(Qplus h d)); [|realify_Q_goal; ring];
    apply Bounded_T_auxiliary_5; trivial; [ring_exact_Q H1|ring_exact_Q H3|ring_exact_Q H5|ring_exact_Q H7].
    (* upper bound *)
    stepr (1/1); [|field; auto]; apply Rmult_Rdiv_pos_Rle; auto; apply Rle_zero_Rminus;
    stepr ((Qminus e a)*r1*r2+(Qminus f b)*r1+(Qminus g c)*r2+(Qminus h d)); [|realify_Q_goal; ring];
    apply Bounded_T_auxiliary_5; trivial; [ring_exact_Q H2|ring_exact_Q H4|ring_exact_Q H6|ring_exact_Q H8].

  (* everything is negative *)
   (* TP: e*r1*r2+f*r1+g*r2+h<0 *)
   assert (H_crd:e*r1*r2+f*r1+g*r2+h<0); [apply Bounded_T_neg with a b c d; trivial|].

   split. 

    (* lower bound *)
    stepl (1/(-1)); [|field; auto]; apply Rmult_Rdiv_neg_Rle; auto; apply Rminus_le;
    stepl ((Qplus e a)*r1*r2+(Qplus f b)*r1+(Qplus g c)*r2+(Qplus h d)); [|realify_Q_goal; ring].
    apply Bounded_T_auxiliary_6; trivial; [ring_exact_Q H1|ring_exact_Q H3|ring_exact_Q H5|ring_exact_Q H7].
    (* upper bound *)
    stepr (-1/-1); [|field; auto]; apply Rmult_Rdiv_neg_Rle; auto; apply Rminus_le;
    stepl ((Qminus e a)*r1*r2+(Qminus f b)*r1+(Qminus g c)*r2+(Qminus h d)); [|realify_Q_goal; ring];
    apply Bounded_T_auxiliary_6; trivial; [ring_exact_Q H2|ring_exact_Q H4|ring_exact_Q H6|ring_exact_Q H8].
Qed.

Lemma denom_nonvanishing_T_left_right_product:forall xi mu1 mu2 r1 r2, 
         denom_nonvanishing_M mu1 r1->denom_nonvanishing_M mu2 r2->
         ((-1)<=as_Moebius mu1 r1<=1)%R->((-1)<=as_Moebius mu2 r2<=1)%R->
                Is_refining_T xi -> denom_nonvanishing_T (right_product (left_product xi mu1) mu2) r1 r2.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) ((A,B),(C,D)) ((A',B'),(C',D')) r1 r2.
 unfold as_Tensor, as_Moebius, denom_nonvanishing_M, denom_nonvanishing_T, right_product, left_product, fst, snd.
 intros  H_denom1 H_denom2 Hr1 Hr2 H_refining.
 realify_Q_goal.
 stepl (e*(A*r1+B)*(A'*r2+B') + f*(A*r1+B)*(C'*r2+D') + g*(C*r1+D)*(A'*r2+B') + h*(C*r1+D)*(C'*r2+D')); [|ring].
 apply Rbilinear_non_zero_2; auto. 
 apply (Is_refining_T_denom_nonvanishing_T _ _ _ H_refining Hr1 Hr2).
Qed.

Lemma Is_refining_T_Bounded_T_left_right_product:forall xi mu1 mu2,
         Is_refining_M mu1 -> Is_refining_M mu2 -> Bounded_T xi -> 
             Bounded_T (right_product (left_product xi mu1) mu2).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) ((A,B),(C,D)) ((A',B'),(C',D')) H_refining1 H_refining2 H_bounded.
 apply denom_nonvanishing_T_Bounded_T; intros r1 r2 Hr1 Hr2.
 assert (H_mu1:=Is_refining_M_property _ r1 Hr1 H_refining1);
 assert (H_mu2:=Is_refining_M_property _ r2 Hr2 H_refining2).
 generalize (Bounded_T_denom_nonvanishing_T _ H_bounded _ _ H_mu1 H_mu2).
 unfold as_Moebius, denom_nonvanishing_T, right_product, left_product, fst, snd.
 intros H_denom.
 realify_Q_goal.
 stepl (e*(A*r1+B)*(A'*r2+B') + f*(A*r1+B)*(C'*r2+D') + g*(C*r1+D)*(A'*r2+B') + h*(C*r1+D)*(C'*r2+D')); [|ring].
 apply Rbilinear_non_zero_2; auto. 
 apply (Is_refining_M_denom_nonvanishing_M _ _ H_refining1 Hr1).
 apply (Is_refining_M_denom_nonvanishing_M _ _ H_refining2 Hr2).
Qed.

Lemma as_Tensor_right_left_product_as_Moebius:forall xi mu1 mu2 r1 r2, 
             denom_nonvanishing_M mu1 r1->denom_nonvanishing_M mu2 r2 -> 
             ((-1)<=as_Moebius mu1 r1<=1)%R -> ((-1)<=as_Moebius mu2 r2<=1)%R -> Is_refining_T xi -> 
     as_Tensor (right_product (left_product xi mu1) mu2) r1 r2= as_Tensor xi (as_Moebius mu1 r1) (as_Moebius mu2 r2).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) ((A,B),(C,D)) ((A',B'),(C',D')) r1 r2 H_denom1 H_denom2 H_mu_r1 H_mu_r2 H_refining.
 generalize (denom_nonvanishing_T_left_right_product _ _ _ _ _ H_denom1 H_denom2 H_mu_r1 H_mu_r2 H_refining).
 generalize H_denom1 H_denom2; clear H_denom1 H_denom2.
 unfold as_Tensor, as_Moebius, denom_nonvanishing_M, denom_nonvanishing_T, right_product, left_product, fst, snd.
 realify_Q.
 intros  H_denom1 H_denom2 H_denom_prod.
 generalize (Rmult_resp_nonzero _ _ H_denom1 H_denom2); intros H_denom3.
 rewrite (Rmult_assoc a); rewrite (Rmult_assoc e).
 rewrite Rdiv_Rmult_numerator_denominator; trivial.
 repeat rewrite Rdiv_Rmult_numerator; auto.
 repeat rewrite Rplus_Rdiv; auto.
 repeat rewrite Rdiv_Rplus_Rmult; auto.
 rewrite Rdiv_Rdiv_simplify; auto.
  rewrite <- (Rdiv_Rmult_simplify  
    (((a * A + c * C) * A' + (b * A + d * C) * C') * r1 * r2 + ((a * A + c * C) * B' + (b * A + d * C) * D') * r1 +
    ((a * B + c * D) * A' + (b * B + d * D) * C') * r2 + ((a * B + c * D) * B' + (b * B + d * D) * D')) _ 
    _ H_denom3 H_denom_prod).
  apply (f_equal2 Rdiv); ring.
  stepl ((C*r1+D)*(C'*r2+D')* (((e*A+g*C)*A'+(f*A+h*C)*C')*r1*r2+((e*A+g*C)*B'+(f*A+h*C)*D')*r1+
                               ((e*B+g*D)*A'+(f*B+h*D)*C')*r2+((e*B+g*D)*B'+(f*B+h*D)*D'))); auto; ring.
Qed.

Open Scope Z_scope.
Open Scope Q_scope.

Lemma Incl_T_absorbs_Is_refining_T_L:forall xi, Incl_T xi LL -> Is_refining_T (m_product inv_LL xi).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))).
 unfold Incl_T, Is_refining_T, Bounded_T, m_product, inv_digit, map_digits, inv_LL, fst, snd.
 replace ((-1)/2 - 1/2) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace (1/2 + 3/2) with (Qone +Qone); [|qZ_numerals; field; auto];
 replace (3/2 - 1/2) with Qone; [|qZ_numerals; field; auto];
 replace (1/2 + -1/2) with Zero; [|qZ_numerals; field; auto];
 repeat rewrite Qmult_one_right.
 intros [[[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]] [H5 [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]].

  (* Zero < d-c,d+c *)
  generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H5); generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H6);
  generalize (Qmult_resp_Qle_pos_l _ _ _ H3 H7); generalize (Qmult_resp_Qle_pos_l _ _ _ H3 H8); 
  generalize (Qmult_resp_Qle_pos_l _ _ _ H4 H9); generalize (Qmult_resp_Qle_pos_l _ _ _ H4 H10);
  generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H11); generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H12); 
  clear H5 H6 H7 H8 H9 H10 H11 H12; repeat rewrite Qmult_zero_right; intros H5 H6 H7 H8 H9 H10 H11 H12;
  split; left; repeat split.
   (* TP: boundedness *)
   abstract (stepr ((1/2)*((e+f+g+h)-(a+b+c+d))); [|qZ_numerals; field; auto];
    apply Qlt_mult_pos_pos; auto; apply Qlt_Qminus_Zero; apply Qle_lt_trans with Zero; trivial;
    apply Qmult_resp_Qle_pos_r with (Qone+Qone);  auto).
   abstract (stepr ((1/2)*((e-f-g+h)-(a-b-c+d))); [|qZ_numerals; field; auto];
    apply Qlt_mult_pos_pos; auto; apply Qlt_Qminus_Zero; apply Qle_lt_trans with Zero; trivial; 
    apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   abstract(stepr ((1/2)*((-e-f+g+h)-(-a-b+c+d))); [|qZ_numerals; field; auto];
    apply Qlt_mult_pos_pos; auto; apply Qlt_Qminus_Zero; apply Qle_lt_trans with Zero; trivial;
    apply Qmult_resp_Qle_pos_r with (Qone+Qone);  auto).
   abstract (stepr ((1/2)*((-e+f-g+h)-(-a+b-c+d))); [|qZ_numerals; field; auto];
    apply Qlt_mult_pos_pos; auto; apply Qlt_Qminus_Zero; apply Qle_lt_trans with Zero; trivial;
    apply Qmult_resp_Qle_pos_r with (Qone+Qone);  auto).
   (* TP: refining *)
   abstract (stepr ((e+f+g+h)+(a+b+c+d)); [|qZ_numerals; field; auto];
    stepl ((e+f+g+h)+(e+f+g+h)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto).
   abstract (stepr (Zero-((a+b+c+d)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((e-f-g+h)+(a-b-c+d)); [|qZ_numerals; field; auto];
    stepl ((e-f-g+h)+(e-f-g+h)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto).
   abstract (stepr (Zero-((a-b-c+d)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((-e-f+g+h)+(-a-b+c+d)); [|qZ_numerals; field; auto];
    stepl ((-e-f+g+h)+(-e-f+g+h)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto).
   abstract (stepr (Zero-((-a-b+c+d)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((-e+f-g+h)+(-a+b-c+d)); [|qZ_numerals; field; auto];
    stepl ((-e+f-g+h)+(-e+f-g+h)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto).
   abstract (stepr (Zero-((-a+b-c+d)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero; trivial).
  (* d-c,d+c < Zero *)
  generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H5); generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H6);
  generalize (Qmult_resp_Qle_neg_l _ _ _ H3 H7); generalize (Qmult_resp_Qle_neg_l _ _ _ H3 H8); 
  generalize (Qmult_resp_Qle_neg_l _ _ _ H4 H9); generalize (Qmult_resp_Qle_neg_l _ _ _ H4 H10);
  generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H11); generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H12); 
  clear H5 H6 H7 H8 H9 H10 H11 H12; repeat rewrite Qmult_zero_right; intros H5 H6 H7 H8 H9 H10 H11 H12;
  split; right; repeat split.
   (* TP: boundedness *)
   abstract (stepl (((e+f+g+h)-(a+b+c+d))*(1/2)); [|qZ_numerals; field; auto];
    apply Qlt_mult_neg_pos; auto; apply Qlt_Qminus_Zero_neg; apply Qlt_le_trans with Zero; trivial;
    apply Qmult_resp_Qle_pos_r with (Qone+Qone);  auto).
   abstract (stepl (((e-f-g+h)-(a-b-c+d))*(1/2)); [|qZ_numerals; field; auto];
    apply Qlt_mult_neg_pos; auto; apply Qlt_Qminus_Zero_neg; apply Qlt_le_trans with Zero; trivial; 
    apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   abstract (stepl (((-e-f+g+h)-(-a-b+c+d))*(1/2)); [|qZ_numerals; field; auto];
    apply Qlt_mult_neg_pos; auto; apply Qlt_Qminus_Zero_neg; apply Qlt_le_trans with Zero; trivial;
    apply Qmult_resp_Qle_pos_r with (Qone+Qone);  auto).
   abstract (stepl (((-e+f-g+h)-(-a+b-c+d))*(1/2)); [|qZ_numerals; field; auto];
    apply Qlt_mult_neg_pos; auto; apply Qlt_Qminus_Zero_neg; apply Qlt_le_trans with Zero; trivial;
    apply Qmult_resp_Qle_pos_r with (Qone+Qone);  auto).
   (* TP: refining *)
   abstract (stepl ((e+f+g+h)+(a+b+c+d)); [|qZ_numerals; field; auto];
    stepr ((e+f+g+h)+(e+f+g+h)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto).
   abstract (stepl (Zero-((a+b+c+d)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((e-f-g+h)+(a-b-c+d)); [|qZ_numerals; field; auto];
    stepr ((e-f-g+h)+(e-f-g+h)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto).
   abstract (stepl (Zero-((a-b-c+d)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((-e-f+g+h)+(-a-b+c+d)); [|qZ_numerals; field; auto];
    stepr ((-e-f+g+h)+(-e-f+g+h)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto).
   abstract (stepl (Zero-((-a-b+c+d)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((-e+f-g+h)+(-a+b-c+d)); [|qZ_numerals; field; auto];
    stepr ((-e+f-g+h)+(-e+f-g+h)*(Qopp Qone)); [|ring]; apply Qle_plus_plus; auto).
   abstract (stepl (Zero-((-a+b-c+d)*(Qone+Qone))); [|qZ_numerals; field; auto];
    apply Qle_Qminus_Zero_neg; trivial).
Qed.

Lemma Incl_T_absorbs_Is_refining_T_R:forall xi, Incl_T xi RR -> Is_refining_T (m_product inv_RR xi).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))).
 unfold Incl_T, Is_refining_T, Bounded_T, m_product, inv_digit, map_digits, inv_RR, fst, snd.
 replace (1/2 - 1/2) with Zero; [|qZ_numerals; field; auto];
 replace (-1/2 + 3/2) with Qone; [|qZ_numerals; field; auto];
 replace (3/2 - -1/2) with (Qone +Qone); [|qZ_numerals; field; auto];
 replace (1/2 + 1/2) with Qone; [|qZ_numerals; field; auto];
 repeat rewrite Qmult_one_right.
 intros [[[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]] [H5 [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]].

  (* Zero < d-c,d+c *)
  generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H5); generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H6);
  generalize (Qmult_resp_Qle_pos_l _ _ _ H3 H7); generalize (Qmult_resp_Qle_pos_l _ _ _ H3 H8); 
  generalize (Qmult_resp_Qle_pos_l _ _ _ H4 H9); generalize (Qmult_resp_Qle_pos_l _ _ _ H4 H10);
  generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H11); generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H12); 
  clear H5 H6 H7 H8 H9 H10 H11 H12; repeat rewrite Qmult_zero_right; intros H5 H6 H7 H8 H9 H10 H11 H12;
  split; left; repeat split.
   (* TP: boundedness *)
   abstract (stepr ((1/2)*((e+f+g+h)+(a+b+c+d))); [|qZ_numerals; field; auto];
   apply Qlt_mult_pos_pos; auto; apply Qlt_le_reg_pos; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   abstract (stepr ((1/2)*((e-f-g+h)+(a-b-c+d))); [|qZ_numerals; field; auto];
   apply Qlt_mult_pos_pos; auto; apply Qlt_le_reg_pos; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   abstract (stepr ((1/2)*((-e-f+g+h)+(-a-b+c+d))); [|qZ_numerals; field; auto];
   apply Qlt_mult_pos_pos; auto; apply Qlt_le_reg_pos; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   abstract (stepr ((1/2)*((-e+f-g+h)+(-a+b-c+d))); [|qZ_numerals; field; auto];
   apply Qlt_mult_pos_pos; auto; apply Qlt_le_reg_pos; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   (* TP: refining *)
   abstract (stepr ((a+b+c+d)*(Qone+Qone)); trivial; qZ_numerals; field; auto).
   abstract (stepr ((e+f+g+h)-(a+b+c+d)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((a-b-c+d)*(Qone+Qone)); trivial; qZ_numerals; field; auto).
   abstract (stepr ((e-f-g+h)-(a-b-c+d)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((-a-b+c+d)*(Qone+Qone)); trivial; qZ_numerals; field; auto).
   abstract (stepr ((-e-f+g+h)-(-a-b+c+d)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((-a+b-c+d)*(Qone+Qone)); trivial; qZ_numerals; field; auto).
   abstract (stepr ((-e+f-g+h)-(-a+b-c+d)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero; trivial).
  (* d-c,d+c < Zero *)
  generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H5); generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H6);
  generalize (Qmult_resp_Qle_neg_l _ _ _ H3 H7); generalize (Qmult_resp_Qle_neg_l _ _ _ H3 H8); 
  generalize (Qmult_resp_Qle_neg_l _ _ _ H4 H9); generalize (Qmult_resp_Qle_neg_l _ _ _ H4 H10);
  generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H11); generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H12); 
  clear H5 H6 H7 H8 H9 H10 H11 H12; repeat rewrite Qmult_zero_right; intros H5 H6 H7 H8 H9 H10 H11 H12;
  split; right; repeat split.
   (* TP: boundedness *)
   abstract (stepl (((e+f+g+h)+(a+b+c+d))*(1/2)); [|qZ_numerals; field; auto];
   apply Qlt_mult_neg_pos; auto; apply Qlt_le_reg_neg; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   abstract (stepl (((e-f-g+h)+(a-b-c+d))*(1/2)); [|qZ_numerals; field; auto];
   apply Qlt_mult_neg_pos; auto; apply Qlt_le_reg_neg; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   abstract (stepl (((-e-f+g+h)+(-a-b+c+d))*(1/2)); [|qZ_numerals; field; auto];
   apply Qlt_mult_neg_pos; auto; apply Qlt_le_reg_neg; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   abstract (stepl (((-e+f-g+h)+(-a+b-c+d))*(1/2)); [|qZ_numerals; field; auto];
   apply Qlt_mult_neg_pos; auto; apply Qlt_le_reg_neg; trivial; apply Qmult_resp_Qle_pos_r with (Qone+Qone); auto).
   (* TP: refining *)
   abstract (stepl ((a+b+c+d)*(Qone+Qone)); trivial; qZ_numerals; field; auto).
   abstract (stepl ((e+f+g+h)-(a+b+c+d)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((a-b-c+d)*(Qone+Qone)); trivial; qZ_numerals; field; auto).
   abstract (stepl ((e-f-g+h)-(a-b-c+d)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((-a-b+c+d)*(Qone+Qone)); trivial; qZ_numerals; field; auto).
   abstract (stepl ((-e-f+g+h)-(-a-b+c+d)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((-a+b-c+d)*(Qone+Qone)); trivial; qZ_numerals; field; auto).
   abstract (stepl ((-e+f-g+h)-(-a+b-c+d)); [|qZ_numerals; field; auto]; apply Qle_Qminus_Zero_neg; trivial).
Qed.

Lemma Incl_T_absorbs_Is_refining_T_M:forall xi, Incl_T xi MM -> Is_refining_T (m_product inv_MM xi).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))).
 unfold Incl_T, Is_refining_T, Bounded_T, m_product, inv_digit, map_digits, inv_MM, fst, snd.
 replace (0/1 - 1/1) with (Qopp Qone); [|qZ_numerals; field; auto];
 replace (1/1 + 0/1) with Qone; [|qZ_numerals; field; auto];
 replace (3/1 - 0/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 replace (0/1 + 3/1) with (Qone+Qone+Qone); [|qZ_numerals; field; auto];
 repeat rewrite Qmult_one_right.
 intros [[[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]] [H5 [H6 [H7 [H8 [H9 [H10 [H11 H12]]]]]]]].

  (* Zero < d-c,d+c *)
  generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H5); generalize (Qmult_resp_Qle_pos_l _ _ _ H2 H6);
  generalize (Qmult_resp_Qle_pos_l _ _ _ H3 H7); generalize (Qmult_resp_Qle_pos_l _ _ _ H3 H8); 
  generalize (Qmult_resp_Qle_pos_l _ _ _ H4 H9); generalize (Qmult_resp_Qle_pos_l _ _ _ H4 H10);
  generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H11); generalize (Qmult_resp_Qle_pos_l _ _ _ H1 H12); 
  clear H5 H6 H7 H8 H9 H10 H11 H12; repeat rewrite Qmult_zero_right; intros H5 H6 H7 H8 H9 H10 H11 H12;
  split; left; repeat split.
   (* TP: boundedness *)
   abstract (stepr ((1/3)*(e+f+g+h)); [|qZ_numerals; field; auto]; apply Qlt_mult_pos_pos; auto).
   abstract (stepr ((1/3)*(e-f-g+h)); [|qZ_numerals; field; auto]; apply Qlt_mult_pos_pos; auto).
   abstract (stepr ((1/3)*(-e-f+g+h)); [|qZ_numerals; field; auto]; apply Qlt_mult_pos_pos; auto).
   abstract (stepr ((1/3)*(-e+f-g+h)); [|qZ_numerals; field; auto]; apply Qlt_mult_pos_pos; auto).
   (* TP: refining *)
   abstract (stepr ((a+b+c+d)+(1/3)*(e+f+g+h)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial; 
    stepr (((a+b+c+d)*(Qone+Qone+Qone))-((e+f+g+h)*-Qone)); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((1/3)*(e+f+g+h)-(a+b+c+d)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial; 
    stepr ((e+f+g+h)-((a+b+c+d)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((a-b-c+d)+(1/3)*(e-f-g+h)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial; 
    stepr (((a-b-c+d)*(Qone+Qone+Qone))-((e-f-g+h)*(-Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((1/3)*(e-f-g+h)-(a-b-c+d)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial; 
    stepr ((e-f-g+h)-((a-b-c+d)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((-a-b+c+d)+(1/3)*(-e-f+g+h)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial; 
    stepr (((-a-b+c+d)*(Qone+Qone+Qone))-((-e-f+g+h)*(-Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((1/3)*(-e-f+g+h)-(-a-b+c+d)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial; 
    stepr ((-e-f+g+h)-((-a-b+c+d)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((-a+b-c+d)+(1/3)*(-e+f-g+h)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial; 
    stepr (((-a+b-c+d)*(Qone+Qone+Qone))-((-e+f-g+h)*(-Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial).
   abstract (stepr ((1/3)*(-e+f-g+h)-(-a+b-c+d)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepl Zero; trivial; 
    stepr ((-e+f-g+h)-((-a+b-c+d)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero; trivial).
  (* d-c,d+c < Zero *)
  generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H5); generalize (Qmult_resp_Qle_neg_l _ _ _ H2 H6);
  generalize (Qmult_resp_Qle_neg_l _ _ _ H3 H7); generalize (Qmult_resp_Qle_neg_l _ _ _ H3 H8); 
  generalize (Qmult_resp_Qle_neg_l _ _ _ H4 H9); generalize (Qmult_resp_Qle_neg_l _ _ _ H4 H10);
  generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H11); generalize (Qmult_resp_Qle_neg_l _ _ _ H1 H12); 
  clear H5 H6 H7 H8 H9 H10 H11 H12; repeat rewrite Qmult_zero_right; intros H5 H6 H7 H8 H9 H10 H11 H12;
  split; right; repeat split.
   (* TP: boundedness *)
   abstract (stepl ((e+f+g+h)*(1/3)); [|qZ_numerals; field; auto]; apply Qlt_mult_neg_pos; auto).
   abstract (stepl ((e-f-g+h)*(1/3)); [|qZ_numerals; field; auto]; apply Qlt_mult_neg_pos; auto).
   abstract (stepl ((-e-f+g+h)*(1/3)); [|qZ_numerals; field; auto]; apply Qlt_mult_neg_pos; auto).
   abstract (stepl ((-e+f-g+h)*(1/3)); [|qZ_numerals; field; auto]; apply Qlt_mult_neg_pos; auto).
   (* TP: refining *)
   abstract (stepl ((a+b+c+d)+(1/3)*(e+f+g+h)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial; 
    stepl (((a+b+c+d)*(Qone+Qone+Qone))-((e+f+g+h)*-Qone)); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((1/3)*(e+f+g+h)-(a+b+c+d)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial; 
    stepl ((e+f+g+h)-((a+b+c+d)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((a-b-c+d)+(1/3)*(e-f-g+h)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial; 
    stepl (((a-b-c+d)*(Qone+Qone+Qone))-((e-f-g+h)*(-Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((1/3)*(e-f-g+h)-(a-b-c+d)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial; 
    stepl ((e-f-g+h)-((a-b-c+d)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((-a-b+c+d)+(1/3)*(-e-f+g+h)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial; 
    stepl (((-a-b+c+d)*(Qone+Qone+Qone))-((-e-f+g+h)*(-Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((1/3)*(-e-f+g+h)-(-a-b+c+d)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial; 
    stepl ((-e-f+g+h)-((-a-b+c+d)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((-a+b-c+d)+(1/3)*(-e+f-g+h)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial; 
    stepl (((-a+b-c+d)*(Qone+Qone+Qone))-((-e+f-g+h)*(-Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial).
   abstract (stepl ((1/3)*(-e+f-g+h)-(-a+b-c+d)); [|qZ_numerals; field; auto];
    apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone); auto; stepr Zero; trivial; 
    stepl ((-e+f-g+h)-((-a+b-c+d)*(Qone+Qone+Qone))); [|qZ_numerals; field; auto];apply Qle_Qminus_Zero_neg; trivial).
Qed.


Close Scope Z_scope.
Close Scope Q_scope.


Lemma Incl_T_absorbs_Is_refining_T:forall xi d, Incl_T xi d -> Is_refining_T (m_product (inv_digit d) xi).
Proof.
 intros xi [ | | ] H_Incl; unfold inv_digit;
 [ apply Incl_T_absorbs_Is_refining_T_L
 | apply Incl_T_absorbs_Is_refining_T_R
 | apply Incl_T_absorbs_Is_refining_T_M
 ]; assumption.
Qed.

Lemma denom_nonvanishing_T_m_product:forall xi mu r1 r2, Is_refining_M mu ->((-1)<=as_Tensor xi r1 r2<=1) -> 
        denom_nonvanishing_T xi r1 r2-> denom_nonvanishing_T (m_product mu xi) r1 r2.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) ((A,B),(C,D)) r1 r2 H_refining.
 unfold as_Tensor, denom_nonvanishing_M, denom_nonvanishing_T, m_product, fst, snd.
 intros Hr H_denom.
 realify_Q_goal.
 stepl (C *(a * r1 * r2 + b * r1 + c * r2 + d)+D*(e * r1 * r2 + f * r1 + g * r2 + h)); [|ring].
 apply Rlinear_non_zero_2; auto.
 apply (Is_refining_M_denom_nonvanishing_M _ _ H_refining Hr).
Qed.

Lemma as_Tensor_L: forall xi r1 r2, denom_nonvanishing_T xi r1 r2 -> 
       ((-1)<=as_Tensor xi r1 r2<=1)%R-> as_Tensor (m_product LL xi) r1 r2 =
       ((as_Tensor xi r1 r2 - 1) / (as_Tensor xi r1 r2 + 3))%R.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) r1 r2 H_denom H_r.
 generalize (denom_nonvanishing_T_m_product  _ _  _ _ Is_refining_M_L H_r H_denom); generalize H_denom; clear H_denom H_r.
 unfold m_product, as_Tensor, denom_nonvanishing_M, denom_nonvanishing_T, map_digits, fst, snd.
 realify_Q ;auto; simpl.
 replace (2+1) with 3; [|ring].
 intros H_denom H_denom_product.
 assert (H_denom':a*r1*r2+b*r1+c*r2+d+(e*r1*r2+f*r1+g*r2+h)*3<>0);
  [ apply Rmult_reg_nonzero_l with (1/2); stepl ((1/2*a+3/2*e)*r1*r2+(1/2*b+3/2*f)*r1+(1/2*c+3/2*g)*r2+(1/2*d+3/2*h));
  trivial; field; auto|].
 rewrite Rdiv_Rminus_Rmult; trivial.
 rewrite Rdiv_Rplus_Rmult; trivial.
 rewrite Rdiv_Rdiv_simplify; trivial.
 transitivity(((a*r1*r2+b*r1+c*r2+d-(e*r1*r2+f*r1+g*r2+h)*1)*(1/2))/((a*r1*r2+b*r1+c*r2+d+(e*r1*r2+f*r1+g*r2+h)*3)*(1/2))).
  apply (f_equal2 Rdiv); field; auto.
  apply Rdiv_Rmult_simplify; auto.
Qed.

Lemma as_Tensor_R: forall xi r1 r2, denom_nonvanishing_T xi r1 r2 ->
       ((-1)<=as_Tensor xi r1 r2<=1)%R-> as_Tensor (m_product RR xi) r1 r2 =
       ((as_Tensor xi r1 r2 + 1) / (-as_Tensor xi r1 r2 + 3))%R.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) r1 r2 H_denom H_r;
 generalize (denom_nonvanishing_T_m_product  _ _  _ _ Is_refining_M_R H_r H_denom); generalize H_denom; clear H_denom H_r;
 unfold m_product, as_Tensor, denom_nonvanishing_M, denom_nonvanishing_T, map_digits, fst, snd;
 realify_Q ;auto; simpl;
 replace (2+1) with 3; [|ring];
 intros H_denom H_denom_product.
 assert (H_denom':-(a*r1*r2+b*r1+c*r2+d)+(e*r1*r2+f*r1+g*r2+h)*3<>0);
  [ apply Rmult_reg_nonzero_l with (1/2); stepl ((-1/2*a+3/2*e)*r1*r2+(-1/2*b+3/2*f)*r1+(-1/2*c+3/2*g)*r2+(-1/2*d+3/2*h));
  trivial; field; auto|].
 rewrite <- Rdiv_Ropp_numerator; trivial.
 repeat rewrite Rdiv_Rplus_Rmult; trivial.
 rewrite Rdiv_Rdiv_simplify; trivial.
 transitivity(((a*r1*r2+b*r1+c*r2+d+(e*r1*r2+f*r1+g*r2+h)*1)*(1/2))/((-(a*r1*r2+b*r1+c*r2+d)+(e*r1*r2+f*r1+g*r2+h)*3)*(1/2))).
  apply (f_equal2 Rdiv); field; auto.
  apply Rdiv_Rmult_simplify; auto.
Qed.

Lemma as_Tensor_M: forall xi r1 r2, denom_nonvanishing_T xi r1 r2 ->
       ((-1)<=as_Tensor xi r1 r2<=1)%R-> as_Tensor (m_product MM xi) r1 r2 = 
       ((as_Tensor xi r1 r2)/3)%R.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) r1 r2 H_denom H_r;
 generalize (denom_nonvanishing_T_m_product  _ _  _ _ Is_refining_M_M H_r H_denom); generalize H_denom; clear H_denom H_r;
 unfold m_product, as_Tensor, denom_nonvanishing_M, denom_nonvanishing_T, map_digits, fst, snd;
 realify_Q ;auto; simpl;
 replace (2+1) with 3; [|ring];
 intros H_denom H_denom_product.
 rewrite Rdiv_Rdiv_Rmult_numerator; auto.
 apply (f_equal2 Rdiv); field; auto.
Qed.

Open Scope Q_scope.

Lemma Is_refining_T_property_fold:  forall xi,
  (forall r1 r2,(-1 <= r1 <= 1)%R -> (-1 <= r2 <= 1)%R -> denom_nonvanishing_T xi r1 r2) ->
  (forall r1 r2,(-1 <= r1 <= 1)%R -> (-1 <= r2 <= 1)%R -> (-1<=as_Tensor xi r1 r2<=1)%R) ->
  Is_refining_T xi.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) H_denom H_xi.
 assert (H_bounded:=(denom_nonvanishing_T_Bounded_T _ H_denom)).
 unfold as_Tensor in H_xi; simpl in H_xi.
 assert (H_efgh1:=Bounded_T_e_mf_mg_h_nonzero _ _ _ _ _ _ _ _ H_bounded); 
 assert (H_efgh2:=Bounded_T_me_mf_g_h_nonzero _ _ _ _ _ _ _ _ H_bounded); 
 assert (H_efgh3:=Bounded_T_me_f_mg_h_nonzero _ _ _ _ _ _ _ _ H_bounded); 
 assert (H_efgh4:=Bounded_T_e_f_g_h_nonzero _ _ _ _ _ _ _ _ H_bounded);
 assert (H_h:=Bounded_T_nonzero _ _ _ _ _ _ _ _ H_bounded).
 unfold Is_refining_T, map_digits, fst, snd; qZ_numerals; repeat split; trivial.
 destruct (denom_nonvanishing_T_Bounded_T (((a,b),(c,d)),((e,f),(g,h))) H_denom) as [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]];
 simpl in H1, H2, H3, H4.
  (* Zero < ... *)
  left; repeat split.
   (* 1 *)
   apply Qle_Qdiv_denom_pos_nonneg with (e+f+g+h); trivial;
   stepr (((a*Qone*Qone+b*Qone+c*Qone+d)/(e*Qone*Qone+f*Qone+g*Qone+h))-(-Qone)); [|field; ring_exact_Q H_efgh4];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj1 (H_xi (1)%R (1)%R one_is_in_base_interval one_is_in_base_interval))| ring_exact_Q H_efgh4].
   (* 2 *)
   apply Qle_Qdiv_denom_pos_nonneg with (e+f+g+h); trivial;
   stepr (Qone -((a*Qone*Qone+b*Qone+c*Qone+d)/(e*Qone*Qone+f*Qone+g*Qone+h))); [|field; ring_exact_Q H_efgh4];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj2 (H_xi (1)%R (1)%R one_is_in_base_interval one_is_in_base_interval))| ring_exact_Q H_efgh4].
   (* 3 *)
   apply Qle_Qdiv_denom_pos_nonneg with (e-f-g+h); trivial;
   stepr (((a*(-Qone)*(-Qone)+b*(-Qone)+c*(-Qone)+d)/(e*(-Qone)*(-Qone)+f*(-Qone)+g*(-Qone)+h))-(-Qone)); [|field; ring_exact_Q H_efgh1];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj1 (H_xi (-1)%R (-1)%R min_one_is_in_base_interval min_one_is_in_base_interval))| ring_exact_Q H_efgh1].
   (* 4 *)
   apply Qle_Qdiv_denom_pos_nonneg with (e-f-g+h); trivial;
   stepr (Qone-((a*(-Qone)*(-Qone)+b*(-Qone)+c*(-Qone)+d)/(e*(-Qone)*(-Qone)+f*(-Qone)+g*(-Qone)+h))); [|field; ring_exact_Q H_efgh1];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj2 (H_xi (-1)%R (-1)%R min_one_is_in_base_interval min_one_is_in_base_interval))| ring_exact_Q H_efgh1].
   (* 5 *)
   apply Qle_Qdiv_denom_pos_nonneg with (-e-f+g+h); trivial;
   stepr (((a*(-Qone)*Qone+b*(-Qone)+c*Qone+d)/(e*(-Qone)*Qone+f*(-Qone)+g*Qone+h))-(-Qone)); [|field; ring_exact_Q H_efgh2];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj1 (H_xi (-1)%R (1)%R min_one_is_in_base_interval one_is_in_base_interval))| ring_exact_Q H_efgh2].
   (* 6 *)
   apply Qle_Qdiv_denom_pos_nonneg with (-e-f+g+h); trivial;
   stepr (Qone-((a*(-Qone)*Qone+b*(-Qone)+c*Qone+d)/(e*(-Qone)*Qone+f*(-Qone)+g*Qone+h))); [|field; ring_exact_Q H_efgh2];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj2 (H_xi (-1)%R (1)%R min_one_is_in_base_interval one_is_in_base_interval))| ring_exact_Q H_efgh2].
   (* 7 *)
   apply Qle_Qdiv_denom_pos_nonneg with (-e+f-g+h); trivial;
   stepr (((a*Qone*(-Qone)+b*Qone+c*(-Qone)+d)/(e*Qone*(-Qone)+f*Qone+g*(-Qone)+h))-(-Qone)); [|field; ring_exact_Q H_efgh3];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj1 (H_xi (1)%R (-1)%R one_is_in_base_interval min_one_is_in_base_interval))| ring_exact_Q H_efgh3].
   (* 8 *)
   apply Qle_Qdiv_denom_pos_nonneg with (-e+f-g+h); trivial;
   stepr (Qone-((a*Qone*(-Qone)+b*Qone+c*(-Qone)+d)/(e*Qone*(-Qone)+f*Qone+g*(-Qone)+h))); [|field; ring_exact_Q H_efgh3];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj2 (H_xi (1)%R (-1)%R one_is_in_base_interval min_one_is_in_base_interval))| ring_exact_Q H_efgh3].
  (* ... < Zero *)
  right; repeat split.
   (* 1 *)
   apply Qle_Qdiv_denom_neg_nonneg with (e+f+g+h); trivial;
   stepr (((a*Qone*Qone+b*Qone+c*Qone+d)/(e*Qone*Qone+f*Qone+g*Qone+h))-(-Qone)); [|field; ring_exact_Q H_efgh4];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj1 (H_xi (1)%R (1)%R one_is_in_base_interval one_is_in_base_interval))| ring_exact_Q H_efgh4].
   (* 2 *)
   apply Qle_Qdiv_denom_neg_nonneg with (e+f+g+h); trivial;
   stepr (Qone -((a*Qone*Qone+b*Qone+c*Qone+d)/(e*Qone*Qone+f*Qone+g*Qone+h))); [|field; ring_exact_Q H_efgh4];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj2 (H_xi (1)%R (1)%R one_is_in_base_interval one_is_in_base_interval))| ring_exact_Q H_efgh4].
   (* 3 *)
   apply Qle_Qdiv_denom_neg_nonneg with (e-f-g+h); trivial;
   stepr (((a*(-Qone)*(-Qone)+b*(-Qone)+c*(-Qone)+d)/(e*(-Qone)*(-Qone)+f*(-Qone)+g*(-Qone)+h))-(-Qone)); [|field; ring_exact_Q H_efgh1];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj1 (H_xi (-1)%R (-1)%R min_one_is_in_base_interval min_one_is_in_base_interval))| ring_exact_Q H_efgh1].
   (* 4 *)
   apply Qle_Qdiv_denom_neg_nonneg with (e-f-g+h); trivial;
   stepr (Qone-((a*(-Qone)*(-Qone)+b*(-Qone)+c*(-Qone)+d)/(e*(-Qone)*(-Qone)+f*(-Qone)+g*(-Qone)+h))); [|field; ring_exact_Q H_efgh1];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj2 (H_xi (-1)%R (-1)%R min_one_is_in_base_interval min_one_is_in_base_interval))| ring_exact_Q H_efgh1].
   (* 5 *)
   apply Qle_Qdiv_denom_neg_nonneg with (-e-f+g+h); trivial;
   stepr (((a*(-Qone)*Qone+b*(-Qone)+c*Qone+d)/(e*(-Qone)*Qone+f*(-Qone)+g*Qone+h))-(-Qone)); [|field; ring_exact_Q H_efgh2];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj1 (H_xi (-1)%R (1)%R min_one_is_in_base_interval one_is_in_base_interval))| ring_exact_Q H_efgh2].
   (* 6 *)
   apply Qle_Qdiv_denom_neg_nonneg with (-e-f+g+h); trivial;
   stepr (Qone-((a*(-Qone)*Qone+b*(-Qone)+c*Qone+d)/(e*(-Qone)*Qone+f*(-Qone)+g*Qone+h))); [|field; ring_exact_Q H_efgh2];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj2 (H_xi (-1)%R (1)%R min_one_is_in_base_interval one_is_in_base_interval))| ring_exact_Q H_efgh2].
   (* 7 *)
   apply Qle_Qdiv_denom_neg_nonneg with (-e+f-g+h); trivial;
   stepr (((a*Qone*(-Qone)+b*Qone+c*(-Qone)+d)/(e*Qone*(-Qone)+f*Qone+g*(-Qone)+h))-(-Qone)); [|field; ring_exact_Q H_efgh3];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj1 (H_xi (1)%R (-1)%R one_is_in_base_interval min_one_is_in_base_interval))| ring_exact_Q H_efgh3].
   (* 8 *)
   apply Qle_Qdiv_denom_neg_nonneg with (-e+f-g+h); trivial;
   stepr (Qone-((a*Qone*(-Qone)+b*Qone+c*(-Qone)+d)/(e*Qone*(-Qone)+f*Qone+g*(-Qone)+h))); [|field; ring_exact_Q H_efgh3];
   apply Qle_Qminus_Zero;
   apply Q_to_R_Qle;
   realify_Q_goal;
   [ apply (proj2 (H_xi (1)%R (-1)%R one_is_in_base_interval min_one_is_in_base_interval))| ring_exact_Q H_efgh3].
Qed.

Lemma Is_refining_T_left_right_product:forall xi mu_l mu_r, Is_refining_T xi -> Is_refining_M mu_l -> Is_refining_M mu_r ->
 Is_refining_T (right_product (left_product xi mu_l) mu_r).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) ((A,B),(C,D)) ((A',B'),(C',D')) H_xi H_l H_r.
 apply Is_refining_T_property_fold; intros r1 r2 Hr1 Hr2.
  apply denom_nonvanishing_T_left_right_product; trivial;
  [ apply Is_refining_M_denom_nonvanishing_M
  | apply Is_refining_M_denom_nonvanishing_M
  | apply Is_refining_M_property
  | apply Is_refining_M_property
  ]; trivial.

  rewrite as_Tensor_right_left_product_as_Moebius; trivial;
  repeat apply Is_refining_M_property; trivial;
  repeat apply Is_refining_M_denom_nonvanishing_M; trivial;
  apply Is_refining_T_property; trivial; repeat apply Is_refining_M_property; trivial.
Qed.

Lemma Is_refining_T_product_hd:forall xi alpha beta, Is_refining_T xi -> 
   Is_refining_T (right_product (left_product xi (map_digits (hd alpha))) (map_digits (hd beta))).
Proof.
 intros xi [[ | | ] alpha] [[ | | ] beta] H_xi;
 unfold hd; apply Is_refining_T_left_right_product; trivial;
 first [apply Is_refining_M_L|apply Is_refining_M_R|apply Is_refining_M_M].
Qed.

Close Scope Q_scope.
