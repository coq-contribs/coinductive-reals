(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import digits.
Require Import Bounded_M.
Require Import Raxioms.
Require Import RIneq.
From QArithSternBrocot Require Import R_addenda.
Require Import Fourier_solvable_ineqs.

(** Properties of the predicate [Bounded_T]. *)

Lemma Bounded_T_auxiliary_1: forall (e f g h:Q), Zero<e+f+g+h -> Zero<e-f-g+h -> Zero< -e-f+g+h -> Zero< -e+f-g+h -> Zero<h.
Proof.
 intros e f g h H1 H2 H3 H4; apply Qlt_Qmult_cancel_l with (Qone+Qone+Qone+Qone); auto; stepl Zero; auto; 
 stepr ((e+f+g+h)+(e-f-g+h)+(-e-f+g+h)+(-e+f-g+h)); auto; ring.
Qed.

Lemma Bounded_T_auxiliary_2: forall (e f g h:Q), e+f+g+h<Zero -> e-f-g+h<Zero -> -e-f+g+h<Zero -> -e+f-g+h<Zero -> h<Zero.
Proof.
 intros e f g h H1 H2 H3 H4; apply Qlt_Qmult_cancel_l with (Qone+Qone+Qone+Qone); auto; stepr Zero; auto; 
 stepl ((e+f+g+h)+(e-f-g+h)+(-e-f+g+h)+(-e+f-g+h)); auto; ring.
Qed.

Lemma Bounded_T_auxiliary_3: forall (e f g h:Q), Zero<=e+f+g+h -> Zero<=e-f-g+h -> Zero<= -e-f+g+h -> Zero<= -e+f-g+h -> Zero<=h.
Proof.
 intros e f g h H1 H2 H3 H4; apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone+Qone); auto; stepl Zero; auto; 
 stepr ((e+f+g+h)+(e-f-g+h)+(-e-f+g+h)+(-e+f-g+h)); auto; ring.
Qed.

Lemma Bounded_T_auxiliary_4: forall (e f g h:Q), e+f+g+h<=Zero -> e-f-g+h<=Zero -> -e-f+g+h<=Zero -> -e+f-g+h<=Zero -> h<=Zero.
Proof.
 intros e f g h H1 H2 H3 H4; apply Qmult_resp_Qle_pos_r with (Qone+Qone+Qone+Qone); auto; stepr Zero; auto; 
 stepl ((e+f+g+h)+(e-f-g+h)+(-e-f+g+h)+(-e+f-g+h)); auto; ring.
Qed.

Lemma Bounded_T_M_1:forall a b c d e f g h,Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
             Bounded_M (c - a, d - b, (g - e, h - f)).
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1; unfold fst, snd in H2; unfold fst, snd in H3; unfold fst, snd in H4.
 left; unfold fst, snd; split.
  stepr (- e - f + g + h); trivial; ring.
  stepr (e - f - g + h); trivial; ring.
 right; unfold fst, snd; split.
  stepl (- e - f + g + h); trivial; ring.
  stepl (e - f - g + h); trivial; ring.
Qed.

Lemma Bounded_T_M_2:forall a b c d e f g h,Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
             Bounded_M (a + c, b + d, (e + g, f + h)).
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1; unfold fst, snd in H2; unfold fst, snd in H3; unfold fst, snd in H4.
 left; unfold fst, snd; split.
  stepr (e  + f + g + h); trivial; ring.
  stepr (- e + f - g + h); trivial; ring.
 right; unfold fst, snd; split.
  stepl (e  + f + g + h); trivial; ring.
  stepl (- e + f - g + h); trivial; ring.
Qed.

Lemma Bounded_T_M_2':forall a b c d e f g h,Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
             Bounded_M (c + a, d + b, (g + e, h + f)).
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1; unfold fst, snd in H2; unfold fst, snd in H3; unfold fst, snd in H4.
 left; unfold fst, snd; split.
  stepr (e  + f + g + h); trivial; ring.
  stepr (- e + f - g + h); trivial; ring.
 right; unfold fst, snd; split.
  stepl (e  + f + g + h); trivial; ring.
  stepl (- e + f - g + h); trivial; ring.
Qed.


Lemma Bounded_T_M_3:forall a b c d e f g h,Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
             Bounded_M (a+b, c+d, (e+f, g+h)).
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1,H2, H3, H4;
 [left|right];  unfold fst, snd; split;
 [ ring_exact_Q H1
 | ring_exact_Q H3
 | ring_exact_Q H1
 | ring_exact_Q H3
 ].
Qed.

Lemma Bounded_T_M_4:forall a b c d e f g h,Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
             Bounded_M (- a + b, - c + d, (- e + f, - g + h)).
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1,H2, H3, H4;
 [left|right];  unfold fst, snd; split;
 [ ring_exact_Q H4
 | ring_exact_Q H2
 | ring_exact_Q H4
 | ring_exact_Q H2
 ].
Qed.

Lemma Bounded_T_e_mf_mg_h_nonzero:forall a b c d e f g h,Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
                 (e - g + (h - f)) <> Zero.
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1; unfold fst, snd in H2; 
                                                               unfold fst, snd in H3; unfold fst, snd in H4;
 stepl (e - f - g + h); auto; try ring; apply sym_not_eq; auto.
Qed.

Lemma Bounded_T_me_mf_g_h_nonzero:forall a b c d e f g h,Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
                 (g - e + (h - f)) <> Zero.
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1; unfold fst, snd in H2; 
                                                               unfold fst, snd in H3; unfold fst, snd in H4;
 stepl (- e - f + g + h); auto; try ring; apply sym_not_eq; auto.
Qed.

Lemma Bounded_T_e_f_g_h_nonzero:forall a b c d e f g h,Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
                 (e + g + (f + h)) <> Zero.
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1; unfold fst, snd in H2; 
                                                               unfold fst, snd in H3; unfold fst, snd in H4;
 stepl (e + f + g + h); auto; try ring; apply sym_not_eq; auto.
Qed.


Lemma Bounded_T_me_f_mg_h_nonzero:forall a b c d e f g h,Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
                 (f + h - (e + g)) <> Zero.
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1; unfold fst, snd in H2; 
                                                               unfold fst, snd in H3; unfold fst, snd in H4;
 stepl (- e + f - g + h); auto; try ring; apply sym_not_eq; auto.
Qed.

Lemma Bounded_T_nonzero: forall a b c d e f g h, Bounded_T (((a,b),(c,d)),((e,f),(g,h))) -> h<> Zero.
Proof.
 intros a b c d e f g h [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]] H5 ; unfold fst, snd in H1; unfold fst, snd in H2; 
                                                                   unfold fst, snd in H3; unfold fst, snd in H4;
  generalize H1 H2 H3 H4; clear H1 H2 H3 H4; rewrite H5; unfold Qminus; repeat rewrite Qplus_zero_right;
  intros H1 H2 H3 H4; apply Qlt_irreflexive with Zero; 
  [ stepr ((e + f + g)+(e + - f + - g)+(- e + - f + g)+(- e + f - g))
  | stepl ((e + f + g)+(e + - f + - g)+(- e + - f + g)+(- e + f - g)) 
  ]; auto; ring.
Qed.


Lemma Bounded_T_pos:forall a b c d e f g h x y, Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
                                        Zero<h ->(-1<=x<=1)%R->(-1<=y<=1)%R->(0<e*x*y+f*x+g*y+h)%R.
Proof.
 intros a b c d e f g h x y H_vanish;
 generalize (Bounded_T_M_1 _ _ _ _ _ _ _ _ H_vanish); 
 generalize (Bounded_T_M_2' _ _ _ _ _ _ _ _ H_vanish); 
 generalize H_vanish;
 intros [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]] H_vanish2 H_vanish1 Hh Hx Hy;
 unfold fst, snd in H1; unfold fst, snd in H2; unfold fst, snd in H3; unfold fst, snd in H4;
 (stepr ((e*y+f)*x+ (g*y+h))%R; [|ring]).

  (* TP: Zero < h-f *)
  assert (H_hf1:Zero<h-f); 
  [apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepl Zero; auto; stepr ((e-f-g+h)+(-e-f+g+h)); auto; ring|].
  (* TP: Zero < h+f *)
  assert (H_hf2:Zero<h+f); 
  [apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepl Zero; auto; stepr ((e+f+g+h)+(-e+f-g+h)); auto; ring|].
  (* TP: Zero < h-g *)
  assert (H_hg1:Zero<h-g); 
  [apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepl Zero; auto; stepr ((e-f-g+h)+(-e+f-g+h)); auto; ring|].
  (* TP: 0 < h-g *)
  assert (H_hg1_R:(0<h-g)%R); 
  [rewrite <- Q_to_R_Zero; rewrite <- Q_to_Rminus; apply Q_to_Rlt;  trivial|]. 
  (* TP: Zero < h+g *)
  assert (H_hg2:Zero<h+g); 
  [apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepl Zero; auto; stepr ((e+f+g+h)+(-e-f+g+h)); auto; ring|].
  (* TP: 0 < h+g *)
  assert (H_hg2_R:(0<h+g)%R); 
  [rewrite <- Q_to_R_Zero; rewrite <- Q_to_Rplus; apply Q_to_Rlt;  trivial|]. 
  (* TP: 0 < h *)
  assert (H_h_R:(0<h)%R); 
  [rewrite <- Q_to_R_Zero; apply Q_to_Rlt; trivial|].
 
  destruct (Rtrichotomy_inf 0 (e*y+f)) as [[Hef|Hef]|Hef]. 
   (* 0<ey+f *)
   apply Bounded_M_pos_auxiliary_1; trivial;
   stepr (Qminus g e * y + Qminus h f)%R;
    [ apply (Bounded_M_pos _ _ _ _ y H_vanish1); trivial
    | repeat rewrite Q_to_Rminus; ring]...
   (* ey+f=0 *)
   rewrite <- Hef; stepr (g*y+h)%R; [|ring].
   destruct (Qtrichotomy_inf Zero g) as [[Hg|Hg]|Hg].
    generalize (Q_to_Rlt _ _ Hg); clear Hg; rewrite Q_to_R_Zero; intro Hg;
    apply Bounded_M_pos_auxiliary_1; trivial...
    rewrite <- Hg; rewrite Q_to_R_Zero; stepr h; trivial; ring...
    generalize (Q_to_Rlt _ _ Hg); clear Hg; rewrite Q_to_R_Zero; intro Hg;
    apply Bounded_M_pos_auxiliary_2; trivial...
   (* ey+f<0 *)
   apply Bounded_M_pos_auxiliary_2; trivial;
   stepr (Qplus g e * y + Qplus h f)%R;
    [ apply (Bounded_M_pos _ _ _ _ y H_vanish2); trivial
    | repeat rewrite Q_to_Rplus; ring]...
 
  apply False_ind; apply Qlt_irreflexive with Zero; apply Qlt_transitive with (h+h+h+h); auto;
  stepl ((e + f + g + h)+(e - f - g + h)+(- e - f + g + h)+(- e + f - g + h)); auto; ring.
Qed.

Lemma Bounded_T_neg:forall a b c d e f g h x y, Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
                                        h<Zero ->(-1<=x<=1)%R->(-1<=y<=1)%R->(e*x*y+f*x+g*y+h<0)%R.
Proof.
 intros a b c d e f g h x y H_vanish;
 generalize (Bounded_T_M_1 _ _ _ _ _ _ _ _ H_vanish); 
 generalize (Bounded_T_M_2' _ _ _ _ _ _ _ _ H_vanish); 
 generalize H_vanish;
 intros [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]] H_vanish2 H_vanish1 Hh Hx Hy;
 unfold fst, snd in H1; unfold fst, snd in H2; unfold fst, snd in H3; unfold fst, snd in H4;
 (stepl ((e*y+f)*x+ (g*y+h))%R; [|ring]).

  apply False_ind; apply Qlt_irreflexive with Zero; apply Qlt_transitive with (h+h+h+h); auto;
  stepr ((e + f + g + h)+(e - f - g + h)+(- e - f + g + h)+(- e + f - g + h)); auto; ring.

  (* TP: h-f < Zero *)
  assert (H_hf1:h-f<Zero); 
  [apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepr Zero; auto; stepl ((e-f-g+h)+(-e-f+g+h)); auto; ring|].
  (* TP: h+f < Zero *)
  assert (H_hf2:h+f<Zero); 
  [apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepr Zero; auto; stepl ((e+f+g+h)+(-e+f-g+h)); auto; ring|].
  (* TP: h-g < Zero *)
  assert (H_hg1:h-g<Zero); 
  [apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepr Zero; auto; stepl ((e-f-g+h)+(-e+f-g+h)); auto; ring|].
  (* TP: h-g < 0 *)
  assert (H_hg1_R:(h-g<0)%R); 
  [rewrite <- Q_to_R_Zero; rewrite <- Q_to_Rminus; apply Q_to_Rlt;  trivial|]. 
  (* TP: h+g < Zero *)
  assert (H_hg2:h+g<Zero); 
  [apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepr Zero; auto; stepl ((e+f+g+h)+(-e-f+g+h)); auto; ring|].
  (* TP: h+g < 0 *)
  assert (H_hg2_R:(h+g<0)%R); 
  [rewrite <- Q_to_R_Zero; rewrite <- Q_to_Rplus; apply Q_to_Rlt;  trivial|]. 
  (* TP: 0 < h *)
  assert (H_h_R:(h<0)%R); 
  [rewrite <- Q_to_R_Zero; apply Q_to_Rlt; trivial|].
 
  destruct (Rtrichotomy_inf 0 (e*y+f)) as [[Hef|Hef]|Hef]. 
   (* 0<ey+f *)
   apply Bounded_M_neg_auxiliary_1; trivial;
   stepl (Qplus g e * y + Qplus h f)%R;
    [ apply (Bounded_M_neg _ _ _ _ y H_vanish2); trivial
    | repeat rewrite Q_to_Rplus; ring]...
   (* ey+f=0 *)
   rewrite <- Hef; stepl (g*y+h)%R; [|ring].
   destruct (Qtrichotomy_inf Zero g) as [[Hg|Hg]|Hg].
    generalize (Q_to_Rlt _ _ Hg); clear Hg; rewrite Q_to_R_Zero; intro Hg;
    apply Bounded_M_neg_auxiliary_1; trivial...
    rewrite <- Hg; rewrite Q_to_R_Zero; stepl h; trivial; ring...
    generalize (Q_to_Rlt _ _ Hg); clear Hg; rewrite Q_to_R_Zero; intro Hg;
    apply Bounded_M_neg_auxiliary_2; trivial...
   (* ey+f<0 *)
   apply Bounded_M_neg_auxiliary_2; trivial;
   stepl (Qminus g e * y + Qminus h f)%R;
    [ apply (Bounded_M_neg _ _ _ _ y H_vanish1); trivial
    | repeat rewrite Q_to_Rminus; ring]...
Qed.

Lemma Bounded_T_nonzero_denum:forall a b c d e f g h x y, Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
                                        (-1<=x<=1)%R->(-1<=y<=1)%R->(e*x*y+f*x+g*y+h<>0)%R.
Proof.
 intros a b c d e f g h x y H_vanish Hx Hy;
 destruct (Qtrichotomy_inf Zero h) as [[Hh|Hh]|Hh];
  [ apply Rlt_not_eq'; apply Bounded_T_pos with a b c d; trivial
  | intros _; apply (Bounded_T_nonzero a b c d e f g h); auto
  | apply Rlt_not_eq; apply Bounded_T_neg with a b c d; trivial].
Qed.

Lemma Bounded_T_twice_pos:forall a b c d e f g h r x y, Bounded_T (((a,b),(c,d)),((e,f),(g,h))) ->
                                 (-1<=r<=1)%R->(-1<=x<=1)%R->(-1<=y<=1)%R->(0<(e*y*r+f*y+g*r+h)*(e*x*r+f*x+g*r+h))%R.
Proof.
 intros a b c d e f g h r x y H_vanish Hr Hx Hy;
 destruct (Qtrichotomy_inf Zero h) as [[Hh|Hh]|Hh].
  apply Rlt_mult_pos_pos; apply Bounded_T_pos with a b c d; trivial.
  apply False_ind; apply (Bounded_T_nonzero a b c d e f g h); auto.
  apply Rlt_mult_neg_neg; apply Bounded_T_neg with a b c d; trivial.
Qed. 


Lemma det2_nonneg_nondecreasing:forall a b c d e f g h r x y, Bounded_T (((a,b),(c,d)),((e,f),(g,h))) -> 
               (-1<=r<=1)%R -> (0 <= (a*r+b)*(g*r+h)-(c*r+d)*(e*r+f))%R -> (-1<=x<=1)%R -> (-1<=y<=1)%R -> (x<=y)%R ->
                      ((a*x*r+b*x+c*r+d)/(e*x*r+f*x+g*r+h)<=(a*y*r+b*y+c*r+d)/(e*y*r+f*y+g*r+h))%R.
Proof.
 intros a b c d e f g h r x y H_vanish Hr H_det Hx Hy Hxy;
 generalize (Bounded_T_nonzero_denum  _ _ _ _ _ _ _ _ _ _ H_vanish Hy Hr);
 generalize (Bounded_T_nonzero_denum  _ _ _ _ _ _ _ _ _ _ H_vanish Hx Hr);
 generalize (Bounded_T_twice_pos  _ _ _ _ _ _ _ _ _ _ _ H_vanish Hr Hx Hy);
 intros H_cxyr H_rx H_ry;
 apply Rle_zero_Rminus;
 rewrite (distance_Tensor a b c d _ _ _ _ _ _ _ H_ry H_rx);
 unfold Rdiv; apply Fourier_util.Rle_mult_inv_pos; auto;
 apply Rmult_le_pos; trivial; apply Rle_Rminus_zero; trivial.
Qed.

Lemma det2_nonpos_nonincreasing:forall a b c d e f g h r x y, Bounded_T (((a,b),(c,d)),((e,f),(g,h))) -> 
               (-1<=r<=1)%R -> ((a*r+b)*(g*r+h)-(c*r+d)*(e*r+f)<=0)%R -> (-1<=x<=1)%R -> (-1<=y<=1)%R -> (x<=y)%R ->
                      ((a*y*r+b*y+c*r+d)/(e*y*r+f*y+g*r+h)<=(a*x*r+b*x+c*r+d)/(e*x*r+f*x+g*r+h))%R.
Proof.
 intros a b c d e f g h r x y H_vanish Hr H_det Hx Hy Hxy;
 generalize (Bounded_T_nonzero_denum  _ _ _ _ _ _ _ _ _ _ H_vanish Hy Hr);
 generalize (Bounded_T_nonzero_denum  _ _ _ _ _ _ _ _ _ _ H_vanish Hx Hr);
 generalize (Bounded_T_twice_pos  _ _ _ _ _ _ _ _ _ _ _ H_vanish Hr Hy Hx);
 intros H_cxyr H_rx H_ry;
 apply Rle_zero_Rminus;
 rewrite (distance_Tensor a b c d _ _ _ _ _ _ _ H_rx H_ry);
 unfold Rdiv; apply Fourier_util.Rle_mult_inv_pos; auto;
 apply Rle_mult_nonpos_nonpos; trivial; apply Rle_minus; trivial.
Qed.

Lemma  Bounded_T_M_l:forall a b c d e f g h, Bounded_T (a, b, (c, d), (e, f, (g, h))) -> 
    forall x, - Qone <= x /\ x <= Qone -> Bounded_M (a*x + c, b*x + d, (e*x + g, f*x + h)).
Proof.
 intros a b c d e f g h H_bound x [Hxl Hxu].  
 assert (Hx_lr:(-1<= x <= 1 )%R); [realify_Q; intros; split; trivial|].
 remember H_bound as H; clear HeqH; destruct H as [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1,H2,H3,H4.
  left; unfold fst, snd; assert (Hh:=Bounded_T_auxiliary_1 _ _ _ _ H1 H2 H3 H4); split.
   assert (Hdenom:= Bounded_T_pos _ _ _ _ _ _ _ _ x 1%R H_bound Hh Hx_lr one_is_in_base_interval);
   apply Q_to_R_Qlt; realify_Q_goal; ring_exact_R Hdenom.
   assert (Hdenom:= Bounded_T_pos _ _ _ _ _ _ _ _ x (-1)%R H_bound Hh Hx_lr min_one_is_in_base_interval);
   apply Q_to_R_Qlt; realify_Q_goal; ring_exact_R Hdenom.
  right; unfold fst, snd; assert (Hh:=Bounded_T_auxiliary_2 _ _ _ _ H1 H2 H3 H4); split.
   assert (Hdenom:= Bounded_T_neg _ _ _ _ _ _ _ _ x 1%R H_bound Hh Hx_lr one_is_in_base_interval);
   apply Q_to_R_Qlt; realify_Q_goal; ring_exact_R Hdenom.
   assert (Hdenom:= Bounded_T_neg _ _ _ _ _ _ _ _ x (-1)%R H_bound Hh Hx_lr min_one_is_in_base_interval);
   apply Q_to_R_Qlt; realify_Q_goal; ring_exact_R Hdenom.
Qed.

Lemma  Bounded_T_M_r:forall a b c d e f g h, Bounded_T (a, b, (c, d), (e, f, (g, h))) -> 
      forall y, - Qone <= y/\ y <= Qone ->  Bounded_M (a*y + b, c*y + d, (e*y + f, g*y + h)).
Proof.
 intros a b c d e f g h H_bound y [Hyl Hyu].  
 assert (Hy_lr:(-1<= y <= 1 )%R); [realify_Q; intros; split; trivial|].
 remember H_bound as H; clear HeqH; destruct H as [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]; unfold fst, snd in H1,H2,H3,H4.
  left; unfold fst, snd; assert (Hh:=Bounded_T_auxiliary_1 _ _ _ _ H1 H2 H3 H4); split.
   assert (Hdenom:= Bounded_T_pos _ _ _ _ _ _ _ _ 1%R y H_bound Hh one_is_in_base_interval Hy_lr);
   apply Q_to_R_Qlt; realify_Q_goal; ring_exact_R Hdenom.
   assert (Hdenom:= Bounded_T_pos _ _ _ _ _ _ _ _ (-1)%R y H_bound Hh min_one_is_in_base_interval Hy_lr);
   apply Q_to_R_Qlt; realify_Q_goal; ring_exact_R Hdenom.
  right; unfold fst, snd; assert (Hh:=Bounded_T_auxiliary_2 _ _ _ _ H1 H2 H3 H4); split.
   assert (Hdenom:= Bounded_T_neg _ _ _ _ _ _ _ _ 1%R y H_bound Hh one_is_in_base_interval Hy_lr);
   apply Q_to_R_Qlt; realify_Q_goal; ring_exact_R Hdenom.
   assert (Hdenom:= Bounded_T_neg _ _ _ _ _ _ _ _ (-1)%R y H_bound Hh min_one_is_in_base_interval Hy_lr);
   apply Q_to_R_Qlt; realify_Q_goal; ring_exact_R Hdenom.
Qed.

Lemma Bounded_T_denom_nonvanishing_T:
  forall xi, Bounded_T xi ->  (forall x y, (-1 <= x <= 1)%R -> (-1 <= y <= 1)%R -> denom_nonvanishing_T xi x y).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) H_bounded r Hr; red; simpl; apply Bounded_T_nonzero_denum with a b c d; assumption.
Qed.

Lemma denom_nonvanishing_T_Bounded_T:
  forall xi,(forall r1 r2,(-1 <= r1 <= 1)%R -> (-1 <= r2 <= 1)%R -> denom_nonvanishing_T xi r1 r2) ->  Bounded_T xi.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) H_denom.
 unfold denom_nonvanishing_T in H_denom; simpl in H_denom.
 assert (H_denomr1m:forall r1,(-1<=r1<=1)%R -> denom_nonvanishing_M (((-a+b),(-c+d)),((-e+f),(-g+h))) r1);
 [intros r1 Hr1; unfold denom_nonvanishing_M, fst, snd;
  realify_Q; stepl (e*r1*(-1)+f*r1+g*(-1)+h)%R; [|ring]; apply (H_denom r1 (-1)%R Hr1 min_one_is_in_base_interval)|].
 assert (H_denomr1:forall r1,(-1<=r1<=1)%R -> denom_nonvanishing_M (((a+b),(c+d)),((e+f),(g+h))) r1);
 [intros r1 Hr1; unfold denom_nonvanishing_M, fst, snd;
  realify_Q; stepl (e*r1*1+f*r1+g*1+h)%R; [|ring]; apply (H_denom r1 (1)%R Hr1 one_is_in_base_interval)|].
 assert (H_denomr2:forall r2,(-1<=r2<=1)%R -> denom_nonvanishing_M (((a+c),(b+d)),((e+g),(f+h))) r2);
 [intros r2 Hr2; unfold denom_nonvanishing_M, fst, snd;
  realify_Q; stepl (e*1*r2+f*1+g*r2+h)%R; [|ring]; apply (H_denom (1)%R r2 one_is_in_base_interval Hr2)|].
 assert (H_denomr2m:forall r2,(-1<=r2<=1)%R -> denom_nonvanishing_M (((-a+c),(-b+d)),((-e+g),(-f+h))) r2);
 [intros r2 Hr2; unfold denom_nonvanishing_M, fst, snd;
  realify_Q; stepl (e*(-1)*r2+f*(-1)+g*r2+h)%R; [|ring]; apply (H_denom (-1)%R r2 min_one_is_in_base_interval Hr2)|].
 assert (Hb1:=denom_nonvanishing_M_Bounded_M _ H_denomr1).
 assert (Hb1m:=denom_nonvanishing_M_Bounded_M _ H_denomr1m).
 assert (Hb2:=denom_nonvanishing_M_Bounded_M _ H_denomr2).
 assert (Hb2m:=denom_nonvanishing_M_Bounded_M _ H_denomr2m).
 assert (Hgh:=Bounded_M_nonzero _ _ _ _ Hb1).
 assert (Hghm:=Bounded_M_nonzero _ _ _ _ Hb1m).
 assert (Hfh:=Bounded_M_nonzero _ _ _ _ Hb2).
 assert (Hfhm:=Bounded_M_nonzero _ _ _ _ Hb2m).
 assert (H_efgh1:e-f-g+h<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (e*(-1)*(-1)+f*(-1)+g*(-1)+h)%R; [|ring]; 
  apply (H_denom (-1)%R (-1)%R min_one_is_in_base_interval min_one_is_in_base_interval)|].
 assert (H_efgh2:-e-f+g+h<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (e*(-1)*(1)+f*(-1)+g*(1)+h)%R; [|ring]; 
  apply (H_denom (-1)%R (1)%R min_one_is_in_base_interval one_is_in_base_interval)|].
 assert (H_efgh3:-e+f-g+h<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (e*(1)*(-1)+f*(1)+g*(-1)+h)%R; [|ring]; 
  apply (H_denom (1)%R (-1)%R one_is_in_base_interval min_one_is_in_base_interval)|].
 assert (H_efgh4:e+f+g+h<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (e*(1)*(1)+f*(1)+g*(1)+h)%R; [|ring]; 
  apply (H_denom (1)%R (1)%R one_is_in_base_interval one_is_in_base_interval)|].
 assert (Hh: h<>Zero);
 [apply Q_to_R_Qneq; realify_Q_goal; stepl (e*0*0+f*0+g*0+h)%R; [|ring]; apply H_denom; split; fourier.Fourier.fourier|].
 unfold Incl_T, Bounded_T, map_digits, fst, snd.
 destruct (not_Qeq_inf _ _ Hgh) as [Hgh_sg|Hgh_sg].
  (* g+h<Zero *)
  right.
  assert (H_goal1:e+f+g+h<Zero);
  [ generalize (Bounded_M_neg _ _ _ _ (1)%R Hb1 Hgh_sg one_is_in_base_interval);
    rationalify_R_goal; intros H_; generalize (Q_to_R_Qlt _ _ H_); clear H_; intros H; ring_exact_Q H|].
  assert (H_goal2:-e-f+g+h<Zero);
  [ generalize (Bounded_M_neg _ _ _ _ (-1)%R Hb1 Hgh_sg min_one_is_in_base_interval);
    rationalify_R_goal; intros H_; generalize (Q_to_R_Qlt _ _ H_); clear H_; intros H; ring_exact_Q H|].
  assert (H_goal3:e-f-g+h<Zero).
   destruct (not_Qeq_inf _ _ H_efgh1) as [H_sg|H_sg]; trivial;
   assert (H_eg:Zero<e-g);
   [ apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepl Zero; auto;
     stepr ((e-f-g+h)-(-e-f+g+h)); try ring; apply Qlt_Qminus_Zero; apply Qlt_transitive with Zero; trivial|];
   contradiction (H_denomr2m ((-f+h)/(e-g))); simpl.
    split; rationalify_R;
    [ apply Qmult_pos_Qle_Qdiv; trivial; apply Qle_Zero_Qminus; stepr (e - f - g + h);[|ring]
    | apply Qmult_pos_Qdiv_Qle; trivial; apply Qle_Zero_Qminus_neg; stepl (-e - f + g + h); [|ring]]; auto.
    rationalify_R_goal; apply Q_to_Req; field; auto.
  repeat split; trivial.
   destruct (not_Qeq_inf _ _ H_efgh3) as [H_sg|H_sg]; trivial;
   assert (H_eg:Zero<f-e);
   [ apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepl Zero; auto;
     stepr ((-e+f-g+h)-(e-f-g+h)); try ring; apply Qlt_Qminus_Zero; apply Qlt_transitive with Zero; trivial|].
   contradiction (H_denomr1m ((g-h)/(f-e))); simpl.
    split; rationalify_R;
    [ apply Qmult_pos_Qle_Qdiv; trivial; apply Qle_Zero_Qminus_neg;  stepl (e - f - g + h);[|ring]
    | apply Qmult_pos_Qdiv_Qle; trivial; apply Qle_Zero_Qminus; stepr (-e + f - g + h); [|ring]]; auto.
    rationalify_R_goal; apply Q_to_Req; field; auto.
  (* Zero<g+h *)
  left.
  assert (H_goal1:Zero<e+f+g+h);
  [ generalize (Bounded_M_pos _ _ _ _ (1)%R Hb1 Hgh_sg one_is_in_base_interval);
    rationalify_R_goal; intros H_; generalize (Q_to_R_Qlt _ _ H_); clear H_; intros H; ring_exact_Q H|].
  assert (H_goal2:Zero< -e-f+g+h);
  [ generalize (Bounded_M_pos _ _ _ _ (-1)%R Hb1 Hgh_sg min_one_is_in_base_interval);
    rationalify_R_goal; intros H_; generalize (Q_to_R_Qlt _ _ H_); clear H_; intros H; ring_exact_Q H|].
  assert (H_goal3:Zero<e-f-g+h).
   destruct (not_Qeq_inf _ _ H_efgh1) as [H_sg|H_sg]; trivial.
   assert (H_eg:e-g<Zero);
   [ apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepr Zero; auto;
     stepl ((e-f-g+h)-(-e-f+g+h)); try ring; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with Zero; trivial|];
   contradiction (H_denomr2m ((-f+h)/(e-g))); simpl.
    split; rationalify_R;
    [ apply Qmult_neg_Qle_Qdiv; trivial; apply Qle_Zero_Qminus_neg; stepl (e - f - g + h);[|ring]
    |apply Qmult_neg_Qdiv_Qle; trivial; apply Qle_Zero_Qminus; stepr (-e - f + g + h); [|ring]]; auto.
    rationalify_R_goal; apply Q_to_Req; field; auto.
  repeat split; trivial.
   destruct (not_Qeq_inf _ _ H_efgh3) as [H_sg|H_sg]; trivial;
   assert (H_eg:f-e<Zero);
   [ apply Qlt_Qmult_cancel_l with (Qone+Qone); auto; stepr Zero; auto;
     stepl ((-e+f-g+h)-(e-f-g+h)); try ring; apply Qlt_Qminus_Zero_neg; apply Qlt_transitive with Zero; trivial |].
   contradiction (H_denomr1m ((g-h)/(f-e))); simpl.
    split; rationalify_R;
    [ apply Qmult_neg_Qle_Qdiv; trivial; apply Qle_Zero_Qminus;  stepr (e - f - g + h);[|ring]
    | apply Qmult_neg_Qdiv_Qle; trivial; apply Qle_Zero_Qminus_neg; stepl (-e + f - g + h); [|ring]]; auto.
    rationalify_R_goal; apply Q_to_Req; field; auto.
Qed.

Lemma denom_nonvanishing_T_within_diameter2: forall xi, 
   (forall r1 r2,(-1 <= r1 <= 1)%R -> (-1 <= r2 <= 1)%R -> denom_nonvanishing_T xi r1 r2) ->
     forall r1 r2,(-1 <= r1 <= 1)%R -> (-1 <= r2 <= 1)%R -> 
 let xi_ll:= as_Tensor_Q xi (-Qone) (-Qone) in
  let xi_lr:= as_Tensor_Q xi (-Qone) Qone in
   let xi_rl:= as_Tensor_Q xi Qone (-Qone) in
    let xi_rr:= as_Tensor_Q xi Qone Qone in
       (Qmin4 xi_ll xi_lr xi_rl xi_rr <= as_Tensor xi r1 r2 <= Qmax4 xi_ll xi_lr xi_rl xi_rr)%R.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) H_denom r1 r2 Hr1 Hr2 xi_ll xi_lr xi_rl xi_rr.
 assert (H_bounded:=(denom_nonvanishing_T_Bounded_T _ H_denom)).
 assert (H_efgh1:=Bounded_T_e_mf_mg_h_nonzero _ _ _ _ _ _ _ _ H_bounded); 
 assert (H_efgh2:=Bounded_T_me_mf_g_h_nonzero _ _ _ _ _ _ _ _ H_bounded); 
 assert (H_efgh3:=Bounded_T_me_f_mg_h_nonzero _ _ _ _ _ _ _ _ H_bounded); 
 assert (H_efgh4:=Bounded_T_e_f_g_h_nonzero _ _ _ _ _ _ _ _ H_bounded).
 assert (H_bounded1:=Bounded_T_M_1 _ _ _ _ _ _ _ _ H_bounded);
 assert (H_bounded2:=Bounded_T_M_2 _ _ _ _ _ _ _ _ H_bounded).

 generalize (H_denom _ _ Hr1 Hr2).
 unfold denom_nonvanishing_T, as_Tensor, fst, snd.
 intros H_efgh.
 destruct (Rle_dec_weak 0 ((a*r2+b)*(g*r2+h)-(c*r2+d)*(e*r2+f))) as [H_det2|H_det2]; split.
  (* 0<=Det2, SPLIT 1 (1/4 OF TOTAL) *)
  (* q is increasing with r2 fixed, so we prove -1<=q(-1,r2)<= q(r1,r2) *)
  apply Rle_trans with (((Qminus c a)*r2+(Qminus d b))/((Qminus g e)*r2+(Qminus h f)))%R.

   destruct (Qle_dec_weak 0 ((c-a)*(h-f)-(d-b)*(g-e))) as [H_det|H_det].
    (* q(-1,-1)<=q(-1,r2) *)
    apply Rle_trans with (((a-c)+(d-b))/((e-g)+(h-f)))%R.
     rationalify_R; trivial; stepr xi_ll; [apply Qle_Qmin4_1|subst xi_ll; unfold as_Tensor_Q, fst,snd; field; trivial].
     stepl (((Qminus c a)*(-1)+(Qminus d b))/((Qminus g e)*(-1)+(Qminus h f)))%R.
      apply (det_nonneg_nondecreasing (c-a) (d-b) (g-e) (h-f) (-1)%R r2 H_bounded1 H_det min_one_is_in_base_interval Hr2 (proj1 Hr2)).
      realify_Q_goal; apply (f_equal2 Rdiv); ring... 
    (* q(-1,1)<=q(-1,r2) *)
    apply Rle_trans with (((c-a)+(d-b))/((g-e)+(h-f)))%R.
     rationalify_R; trivial; stepr xi_lr; [apply Qle_Qmin4_2|subst xi_lr; unfold as_Tensor_Q, fst,snd; field; trivial].
     stepl (((Qminus c a)*1+(Qminus d b))/((Qminus g e)*1+(Qminus h f)))%R.
      apply (det_nonpos_nonincreasing (c-a) (d-b) (g-e) (h-f) r2 (1)%R H_bounded1 H_det Hr2 one_is_in_base_interval (proj2 Hr2)).
     realify_Q_goal; apply (f_equal2 Rdiv); ring... 
   (* This is the subgoal generated by Rle trans. Back to: q(-1,r2)<=q(r1,r2) *)
   stepl ((a*(-1)*r2+b*(-1)+c*r2+d)/(e*(-1)*r2+f*(-1)+g*r2+h))%R.
    apply (det2_nonneg_nondecreasing _ _ _ _ _ _ _ _ _ _ _ H_bounded Hr2 H_det2 min_one_is_in_base_interval Hr1 
                                         (proj1 Hr1)).
    realify_Q_goal; apply (f_equal2 Rdiv); ring... 
  (* END 0<=Det2, SPLIT 1 *)
  (* 0<=Det2, SPLIT 2 (2/4 OF TOTAL) *)
  (* q is increasing with r2 fixed, so we prove q(r1,r2)<=q(1,r2)<=0 *)
  apply Rle_trans with (((Qplus a c)*r2+(Qplus b d))/((Qplus e g)*r2+(Qplus f h)))%R.
   (* This is the subgoal generated by Rle trans. Back to: q(r1,r2)<=q(1,r2) *)
   stepr ((a*1*r2+b*1+c*r2+d)/(e*1*r2+f*1+g*r2+h))%R.
    apply (det2_nonneg_nondecreasing _ _ _ _ _ _ _ _ _ _ _ H_bounded Hr2 H_det2 Hr1 one_is_in_base_interval
                                         (proj2 Hr1)).
    realify_Q_goal; apply (f_equal2 Rdiv); ring... 

   destruct (Qle_dec_weak 0 ((a+c)*(f+h)-(b+d)*(e+g))) as [H_det|H_det].
    (* q(1,r2)<=q(1,1) *)
    apply Rle_trans with (((a+c)+(b+d))/((e+g)+(f+h)))%R.
     stepr (((Qplus a c)*1+(Qplus b d))/((Qplus e g)*(1)+(Qplus f h)))%R.
      apply (det_nonneg_nondecreasing (a+c) (b+d) (e+g) (f+h) r2 (1)%R H_bounded2 H_det Hr2 one_is_in_base_interval
                                         (proj2 Hr2)).
      realify_Q_goal; apply (f_equal2 Rdiv); ring... 
     rationalify_R; trivial; stepl xi_rr; [apply Qle_Qmax4_4|subst xi_rr; unfold as_Tensor_Q, fst,snd; field; trivial].
    (* q(1,r2)<=q(1,-1) *)
    apply Rle_trans with (((b+d)-(a+c))/((f+h)-(e+g)))%R.
     stepr (((Qplus a c)*(-1)+(Qplus b d))/((Qplus e g)*(-1)+(Qplus f h)))%R.
      apply (det_nonpos_nonincreasing (a+c) (b+d) (e+g) (f+h) (-1)%R r2 H_bounded2 H_det min_one_is_in_base_interval Hr2 (proj1 Hr2)).
      realify_Q_goal; apply (f_equal2 Rdiv); ring... 

     rationalify_R; trivial; stepl xi_rl; [apply Qle_Qmax4_3|subst xi_rl; unfold as_Tensor_Q, fst,snd; field; trivial].
  (* END 0<=Det2, SPLIT 2 *)

  (* Det2<=0, SPLIT 1 (3/4 OF TOTAL) *)
  (* q is decreasing with r2 fixed, so we prove -1<=q(1,r2)<= q(r1,r2) *)
  apply Rle_trans with (((Qplus a c)*r2+(Qplus b d))/((Qplus e g)*r2+(Qplus f h)))%R.

   destruct (Qle_dec_weak 0 ((a+c)*(f+h)-(b+d)*(e+g))) as [H_det|H_det].
    (* q(1,-1)<=q(1,r2) *)
    apply Rle_trans with (((b+d)-(a+c))/((f+h)-(e+g)))%R.

     rationalify_R; trivial; stepr xi_rl; [apply Qle_Qmin4_3|subst xi_rl; unfold as_Tensor_Q, fst,snd; field; trivial].
     stepl (((Qplus a c)*(-1)+(Qplus b d))/((Qplus e g)*(-1)+(Qplus f h)))%R.
      apply (det_nonneg_nondecreasing (a+c) (b+d) (e+g) (f+h) (-1)%R r2 H_bounded2 H_det min_one_is_in_base_interval Hr2 (proj1 Hr2)).
      realify_Q_goal; apply (f_equal2 Rdiv); ring... 
    (* q(1,1)<=q(1,r2) *)
    apply Rle_trans with (((a+c)+(b+d))/((e+g)+(f+h)))%R.
     rationalify_R; trivial; stepr xi_rr; [apply Qle_Qmin4_4|subst xi_rr; unfold as_Tensor_Q, fst,snd; field; trivial].
     stepl (((Qplus a c)*1+(Qplus b d))/((Qplus e g)*(1)+(Qplus f h)))%R.
      apply (det_nonpos_nonincreasing (a+c) (b+d) (e+g) (f+h) r2 (1)%R H_bounded2 H_det Hr2 one_is_in_base_interval
                                         (proj2 Hr2)).
      realify_Q_goal; apply (f_equal2 Rdiv); ring... 
   (* This is the subgoal generated by Rle trans. Back to: q(1,r2)<=q(r1,r2) *)
   stepl ((a*1*r2+b*1+c*r2+d)/(e*1*r2+f*1+g*r2+h))%R.
    apply (det2_nonpos_nonincreasing _ _ _ _ _ _ _ _ _ _ _ H_bounded Hr2 H_det2 Hr1 one_is_in_base_interval
                                         (proj2 Hr1)).
    realify_Q_goal; apply (f_equal2 Rdiv); ring... 
  (* END Det2<=0, SPLIT 1 *)

  (* Det2<=0, SPLIT 2 (4/4 OF TOTAL) *)
  (* q is decreasing with r2 fixed, so we prove q(r1,r2)<=q(-1,r2)<=0 *)
  apply Rle_trans with (((Qminus c a)*r2+(Qminus d b))/((Qminus g e)*r2+(Qminus h f)))%R.
   (* This is the subgoal generated by Rle trans. Back to: q(r1,r2)<=q(-1,r2) *)
   stepr ((a*(-1)*r2+b*(-1)+c*r2+d)/(e*(-1)*r2+f*(-1)+g*r2+h))%R.
    apply (det2_nonpos_nonincreasing _ _ _ _ _ _ _ _ _ _ _ H_bounded Hr2 H_det2 min_one_is_in_base_interval Hr1
                                         (proj1 Hr1)).
    realify_Q_goal; apply (f_equal2 Rdiv); ring...

   destruct (Qle_dec_weak 0 ((c-a)*(h-f)-(d-b)*(g-e))) as [H_det|H_det].
    (* q(-1,r2)<=q(-1,1) *)
    apply Rle_trans with (((c-a)+(d-b))/((g-e)+(h-f)))%R.

     stepr (((Qminus c a)*1+(Qminus d b))/((Qminus g e)*1+(Qminus h f)))%R.
      apply (det_nonneg_nondecreasing (c-a) (d-b) (g-e) (h-f) r2 (1)%R H_bounded1 H_det Hr2 one_is_in_base_interval (proj2 Hr2)).
      realify_Q_goal; apply (f_equal2 Rdiv); ring...

     rationalify_R; trivial; stepl xi_lr; [apply Qle_Qmax4_2|subst xi_lr; unfold as_Tensor_Q, fst,snd; field; trivial].
    (* q(-1,r2)<=q(-1,-1) *)
    apply Rle_trans with (((a-c)+(d-b))/((e-g)+(h-f)))%R.
     stepr (((Qminus c a)*(-1)+(Qminus d b))/((Qminus g e)*(-1)+(Qminus h f)))%R.
      apply (det_nonpos_nonincreasing (c-a) (d-b) (g-e) (h-f) (-1)%R r2 H_bounded1 H_det min_one_is_in_base_interval Hr2 (proj1 Hr2)).
      realify_Q_goal; apply (f_equal2 Rdiv); ring...
     rationalify_R; trivial; stepl xi_ll; [apply Qle_Qmax4_1|subst xi_ll; unfold as_Tensor_Q, fst,snd; field; trivial].
  (* END Det2<=0, SPLIT 2 *)
Qed.
