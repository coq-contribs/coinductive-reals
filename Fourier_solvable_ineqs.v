(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import Reals.
Require Import R_addenda.
Require Import Fourier.

(** This is an auxiliary file includes very specific basic facts about
real numbers in and around the base interval. *)


Lemma Two_pos: 0<2.
Proof.
 fourier.
Qed.

Lemma Three_pos: 0<3.
Proof. 
 fourier.
Qed.

Lemma Four_pos: 0<4.
Proof. 
 fourier.
Qed.

Lemma minus_One_neg: (-1)<0.
Proof.
 fourier.
Qed.

Lemma Half_pos: 0<1/2.
Proof.
 fourier.
Qed.

Lemma minus_Half_neg: (-1)/2<0.
Proof.
 fourier.
Qed.

Lemma Third_pos: 0<1/3.
Proof.
 fourier.
Qed.

Lemma minus_Third_neg: (-1)/3<0.
Proof.
 fourier.
Qed.


Hint Resolve Rlt_0_1 Two_pos Three_pos Four_pos minus_One_neg Half_pos
             minus_Half_neg Third_pos minus_Third_neg.

(* Properties of numbers in the base interval *)

Lemma base_plus_3_pos:forall r, -1 <= r ->  0 < (r+3).
Proof.
 intros r Hr; fourier.
Qed.

Hint Resolve base_plus_3_pos.

Lemma base_plus_3_nonzero:forall r, -1 <= r ->  (r+3)<>0.
Proof.
 intros r Hr; apply sym_not_eq; apply Rlt_not_eq; auto.
Qed.

Lemma min_base_plus_3_pos:forall r, r <= 1 ->  0 < (-r+3).
Proof.
 intros r Hr; fourier.
Qed.

Hint Resolve min_base_plus_3_pos.

Lemma min_base_plus_3_nonzero:forall r, r<=1 ->  (-r+3)<>0.
Proof.
 intros r Hr; apply sym_not_eq; apply Rlt_not_eq; auto.
Qed.

Hint Resolve base_plus_3_nonzero min_base_plus_3_nonzero.

Lemma rep_lb_auxiliary_L:forall l' r, 0 <= l' + 1 -> 0 < l' + 3 -> -1 <= r -> r <= 0 -> l' <= (3 * r + 1) / (- r + 1) ->
   (l' - 1) / (l' + (2 + 1)) <= r.
Proof.
 intros l' r H1 H2 Hr1 Hr2 IH.
 apply Rle_zero_Rminus.
 generalize (Rle_Rminus_zero _ _ IH); clear IH.
 rewrite Rminus_Rdiv_Rmult; try (solve [apply Rlt_not_eq ; fourier| apply Rlt_not_eq' ; fourier]).
 rewrite Rdiv_Rminus_Rmult; try (solve [apply Rlt_not_eq ; fourier| apply Rlt_not_eq' ; fourier]).
 intro IH.
 assert (Hr3:0< -r+1); [fourier|].
 generalize (Rle_pos_nonneg_Rdiv _ _ Hr3 IH); clear IH; intro IH.
 unfold Rdiv; apply Rle_mult_inv_pos; try fourier. 
 stepr (3*r+1-(-r+1)*l'); auto; ring.
Qed.


Lemma rep_lb_auxiliary_R:forall l' r, 0 <= -l' + 1 -> 0 < -l' + 3 -> 0 <= r -> r <= 1 -> l' <= (3 * r - 1) / (r + 1) ->
   (l' + 1) / (-l' + (2 + 1)) <= r.
Proof.
 intros l' r H1 H2 Hr1 Hr2 IH.
 apply Rle_zero_Rminus.
 generalize (Rle_Rminus_zero _ _ IH); clear IH.
 rewrite Rminus_Rdiv_Rmult; try (solve [apply Rlt_not_eq ; fourier| apply Rlt_not_eq' ; fourier]).
 rewrite Rdiv_Rminus_Rmult; try (solve [apply Rlt_not_eq ; fourier| apply Rlt_not_eq' ; fourier]).
 intro IH.
 assert (Hr3:0< r+1); [fourier|].
 generalize (Rle_pos_nonneg_Rdiv _ _ Hr3 IH); clear IH; intro IH.
 unfold Rdiv; apply Rle_mult_inv_pos; try fourier. 
 stepr (3*r-1-(r+1)*l'); auto; ring.
Qed.

Lemma rep_lb_auxiliary_M:forall l' r, l' <= 3*r -> l'/(2 + 1) <= r.
Proof.
 intros l' r IH; fourier.
Qed.

Lemma rep_ub_auxiliary_L:forall u' r, 0 <= u' + 1 -> 0 < u' + 3 -> -1 <= r -> r <= 0 -> (3 * r + 1) / (- r + 1) <= u' ->
   r <= (u' - 1) / (u' + (2 + 1)).
Proof.
 intros u' r H1 H2 Hr1 Hr2 IH.
 apply Rle_zero_Rminus.
 generalize (Rle_Rminus_zero _ _ IH); clear IH.
 rewrite Rminus_Rdiv_Rmult; try (solve [apply Rlt_not_eq ; fourier| apply Rlt_not_eq' ; fourier]).
 rewrite Rdiv_Rminus_Rmult; try (solve [apply Rlt_not_eq ; fourier| apply Rlt_not_eq' ; fourier]).
 intro IH.
 assert (Hr3:0< -r+1); [fourier|].
 generalize (Rle_pos_nonneg_Rdiv _ _ Hr3 IH); clear IH; intro IH.
 unfold Rdiv; apply Rle_mult_inv_pos; try fourier. 
 stepr ((-r+1)*u'-(3*r+1)); auto; ring.
Qed.

Lemma rep_ub_auxiliary_R:forall u' r, 0 <= -u' + 1 -> 0 < -u' + 3 -> 0 <= r -> r <= 1 -> (3 * r - 1) / (r + 1) <= u' ->
   r <= (u' + 1) / (-u' + (2 + 1)).
Proof.
 intros u' r H1 H2 Hr1 Hr2 IH.
 apply Rle_zero_Rminus.
 generalize (Rle_Rminus_zero _ _ IH); clear IH.
 rewrite Rminus_Rdiv_Rmult; try (solve [apply Rlt_not_eq ; fourier| apply Rlt_not_eq' ; fourier]).
 rewrite Rdiv_Rminus_Rmult; try (solve [apply Rlt_not_eq ; fourier| apply Rlt_not_eq' ; fourier]).
 intro IH.
 assert (Hr3:0< r+1); [fourier|].
 generalize (Rle_pos_nonneg_Rdiv _ _ Hr3 IH); clear IH; intro IH.
 unfold Rdiv; apply Rle_mult_inv_pos; try fourier. 
 stepr ((r+1)*u'-(3*r-1)); auto; ring.
Qed.

Lemma rep_ub_auxiliary_M:forall u' r, 3*r <= u' -> r <= u'/(2 + 1).
Proof.
 intros u' r IH; fourier.
Qed.


Lemma N_2_epsilon_plus_one:forall eps N, 0 < eps -> 2 / eps< IZR (Z_of_nat N) -> 2/((IZR (Z_of_nat N))+1) <eps.
Proof.
 intros eps N H_eps H_N.
 apply Rlt_zero_Rminus.
 (* TP 0<(IZR (Z_of_nat N) + 1*)
 assert (H_N_1:0<(IZR (Z_of_nat N)+1));
 [ rewrite_all <- INR_IZR_INZ; rewrite <- S_INR; auto|].

 generalize (Rlt_Rminus_zero _ _ H_N);
 repeat rewrite Rminus_Rdiv_Rmult; auto;
  clear H_N; intro H_N; unfold Rdiv; apply Rlt_mult_inv_pos; auto.
   generalize (Rlt_pos_pos_Rdiv _ _ H_eps H_N); clear H_N; intro H_N;
   apply Rlt_trans with (eps*(IZR (Z_of_nat N))-2); auto;
   apply Rlt_zero_Rminus; stepr eps; auto; ring.
Qed.

Lemma epsilon_pos_2_epsilon:forall eps, 0<eps-> 0<2/eps.
Proof.
 intros eps H_eps; unfold Rdiv; apply Rlt_mult_inv_pos; auto.
Qed.

Hint Resolve epsilon_pos_2_epsilon.

Lemma up_2_epsilon:forall eps, 0<eps-> (0< up (2/eps))%Z.
Proof.
 intros eps H_eps.
  apply lt_O_IZR.
    apply Raxioms.Rlt_trans with (2 / eps)%R; auto.
    elim (Raxioms.archimed (2/eps)); auto.  
Qed.

Hint Resolve up_2_epsilon.

Lemma very_sepcific_0:forall l y, l - y < 2 -> -1 <= l -> 0 < y + 3.
Proof.
 intros; fourier.
Qed.

Lemma very_sepcific_1:forall l y, -2 < l - y -> l <= 1 -> 0 < -y + 3.
Proof.
 intros; fourier.
Qed.


Lemma rep_interval_auxiliary: forall b l u r1 r2, r2 <= u -> r1 <= u -> l <= r2 -> l <= r1 -> u - l <= b->
                         -b <= r1-r2 <= b.
Proof.
 intros; split; fourier.
Qed.

Lemma Bounded_M_pos_auxiliary_1:forall c d r, 0 < d - c -> (0 < c)%R -> (-1 <= r <= 1)%R -> 0<c*r+d.
Proof. 
 intros c d r Hdc Hc [Hr1 Hr2];
 apply Rlt_le_trans with (d-c); trivial;
 stepl (c*(-1)+d); [|ring]; apply Rplus_le_compat_r; apply Rfourier_le; trivial.
Qed.

Lemma Bounded_M_pos_auxiliary_2:forall c d r, 0 < d + c -> (c < 0)%R -> (-1 <= r <= 1)%R -> 0<c*r+d.
Proof. 
 intros c d r Hdc Hc [Hr1 Hr2];
 apply Rlt_le_trans with (d+c); trivial;
 stepl (c*(1)+d); [|ring]; apply Rplus_le_compat_r; apply Rmult_le_compat_neg_l; trivial; fourier.
Qed.

Lemma Bounded_M_pos_auxiliary_3:forall c d r, 0 <= d - c -> (0 < c)%R -> (-1 <= r <= 1)%R -> 0<=c*r+d.
Proof. 
 intros c d r Hdc Hc [Hr1 Hr2];
 apply Rle_trans with (d-c); trivial;
 stepl (c*(-1)+d); [|ring]; apply Rplus_le_compat_r; apply Rfourier_le; trivial.
Qed.

Lemma Bounded_M_pos_auxiliary_4:forall c d r, 0 <= d + c -> (c < 0)%R -> (-1 <= r <= 1)%R -> 0<=c*r+d.
Proof. 
 intros c d r Hdc Hc [Hr1 Hr2];
 apply Rle_trans with (d+c); trivial;
 stepl (c*(1)+d); [|ring]; apply Rplus_le_compat_r; apply Rmult_le_compat_neg_l; trivial; fourier.
Qed.

Lemma Bounded_M_neg_auxiliary_1:forall c d r, d + c < 0 -> (0 < c)%R -> (-1 <= r <= 1)%R -> c*r+d<0.
Proof. 
 intros c d r Hdc Hc [Hr1 Hr2];
 apply Rle_lt_trans with (d+c); trivial;
 stepr (c*(1)+d); [|ring]; apply Rplus_le_compat_r; apply Rfourier_le; trivial.
Qed.

Lemma Bounded_M_neg_auxiliary_2:forall c d r, d - c < 0 -> (c < 0)%R -> (-1 <= r <= 1)%R -> c*r+d<0.
Proof. 
 intros c d r Hdc Hc [Hr1 Hr2];
 apply Rle_lt_trans with (d-c); trivial;
 stepr (c*(-1)+d); [|ring]; apply Rplus_le_compat_r; apply Rmult_le_compat_neg_l; trivial; fourier.
Qed.

Lemma Bounded_M_neg_auxiliary_3:forall c d r, d + c <= 0 -> (0 < c)%R -> (-1 <= r <= 1)%R -> c*r+d<=0.
Proof. 
 intros c d r Hdc Hc [Hr1 Hr2];
 apply Rle_trans with (d+c); trivial;
 stepr (c*(1)+d); [|ring]; apply Rplus_le_compat_r; apply Rfourier_le; trivial.
Qed.

Lemma Bounded_M_neg_auxiliary_4:forall c d r, d - c <= 0 -> (c < 0)%R -> (-1 <= r <= 1)%R -> c*r+d<=0.
Proof. 
 intros c d r Hdc Hc [Hr1 Hr2];
 apply Rle_trans with (d-c); trivial;
 stepr (c*(-1)+d); [|ring]; apply Rplus_le_compat_r; apply Rmult_le_compat_neg_l; trivial; fourier.
Qed.


Lemma distance_Moebius:forall a b c d x y, c*y+d<>0 -> c*x+d<>0 ->
  ((a*y+b)/(c*y+d))-((a*x+b)/(c*x+d))=((y-x)*(a*d-b*c))/((c*y+d)*(c*x+d)).
Proof.
 intros a b c d x y Hcyd Hcxd; rewrite Rminus_Rdiv; auto; apply (f_equal2 Rdiv); ring.
Qed.

Lemma min_one_is_in_base_interval:-1 <= -1 <= 1.
Proof.
 split; fourier.
Qed.

Lemma one_is_in_base_interval:-1 <= 1 <= 1.
Proof.
 split; fourier.
Qed.

Lemma Incl_M_L_unfolded_auxiliary_1: forall a b c d, d - c <> 0 -> 
                (d - c) * (-1 / 2 - 1 / 2) <= (b - a) * ((2 + 1) / 2 - 1 / 2) ->
                (b - a) * (1 / 2 + (2 + 1) / 2) <= (d - c) * (1 / 2 + -1 / 2) ->
                 -1 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc.
 (* TP : (c-d)<> 0 *)
 assert (Hcd:(c-d)<>0);[apply Rminus_eq_contra; intro; apply Hdc; apply Rminus_diag_eq; auto|];
 replace (1 / 2 + -1 / 2) with 0; [|field;auto];
 replace (-1 / 2 - 1 / 2) with (-1); [|field;auto];
 replace ((2 + 1) / 2 - 1 / 2) with 1; [|field;auto];
 replace (1 / 2 + (2 + 1) / 2) with 2; [|field;auto];
 replace ((b - a) * 2) with ((b-a)+(b-a)); [|field;auto].
 rewrite Rmult_0_r; rewrite Rmult_1_r;
 intros H1 H2; stepl ((-1)/1); [|field;auto]; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=d-c).
   apply Ropp_le_cancel; stepl ((d-c)*(-1));[|ring]; apply Rle_trans with (b-a); trivial; fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepl ((d - c) * -1); [|ring]; stepr (b - a); [|ring]; trivial.
Qed. 

Lemma Incl_M_L_unfolded_auxiliary_2: forall a b c d, c + d <> 0 -> 
                (c + d) * (-1 / 2 - 1 / 2) <= (a + b) * ((2 + 1) / 2 - 1 / 2) ->
		(a + b) * (1 / 2 + (2 + 1) / 2) <= (c + d) * (1 / 2 + -1 / 2) ->
                    (a + b) / (c + d) <= 0.
Proof.
 intros a b c d Hdc.
 (* TP : (c+d)<> 0 *)
 replace (1 / 2 + -1 / 2) with 0; [|field;auto];
 replace (-1 / 2 - 1 / 2) with (-1); [|field;auto];
 replace ((2 + 1) / 2 - 1 / 2) with 1; [|field;auto];
 replace (1 / 2 + (2 + 1) / 2) with 2; [|field;auto];
 replace ((a+b) * 2) with ((a+b)+(a+b)); [|field;auto];
 rewrite Rmult_0_r; rewrite Rmult_1_r.
 intros H1 H2; stepr (0/1); [|field;auto]; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=c+d).
   apply Ropp_le_cancel; stepl ((c+d)*(-1));[|ring]; apply Rle_trans with (a+b); trivial; fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepr 0; [|ring]; stepl (a+b); [|ring]; fourier.
Qed. 


Lemma Incl_M_L_unfolded_auxiliary_3: forall a b c d, c+d  <> 0 -> 
                (c + d) * (-1 / 2 - 1 / 2) <= (a + b) * ((2 + 1) / 2 - 1 / 2) ->
		(a + b) * (1 / 2 + (2 + 1) / 2) <= (c + d) * (1 / 2 + -1 / 2) ->
                    -1 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc.
 replace (1 / 2 + -1 / 2) with 0; [|field;auto];
 replace (-1 / 2 - 1 / 2) with (-1); [|field;auto];
 replace ((2 + 1) / 2 - 1 / 2) with 1; [|field;auto];
 replace (1 / 2 + (2 + 1) / 2) with 2; [|field;auto];
 replace ((a+b) * 2) with ((a+b)+(a+b)); [|field;auto];
 rewrite Rmult_0_r; rewrite Rmult_1_r;
 intros H1 H2; stepl ((-1)/1); [|field;auto]; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=c+d).
   apply Ropp_le_cancel; stepl ((c+d)*(-1));[|ring]; apply Rle_trans with (a+b); trivial; fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepl ((c + d) * -1); [|ring]; stepr (a+b); [|ring]; trivial. 
Qed. 

Lemma Incl_M_L_unfolded_auxiliary_4: forall a b c d, d - c <> 0 -> 
                (d - c) * (-1 / 2 - 1 / 2) <= (b - a) * ((2 + 1) / 2 - 1 / 2) ->
                (b - a) * (1 / 2 + (2 + 1) / 2) <= (d - c) * (1 / 2 + -1 / 2) ->
                 (b - a) / (d - c)<=0.
Proof.
 intros a b c d Hdc.
 (* TP : (c-d)<> 0 *)
 assert (Hcd:(c-d)<>0);[apply Rminus_eq_contra; intro; apply Hdc; apply Rminus_diag_eq; auto|];
 replace (1 / 2 + -1 / 2) with 0; [|field;auto];
 replace (-1 / 2 - 1 / 2) with (-1); [|field;auto];
 replace ((2 + 1) / 2 - 1 / 2) with 1; [|field;auto];
 replace (1 / 2 + (2 + 1) / 2) with 2; [|field;auto];
 replace ((b - a) * 2) with ((b-a)+(b-a)); [|field;auto].
 rewrite Rmult_0_r; rewrite Rmult_1_r;
 intros H1 H2; stepr (0/1); [|field;auto]; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=d-c).
   apply Ropp_le_cancel; stepl ((d-c)*(-1));[|ring]; apply Rle_trans with (b-a); trivial; fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepr 0; [|ring]; stepl (b-a); [|ring]; fourier.
Qed. 

Lemma Incl_M_R_unfolded_auxiliary_1: forall a b c d, d - c <> 0 -> 
                (d - c) * (1 / 2 - 1 / 2) <= (b - a) * ((2 + 1) / 2 - -1 / 2) ->
		(b - a) * (-1 / 2 + (2 + 1) / 2) <= (d - c) * (1 / 2 + 1 / 2) ->
                 0 <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc.
 (* TP : (c-d)<> 0 *)
 assert (Hcd:(c-d)<>0);[apply Rminus_eq_contra; intro; apply Hdc; apply Rminus_diag_eq; auto|];
 replace (1 / 2 - 1 / 2) with 0; [|field;auto];
 replace (1 / 2 + 1 / 2) with 1; [|field;auto];
 replace ((2 + 1) / 2 - -1 / 2) with 2; [|field;auto];
 replace (-1 / 2 + (2 + 1) / 2) with 1; [|field;auto];
 replace ((b - a) * 2) with ((b-a)+(b-a)); [|ring;auto];
 rewrite Rmult_0_r; rewrite Rmult_1_r.
 intros H1 H2; stepl (0/1); [|field;auto]; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=d-c).
   stepr ((d-c)*1);[|ring]; apply Rle_trans with (b-a); trivial; fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepl 0; [|ring]; stepr (b - a); [|ring]; fourier.
Qed. 

Lemma Incl_M_R_unfolded_auxiliary_2: forall a b c d, c + d <> 0 -> 
                (c + d) * (1 / 2 - 1 / 2) <= (a + b) * ((2 + 1) / 2 - -1 / 2) ->
		(a + b) * (-1 / 2 + (2 + 1) / 2) <= (c + d) * (1 / 2 + 1 / 2) ->
                    (a + b) / (c + d) <= 1.
Proof.
 intros a b c d Hdc.
 replace (1 / 2 - 1 / 2) with 0; [|field;auto];
 replace (1 / 2 + 1 / 2) with 1; [|field;auto];
 replace ((2 + 1) / 2 - -1 / 2) with 2; [|field;auto];
 replace (-1 / 2 + (2 + 1) / 2) with 1; [|field;auto];
 replace ((a+b) * 2) with ((a+b)+(a+b)); [|ring;auto];
 rewrite Rmult_0_r; rewrite Rmult_1_r.
 intros H1 H2; stepr (1/1); [|field;auto]; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=c+d).
   stepr ((c+d)*1);[|ring]; apply Rle_trans with (a+b); trivial; fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepr ((c + d)*1); [|ring]; stepl (a+b); [|ring]; trivial. 
Qed. 

Lemma Incl_M_R_unfolded_auxiliary_3: forall a b c d, c+d  <> 0 -> 
                (c + d) * (1 / 2 - 1 / 2) <= (a + b) * ((2 + 1) / 2 - -1 / 2) ->
		(a + b) * (-1 / 2 + (2 + 1) / 2) <= (c + d) * (1 / 2 + 1 / 2) ->
                    0 <= (a + b) / (c + d).
Proof.
 intros a b c d Hdc.
 replace (1 / 2 - 1 / 2) with 0; [|field;auto];
 replace (1 / 2 + 1 / 2) with 1; [|field;auto];
 replace ((2 + 1) / 2 - -1 / 2) with 2; [|field;auto];
 replace (-1 / 2 + (2 + 1) / 2) with 1; [|field;auto];
 replace ((a+b) * 2) with ((a+b)+(a+b)); [|ring;auto];
 rewrite Rmult_0_r; rewrite Rmult_1_r.
 intros H1 H2; stepl (0/1); [|field;auto]; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=c+d).
   stepr ((c+d)*1);[|ring]; apply Rle_trans with (a+b); trivial; fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepl 0; [|ring]; stepr (a+b); [|ring]; fourier. 
Qed. 

Lemma Incl_M_R_unfolded_auxiliary_4: forall a b c d, d - c <> 0 -> 
                (d - c) * (1 / 2 - 1 / 2) <= (b - a) * ((2 + 1) / 2 - -1 / 2) ->
		(b - a) * (-1 / 2 + (2 + 1) / 2) <= (d - c) * (1 / 2 + 1 / 2) ->
                   (b - a) / (d - c)<=1.
Proof.
 intros a b c d Hdc.
 replace (1 / 2 - 1 / 2) with 0; [|field;auto];
 replace (1 / 2 + 1 / 2) with 1; [|field;auto];
 replace ((2 + 1) / 2 - -1 / 2) with 2; [|field;auto];
 replace (-1 / 2 + (2 + 1) / 2) with 1; [|field;auto];
 replace ((b - a) * 2) with ((b-a)+(b-a)); [|ring;auto];
 rewrite Rmult_0_r; rewrite Rmult_1_r.
 intros H1 H2; stepr (1/1); [|field;auto]; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=d-c).
   stepr ((d-c)*1);[|ring]; apply Rle_trans with (b-a); trivial; fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepr ((d-c)*1); [|ring]; stepl (b-a); [|ring]; trivial.
Qed. 

Lemma Incl_M_M_unfolded_auxiliary_1: forall a b c d, d - c <> 0 -> 
                (d - c) * (0 / 1 - 1 / 1) <= (b - a) * ((2 + 1) / 1 - 0 / 1) ->
                (b - a) * (0 / 1 + (2 + 1) / 1) <= (d - c) * (1 / 1 + 0 / 1) ->
                 ((-1)/3) <= (b - a) / (d - c).
Proof.
 intros a b c d Hdc.
 replace (0 / 1 - 1 / 1) with (-1); [|field;auto];
 replace ((2 + 1) / 1 - 0 / 1) with 3; [|field;auto];
 replace (0 / 1 + (2 + 1) / 1) with 3; [|field;auto];
 replace (1 / 1 + 0 / 1) with 1; [|field;auto];
 replace ((b - a) * 3) with ((b-a)+(b-a)+(b-a)); [|ring;auto];
 replace ((d - c) * -1) with (-(d-c)); [|ring;auto];
 rewrite Rmult_1_r.
 intros H1 H2; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=d-c).
   fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepl (- (d - c)); [|ring]; stepr ((b-a)+(b-a)+(b-a)); [|ring]; trivial.
Qed. 

Lemma Incl_M_M_unfolded_auxiliary_2: forall a b c d, c + d <> 0 -> 
                (c + d) * (0 / 1 - 1 / 1) <= (a + b) * ((2 + 1) / 1 - 0 / 1) ->
		(a + b) * (0 / 1 + (2 + 1) / 1) <= (c + d) * (1 / 1 + 0 / 1) ->
                    (a + b) / (c + d) <= 1/3.
Proof.
 intros a b c d Hdc.
 replace (0 / 1 - 1 / 1) with (-1); [|field;auto];
 replace ((2 + 1) / 1 - 0 / 1) with 3; [|field;auto];
 replace (0 / 1 + (2 + 1) / 1) with 3; [|field;auto];
 replace (1 / 1 + 0 / 1) with 1; [|field;auto];
 replace ((a+b) * 3) with ((a+b)+(a+b)+(a+b)); [|ring;auto];
 replace ((c+d) * -1) with (-(c+d)); [|ring;auto];
 rewrite Rmult_1_r.
 intros H1 H2; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=c+d).
   fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepr (c + d); [|ring]; stepl ((a+b)+(a+b)+(a+b)); [|ring]; trivial. 
Qed. 


Lemma Incl_M_M_unfolded_auxiliary_3: forall a b c d, c+d  <> 0 -> 
                (c + d) * (0 / 1 - 1 / 1) <= (a + b) * ((2 + 1) / 1 - 0 / 1) ->
		(a + b) * (0 / 1 + (2 + 1) / 1) <= (c + d) * (1 / 1 + 0 / 1) ->
                    (-1)/3<=(a + b) / (c + d).
Proof.
 intros a b c d Hdc.
 replace (0 / 1 - 1 / 1) with (-1); [|field;auto];
 replace ((2 + 1) / 1 - 0 / 1) with 3; [|field;auto];
 replace (0 / 1 + (2 + 1) / 1) with 3; [|field;auto];
 replace (1 / 1 + 0 / 1) with 1; [|field;auto];
 replace ((a+b) * 3) with ((a+b)+(a+b)+(a+b)); [|ring;auto];
 replace ((c+d) * -1) with (-(c+d)); [|ring;auto];
 rewrite Rmult_1_r.
 intros H1 H2; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=c+d).
   fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepl (-(c + d)); [|ring]; stepr ((a+b)+(a+b)+(a+b)); [|ring]; trivial. 
Qed.

Lemma Incl_M_M_unfolded_auxiliary_4: forall a b c d, d - c <> 0 -> 
                (d - c) * (0 / 1 - 1 / 1) <= (b - a) * ((2 + 1) / 1 - 0 / 1) ->
                (b - a) * (0 / 1 + (2 + 1) / 1) <= (d - c) * (1 / 1 + 0 / 1) ->
                   (b - a) / (d - c)<=1/3.
Proof.
 intros a b c d Hdc.
 replace (0 / 1 - 1 / 1) with (-1); [|field;auto];
 replace ((2 + 1) / 1 - 0 / 1) with 3; [|field;auto];
 replace (0 / 1 + (2 + 1) / 1) with 3; [|field;auto];
 replace (1 / 1 + 0 / 1) with 1; [|field;auto];
 replace ((b - a) * 3) with ((b-a)+(b-a)+(b-a)); [|ring;auto];
 replace ((d - c) * -1) with (-(d-c)); [|ring;auto];
 rewrite Rmult_1_r.
 intros H1 H2; apply Rmult_Rdiv_pos_Rle; auto.
  assert (H3:0<=d-c).
   fourier.
   destruct (Rle_lt_or_eq_dec _ _ H3) as [H4|H4]; trivial; apply False_ind; apply Hdc; auto. 
  stepr (d - c); [|ring]; stepl ((b-a)+(b-a)+(b-a)); [|ring]; trivial.
Qed.

Lemma distance_Tensor:forall a b c d e f g h r x y, e*y*r+f*y+g*r+h<>0 -> e*x*r+f*x+g*r+h<>0 ->
  ((a*y*r+b*y+c*r+d)/(e*y*r+f*y+g*r+h)) - ((a*x*r+b*x+c*r+d)/(e*x*r+f*x+g*r+h))=
  ((y-x)*((a*r+b)*(g*r+h)-(c*r+d)*(e*r+f)))/((e*y*r+f*y+g*r+h)*(e*x*r+f*x+g*r+h)).
Proof.
 intros a b c d e f g h r x y Hcyd Hcxd; rewrite Rminus_Rdiv; auto; apply (f_equal2 Rdiv); ring.
Qed.
 
