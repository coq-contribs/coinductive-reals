(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import digits.
Require Import ub.
Require Import rep.
Require Import Rseries.
Require Import Rdefinitions.
Require Import RIneq.
Require Import Rcomplete.
From QArithSternBrocot Require Import R_addenda.
Require Import Fourier_solvable_ineqs.

(** This file deals with the correctness of the representation predicate [rep]. *)

Lemma lb_Cauchy:forall alpha, Rseries.Cauchy_crit (lb alpha).
Proof.
 intros alpha.
 intros eps H_eps_pos.
 set (N:=Z.abs_nat (up (2 / eps))).
 exists N.
 intros m n Hn Hm.
 unfold Rfunctions.R_dist.
 apply Raxioms.Rlt_trans with (Qminus (ub alpha N)(lb alpha N)).
 set (u_N:=ub alpha N); set (l_N:=lb alpha N); set (l_n:=lb alpha n);set (l_m:=lb alpha m).


  apply Rbasic_fun.Rabs_def1.

   repeat rewrite <- Q_to_Rminus; apply Q_to_Rlt.
   apply Qlt_Zero_Qminus.
   stepr (Qplus (Qminus u_N l_m)(Qminus l_n l_N)); try ring.
   apply Qlt_le_reg_pos.
    apply Qlt_Qminus_Zero; subst u_N l_m; apply lb_lt_ub.
    apply Qle_Qminus_Zero; subst l_N l_n; apply lb_nondecreasing; auto.

   apply RIneq.Ropp_lt_cancel; rewrite RIneq.Ropp_involutive; rewrite RIneq.Ropp_minus_distr.
   repeat rewrite <- Q_to_Rminus; apply Q_to_Rlt.
   apply Qlt_Zero_Qminus.
   stepr (Qplus(Qminus u_N l_n)(Qminus l_m l_N)); try ring.
   apply Qlt_le_reg_pos.
    apply Qlt_Qminus_Zero; subst u_N l_n; apply lb_lt_ub.
    apply Qle_Qminus_Zero; subst l_N l_m; apply lb_nondecreasing; auto.

   apply RIneq.Rle_lt_trans with (Qdiv (Z_to_Q (Z_of_nat 2)) (Qplus (Z_to_Q (Z_of_nat N)) (Z_to_Q (Z_of_nat 1)))).

    apply Q_to_Rle; apply thesis_5_7_9.

    (* TP: 0 < IZR N +1 *)
    assert (H_N_plus_one_pos:(0 < Rdefinitions.IZR N +1)%R);
    [ apply RIneq.Rle_lt_trans with (Rdefinitions.IZR N); rewrite <- INR_IZR_INZ; auto with real| ].
    (* TP: IZR N +1 <> 0 *)
    assert (H_N_plus_one_nonzero:(Rdefinitions.IZR N +1<>0)%R); auto with real.

    elim (Raxioms.archimed (2/eps)); intros H_N _.
    rewrite <- (Z_of_nat_Zabs_nat_pos (up(2/eps))) in H_N.
    rewrite Q_to_Rdiv.
    rewrite Q_to_Rplus.
    repeat rewrite Z_to_Q_to_R_IZR.
    assert (2/eps-1<(Rdefinitions.IZR N))%R.

     apply Raxioms.Rlt_trans with (2/eps)%R; auto.
      apply RIneq.Rminus_lt.
      stepl (Ropp (Rdefinitions.IZR 1%nat)).
      simpl.
      apply RIneq.Ropp_lt_gt_0_contravar.
      apply Rlt_gt, Rlt_0_1.
      simpl; ring.

     simpl.
     apply Rmult_lt_reg_l with ((Rdefinitions.IZR N + 1)*(Rinv eps))%R.
     apply Fourier_util.Rlt_mult_inv_pos; auto.

      stepl (2/eps)%R.
       stepr (Rdefinitions.IZR N+1)%R.
        apply Rplus_lt_reg_r with (Ropp 1).
	stepl (2/eps -1)%R; try ring.
	stepr (Rdefinitions.IZR N)%R; auto; try ring.
       field; auto with real.
      field; auto with real.

    natq_S N; natq_zero; apply Z_to_Q_not_eq; apply inj_neq; discriminate.

    apply le_O_IZR.
    apply RIneq.Rlt_le.
    apply Raxioms.Rlt_trans with (2 / eps)%R; auto;
    unfold Rdiv; apply Fourier_util.Rlt_mult_inv_pos; auto; apply DiscrR.Rlt_R0_R2.
Qed.



(** This is the real number in #&#91;#-1,+1#&#93;# represented by [alpha] *)
Definition real_value alpha := (proj1_sig (Rcomplete.R_complete (lb alpha) (lb_Cauchy alpha))).

Lemma rep_lb: forall (k:nat) alpha r, rep alpha r -> ((lb alpha k)<=r)%R.
Proof.
 induction k.
  (* 0 *)
  intros alpha r H_rep.
  simpl; rewrite Q_to_R_Qneg_One.
  elim (rep_inv_interval _ _ H_rep); trivial.
  (* S k *)
  intros [[ | | ] alpha] r H_rep; rewrite lb_S_n; unfold hd,tl; set (l':=(lb alpha k)).
   (* L *)
   (* TP: Zero <= l'+ 1 *)
   assert (H_l'_one_nonneg: Zero <= l'+1);
   [ stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_low|].
   (* TP: Zero < l'+3 *)
   assert (H_l'_three_pos: Zero < l'+3);
   [ apply Qle_lt_trans with (l'+1); auto; apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|].

   generalize (Q_to_Rle _ _ H_l'_one_nonneg);
   generalize (Q_to_Rlt _ _ H_l'_three_pos);
   do 2 rewrite Q_to_Rplus; rewrite Q_to_R_Zero;
   do 2 rewrite Z_to_Q_to_R_IZR; intros H1 H2; simpl in H1,H2. 

   rewrite as_Moebius_Q_L; trivial; natZ_numerals;
   rewrite Q_to_Rdiv; auto;
   rewrite Q_to_Rplus; rewrite Q_to_Rminus;
   repeat rewrite Z_to_Q_to_R_IZR; simpl;
   elim (rep_L_inv_interval _ _ H_rep); intros Hr1 Hr2;
   generalize (IHk _ _ (rep_L_inv _ _ H_rep)); clear IHk; fold l'; intro IHk;
   apply rep_lb_auxiliary_L; auto; stepr (l'+(2+1))%R; auto; ring.
   (* R *)
   (* TP: Zero <= -l'+ 1 *)
   assert (H_min_l'_one_nonneg: Zero <= -l'+1);
   [stepr (1-l'); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_up|].
   (* TP: Zero < -l'+3 *)
   assert (H_min_l'_three_pos: Zero < -l'+3);
   [ apply Qle_lt_trans with ((-l')+1); auto;
     apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|].

   generalize (Q_to_Rle _ _ H_min_l'_one_nonneg);
   generalize (Q_to_Rlt _ _ H_min_l'_three_pos);
   do 2 rewrite Q_to_Rplus; rewrite Q_to_R_Zero; rewrite Q_to_Ropp;
   do 2 rewrite Z_to_Q_to_R_IZR; intros H1 H2; simpl in H1,H2. 

   rewrite as_Moebius_Q_R; trivial; natZ_numerals;
   rewrite Q_to_Rdiv; auto;
   repeat rewrite Q_to_Rplus; rewrite Q_to_Ropp;
   repeat rewrite Z_to_Q_to_R_IZR; simpl;
   elim (rep_R_inv_interval _ _ H_rep); intros Hr1 Hr2;
   generalize (IHk _ _ (rep_R_inv _ _ H_rep)); clear IHk; fold l'; intro IHk;
   apply rep_lb_auxiliary_R; auto; stepr (-l'+(2+1))%R; auto; ring.
   (* M *)
   rewrite as_Moebius_Q_M; natZ_numerals;
   rewrite Q_to_Rdiv; auto;
   rewrite Z_to_Q_to_R_IZR; simpl;
   elim (rep_M_inv_interval _ _ H_rep); intros Hr1 Hr2;
   generalize (IHk _ _ (rep_M_inv _ _ H_rep)); clear IHk; fold l'; intro IHk;
   apply rep_lb_auxiliary_M; auto. 
Qed.

Lemma rep_ub: forall (k:nat) alpha r, rep alpha r -> (r<=(ub alpha k))%R.
Proof.
 induction k.
  (* 0 *)
  intros alpha r H_rep;
  unfold ub; rewrite Z_to_Q_to_R_IZR; simpl;
  elim (rep_inv_interval _ _ H_rep); trivial.
  (* S k *)
  intros [[ | | ] alpha] r H_rep; rewrite ub_S_n; unfold hd,tl; set (u':=(ub alpha k)).
   (* L *)
   (* TP: Zero <= u'+ 1 *)
   assert (H_u'_one_nonneg: Zero <= u'+1);
   [ stepr (u'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_low|]. 
   (* TP: Zero < u'+3 *)
   assert (H_u'_three_pos: Zero < u'+3);
   [ apply Qle_lt_trans with (u'+1); auto; apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|].

   generalize (Q_to_Rle _ _ H_u'_one_nonneg);
   generalize (Q_to_Rlt _ _ H_u'_three_pos);
   do 2 rewrite Q_to_Rplus; rewrite Q_to_R_Zero;
   do 2 rewrite Z_to_Q_to_R_IZR; intros H1 H2; simpl in H1,H2. 

   rewrite as_Moebius_Q_L; trivial; natZ_numerals;
   rewrite Q_to_Rdiv; auto;
   rewrite Q_to_Rplus; rewrite Q_to_Rminus;
   repeat rewrite Z_to_Q_to_R_IZR; simpl;
   elim (rep_L_inv_interval _ _ H_rep); intros Hr1 Hr2;
   generalize (IHk _ _ (rep_L_inv _ _ H_rep)); clear IHk; fold u'; intro IHk;
   apply rep_ub_auxiliary_L; auto; stepr (u'+(2+1))%R; auto; ring.
   (* R *)
   (* TP: Zero <= -u'+ 1 *)
   assert (H_min_u'_one_nonneg: Zero <= -u'+1);
   [stepr (1-u'); try ring; apply Qle_Qminus_Zero; subst u'; apply ub_is_in_base_interval_up|].
   (* TP: Zero < -u'+3 *)
   assert (H_min_u'_three_pos: Zero < -u'+3);
   [ apply Qle_lt_trans with ((-u')+1); auto;apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|].
 
   generalize (Q_to_Rle _ _ H_min_u'_one_nonneg);
   generalize (Q_to_Rlt _ _ H_min_u'_three_pos);
   do 2 rewrite Q_to_Rplus; rewrite Q_to_R_Zero; rewrite Q_to_Ropp;
   do 2 rewrite Z_to_Q_to_R_IZR; intros H1 H2; simpl in H1,H2. 

   rewrite as_Moebius_Q_R; trivial; natZ_numerals;
   rewrite Q_to_Rdiv; auto;
   repeat rewrite Q_to_Rplus; rewrite Q_to_Ropp;
   repeat rewrite Z_to_Q_to_R_IZR; simpl;
   elim (rep_R_inv_interval _ _ H_rep); intros Hr1 Hr2;
   generalize (IHk _ _ (rep_R_inv _ _ H_rep)); clear IHk; fold u'; intro IHk;
   apply rep_ub_auxiliary_R; auto; stepr (-u'+(2+1))%R; auto; ring.
   (* M *)
   rewrite as_Moebius_Q_M; natZ_numerals;
   rewrite Q_to_Rdiv; auto;
   rewrite Z_to_Q_to_R_IZR; simpl;
   elim (rep_M_inv_interval _ _ H_rep); intros Hr1 Hr2;
   generalize (IHk _ _ (rep_M_inv _ _ H_rep)); clear IHk; fold u'; intro IHk;
   apply rep_ub_auxiliary_M; auto. 
Qed.


Lemma rep_interval : forall (k:nat) alpha r1 r2, rep alpha r1 -> rep alpha r2 ->  (-(2)/(k+1) <= r1-r2 <= 2/(k+1))%R.
Proof.
 intros k alpha r1 r2 Hr1 Hr2.
 (* TP: O <= k  *) 
 assert (H_k_nonneg:  0 <= k); [ apply Z_to_Qle; apply inj_le; auto with arith|];
 (* TP: Zero < k + 1 *) 
 assert (H_k_one_pos: Zero < k + 1); [natq_zero; qnat_one; natq_S k; natq_S (S k); auto|].

 generalize (rep_lb k _ _ Hr1); generalize (rep_lb k _ _ Hr2); generalize (rep_ub k _ _ Hr1); generalize (rep_ub k _ _ Hr2);
 intros H_r2_u H_r1_u H_r2_l H_r1_l;
 generalize (Q_to_Rle _ _ (thesis_5_7_9 k alpha));
 rewrite Q_to_Rdiv; auto; rewrite Q_to_Rminus; rewrite Q_to_Rplus;
 rewrite Z_to_Q_to_R_IZR; simpl; fold Qone; rewrite Q_to_R_Qone; intro H_ub_lb; rewrite Rdiv_Ropp_numerator.
  apply rep_interval_auxiliary with (lb alpha k) (ub alpha k); trivial.
  change R0 with 0%R; rewrite <- Q_to_R_Qone; rewrite <- Q_to_R_Zero; rewrite <- Q_to_Rplus; apply Rlt_not_eq'; apply Q_to_Rlt; auto.
Qed.

Lemma real_value_base_interval:forall alpha, (-1 <= real_value alpha <= 1)%R.
Proof.
 intros alpha; unfold real_value.
 destruct (R_complete (fun n : nat => lb alpha n) (lb_Cauchy alpha)) as [y Hy]; simpl; 
 generalize RiemannInt.Rle_cv_lim; intro H_sandwich; split.
   
  apply (H_sandwich (fun (n:nat)=>(-1)%R) (fun n : nat => lb alpha n) (-1)%R y); trivial.
   intros n; rewrite <- Q_to_R_Qneg_One; apply Q_to_Rle; apply lb_is_in_base_interval_low. 
   apply CV_const.
  apply (H_sandwich (fun n : nat => lb alpha n) (fun (n:nat)=>(1)%R) y (1)%R); trivial.
   intros n; rewrite <- Q_to_R_Qone; apply Q_to_Rle; apply lb_is_in_base_interval_up. 
   apply CV_const.
Qed.

Lemma real_value_L:forall alpha, real_value (Cons LL alpha) = (((real_value alpha) -1 )/((real_value alpha)+ 3))%R. 
Proof.
 intros alpha; unfold real_value;
 destruct (R_complete (fun n : nat => lb (Cons LL alpha) n) (lb_Cauchy (Cons LL alpha))) as [x H_x];
 destruct (R_complete (fun n : nat => lb alpha n) (lb_Cauchy alpha)) as [y Hy]; simpl;
 apply SeqProp.UL_sequence with (fun n : nat => lb (Cons LL alpha) n); trivial;
 apply CV_shift_S';
 apply CV_extensionality with (fun n=>(((lb alpha n) - 1) / ((lb alpha n) + 3))%R).

  intro n;
  rewrite lb_S_n;
   set (l':=lb alpha n);
   (* TP: Zero <= l'+ 1 *)
   assert (H_l'_one_nonneg: Zero <= l'+1);
   [ stepr (l'-(Qopp 1)); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_low|];
   (* TP: Zero < l'+3 *)
   assert (H_l'_three_pos: Zero < l'+3);
   [ apply Qle_lt_trans with (l'+1); auto; apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|];
   auto.

  unfold hd, tl; fold l';
  rewrite as_Moebius_Q_L; trivial; unfold tl; rewrite Q_to_Rdiv; auto;
   rewrite Q_to_Rminus; rewrite Q_to_Rplus;  do 2 rewrite Z_to_Q_to_R_IZR; simpl; replace (2+1)%R with 3%R; trivial; ring.

  apply (Rsqrt_def.continuity_seq (fun y=>((y - 1) / (y + 3))%R) (lb alpha) y); trivial;
  unfold Ranalysis1.continuity_pt; unfold Rderiv.continue_in; unfold Rdiv;
  apply (Rlimit.limit_mul (fun y=>(y-1)%R) (fun y=>(Rinv (y+3)))).  
   apply (Rlimit.limit_minus (fun y=>y) (fun y=>1%R)).
    apply Rlimit.lim_x.
    apply (Rlimit.limit_free (fun y=>1%R)); exact y.
   apply (Rlimit.limit_inv (fun y=>(y+3)%R)).
    apply (Rlimit.limit_plus (fun y=>y) (fun y=>3%R)).
     apply Rlimit.lim_x.
     apply (Rlimit.limit_free (fun y=>3%R)); exact y.
    apply Rlt_not_eq';
    unfold Un_cv in Hy;
    destruct (Hy 2%R) as [N H_N]; try red; auto;
    assert (H_N_le:N>=N); auto; destruct (Rbasic_fun.Rabs_def2 _ _ (H_N N H_N_le)) as [H1 H2];
    generalize (Q_to_Rle _ _ (lb_is_in_base_interval_low N alpha));
    rewrite Q_to_Ropp; rewrite Q_to_R_Qone;
    apply very_sepcific_0; trivial.
Qed.


Lemma real_value_R:forall alpha, real_value (Cons RR alpha) = (((real_value alpha) +1 )/(-(real_value alpha)+ 3))%R. 
Proof.
 intros alpha; unfold real_value;
 destruct (R_complete (fun n : nat => lb (Cons RR alpha) n) (lb_Cauchy (Cons RR alpha))) as [x H_x];
 destruct (R_complete (fun n : nat => lb alpha n) (lb_Cauchy alpha)) as [y Hy]; simpl;
 apply SeqProp.UL_sequence with (fun n : nat => lb (Cons RR alpha) n); trivial;
 apply CV_shift_S';
 apply CV_extensionality with (fun n=>(((lb alpha n) + 1) / (-(lb alpha n) + 3))%R).
  intro n;
  rewrite lb_S_n;
   set (l':=lb alpha n);
   (* TP: Zero <= -l'+ 1 *)
   assert (H_min_l'_one_nonneg: Zero <= -l'+1);
   [stepr (1-l'); try ring; apply Qle_Qminus_Zero; subst l'; apply lb_is_in_base_interval_up|];
   (* TP: Zero < -l'+3 *)
   assert (H_min_l'_three_pos: Zero < -l'+3);
   [ apply Qle_lt_trans with ((-l')+1); auto;
     apply Qlt_Zero_Qminus; stepr 2; auto; qnat_S 2; qnat_S 1; qnat_one; ring|];
   auto.


  unfold hd, tl; fold l'; rewrite as_Moebius_Q_R; trivial; unfold tl; 
   rewrite Q_to_Rdiv; auto; do 2 rewrite Q_to_Rplus;  rewrite Q_to_Ropp; do 2 rewrite Z_to_Q_to_R_IZR; simpl; 
   replace (2+1)%R with 3%R; trivial; ring.

  apply (Rsqrt_def.continuity_seq (fun y=>((y + 1) / (-y + 3))%R) (lb alpha) y); trivial;
  unfold Ranalysis1.continuity_pt; unfold Rderiv.continue_in; unfold Rdiv;
  apply (Rlimit.limit_mul (fun y=>(y+1)%R) (fun y=>(Rinv (-y+3)))).  
   apply (Rlimit.limit_plus (fun y=>y) (fun y=>1%R)).
    apply Rlimit.lim_x.
    apply (Rlimit.limit_free (fun y=>1%R)); exact y.
   apply (Rlimit.limit_inv (fun y=>(-y+3)%R)).
    apply (Rlimit.limit_plus (fun y=>(Ropp y)) (fun y=>3%R)).
     apply (Rlimit.limit_Ropp (fun y=>y)); apply Rlimit.lim_x.
     apply (Rlimit.limit_free (fun y=>3%R)); exact y.
    apply Rlt_not_eq';
    unfold Un_cv in Hy;
    destruct (Hy 2%R) as [N H_N]; try red; auto;
    assert (H_N_le:N>=N); auto; destruct (Rbasic_fun.Rabs_def2 _ _ (H_N N H_N_le)) as [H1 H2];
    generalize (Q_to_Rle _ _ (lb_is_in_base_interval_up N alpha));
    rewrite Q_to_R_Qone.
    apply very_sepcific_1; trivial.
Qed.


Lemma real_value_M:forall alpha, real_value (Cons MM alpha) = ((real_value alpha)/3)%R. 
Proof.
 intros alpha; unfold real_value;
 destruct (R_complete (fun n : nat => lb (Cons MM alpha) n) (lb_Cauchy (Cons MM alpha))) as [x H_x];
 destruct (R_complete (fun n : nat => lb alpha n) (lb_Cauchy alpha)) as [y Hy]; simpl;
 apply SeqProp.UL_sequence with (fun n : nat => lb (Cons MM alpha) n); trivial;
 apply CV_shift_S';
 apply CV_extensionality with (fun n=>((lb alpha n)/3)%R).
  intro n;
  rewrite lb_S_n;
  rewrite as_Moebius_Q_M; unfold tl; rewrite Q_to_Rdiv; auto.
   rewrite Z_to_Q_to_R_IZR; simpl; replace (2+1)%R with 3%R; trivial; ring.

  apply (Rsqrt_def.continuity_seq (fun y=>(y/3)%R) (lb alpha) y); trivial;
  unfold Ranalysis1.continuity_pt; unfold Rderiv.continue_in; unfold Rdiv;
  apply (Rlimit.limit_mul (fun y=>y) (fun y=>(Rinv 3))).  
   apply Rlimit.lim_x.
   apply (Rlimit.limit_inv (fun y=>(3)%R)); auto.
   apply (Rlimit.limit_free (fun y=>3%R)); exact y.
Qed.


Lemma real_value_digits: forall d alpha, real_value (Cons d alpha) = as_Moebius d (real_value alpha).
Proof.
 intros [ | | ] alpha; unfold as_Moebius, fst, snd, map_digits;
 [ rewrite real_value_L
 | rewrite real_value_R
 | rewrite real_value_M
 ];
 qZ_numerals; realify_Q; auto; field. 
 assert (H_alpha_base:=proj1 (real_value_base_interval alpha)); auto. 
 assert (H_alpha_base:=proj2 (real_value_base_interval alpha)); apply Rlt_not_eq'; lra.
Qed.


Theorem rep_real_value : forall alpha, rep alpha (real_value alpha).
Proof.
 cofix rep_real_value.
 intros [[ | | ] alpha].
  rewrite real_value_L; apply rep_L with alpha;
   [ apply real_value_base_interval 
   | apply rep_real_value
   | unfold bisim; apply EqSt_reflex].
  rewrite real_value_R; apply rep_R with alpha;
   [ apply real_value_base_interval 
   | apply rep_real_value
   | unfold bisim; apply EqSt_reflex].
  rewrite real_value_M; apply rep_M with alpha;
   [ apply real_value_base_interval 
   | apply rep_real_value
   | unfold bisim; apply EqSt_reflex].
Qed.

Theorem real_value_implies_rep: forall alpha r, real_value alpha = r -> rep alpha r.  
Proof.
 intros [[ | | ] alpha] r Hrep.
  rewrite real_value_L in Hrep; rewrite <- Hrep;
  apply (rep_L alpha (Cons LL alpha) (real_value alpha) (real_value_base_interval alpha) (rep_real_value alpha) (EqSt_reflex _)).
  rewrite real_value_R in Hrep; rewrite <- Hrep;
  apply (rep_R alpha (Cons RR alpha) (real_value alpha) (real_value_base_interval alpha) (rep_real_value alpha) (EqSt_reflex _)).
  rewrite real_value_M in Hrep; rewrite <- Hrep;
  apply (rep_M alpha (Cons MM alpha) (real_value alpha) (real_value_base_interval alpha) (rep_real_value alpha) (EqSt_reflex _)).
Qed.

Theorem rep_implies_real_value: forall alpha r, rep alpha r -> real_value alpha = r.
Proof.
 intros alpha r H_rep.
 apply SeqProp.cond_eq.
 intros eps H_eps. 
 set (N:=Z.abs_nat (up (2 / eps))).
 destruct (rep_interval N _ _ _  (rep_real_value alpha) H_rep) as [H1 H2].
 elim (Raxioms.archimed (2/eps)); intros H_N _.
 rewrite <- (Z_of_nat_Zabs_nat_pos (up(2/eps))) in H_N; [|apply Zlt_le_weak; auto].
 apply Rbasic_fun.Rabs_def1.

   apply Rle_lt_trans with (2/((Rdefinitions.IZR N)+1))%R.
    stepr (2 / (N + 1))%R; auto.
    rewrite Z_to_Q_to_R_IZR; trivial.
    apply N_2_epsilon_plus_one; auto.

   apply Rlt_le_trans with (-(2/((Rdefinitions.IZR N)+1)))%R.
    apply Ropp_lt_contravar; apply N_2_epsilon_plus_one; auto.
    stepl (-2 / (N + 1))%R; auto.
    rewrite Z_to_Q_to_R_IZR; unfold Rdiv; rewrite IZR_Zneg_Zpos; rewrite Ropp_mult_distr_l_reverse; trivial.
Qed.

