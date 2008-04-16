(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import R_addenda.
Require Import Fourier_solvable_ineqs.
Require Import Fourier.
Require Import digits.
Require Import ub.
Require Import LNP_Digit.
Require Import homographic.
Require Import hcorrectness.
Require Import Refining_M.
Require Import Bounded_M.
Require Import Incl_M.

(** * Obtaining the productivity predicate for the refining Moebius maps. *)

Open Scope Z_scope.
Open Scope Q_scope.

Lemma thesis_5_6_9:forall mu H_refining, diameter mu H_refining < redundancy -> {d:Digit| Incl_M mu d}.
Proof.
 intros ((a,b),(c,d)) H_refining.
 assert (H_bounded:=proj1 H_refining).
 assert (H_denom: forall r : R, (-1 <= r <= 1)%R -> denom_nonvanishing_M (a, b, (c, d)) r);
  [intros r Hr; apply Is_refining_M_denom_nonvanishing_M; trivial|].
 set (mu_1:=as_Moebius_Q ((a,b),(c,d)) Qone).
 set (mu_2:=as_Moebius_Q ((a,b),(c,d)) (- Qone)).
 destruct (Qle_dec_weak (a*d-b*c) Zero) as [H_det|H_det]; unfold diameter,redundancy; fold mu_1 mu_2.
  (* det(mu)<=0 *)
  assert (H_mu:=det_nonpos_refining_endpoints _ _ _ _ H_refining H_det); fold mu_1 mu_2 in H_mu.
  rewrite (Qabs_non_eq _ (Qle_Qminus_Zero_neg _ _ H_mu)); intro H_diam.
  destruct (Q_le_lt_dec mu_2 Zero) as [H_mu_2|H_mu_2].
   (* mu(-1)<=0 *) 
   exists LL.
   apply Incl_M_L_folded; trivial; intros r Hr; split. 
    elim (Is_refining_M_property _ _ Hr H_refining); trivial.
    apply Rle_trans with mu_2; [ | realify_Q; auto].
     generalize (det_nonpos_nonincreasing _ _ _ _ (-1) r H_bounded H_det min_one_is_in_base_interval Hr (proj1 Hr));
     unfold mu_2, as_Moebius_Q, as_Moebius; simpl;
     let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in realify_Q_goal;
     [ trivial
     | stepl (d-c); try ring; t_local 
     ].
   (* 0<mu(-1) *) 
   destruct (Q_le_lt_dec Zero mu_1) as [H_mu_1|H_mu_1].
    (* 0<=mu(1) *) 
    exists RR.
    apply Incl_M_R_folded; trivial; intros r Hr; split. 
     apply Rle_trans with mu_1; [ realify_Q; auto| ].
      generalize (det_nonpos_nonincreasing _ _ _ _ r 1 H_bounded H_det Hr one_is_in_base_interval (proj2 Hr));
      unfold mu_1, as_Moebius_Q, as_Moebius; simpl.
      let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in realify_Q_goal;
      [ trivial
      | stepl (d+c); try ring; t_local 
      ].
     elim (Is_refining_M_property _ _ Hr H_refining); trivial.
    (* mu(1)<Zero *) 
    exists MM.
    apply Incl_M_M_folded; trivial; intros r Hr; split. 
     apply Rle_trans with mu_1.
      generalize (Q_to_Rlt _ _ H_mu_2);
      assert (H_diam':(mu_2-mu_1<1/3)%R);
      [ stepl (-(mu_1 - mu_2))%R; [|ring]; generalize (Q_to_Rlt _ _ H_diam); rationalify_R_goal
      | realify_Q_goal; intros H_mu_2'; fourier
      ]...
      generalize (det_nonpos_nonincreasing _ _ _ _ r 1 H_bounded H_det Hr one_is_in_base_interval (proj2 Hr));
      unfold mu_1, as_Moebius_Q, as_Moebius; simpl;
      let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in realify_Q_goal;
      [ trivial
      | stepl (d+c); try ring; t_local 
      ]...
     apply Rle_trans with mu_2.
      generalize (det_nonpos_nonincreasing _ _ _ _ (-1) r H_bounded H_det min_one_is_in_base_interval Hr (proj1 Hr));
      unfold mu_2, as_Moebius_Q, as_Moebius; simpl;
      let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in realify_Q_goal;
      [ trivial
      | stepl (d-c); try ring; t_local 
      ]...
      generalize (Q_to_Rlt _ _ H_mu_1);
      assert (H_diam':(mu_2-mu_1<1/3)%R);
      [ stepl (-(mu_1 - mu_2))%R; [|ring]; generalize (Q_to_Rlt _ _ H_diam); rationalify_R_goal
      | realify_Q_goal; intros H_mu_2'; fourier
      ]...
  (* 0<=det(mu) *)
  assert (H_mu:=det_nonneg_refining_endpoints _ _ _ _ H_refining H_det); fold mu_1 mu_2 in H_mu.
  rewrite (Qabs_eq _ (Qle_Qminus_Zero _ _ H_mu)); intro H_diam.
  destruct (Q_le_lt_dec mu_1 Zero) as [H_mu_1|H_mu_1].
   (* mu(1)<=0 *) 
   exists LL.
   apply Incl_M_L_folded; trivial; intros r Hr; split. 
    elim (Is_refining_M_property _ _ Hr H_refining); trivial.
    apply Rle_trans with mu_1; [ | realify_Q; auto].
     generalize (det_nonneg_nondecreasing _ _ _ _ r 1 H_bounded H_det Hr one_is_in_base_interval (proj2 Hr));
     unfold mu_1, as_Moebius_Q, as_Moebius; simpl;
     let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in realify_Q_goal;
     [ trivial
     | stepl (d+c); try ring; t_local 
     ].
   (* 0<mu(1) *) 
   destruct (Q_le_lt_dec Zero mu_2) as [H_mu_2|H_mu_2].
    (* 0<=mu(-1) *) 
    exists RR.
    apply Incl_M_R_folded; trivial; intros r Hr; split. 
     apply Rle_trans with mu_2; [ realify_Q; auto| ].
      generalize (det_nonneg_nondecreasing _ _ _ _ (-1) r H_bounded H_det min_one_is_in_base_interval Hr (proj1 Hr));
      unfold mu_2, as_Moebius_Q, as_Moebius; simpl.
      let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in realify_Q_goal;
      [ trivial
      | stepl (d-c); try ring; t_local 
      ].
     elim (Is_refining_M_property _ _ Hr H_refining); trivial.
    (* mu(-1)<Zero *) 
    exists MM.
    apply Incl_M_M_folded; trivial; intros r Hr; split. 
     apply Rle_trans with mu_2.
      generalize (Q_to_Rlt _ _ H_mu_1);
      assert (H_diam':(mu_1-mu_2<1/3)%R);
      [ generalize (Q_to_Rlt _ _ H_diam); rationalify_R_goal
      | realify_Q_goal; intros H_mu_2'; fourier
      ]...
      generalize (det_nonneg_nondecreasing _ _ _ _ (-1) r H_bounded H_det min_one_is_in_base_interval Hr (proj1 Hr));
      unfold mu_2, as_Moebius_Q, as_Moebius; simpl;
      let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in realify_Q_goal;
      [ trivial
      | stepl (d-c); try ring; t_local 
      ]...
     apply Rle_trans with mu_1.
      generalize (det_nonneg_nondecreasing _ _ _ _ r 1 H_bounded H_det Hr one_is_in_base_interval (proj2 Hr));
      unfold mu_1, as_Moebius_Q, as_Moebius; simpl;
      let t_local:=  (destruct H_bounded as [[H1 H2]|[H1 H2]]; simpl in H1, H2; auto) in realify_Q_goal;
      [ trivial
      | stepl (d+c); try ring; t_local 
      ]...
      generalize (Q_to_Rlt _ _ H_mu_2);
      assert (H_diam':(mu_1-mu_2<1/3)%R);
      [ generalize (Q_to_Rlt _ _ H_diam); rationalify_R_goal
      | realify_Q_goal; intros H_mu_2'; fourier
      ]...
Qed.


Lemma product_init_pure_ub:forall alpha n, as_Moebius_Q (product_init_pure alpha n) Qone = ub alpha n.
Proof.
 intros alpha n; revert alpha; induction n; intros [d alpha]; unfold product_init_pure.
  (* O *)
  simpl; auto.
  (* S n *)
  rewrite ub_S_n.
  rewrite Streams_addenda.take_S_n;
  rewrite (Streams_addenda.fold_right_cons _ _ product).
  unfold map_reals. rewrite Streams_addenda.map_unfolded.
  unfold hd, tl. 
  fold  map_reals. 
  rewrite <- (IHn alpha).
  replace (List.fold_right product idM (Streams_addenda.take n (map_reals alpha))) with (product_init_pure alpha n); trivial.
  rewrite as_Moebius_Q_product; trivial.
   apply Is_refining_M_denom_nonvanishing_M.
    apply Is_refining_M_product_init_pure.
    realify_Q; apply one_is_in_base_interval.
   rewrite (IHn alpha); qZ_numerals; apply ub_is_in_base_interval_low.
   rewrite (IHn alpha); qZ_numerals; apply ub_is_in_base_interval_up.
   destruct d; [apply Is_refining_M_L|apply Is_refining_M_R|apply Is_refining_M_M].
Qed.

Lemma product_init_pure_lb:forall alpha n, as_Moebius_Q (product_init_pure alpha n) (-Qone) = lb alpha n.
 intros alpha n; revert alpha; induction n; intros [d alpha]; unfold product_init_pure.
  (* O *)
  simpl; auto.
  (* S n *)
  rewrite lb_S_n.
  rewrite Streams_addenda.take_S_n;
  rewrite (Streams_addenda.fold_right_cons _ _ product).
  unfold map_reals. rewrite Streams_addenda.map_unfolded.
  unfold hd, tl. 
  fold  map_reals. 
  rewrite <- (IHn alpha).
  replace (List.fold_right product idM (Streams_addenda.take n (map_reals alpha))) with (product_init_pure alpha n); trivial.
  rewrite as_Moebius_Q_product; trivial.
   apply Is_refining_M_denom_nonvanishing_M.
    apply Is_refining_M_product_init_pure.
    realify_Q; apply min_one_is_in_base_interval.
   rewrite (IHn alpha); qZ_numerals; apply lb_is_in_base_interval_low.
   rewrite (IHn alpha); qZ_numerals; apply lb_is_in_base_interval_up.
   destruct d; [apply Is_refining_M_L|apply Is_refining_M_R|apply Is_refining_M_M].
Qed.

Lemma diameter_product:forall mu mu' H_mu H_mu', diameter (product mu mu') (Is_refining_M_product _ _ H_mu H_mu') = 
(Qabs (Determinant mu))*  (diameter mu' H_mu') * 
 (Qabs(as_Moebius_Q  (eta_discriminant mu) (as_Moebius_Q mu' (-Qone)))*Qabs(as_Moebius_Q  (eta_discriminant mu) (as_Moebius_Q mu' Qone))).
Proof.
 intros ((a,b),(c,d)) ((a',b'),(c',d')) H_mu H_mu'.
 assert (H_mu_bound:=proj1 H_mu); assert (H_mu'_bound:=proj1 H_mu'). 
 assert (H_prod:=Is_refining_M_product _ _ H_mu H_mu'); generalize (proj1 H_prod).
 revert H_prod;
 unfold diameter, Determinant, eta_discriminant, product, as_Moebius_Q, fst, snd.
 intros H_prod H_prod_bound.
 assert (H_cd:=Bounded_M_c_plus_d_nonzero _ _ _ _ H_mu_bound).
 assert (H_dc:=Bounded_M_d_minus_c_nonzero _ _ _ _ H_mu_bound).
 assert (H_cd':=Bounded_M_c_plus_d_nonzero _ _ _ _ H_mu'_bound).
 assert (H_dc':=Bounded_M_d_minus_c_nonzero _ _ _ _ H_mu'_bound).
 assert (H_pord_denom_one:=Bounded_M_c_plus_d_nonzero _ _ _ _ H_prod_bound).
 assert (H_prod_denom_min_one:=Bounded_M_d_minus_c_nonzero _ _ _ _ H_prod_bound).
 assert (H_cd_:c * - Qone + d<>Zero); [ring_exact_Q H_dc|].
 assert (H_cd'_:c' * - Qone + d'<>Zero); [ring_exact_Q H_dc'|].
 assert (H_prod_denom_min_one_:(c*a'+d*c')* - Qone + (c*b'+d*d') <> Zero); [ring_exact_Q H_prod_denom_min_one|].
 qZ_numerals.
 repeat rewrite <- Qabs_Qmult.
 repeat rewrite Qminus_Qdiv; trivial.
 apply (f_equal Qabs).
 field; repeat split; auto.
  ring_exact_Q H_pord_denom_one.
  ring_exact_Q H_prod_denom_min_one.
Qed.


Lemma diameter_product_init_pure:forall alpha n H_diam, diameter(product_init_pure alpha n) H_diam= ub alpha n-lb alpha n.
Proof.
 intros alpha n H_diam;
 unfold diameter; rewrite product_init_pure_ub; rewrite product_init_pure_lb; rewrite Qabs_eq_pos; trivial;
 apply Qlt_Qminus_Zero; apply lb_lt_ub_pointwise.
Qed.

Lemma diameter_product_init:forall a b c d alpha n H_mualpha, 
 Is_refining_M ((a,b),(c,d)) -> diameter (product_init ((a,b),(c,d)) alpha n) H_mualpha = 
  (Qabs (a*d - b*c)) * (ub alpha n - lb alpha n) 
  * (Qabs (as_Moebius_Q  ((0/1,1/1),(c,d)) (lb alpha n)) * Qabs (as_Moebius_Q  ((0/1,1/1),(c,d)) (ub alpha n))).
Proof.
 intros a b c d alpha n.
 rewrite product_init_product_init_pure.  
 intros H_mualpha H_mu.
 assert (H_alpha:=(Is_refining_M_product_init_pure alpha n)).
 rewrite <- (diameter_product_init_pure alpha n H_alpha).
 rewrite <- product_init_pure_lb.
 rewrite <- product_init_pure_ub.
 transitivity (diameter (product (a, b, (c, d)) (product_init_pure alpha n))
                (Is_refining_M_product (a, b, (c, d)) (product_init_pure alpha n) H_mu H_alpha)); [apply diameter_PI|].
 rewrite (diameter_product _ _ H_mu H_alpha).
 repeat apply (f_equal2 Qmult); trivial.
Qed.

Lemma eta_discriminant_twice_majorised: forall a b c d alpha n,  Is_refining_M ((a,b),(c,d)) ->
 let X := Qmax (Qabs(Qone/(c+d))) (Qabs (Qone/(d-c))) in
  (Qabs (as_Moebius_Q  ((0/1,1/1),(c,d)) (lb alpha n)) * Qabs (as_Moebius_Q  ((0/1,1/1),(c,d)) (ub alpha n)))<= X * X.
Proof.
 intros a b c d alpha n [H_bounded _] X.
 apply Qmult_Qle_compat ; [| |apply Qabs_nonneg|apply Qabs_nonneg];
 subst X; apply maximum_eta_discriminant_base_interval with a b; trivial. 
  apply lb_is_in_base_interval_low. 
  apply lb_is_in_base_interval_up.  
  apply ub_is_in_base_interval_low. 
  apply ub_is_in_base_interval_up.  
Qed.

(** This is the main productivity lemma (similar to Lemma 5.6.10 of
the thesis) for the homographic algorithm. It extracts [n] --- number
of the absorption steps after which emission occurs. *)

Theorem thesis_5_6_10: forall mu alpha, Is_refining_M mu -> {n:nat & {d | Incl_M (product_init mu alpha n) d}}. 
Proof.
 intros ((a,b),(c,d)) alpha H_refining.
 set (det:=a*d-b*c).
 set (X := Qmax (Qabs(Qone/(c+d))) (Qabs (Qone/(d-c)))).
 set (q:=3*(2*(Qabs det))*(X*X)).
 destruct (Q_Archimedean_nat_inf q) as [n Hn].
 exists n.
 assert (H_n_one_pos: Zero < n + 1); [natZ_numerals; qnat_one; natq_zero; natq_S n; natq_S (S n); auto|].
 assert (H_refining_prod:=Is_refining_M_product_init _ alpha n H_refining).
 apply thesis_5_6_9 with H_refining_prod; unfold redundancy.
 rewrite (diameter_product_init _ _ _ _ _ _ H_refining_prod H_refining).
 fold det.
 rewrite <- Qmult_assoc.
 apply Qle_lt_trans with ((Qabs det)*((2%nat/(n+1%nat))*(X*X))).
  apply Qle_reg_mult_l_strong; [apply Qabs_nonneg|].
  apply Qmult_Qle_compat.
   apply thesis_5_7_9.
   unfold X; apply eta_discriminant_twice_majorised with a b; assumption.
   apply Qle_Qminus_Zero; apply lb_leq_ub_pointwise.
   apply Qle_mult_nonneg_nonneg; apply Qabs_nonneg.
  stepl (((2*Qabs det)*(X*X))/(n+1)).
   apply Qmult_Qdiv_pos.
    auto.  
    stepl (3*(2*Qabs det)*(X*X)); [|ring].
    stepr (n+1); [| qZ_numerals_one; ring].
    fold q.
    apply Qle_lt_trans with n; trivial.
    rewrite <- Z_to_Qplus; apply Z_to_Qlt; natZ_numerals; rewrite <- inj_plus; apply inj_lt; omega.
   revert H_n_one_pos; natZ_numerals; intros H_n_one_pos; field; auto. 
Qed.

Close Scope Q_scope.
Close Scope Z_scope.


(** Using the above we prove that [n] can always be chosen to be the smallest such number. *)
Lemma semantic_modulus_h: forall mu alpha, Is_refining_M mu -> 
  {n:nat & { d | Incl_M (product_init mu alpha n) d /\
                      (forall m d', (m<n)%nat ->~Incl_M (product_init mu alpha m) d') } }.
Proof.
 intros mu alpha H_r.
 apply LNP_sigS_nat_Digit.
  intros n d; apply Incl_M_dec_D.
  apply thesis_5_6_10; assumption.
Qed.

Lemma semantic_modulus_h_S_product:forall n n' mu alpha (H_r:Is_refining_M mu) H_r', 
   let smodu':=semantic_modulus_h (product mu (map_digits (hd alpha))) (tl alpha) H_r' in
    let smodu:=semantic_modulus_h mu alpha H_r in
      (0 < n)%nat -> n' = projT1 smodu' -> n = projT1 smodu -> n =  S n'.
Proof.
 destruct n; intros n' mu alpha H_r H_r' smodu' smodu Hn_pos Hn' Hn; [inversion  Hn_pos |].
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
  rewrite_all (product_init_folds mu alpha n);
  contradiction...
  generalize (lt_n_S _ _ Hnn'); intros Hnn'_S;
  generalize (H3 (S n') d' Hnn'_S);
  rewrite (product_init_folds mu alpha n');
  contradiction...
Qed.

Lemma Is_refining_M_emits_h_pointwise: forall n mu alpha H_r, 
    let smodu:=semantic_modulus_h mu alpha H_r in
       n = projT1 smodu ->  emits_h mu alpha.
Proof.
 induction n;
 intros mu alpha H_r smodu Hn;
 set (n':=projS1 smodu);
 set (d:=(proj1_sig (projT2 smodu)));
 assert (Hn':n'=(projT1 smodu)); trivial;
 assert (Hd:d=(proj1_sig (projT2 smodu))); trivial;
 destruct (proj2_sig (projT2 smodu)) as [H1 H3].
 (* O *)
  simpl in H1.
  case (Incl_M_dec_D mu LL); intros t_l.
   constructor 1; trivial.
   case (Incl_M_dec_D mu RR); intros t_r.
    constructor 2; trivial.
    case (Incl_M_dec_D mu MM); intros t_m.
     constructor 3; trivial.
     rewrite_all <- Hd; rewrite_all <- Hn'; rewrite_all <- Hn; destruct d; contradiction.
 (* S n *)
 rewrite_all <- Hd; rewrite_all <- Hn.
 generalize (H3 O LL (lt_O_Sn _));  generalize (H3 O RR (lt_O_Sn _));  generalize (H3 O MM (lt_O_Sn _)).
 simpl; intros t_m t_r t_l.
 constructor 4; trivial.
 apply (IHn (product mu (hd alpha)) (tl alpha) (Is_refining_M_product_hd _ _ H_r)).
 apply eq_add_S.
 apply (semantic_modulus_h_S_product (S n) (projT1 (semantic_modulus_h (product mu (hd alpha)) 
                                                           (tl alpha) (Is_refining_M_product_hd mu alpha H_r)))
                                                mu alpha H_r (Is_refining_M_product_hd _ _ H_r)); trivial.
  apply lt_O_Sn.
Qed.

Lemma Is_refining_M_emits_h: forall mu alpha, Is_refining_M mu -> emits_h mu alpha.
Proof.
 intros mu alpha H_r.
 set (smodu:=semantic_modulus_h mu alpha H_r).
 set (n:=projS1 smodu).
 assert (Hn:n=(projT1 smodu)); trivial.
 apply Is_refining_M_emits_h_pointwise with n H_r; trivial.
Qed.

Lemma Is_refining_M_depth_h:forall n mu alpha (H_r:Is_refining_M mu), 
   let smodu:=semantic_modulus_h mu alpha H_r in
     n= projS1 smodu ->  depth_h mu alpha (Is_refining_M_emits_h mu alpha H_r) = n.
Proof.
 induction n; intros mu alpha H_r smodu Hn;
 set (d:=(proj1_sig (projT2 smodu)));
 assert (Hd':d=(proj1_sig (projT2 smodu))); trivial;
 destruct (proj2_sig (projT2 smodu)) as [H1 H3].
  (* 0 *)
  revert H1; rewrite <- Hd'; rewrite <- Hn; intros H1.
  case (Incl_M_dec_D mu LL); intros t_l.
   apply depth_h_L; trivial.
   case (Incl_M_dec_D mu RR); intros t_r.
    apply depth_h_R; trivial.
    case (Incl_M_dec_D mu MM); intros t_m.
     apply depth_h_M; trivial.
     destruct d; contradiction.
  (* S n *)
  generalize H1 (H3 O); clear H1 H3; rewrite <- Hd'; rewrite <- Hn; intros H1 H3.
  case (Incl_M_dec_D mu LL); intros t_l.
   rewrite depth_h_L; trivial; generalize (H3 LL (lt_O_Sn _)); simpl; intros H4; contradiction. 
   case (Incl_M_dec_D mu RR); intros t_r.
    rewrite depth_h_R; trivial; generalize (H3 RR (lt_O_Sn _)); simpl; intros H4; contradiction. 
    case (Incl_M_dec_D mu MM); intros t_m.
     rewrite depth_h_M; trivial; generalize (H3 MM (lt_O_Sn _)); simpl; intros H4; contradiction. 

     set (smodu':=semantic_modulus_h (product mu (map_digits (hd alpha))) (tl alpha) (Is_refining_M_product_hd _ _ H_r)).
     generalize (semantic_modulus_h_S_product  (S n) (projT1 smodu') _ alpha H_r (Is_refining_M_product_hd _ _ H_r)).
     intros H_Sn.
     rewrite (depth_h_absorbs _ _ (Is_refining_M_emits_h mu alpha H_r) t_l t_r t_m (Is_refining_M_emits_h _ (tl alpha)
     (Is_refining_M_product_hd mu alpha H_r))).
     apply eq_S.
     apply IHn.
     rewrite (eq_add_S _ _ (H_Sn (lt_O_Sn _) (refl_equal _) Hn)); trivial.
Qed.

Lemma Is_refining_M_modulus_h:forall mu alpha (H_r:Is_refining_M mu), 
  let modu:=modulus_h mu alpha (Is_refining_M_emits_h mu alpha H_r) in
   let mu' := fstT (sndT modu) in 
      Is_refining_M mu'.
Proof.
 intros mu alpha H_r.
 set (smodu:=semantic_modulus_h mu alpha H_r).
 set (n:=projS1 smodu).
 set (d':=(proj1_sig (projT2 smodu))).
 assert (Hn:n=(projT1 smodu)); trivial.
 assert (Hd':d'=(proj1_sig (projT2 smodu))); trivial.
 assert (H_depth: depth_h mu alpha (Is_refining_M_emits_h mu alpha H_r) = n);[apply (Is_refining_M_depth_h n _ alpha H_r Hn)|].
 destruct (depth_h_modulus_h mu alpha (Is_refining_M_emits_h mu alpha H_r) n (Is_refining_M_depth_h n _ _ _ Hn)) as [d Hd].
 destruct (proj2_sig (projS2 smodu)) as [H_Incl _].
 rewrite Hd; simpl.
 apply Incl_M_absorbs_Is_refining_M.
 destruct (depth_h_Incl_M_inf_strong_general _ _ (Is_refining_M_emits_h mu alpha H_r) n H_depth) as [d'' [Hd''1 Hd''2]].
 revert Hd''2.
 rewrite Hd; simpl.
 intros Hd''2. 
 subst d''.
 assumption.
Qed.

Lemma Is_refining_M_step_productive_h: forall n mu alpha, Is_refining_M mu -> step_productive_h n mu alpha.
Proof.
 induction n;
 intros mu alpha H_refining. 
 (* 0 *) constructor; apply Is_refining_M_emits_h; trivial.
 (* S *) apply (step_productive_h_S n _ _ (Is_refining_M_emits_h _ alpha H_refining)). 
 apply IHn.
 apply (Is_refining_M_modulus_h _ alpha H_refining).
Qed.

Theorem Is_refining_M_productive_h: forall mu alpha, Is_refining_M mu -> productive_h mu alpha.
Proof.
 intros mu alpha H_refining.
 constructor; intros n; apply Is_refining_M_step_productive_h; trivial.
Qed. 
