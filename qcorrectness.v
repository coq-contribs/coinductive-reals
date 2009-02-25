(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)


Require Import digits.
Require Import Refining_T.
Require Import quadratic.
Require Import Streams_addenda.
Require Import rep.
Require Import RIneq.
Require Import R_addenda.

(** * Coinductive correctness of the quadratic algorithm. *)

(** Calculating the left and right products of [xi] and the first [n] elements of [alpha] and [beta]. *)

Fixpoint product_init_zip (xi:Tensor) (alpha beta:Reals) (n:nat) {struct n}: Tensor := 
 match n with
 | O => xi
 | S n' => right_product (left_product (product_init_zip xi alpha beta n') (Str_nth n' alpha)) (Str_nth n' beta) 
 end.


Lemma product_init_zip_S:forall xi alpha beta n, 
   product_init_zip xi alpha beta (S n) = 
        right_product (left_product (product_init_zip xi alpha beta n) (Str_nth n alpha)) (Str_nth n beta).
Proof.
 intros xi alpha beta [|n]; trivial.
Qed.

Lemma product_init_zip_folds:forall xi alpha beta n, 
   product_init_zip xi alpha beta (S n) =
       product_init_zip (right_product (left_product xi (Streams.hd alpha)) (Streams.hd beta)) (tl alpha) (tl beta) n.
Proof.
 intros xi alpha beta n; generalize xi alpha beta; clear xi alpha beta; induction n; intros xi alpha beta; simpl; trivial;
 rewrite <- IHn; rewrite product_init_zip_S; apply (f_equal2 right_product); trivial.
Defined.

Lemma product_init_zip_init_rev_id: forall xi alpha beta n, 
    xi = 
   (right_product (left_product (product_init_zip xi alpha beta n) (product_init_rev alpha n)) (product_init_rev beta n)).
Proof.
 intros xi alpha beta n; generalize xi alpha beta; clear xi alpha beta; induction n; intros xi alpha beta.

  unfold product_init_zip, product_init_rev; simpl; rewrite right_left_product_idM_identity_right; reflexivity.
   
  unfold product_init_rev; repeat rewrite rev_take_S_Str_nth; repeat rewrite fold_right_cons;
  replace (fold_right product idM (rev (take n (Streams.map inv_digit alpha)))) with (product_init_rev alpha n); trivial;
  replace (fold_right product idM (rev (take n (Streams.map inv_digit beta)))) with (product_init_rev beta n); trivial;
  repeat rewrite <- Str_nth_map_pointwise;
  rewrite product_init_zip_S; rewrite product_left_right_product_associative;
  rewrite (product_associative (map_digits (Str_nth n alpha))); rewrite product_digit_inv_digit_identity_right;
  rewrite (product_associative (map_digits (Str_nth n beta))); rewrite product_digit_inv_digit_identity_right;
  rewrite <- product_left_right_product_associative; rewrite right_left_product_idM_identity_right; apply IHn.
Qed.  

Lemma product_init_zip_product_init_pure:forall xi alpha beta n,  
 product_init_zip xi alpha beta n = right_product (left_product xi (product_init_pure alpha n)) (product_init_pure beta n).
Proof.
 intros xi alpha beta n; revert xi alpha beta; induction n; intros xi alpha beta; unfold product_init_pure.
  (* O *)
  simpl; rewrite right_left_product_idM_identity_right; trivial.
  (* S n *)
  repeat rewrite Streams_addenda.take_S_n;
  repeat rewrite (Streams_addenda.fold_right_cons product);
  rewrite <- product_left_right_product_associative;
  rewrite product_init_zip_folds;
  rewrite (IHn (right_product (left_product xi (Streams.hd alpha)) (Streams.hd beta)) (tl alpha) (tl beta)); trivial.
Qed.


Section depth_of_modulus_q.

Fixpoint depth_q (xi:Tensor) (alpha beta:Reals) (H1:emits_q xi alpha beta) {struct H1}:nat:=
   match Incl_T_dec_D xi LL with
   | left _ => 0
   | right H_emission_L =>
       match Incl_T_dec_D xi RR with
       | left _ => 0
       | right H_emission_R =>
           match Incl_T_dec_D xi MM with
           | left _ => 0
           | right H_emission_M =>
               S(depth_q (right_product (left_product xi (Streams.hd alpha)) (Streams.hd beta)) (tl alpha) (tl beta)
                 (emits_q_absorbs_inv xi alpha beta H_emission_L H_emission_R H_emission_M H1))
           end
       end
   end.


Lemma depth_q_PI:forall xi alpha beta H1 H2,  depth_q xi alpha beta H1 = depth_q xi alpha beta H2.
Proof.
 intros xi alpha beta H1.
 pattern alpha, beta, H1.
 elim H1 using emits_q_ind_dep;
 clear H1 xi;
   [ intros xi alpha0 beta0 i H2; generalize i
   | intros xi alpha0 beta0 i H2; generalize i 
   | intros xi alpha0 beta0 i H2; generalize i
   | intros xi alpha0 beta0 f H H2; generalize f H
   ];
   pattern alpha0, beta0, H2;
   elim H2 using emits_q_ind_dep;
   first 
    [ intros xi0 alpha' beta' H_primity H_primity'; simpl; case (Incl_T_dec_D xi0 LL); intro; trivial; contradiction
    | intros xi0 alpha' beta' H_primity H_primity'; simpl; case (Incl_T_dec_D xi0 RR); intro; trivial; contradiction
    | intros xi0 alpha' beta' H_primity H_primity'; simpl; case (Incl_T_dec_D xi0 MM); intro; trivial; contradiction
    | intros; contradiction]  || 
    (intro xi0; intros; simpl;
      case (Incl_T_dec_D xi0 LL); intro; contradiction || 
	case (Incl_T_dec_D xi0 RR); intro; contradiction ||
	  case (Incl_T_dec_D xi0 MM); intro; contradiction ||
	    trivial;apply eq_S; trivial).
Defined.

Lemma depth_q_PI_strong:forall xi xi' alpha beta alpha' beta' H1 H2, xi=xi'->alpha=alpha' -> beta = beta' ->
   depth_q xi alpha beta H1 = depth_q xi' alpha' beta' H2.
Proof.
 intros; subst; apply depth_q_PI.
Defined.

Lemma depth_q_L:forall (xi:Tensor) (alpha beta:Reals) (t: emits_q xi alpha beta),(Incl_T xi LL) ->
                 depth_q xi alpha beta t=0.
Proof.
 intros xi alpha beta t t_l.
 transitivity (depth_q xi alpha beta (emits_q_L _ _ _ t_l)).
 apply depth_q_PI.
 simpl;
  case (Incl_T_dec_D xi LL); try contradiction;
   intros; reflexivity.
Defined.

Lemma depth_q_R:forall (xi:Tensor) (alpha beta:Reals) (t: emits_q xi alpha beta), ~(Incl_T xi LL) ->  (Incl_T xi RR) ->
                 depth_q xi alpha beta t=0.
Proof.
 intros xi alpha beta t t_l t_r.
 transitivity (depth_q xi alpha beta (emits_q_R _ _ _ t_r)).
 apply depth_q_PI.
 simpl;
   case (Incl_T_dec_D xi LL); try contradiction;
     case (Incl_T_dec_D xi RR); try contradiction;
      intros; reflexivity.
Defined.

Lemma depth_q_M:forall (xi:Tensor) (alpha beta:Reals) (t: emits_q xi alpha beta),~(Incl_T xi LL)->~(Incl_T xi RR)->(Incl_T xi MM)->
                 depth_q xi alpha beta t=0.
Proof.
 intros xi alpha beta t t_l t_r t_m.
 transitivity (depth_q xi alpha beta (emits_q_M _ _ _ t_m)).
 apply depth_q_PI.
 simpl;
 case (Incl_T_dec_D xi LL); try contradiction;
  case (Incl_T_dec_D xi RR); try contradiction;
   case (Incl_T_dec_D xi MM); try contradiction;
    intros; reflexivity.
Defined.

Lemma depth_q_absorbs:forall (xi:Tensor) (alpha beta:Reals) (t: emits_q xi alpha beta),~(Incl_T xi LL)->~(Incl_T xi RR)->~(Incl_T xi MM)->
  forall t', depth_q xi alpha beta t = S(depth_q (right_product (left_product xi (Streams.hd alpha)) (Streams.hd beta)) (tl alpha) (tl beta) t').
Proof.
 intros xi alpha beta t t_l t_r t_m t'.
 transitivity (depth_q xi alpha beta (emits_q_absorbs _ _ _ t')).
 apply depth_q_PI.
 simpl.
 case (Incl_T_dec_D xi LL); try contradiction;
  case (Incl_T_dec_D xi RR); try contradiction;
   case (Incl_T_dec_D xi MM); try contradiction;
    intros _; reflexivity.
Defined.

Lemma depth_q_modulus_q:forall (xi:Tensor) (alpha beta:Reals) (t: emits_q xi alpha beta) n,depth_q xi alpha beta t=n->
       exists d:Digit, modulus_q xi alpha beta t = 
                                     pairT d (pairT (m_product (inv_digit d) (product_init_zip xi alpha beta n))
                                                    (pairT (drop n alpha) (drop n beta))).
Proof.
 intros xi alpha beta t n H_eq.
 generalize xi alpha beta t H_eq; clear xi alpha beta t H_eq; induction n; intros xi alpha beta t H_eq.
  (* n=0 *)
  simpl.
  case (Incl_T_dec_D xi LL); intro t_l.
   exists LL; rewrite (modulus_q_L _ _ _ t t_l); trivial.
   case (Incl_T_dec_D xi RR); intro t_r.
    exists RR; rewrite (modulus_q_R _ _ _ t t_l t_r); trivial.
    case (Incl_T_dec_D xi MM); intro t_m.
     exists MM; rewrite (modulus_q_M _ _ _ t t_l t_r t_m); trivial.
       
     apply False_ind;
     rewrite (depth_q_absorbs xi alpha beta t t_l t_r t_m (emits_q_absorbs_inv xi alpha beta t_l t_r t_m t)) in H_eq;
     discriminate.
  (* n=S n *)
  case (Incl_T_dec_D xi LL); intro t_l.
   apply False_ind; rewrite (depth_q_L xi alpha beta t t_l) in H_eq; discriminate.
   case (Incl_T_dec_D xi RR); intro t_r.
    apply False_ind; rewrite (depth_q_R xi alpha beta t t_l t_r) in H_eq; discriminate.
    case (Incl_T_dec_D xi MM); intro t_m.
     apply False_ind; rewrite (depth_q_M xi alpha beta t t_l t_r t_m) in H_eq; discriminate.

     rewrite (depth_q_absorbs xi alpha beta t t_l t_r t_m (emits_q_absorbs_inv xi alpha beta t_l t_r t_m t)) in H_eq.
     destruct (IHn _ _ _ _ (eq_add_S _ _ H_eq)) as [d H_ind]; exists d.
     rewrite (modulus_q_absorbs xi alpha beta t t_l t_r t_m (emits_q_absorbs_inv xi alpha beta t_l t_r t_m t)). 
     rewrite H_ind.
     apply (@f_equal2 _ _ _ (@pairT Digit (@prodT Tensor (@prodT Reals Reals)))); trivial;
     apply (@f_equal2 _ _ _ (@pairT Tensor (@prodT Reals Reals))); trivial.
     rewrite product_init_zip_folds; trivial.
     destruct alpha; destruct beta; reflexivity.
Defined.

Lemma depth_q_Incl_T_inf_strong : forall xi alpha beta (t: emits_q xi alpha beta) n, depth_q xi alpha beta t = n -> 
        {Incl_T (product_init_zip xi alpha beta n) LL/\ fst (modulus_q xi alpha beta t)=LL}+
        {Incl_T (product_init_zip xi alpha beta n) RR/\ fst (modulus_q xi alpha beta t)=RR}+
        {Incl_T (product_init_zip xi alpha beta n) MM/\ fst (modulus_q xi alpha beta t)=MM}.
Proof.
 intros xi alpha beta t n H_eq.
 generalize xi alpha beta t H_eq.
 clear xi alpha beta t H_eq.
 induction n; intros xi alpha beta t H_eq.
  case (Incl_T_dec_D xi LL); intro t_l.
   left; left; split; trivial; rewrite (modulus_q_L _ _ _ t t_l); trivial.
   case (Incl_T_dec_D xi RR); intro t_r.
    left; right; split; trivial; rewrite (modulus_q_R _ _ _ t t_l t_r); trivial.
    case (Incl_T_dec_D xi MM); intro t_m. 
    right; split; trivial; rewrite (modulus_q_M _ _ _ t t_l t_r t_m); trivial...   

    apply False_rec;
    rewrite (depth_q_absorbs xi alpha beta t t_l t_r t_m (emits_q_absorbs_inv xi alpha beta t_l t_r t_m t)) in H_eq;
    discriminate...

  case (Incl_T_dec_D xi LL); intro t_l.
   apply False_rec; rewrite (depth_q_L xi alpha beta t t_l) in H_eq; discriminate.
   case (Incl_T_dec_D xi RR); intro t_r.
    apply False_rec; rewrite (depth_q_R xi alpha beta t t_l t_r) in H_eq; discriminate.
     case (Incl_T_dec_D xi MM); intro t_m.
     apply False_rec; rewrite (depth_q_M xi alpha beta t t_l t_r t_m) in H_eq; discriminate. 

     rewrite (depth_q_absorbs xi alpha beta t t_l t_r t_m (emits_q_absorbs_inv xi alpha beta t_l t_r t_m t)) in H_eq.
     rewrite product_init_zip_folds.
     destruct (IHn _ _ _ _ (eq_add_S _ _ H_eq)) as  [[[H_Incl H_modulus]|[H_Incl H_modulus]]|[H_Incl H_modulus]];
     [ left; left
     | left; right
     | right
     ]; split; trivial;
     rewrite <- H_modulus;
     apply (f_equal (@fst Digit (Tensor*(Reals*Reals))));
     rewrite (modulus_q_absorbs _ _ _ t t_l t_r t_m (emits_q_absorbs_inv xi alpha beta t_l t_r t_m t)); trivial.
Defined.

Lemma depth_q_Incl_T_inf_strong_general
     : forall (xi : Tensor) (alpha beta: Reals) (t : emits_q xi alpha beta) (n : nat),
       depth_q xi alpha beta t = n -> 
           exists d,Incl_T (product_init_zip xi alpha beta n) d /\ fst (modulus_q xi alpha beta t) = d. 
Proof.
 intros xi alpha beta t n H_depth.
 destruct (depth_q_Incl_T_inf_strong _ _ _ t n H_depth) as [[Hd|Hd]|Hd];
  [ exists LL
  | exists RR
  | exists MM
  ]; assumption.
Qed.

End depth_of_modulus_q.


Lemma quadratic_emits_strong: forall xi alpha beta (p:productive_q xi alpha beta), 
      exists n, 
       (exists d:Digit, 
               productive_q (m_product (inv_digit d) (product_init_zip xi alpha beta n)) (drop n alpha) (drop n beta) /\
	       Incl_T (product_init_zip xi alpha beta n) d/\
	       forall p', bisim (quadratic xi alpha beta p)  
       (Cons d (quadratic (m_product (inv_digit d) (product_init_zip xi alpha beta n)) (drop n alpha) (drop n beta) p'))).
Proof.
 intros xi alpha beta H_productive.
 generalize (productive_q_emits_q xi alpha beta H_productive); intro H_emits.

 exists (depth_q xi alpha beta H_emits).
 destruct (depth_q_modulus_q xi alpha beta H_emits (depth_q xi alpha beta H_emits) (refl_equal _)) as [d H_modulus].
 exists d; split.
  generalize (modulus_q_productive_q xi alpha beta H_emits H_productive); rewrite H_modulus; trivial.
  split. 
   
   destruct (depth_q_Incl_T_inf_strong _ _ _ H_emits (depth_q xi alpha beta H_emits) (refl_equal _)) as
         [[[H_Incl H_modulus']|[H_Incl H_modulus']]|[H_Incl H_modulus']];
    rewrite H_modulus in H_modulus'; simpl in H_modulus'; rewrite H_modulus'; assumption...

   intros H_productive'.
   rewrite (quadratic_unfolded xi alpha beta H_productive);
   constructor; simpl;
   [ idtac 
   | apply quadratic_EPI_strong
   ];
   rewrite <- (modulus_q_PI _ _ _ H_emits (productive_q_emits_q xi alpha beta H_productive));
   rewrite H_modulus;
   trivial.
Defined.


Theorem quadratic_correctness (xi:Tensor) (alpha beta:Reals) (H:productive_q xi alpha beta) (r1 r2:Rdefinitions.R): 
     rep alpha r1 ->  rep beta r2-> rep (quadratic xi alpha beta H) (as_Tensor xi r1 r2).
Proof.
 cofix.
 intros xi alpha beta H_productive r1 r2 Hr1_alpha Hr2_beta;
 destruct (quadratic_emits_strong xi alpha beta H_productive) as [n [[ | | ] [H_productive_dropped [H_Incl H_bis]]]];
 unfold inv_digit in H_bis; unfold inv_digit;
 generalize (H_bis H_productive_dropped); clear H_bis; intro H_bis.
  (* L *)
  replace (as_Tensor xi r1 r2) with (as_Tensor (m_product LL (m_product inv_LL xi)) r1 r2);
  [ idtac | rewrite <- m_product_inv_L;  reflexivity];
  replace (m_product inv_LL xi) with (m_product inv_LL
  (right_product (left_product (product_init_zip xi alpha beta n) (product_init_rev alpha n)) (product_init_rev beta n)));
  [ idtac | rewrite <- product_init_zip_init_rev_id; trivial].

  assert (H_base: (-1<=as_Tensor (m_product inv_LL (right_product (left_product (product_init_zip xi alpha beta n)
                                 (product_init_rev alpha n)) (product_init_rev beta n))) r1 r2 <= 1)%R).
   rewrite m_product_left_right_product_associative.
   rewrite as_Tensor_right_left_product_as_Moebius.
    apply Is_refining_T_property;
     try (apply rep_drop_in_range; assumption).
     replace inv_LL with (inv_digit LL); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply rep_drop_in_range; assumption.
    apply rep_drop_in_range; assumption.
    replace inv_LL with (inv_digit LL); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.

  rewrite as_Tensor_L; try exact H_base.
   refine
     (rep_L 
       (quadratic (m_product inv_LL (product_init_zip xi alpha beta n)) (drop n alpha) (drop n beta) H_productive_dropped)
       _ _ _ _ H_bis).

    exact H_base.

    rewrite m_product_left_right_product_associative;
    rewrite as_Tensor_right_left_product_as_Moebius.
     apply quadratic_correctness;
     [ apply (rep_drop _ _ n Hr1_alpha)
     | apply (rep_drop _ _ n Hr2_beta)
     ]. 
     apply denom_nonvanishing_product_init; assumption.
     apply denom_nonvanishing_product_init; assumption.
     apply rep_drop_in_range; assumption.
     apply rep_drop_in_range; assumption.
     replace inv_LL with (inv_digit LL); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.
   rewrite m_product_left_right_product_associative; apply denom_nonvanishing_T_left_right_product.
    apply denom_nonvanishing_product_init; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply rep_drop_in_range; assumption.
    apply rep_drop_in_range; assumption.
    replace inv_LL with (inv_digit LL); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.
  (* R *)
  replace (as_Tensor xi r1 r2) with (as_Tensor (m_product RR (m_product inv_RR xi)) r1 r2);
  [ idtac | rewrite <- m_product_inv_R;  reflexivity];
  replace (m_product inv_RR xi) with (m_product inv_RR
  (right_product (left_product (product_init_zip xi alpha beta n) (product_init_rev alpha n)) (product_init_rev beta n)));
  [ idtac | rewrite <- product_init_zip_init_rev_id; trivial].

  assert (H_base: (-1<=as_Tensor (m_product inv_RR (right_product (left_product (product_init_zip xi alpha beta n)
                                 (product_init_rev alpha n)) (product_init_rev beta n))) r1 r2 <= 1)%R).
   rewrite m_product_left_right_product_associative.
   rewrite as_Tensor_right_left_product_as_Moebius.
    apply Is_refining_T_property;
     try (apply rep_drop_in_range; assumption).
     replace inv_RR with (inv_digit RR); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply rep_drop_in_range; assumption.
    apply rep_drop_in_range; assumption.
    replace inv_RR with (inv_digit RR); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.

  rewrite as_Tensor_R; try exact H_base.
   refine
     (rep_R 
       (quadratic (m_product inv_RR (product_init_zip xi alpha beta n)) (drop n alpha) (drop n beta) H_productive_dropped)
       _ _ _ _ H_bis).

    exact H_base.

    rewrite m_product_left_right_product_associative;
    rewrite as_Tensor_right_left_product_as_Moebius.
     apply quadratic_correctness;
     [ apply (rep_drop _ _ n Hr1_alpha)
     | apply (rep_drop _ _ n Hr2_beta)
     ]. 
     apply denom_nonvanishing_product_init; assumption.
     apply denom_nonvanishing_product_init; assumption.
     apply rep_drop_in_range; assumption.
     apply rep_drop_in_range; assumption.
     replace inv_RR with (inv_digit RR); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.
   rewrite m_product_left_right_product_associative; apply denom_nonvanishing_T_left_right_product.
    apply denom_nonvanishing_product_init; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply rep_drop_in_range; assumption.
    apply rep_drop_in_range; assumption.
    replace inv_RR with (inv_digit RR); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.
  (* M *)
  replace (as_Tensor xi r1 r2) with (as_Tensor (m_product MM (m_product inv_MM xi)) r1 r2);
  [ idtac | rewrite <- m_product_inv_M;  reflexivity];
  replace (m_product inv_MM xi) with (m_product inv_MM
  (right_product (left_product (product_init_zip xi alpha beta n) (product_init_rev alpha n)) (product_init_rev beta n)));
  [ idtac | rewrite <- product_init_zip_init_rev_id; trivial].

  assert (H_base: (-1<=as_Tensor (m_product inv_MM (right_product (left_product (product_init_zip xi alpha beta n)
                                 (product_init_rev alpha n)) (product_init_rev beta n))) r1 r2 <= 1)%R).
   rewrite m_product_left_right_product_associative.
   rewrite as_Tensor_right_left_product_as_Moebius.
    apply Is_refining_T_property;
     try (apply rep_drop_in_range; assumption).
     replace inv_MM with (inv_digit MM); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply rep_drop_in_range; assumption.
    apply rep_drop_in_range; assumption.
    replace inv_MM with (inv_digit MM); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.

  rewrite as_Tensor_M; try exact H_base.
   refine
     (rep_M 
       (quadratic (m_product inv_MM (product_init_zip xi alpha beta n)) (drop n alpha) (drop n beta) H_productive_dropped)
       _ _ _ _ H_bis).

    exact H_base.

    rewrite m_product_left_right_product_associative;
    rewrite as_Tensor_right_left_product_as_Moebius.
     apply quadratic_correctness;
     [ apply (rep_drop _ _ n Hr1_alpha)
     | apply (rep_drop _ _ n Hr2_beta)
     ]. 
     apply denom_nonvanishing_product_init; assumption.
     apply denom_nonvanishing_product_init; assumption.
     apply rep_drop_in_range; assumption.
     apply rep_drop_in_range; assumption.
     replace inv_MM with (inv_digit MM); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.
   rewrite m_product_left_right_product_associative; apply denom_nonvanishing_T_left_right_product.
    apply denom_nonvanishing_product_init; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply rep_drop_in_range; assumption.
    apply rep_drop_in_range; assumption.
    replace inv_MM with (inv_digit MM); trivial; apply Incl_T_absorbs_Is_refining_T; assumption.
Defined.

