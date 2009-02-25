(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)


Require Import digits.
Require Import Refining_M.
Require Import homographic.
Require Import Streams_addenda.
Require Import RIneq.
Require Import R_addenda.
Require Import rep.

(** * Coinductive correctness of the homographic algorithm. *)

(** Calculating the product of [mu] and the first [n] elements of [alpha]. *)

Fixpoint product_init (mu:Matrix) (alpha:Reals) (n:nat) {struct n}: Matrix := 
 match n with
 | O => mu
 | S n' => product (product_init mu alpha n') (Str_nth n' alpha)
 end.

Lemma product_init_S:forall mu alpha n, 
   product_init mu alpha (S n) = product (product_init mu alpha n) (Str_nth n alpha).
Proof.
 intros mu alpha [|n]; trivial.
Qed.

Lemma product_init_folds:forall mu alpha n,
               (product_init mu alpha (S n) = (product_init (product mu (Streams.hd alpha)) (tl alpha) n)).
Proof.
 intros mu alpha n; generalize mu alpha; clear mu alpha; induction n; intros mu alpha; simpl; trivial;
 rewrite <- IHn; rewrite product_init_S; apply (f_equal2 product); trivial.
Defined.


Lemma product_init_init_rev_id: forall mu alpha n, mu = product (product_init mu alpha n) (product_init_rev alpha n).
Proof.
 intros mu alpha n; generalize mu alpha; clear mu alpha; induction n; intros mu alpha.

  unfold product_init, product_init_rev; simpl; rewrite product_idM_identity_right; reflexivity.
   
  unfold product_init_rev; rewrite rev_take_S_Str_nth; rewrite fold_right_cons;
  replace (fold_right product idM (rev (take n (Streams.map inv_digit alpha)))) with (product_init_rev alpha n); trivial;
  rewrite <- Str_nth_map_pointwise; 
  rewrite product_init_S; rewrite <- product_associative;
  rewrite (product_associative (map_digits (Str_nth n alpha))); rewrite product_digit_inv_digit_identity_right;
  rewrite product_associative; rewrite product_idM_identity_right; apply IHn.
Qed.  

Lemma product_init_product_init_pure:forall mu alpha n, product_init mu alpha n = product mu (product_init_pure alpha n).
Proof.
 intros mu alpha n; revert mu alpha; induction n; intros mu alpha; unfold product_init_pure.
  (* O *)
  simpl; rewrite product_idM_identity_right; trivial.
  (* S n *)
  rewrite Streams_addenda.take_S_n;
  rewrite (Streams_addenda.fold_right_cons product);
  rewrite product_associative;
  rewrite product_init_folds;
  rewrite (IHn (product mu (Streams.hd alpha)) (tl alpha)); trivial.
Qed.

Lemma Is_refining_M_product_init: forall mu alpha n, Is_refining_M mu -> Is_refining_M (product_init mu alpha n).
Proof.
 intros mu alpha n H_mu; rewrite product_init_product_init_pure;
 apply Is_refining_M_product; trivial; apply Is_refining_M_product_init_pure.
Qed.

Section depth_of_modulus_h.

Fixpoint depth_h (mu:Matrix) (alpha:Reals) (H1:emits_h mu alpha) {struct H1}: nat :=
   match Incl_M_dec_D mu LL with
   | left _ => 0
   | right H_emission_L =>
       match Incl_M_dec_D mu RR with
       | left _ => 0
       | right H_emission_R =>
           match Incl_M_dec_D mu MM with
           | left _ => 0
           | right H_emission_M =>
               S(depth_h (product mu (Streams.hd alpha)) (tl alpha)
                 (emits_h_absorbs_inv mu alpha H_emission_L H_emission_R
                    H_emission_M H1))
           end
       end
   end.

Lemma depth_h_PI:forall mu alpha H1 H2,  depth_h mu alpha H1 = depth_h mu alpha H2.
Proof.
 intros mu alpha H1.
 pattern alpha, H1;
 elim H1 using emits_h_ind_dep;
 clear H1 mu;
   [ intros mu alpha0 i H2; generalize i
   | intros mu alpha0 i H2; generalize i 
   | intros mu alpha0 i H2; generalize i
   | intros mu alpha0 f H H2; generalize f H
   ];
   pattern alpha0, H2;
   elim H2 using emits_h_ind_dep;
   first 
    [ intros mu0 alpha' H_primity H_primity'; simpl; case (Incl_M_dec_D mu0 LL); intro; trivial; contradiction
    | intros mu0 alpha' H_primity H_primity'; simpl; case (Incl_M_dec_D mu0 RR); intro; trivial; contradiction
    | intros mu0 alpha' H_primity H_primity'; simpl; case (Incl_M_dec_D mu0 MM); intro; trivial; contradiction
    | intros; contradiction]  || 
    (intro mu0; intros; simpl;
      case (Incl_M_dec_D mu0 LL); intro; contradiction || 
	case (Incl_M_dec_D mu0 RR); intro; contradiction ||
	  case (Incl_M_dec_D mu0 MM); intro; contradiction ||
	    trivial; apply eq_S; trivial).
Defined.

Lemma depth_h_PI_strong:forall mu mu' alpha alpha' H1 H2, mu=mu'->alpha=alpha' ->
   depth_h mu alpha H1 = depth_h mu' alpha' H2.
Proof.
 intros; subst; apply depth_h_PI.
Defined.

Lemma depth_h_L:forall (mu:Matrix) (alpha:Reals) (t: emits_h mu alpha),
      (Incl_M mu LL) -> depth_h mu alpha t = 0.
Proof.
 intros mu alpha t t_l.
 transitivity (depth_h mu alpha (emits_h_L _ _ t_l)).
 apply depth_h_PI.
 simpl;
  case (Incl_M_dec_D mu LL); try contradiction;
   intros; reflexivity.
Defined.

Lemma depth_h_R:forall (mu:Matrix) (alpha:Reals) (t: emits_h mu alpha), ~(Incl_M mu LL) ->  (Incl_M mu RR) ->
                             depth_h mu alpha t = 0.
Proof.
 intros mu alpha t t_l t_r.
 transitivity (depth_h mu alpha (emits_h_R _ _ t_r)).
 apply depth_h_PI.
 simpl;
   case (Incl_M_dec_D mu LL); try contradiction;
     case (Incl_M_dec_D mu RR); try contradiction;
      intros; reflexivity.
Defined.

Lemma depth_h_M:forall (mu:Matrix) (alpha:Reals) (t: emits_h mu alpha),~(Incl_M mu LL)->~(Incl_M mu RR)->(Incl_M mu MM)->
                             depth_h mu alpha t = 0.
Proof.
 intros mu alpha t t_l t_r t_m.
 transitivity (depth_h mu alpha (emits_h_M _ _ t_m)).
 apply depth_h_PI.
 simpl;
 case (Incl_M_dec_D mu LL); try contradiction;
  case (Incl_M_dec_D mu RR); try contradiction;
   case (Incl_M_dec_D mu MM); try contradiction;
    intros; reflexivity.
Defined.

Lemma depth_h_absorbs:forall (mu:Matrix) (alpha:Reals) (t: emits_h mu alpha),~(Incl_M mu LL)->~(Incl_M mu RR)->~(Incl_M mu MM)->
  forall t', depth_h mu alpha t = S(depth_h (product mu (Streams.hd alpha)) (tl alpha) t').
Proof.
 intros mu alpha t t_l t_r t_m t'.
 transitivity (depth_h mu alpha (emits_h_absorbs _ _ t')).
 apply depth_h_PI.
 simpl.
 case (Incl_M_dec_D mu LL); try contradiction;
  case (Incl_M_dec_D mu RR); try contradiction;
   case (Incl_M_dec_D mu MM); try contradiction;
    intros _; reflexivity.
Defined.


Lemma depth_h_Incl_M_inf : forall mu alpha (t: emits_h mu alpha) n, depth_h mu alpha t = n -> 
        {Incl_M (product_init mu alpha n) LL}+{Incl_M (product_init mu alpha n) RR}+{Incl_M (product_init mu alpha n) MM}.
Proof.
 intros mu alpha t n H_eq.
 generalize mu alpha t H_eq.
 clear mu alpha t H_eq.
 induction n; intros mu alpha t H_eq.
  case (Incl_M_dec_D mu LL).
   left; left; trivial. 
   case (Incl_M_dec_D mu RR).
    left; right; trivial.
    case (Incl_M_dec_D mu MM). 
    right; trivial...   

    intros t_m t_r t_l;
    apply False_rec;
    rewrite (depth_h_absorbs mu alpha t t_l t_r t_m (emits_h_absorbs_inv mu alpha t_l t_r t_m t)) in H_eq;
    discriminate...

  case (Incl_M_dec_D mu LL); intro t_l.
   apply False_rec; rewrite (depth_h_L mu alpha t t_l) in H_eq; discriminate.
   case (Incl_M_dec_D mu RR); intro t_r.
    apply False_rec; rewrite (depth_h_R mu alpha t t_l t_r) in H_eq; discriminate.
     case (Incl_M_dec_D mu MM); intro t_m.
     apply False_rec; rewrite (depth_h_M mu alpha t t_l t_r t_m) in H_eq; discriminate. 

     rewrite (depth_h_absorbs mu alpha t t_l t_r t_m (emits_h_absorbs_inv mu alpha t_l t_r t_m t)) in H_eq.
     rewrite product_init_folds.
     decompose sum (IHn _ _ _ (eq_add_S _ _ H_eq));
      [ left; left
      | left; right
      | right
      ]; trivial.
Defined.

Lemma depth_h_modulus_h:forall mu alpha (t: emits_h mu alpha) n, depth_h mu alpha t = n -> 
       exists d:Digit, modulus_h mu alpha t = pairT d (pairT (product (inv_digit d) (product_init mu alpha n)) (drop n alpha)).
Proof.
 intros mu alpha t n H_eq.
 generalize mu alpha t H_eq.
 clear mu alpha t H_eq.
 induction n; intros mu alpha t H_eq.
  (* n=0 *)
  simpl.
  case (Incl_M_dec_D mu LL); intro t_l.
   exists LL; rewrite (modulus_h_L _ _ t t_l); trivial.
   case (Incl_M_dec_D mu RR); intro t_r.
    exists RR; rewrite (modulus_h_R _ _ t t_l t_r); trivial.
    case (Incl_M_dec_D mu MM); intro t_m.
     exists MM; rewrite (modulus_h_M _ _ t t_l t_r t_m); trivial.
       
     apply False_ind;
     rewrite (depth_h_absorbs mu alpha t t_l t_r t_m (emits_h_absorbs_inv mu alpha t_l t_r t_m t)) in H_eq;
     discriminate.
  (* n=S n *)
  case (Incl_M_dec_D mu LL); intro t_l.
   apply False_ind; rewrite (depth_h_L mu alpha t t_l) in H_eq; discriminate.
   case (Incl_M_dec_D mu RR); intro t_r.
    apply False_ind; rewrite (depth_h_R mu alpha t t_l t_r) in H_eq; discriminate.
    case (Incl_M_dec_D mu MM); intro t_m.
     apply False_ind; rewrite (depth_h_M mu alpha t t_l t_r t_m) in H_eq; discriminate.

     rewrite (depth_h_absorbs mu alpha t t_l t_r t_m (emits_h_absorbs_inv mu alpha t_l t_r t_m t)) in H_eq.
     destruct (IHn _ _ _ (eq_add_S _ _ H_eq)) as [d H_ind]; exists d.
     rewrite (modulus_h_absorbs mu alpha t t_l t_r t_m (emits_h_absorbs_inv mu alpha t_l t_r t_m t)). 
     rewrite H_ind.
     apply (@f_equal2 _ _ _ (@pairT Digit (@prodT Matrix Reals))); trivial;
     apply (@f_equal2 _ _ _ (@pairT Matrix Reals)); trivial.
     rewrite product_init_folds; trivial.
     destruct alpha; reflexivity.
Defined.


Lemma depth_h_Incl_M_inf_strong : forall mu alpha (t: emits_h mu alpha) n, depth_h mu alpha t = n -> 
        {Incl_M (product_init mu alpha n) LL/\ fst (modulus_h mu alpha t)=LL}+
        {Incl_M (product_init mu alpha n) RR/\ fst (modulus_h mu alpha t)=RR}+
        {Incl_M (product_init mu alpha n) MM/\ fst (modulus_h mu alpha t)=MM}.
Proof.
 intros mu alpha t n H_eq.
 generalize mu alpha t H_eq.
 clear mu alpha t H_eq.
 induction n; intros mu alpha t H_eq.
  case (Incl_M_dec_D mu LL); intro t_l.
   left; left; split; trivial; rewrite (modulus_h_L _ _ t t_l); trivial.
   case (Incl_M_dec_D mu RR); intro t_r.
    left; right; split; trivial; rewrite (modulus_h_R _ _ t t_l t_r); trivial.
    case (Incl_M_dec_D mu MM); intro t_m. 
    right; split; trivial; rewrite (modulus_h_M _ _ t t_l t_r t_m); trivial...   

    apply False_rec;
    rewrite (depth_h_absorbs mu alpha t t_l t_r t_m (emits_h_absorbs_inv mu alpha t_l t_r t_m t)) in H_eq;
    discriminate...

  case (Incl_M_dec_D mu LL); intro t_l.
   apply False_rec; rewrite (depth_h_L mu alpha t t_l) in H_eq; discriminate.
   case (Incl_M_dec_D mu RR); intro t_r.
    apply False_rec; rewrite (depth_h_R mu alpha t t_l t_r) in H_eq; discriminate.
     case (Incl_M_dec_D mu MM); intro t_m.
     apply False_rec; rewrite (depth_h_M mu alpha t t_l t_r t_m) in H_eq; discriminate. 

     rewrite (depth_h_absorbs mu alpha t t_l t_r t_m (emits_h_absorbs_inv mu alpha t_l t_r t_m t)) in H_eq.
     rewrite product_init_folds.
     destruct (IHn _ _ _ (eq_add_S _ _ H_eq)) as  [[[H_Incl H_modulus]|[H_Incl H_modulus]]|[H_Incl H_modulus]];
     [ left; left
     | left; right
     | right
     ]; split; trivial;
     rewrite <- H_modulus;
     apply (@f_equal _ _ (@fst Digit (Matrix*Reals)));
     rewrite (modulus_h_absorbs _ _ t t_l t_r t_m (emits_h_absorbs_inv mu alpha t_l t_r t_m t)); trivial.
Defined.

Lemma depth_h_Incl_M_inf_strong_general
     : forall (mu : Matrix) (alpha : Reals) (t : emits_h mu alpha) (n : nat),
       depth_h mu alpha t = n -> exists d,Incl_M (product_init mu alpha n) d /\ fst (modulus_h mu alpha t) = d. 
Proof.
 intros mu alpha t n H_depth.
 destruct (depth_h_Incl_M_inf_strong _ _ t n H_depth) as [[Hd|Hd]|Hd];
  [ exists LL
  | exists RR
  | exists MM
  ]; assumption.
Qed.

End depth_of_modulus_h.

Lemma homographic_emits_strong: forall mu alpha (p:productive_h mu alpha), 
         exists n, (exists d:Digit, productive_h (product (inv_digit d) (product_init mu alpha n)) (drop n alpha) /\
	                            Incl_M (product_init mu alpha n) d/\
	                            forall p', bisim (homographic mu alpha p)  
                    (Cons d (homographic (product (inv_digit d) (product_init mu alpha n)) (drop n alpha) p'))).
Proof.
 intros mu alpha H_productive.
 generalize (productive_h_emits_h mu alpha H_productive); intro H_emits.

 exists (depth_h mu alpha H_emits).
 destruct (depth_h_modulus_h mu alpha H_emits (depth_h mu alpha H_emits) (refl_equal _)) as [d H_modulus].
 exists d; split.
  generalize (modulus_h_productive_h mu alpha H_emits H_productive); rewrite H_modulus; trivial.
  split. 
   
   destruct (depth_h_Incl_M_inf_strong _ _ H_emits (depth_h mu alpha H_emits) (refl_equal _)) as
         [[[H_Incl H_modulus']|[H_Incl H_modulus']]|[H_Incl H_modulus']];
    rewrite H_modulus in H_modulus'; simpl in H_modulus'; rewrite H_modulus'; assumption...

   intros H_productive'.
   rewrite (homographic_unfolded mu alpha H_productive);
   constructor; simpl;
   [ idtac 
   | apply homographic_EPI_strong
   ];
   rewrite <- (modulus_h_PI _ _ H_emits (productive_h_emits_h mu alpha H_productive));
   rewrite H_modulus;
   trivial.
Defined.



Theorem homographic_correctness (mu:Matrix) (alpha : Reals) (H : productive_h mu alpha) (r:R): 
     rep alpha r ->  rep (homographic mu alpha H) (as_Moebius mu r).
Proof.
 cofix.
 intros mu alpha H_productive (* H_refining *) r Hr_alpha;
 destruct (homographic_emits_strong mu alpha H_productive) as [n [[ | | ] [H_productive_dropped [H_Incl H_bis]]]];
 unfold inv_digit in H_bis; unfold inv_digit;
 generalize (H_bis H_productive_dropped); clear H_bis; intro H_bis.
  (* L *)
  replace (as_Moebius mu r) with (as_Moebius (product LL (product inv_LL mu)) r);
  [ idtac | rewrite <- product_inv_L;  reflexivity];
  replace (product inv_LL mu) with (product inv_LL (product (product_init mu alpha n) (product_init_rev alpha n)));
  [ idtac | rewrite <- product_init_init_rev_id; trivial].

  assert (H_base:(-1 <= as_Moebius (product inv_LL (product (product_init mu alpha n) (product_init_rev alpha n))) r <= 1)%R).
   rewrite product_associative.
   rewrite as_Moebius_product.
    apply Is_refining_M_property.
     apply rep_drop_in_range; assumption.
     replace inv_LL with (inv_digit LL); trivial; apply Incl_M_absorbs_Is_refining_M; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply rep_drop_in_range; assumption.
    replace inv_LL with (inv_digit LL); trivial; apply Incl_M_absorbs_Is_refining_M; assumption...

  rewrite as_Moebius_L; try exact H_base.
   refine (rep_L (homographic (product inv_LL (product_init mu alpha n)) (drop n alpha) H_productive_dropped) 
          _ _ _ _ H_bis).

    exact H_base.

    rewrite product_associative;
    rewrite as_Moebius_product.
     apply homographic_correctness.
     apply (rep_drop _ _ n Hr_alpha)...
     apply denom_nonvanishing_product_init; assumption...
     apply rep_drop_in_range; assumption...
     replace inv_LL with (inv_digit LL); trivial; apply Incl_M_absorbs_Is_refining_M; assumption...
    rewrite product_associative; apply denom_nonvanishing_M_product. 
     replace inv_LL with (inv_digit LL); trivial; apply Incl_M_absorbs_Is_refining_M; assumption.
     apply rep_drop_in_range; assumption. 
     apply denom_nonvanishing_product_init; assumption.
  (* R *)
  replace (as_Moebius mu r) with (as_Moebius (product RR (product inv_RR mu)) r);
  [ idtac | rewrite <- product_inv_R;  reflexivity];
  replace (product inv_RR mu) with (product inv_RR (product (product_init mu alpha n) (product_init_rev alpha n)));
  [ idtac | rewrite <- product_init_init_rev_id; trivial].

  assert (H_base:(-1 <= as_Moebius (product inv_RR (product (product_init mu alpha n) (product_init_rev alpha n))) r <= 1)%R).
   rewrite product_associative.
   rewrite as_Moebius_product.
    apply Is_refining_M_property.
     apply rep_drop_in_range; assumption.
     replace inv_RR with (inv_digit RR); trivial; apply Incl_M_absorbs_Is_refining_M; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply rep_drop_in_range; assumption.
    replace inv_RR with (inv_digit RR); trivial; apply Incl_M_absorbs_Is_refining_M; assumption...

  rewrite as_Moebius_R; try exact H_base.
   refine (rep_R (homographic (product inv_RR (product_init mu alpha n)) (drop n alpha) H_productive_dropped) 
          _ _ _ _ H_bis).

    exact H_base.

    rewrite product_associative;
    rewrite as_Moebius_product.
     apply homographic_correctness.
     apply (rep_drop _ _ n Hr_alpha)...
     apply denom_nonvanishing_product_init; assumption...
     apply rep_drop_in_range; assumption...
     replace inv_RR with (inv_digit RR); trivial; apply Incl_M_absorbs_Is_refining_M; assumption...
    rewrite product_associative; apply denom_nonvanishing_M_product. 
     replace inv_RR with (inv_digit RR); trivial; apply Incl_M_absorbs_Is_refining_M; assumption.
     apply rep_drop_in_range; assumption. 
     apply denom_nonvanishing_product_init; assumption.
  (* M *)
  replace (as_Moebius mu r) with (as_Moebius (product MM (product inv_MM mu)) r);
  [ idtac | rewrite <- product_inv_M;  reflexivity];
  replace (product inv_MM mu) with (product inv_MM (product (product_init mu alpha n) (product_init_rev alpha n)));
  [ idtac | rewrite <- product_init_init_rev_id; trivial].

  assert (H_base:(-1 <= as_Moebius (product inv_MM (product (product_init mu alpha n) (product_init_rev alpha n))) r <= 1)%R).
   rewrite product_associative.
   rewrite as_Moebius_product.
    apply Is_refining_M_property.
     apply rep_drop_in_range; assumption.
     replace inv_MM with (inv_digit MM); trivial; apply Incl_M_absorbs_Is_refining_M; assumption.
    apply denom_nonvanishing_product_init; assumption.
    apply rep_drop_in_range; assumption.
    replace inv_MM with (inv_digit MM); trivial; apply Incl_M_absorbs_Is_refining_M; assumption...

  rewrite as_Moebius_M; try exact H_base.
   refine (rep_M (homographic (product inv_MM (product_init mu alpha n)) (drop n alpha) H_productive_dropped) 
          _ _ _ _ H_bis).

    exact H_base.

    rewrite product_associative;
    rewrite as_Moebius_product.
     apply homographic_correctness.
     apply (rep_drop _ _ n Hr_alpha)...
     apply denom_nonvanishing_product_init; assumption...
     apply rep_drop_in_range; assumption...
     replace inv_MM with (inv_digit MM); trivial; apply Incl_M_absorbs_Is_refining_M; assumption...
    rewrite product_associative; apply denom_nonvanishing_M_product. 
     replace inv_MM with (inv_digit MM); trivial; apply Incl_M_absorbs_Is_refining_M; assumption.
     apply rep_drop_in_range; assumption. 
     apply denom_nonvanishing_product_init; assumption.
Defined.


