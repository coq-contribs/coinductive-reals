(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import digits.
Require Import Refining_M.
Require Import Streams_addenda.
Require Import Raxioms.
Require Import RIneq.
From QArithSternBrocot Require Import R_addenda.
Require Import Fourier_solvable_ineqs.

(** Coinductive definition of the representation and its properties. *)

CoInductive rep : Reals -> Rdefinitions.R -> Prop :=
  | rep_L : forall alpha beta x, (-1<=x<=1)%R-> rep alpha x -> bisim beta (Cons LL alpha) -> rep beta ((x-1)/(x+3))%R
  | rep_R : forall alpha beta x, (-1<=x<=1)%R-> rep alpha x -> bisim beta (Cons RR alpha) -> rep beta ((x+1)/((-x)+3))%R
  | rep_M : forall alpha beta x, (-1<=x<=1)%R-> rep alpha x -> bisim beta (Cons MM alpha) -> rep beta (x/3)%R.



Lemma rep_stepl: forall alpha beta x, rep alpha x -> bisim alpha beta -> rep beta x.
Proof.
 cofix rep_stepl.
 intros [[ | | ] alpha] [[ | | ] beta] x h_rep h_bisim; try (inversion h_bisim; discriminate H). 

  inversion_clear h_rep as 
     [alpha0 dummy x0 H_x0 h_rep0 h_bisim0|alpha0 dummy x0 H_x0 h_rep0 h_bisim0|alpha0 dummy x0 H_x0 h_rep0 h_bisim0];
       try (inversion h_bisim0; discriminate H) ||
   apply (rep_L alpha (Cons LL beta) x0 H_x0);
    [ apply (rep_stepl alpha0); trivial;inversion h_bisim0
    | 
    ] ; unfold bisim; apply sym_EqSt ; trivial.

  inversion_clear h_rep as 
     [alpha0 dummy x0 H_x0 h_rep0 h_bisim0|alpha0 dummy x0 H_x0 h_rep0 h_bisim0|alpha0 dummy x0 H_x0 h_rep0 h_bisim0];
       try (inversion h_bisim0; discriminate H) ||
   apply (rep_R alpha (Cons RR beta) x0 H_x0);
    [ apply (rep_stepl alpha0); trivial;inversion h_bisim0
    | 
    ] ; unfold bisim; apply sym_EqSt ; trivial.

  inversion_clear h_rep as 
     [alpha0 dummy x0 H_x0 h_rep0 h_bisim0|alpha0 dummy x0 H_x0 h_rep0 h_bisim0|alpha0 dummy x0 H_x0 h_rep0 h_bisim0];
       try (inversion h_bisim0; discriminate H) ||
   apply (rep_M alpha (Cons MM beta) x0 H_x0);
    [ apply (rep_stepl alpha0); trivial;inversion h_bisim0
    | 
    ] ; unfold bisim; apply sym_EqSt ; trivial.
Qed.

Lemma rep_stepr: forall alpha x y, rep alpha x -> x=y -> rep alpha y.
Proof.
 intros alpha x y H_rep H_eq; subst x; trivial.
Defined.

Declare Left Step rep_stepl.
Declare Right Step rep_stepr.


Lemma rep_L_inv: forall alpha r, rep (Cons LL alpha) r -> rep alpha ((3*r+1)/(-r+1))%R. 
Proof.
 intros alpha r H_rep;
 inversion H_rep as [alpha0 beta x [H1 H2] H_rep0 H_bisim H3 H_rx
                    |alpha0 beta x [H1 H2] H_rep0 H_bisim H3 H_rx
                    |alpha0 beta x [H1 H2] H_rep0 H_bisim H3 H_rx];
 try (inversion H_bisim as [H4 H5]; discriminate H4);
  destruct H_bisim;  stepr x; 
  [ stepl alpha0; trivial; unfold bisim; apply sym_EqSt ; trivial
  |];
  rewrite <- R_addenda.Rdiv_Ropp_numerator; auto;
  rewrite R_addenda.Rdiv_Rmult_numerator; auto;
  repeat rewrite R_addenda.Rdiv_Rplus_Rmult; auto;
  rewrite R_addenda.Rdiv_Rdiv_simplify; auto.
   transitivity (x/1)%R; [field; auto|];
   apply Rmult_Rdiv; auto; [| ring];
   stepl 4%R; auto; ring.
  stepl 4%R; auto; ring.
Qed.


Lemma rep_R_inv: forall alpha r, rep (Cons RR alpha) r -> rep alpha ((3*r-1)/(r+1))%R. 
Proof.
 intros alpha r H_rep;
 inversion H_rep as [alpha0 beta x [H1 H2] H_rep0 H_bisim H3 H_rx
                    |alpha0 beta x [H1 H2] H_rep0 H_bisim H3 H_rx
                    |alpha0 beta x [H1 H2] H_rep0 H_bisim H3 H_rx];
 try (inversion H_bisim as [H4 H5]; discriminate H4);
  destruct H_bisim;  stepr x; 
  [ stepl alpha0; trivial; unfold bisim; apply sym_EqSt ; trivial
  |];
  rewrite Rdiv_Rmult_numerator; auto;
  rewrite Rdiv_Rminus_Rmult; auto;
  rewrite Rdiv_Rplus_Rmult; auto;
  rewrite Rdiv_Rdiv_simplify; auto.
   transitivity (x/1)%R; [field; auto|];
   apply Rmult_Rdiv; auto; [| ring];
   stepl 4%R; auto; ring.
  stepl 4%R; auto; ring.
Qed.

Lemma rep_M_inv: forall alpha r, rep (Cons MM alpha) r -> rep alpha (3*r)%R. 
Proof.
 intros alpha r H_rep;
 inversion H_rep as [alpha0 beta x [H1 H2] H_rep0 H_bisim H3 H_rx
                    |alpha0 beta x [H1 H2] H_rep0 H_bisim H3 H_rx
                    |alpha0 beta x [H1 H2] H_rep0 H_bisim H3 H_rx];
 try (inversion H_bisim as [H4 H5]; discriminate H4);
  destruct H_bisim;  stepr x; 
  [ stepl alpha0; trivial; unfold bisim; apply sym_EqSt ; trivial
  |];
  field; auto.
Qed.

Lemma rep_L_inv_interval : forall alpha r, rep (Cons LL alpha) r -> (-1 <= r <= 0)%R.
Proof.
 intros alpha r H_rep; inversion_clear H_rep as [alpha0 y x [H1 H2] _ _|alpha0|alpha0];
 try (inversion H1; discriminate H2);
 split; [ apply conjL_range_l | apply conjL_range_r]; trivial.
Qed.

Lemma rep_R_inv_interval : forall alpha r, rep (Cons RR alpha) r -> (0 <= r <= 1)%R.
Proof.
 intros alpha r H_rep; inversion_clear H_rep as [alpha0|alpha0 y x [H1 H2] _ _|alpha0];
 try (inversion H1; discriminate H2);
 split; [ apply conjR_range_l | apply conjR_range_r]; trivial.
Qed.

Lemma rep_M_inv_interval : forall alpha r, rep (Cons MM alpha) r -> (-1/3 <= r <= 1/3)%R.
Proof.
 intros alpha r H_rep; inversion_clear H_rep as [alpha0|alpha0|alpha0 y x [H1 H2] _ _];
 try (inversion H1; discriminate H2);
 split; [ apply conjM_range_l | apply conjM_range_r]; trivial.
Qed.

Lemma rep_inv_interval : forall alpha r, rep alpha r -> (-1 <= r <= 1)%R.
Proof.
 intros alpha r H_rep; inversion_clear H_rep;
 [ apply conjL_range_weak| apply conjR_range_weak | apply conjM_range_weak]; trivial.
Qed.


Lemma product_init_rev_rep_drop_denom_nonvanishing: forall alpha n r d, rep alpha r -> Streams.hd (drop n alpha) = d ->
    (as_Moebius (map_digits d) (-1)<= as_Moebius (product_init_rev alpha n) r<= as_Moebius (map_digits d) 1)%R/\
    rep (drop n alpha)  (as_Moebius (product_init_rev alpha n) r)/\
     denom_nonvanishing_M (product_init_rev alpha n) r.
Proof.
 intros alpha n.
 generalize alpha; clear alpha; induction n.

 intros [[ | | ] alpha]  r d  Hr H_nth;
 unfold product_init_rev; simpl;
 unfold drop,Streams.hd in H_nth;
 subst d;
 [ rewrite as_Moebius_L_one; rewrite as_Moebius_L_min_one 
 | rewrite as_Moebius_R_one; rewrite as_Moebius_R_min_one 
 | rewrite as_Moebius_M_one; rewrite as_Moebius_M_min_one 
 ];
 unfold denom_nonvanishing_M, as_Moebius at 1 2 3, idM, fst, snd, Qdiv at 2 3 6 7;  rewrite Qmult_zero;  repeat rewrite Q_to_Rdiv; auto;
 repeat rewrite Q_to_R_Zero; repeat rewrite Z_to_Q_to_R_IZR; simpl;
 unfold Rdiv; repeat rewrite Rmult_0_l;  rewrite Rplus_0_r; rewrite Rplus_0_l; rewrite Rmult_1_l;
 replace (/ 1 * r * / / 1)%R with r; try(field; auto); split; try (solve[split; auto]).
   apply (rep_L_inv_interval _ _ Hr). 
   apply (rep_R_inv_interval _ _ Hr). 
   apply (rep_M_inv_interval _ _ Hr). 

 intros alpha  r d  Hr H_nth.
 unfold product_init_rev.
 rewrite rev_take_S_Str_nth; rewrite fold_right_cons. 
  replace (fold_right product idM (rev (take n (Streams.map inv_digit alpha)))) with (product_init_rev alpha n); trivial.
  unfold map_reals; rewrite <- Str_nth_map_pointwise.
  generalize (drop_Str_nth n alpha).
  destruct (Str_nth n alpha); intros H_drop_n; 
  destruct (IHn alpha _ _ Hr H_drop_n) as [[Hind1 Hind2] [Hind_rep H_denom]].

   (* L *)
   rewrite (hd_tl_id (drop n alpha)) in Hind_rep;
   rewrite H_drop_n in Hind_rep;
   rewrite <- (drop_tl_S n alpha) in Hind_rep;
   generalize (rep_L_inv _ _ Hind_rep);
   intros H_rep_Sn.

   rewrite as_Moebius_inv_L.
    split; [|split]; try exact (H_rep_Sn).
     rewrite (hd_tl_id (drop (S n) alpha)) in H_rep_Sn; rewrite H_nth in H_rep_Sn.
     destruct d.
      rewrite as_Moebius_L_min_one; rewrite as_Moebius_L_one; apply (rep_L_inv_interval _ _ H_rep_Sn).
      rewrite as_Moebius_R_min_one; rewrite as_Moebius_R_one; apply (rep_R_inv_interval _ _ H_rep_Sn).
      rewrite as_Moebius_M_min_one; rewrite as_Moebius_M_one; apply (rep_M_inv_interval _ _ H_rep_Sn)...
     apply denom_nonvanishing_M_product_inv_L. 
      exact H_denom. 
      rewrite <- as_Moebius_L_min_one; rewrite <- as_Moebius_L_one; split; trivial.
    exact  H_denom.
    rewrite <- as_Moebius_L_min_one; rewrite <- as_Moebius_L_one; split; trivial.
   (* R *)
   rewrite (hd_tl_id (drop n alpha)) in Hind_rep;
   rewrite H_drop_n in Hind_rep;
   rewrite <- (drop_tl_S n alpha) in Hind_rep;
   generalize (rep_R_inv _ _ Hind_rep);
   intros H_rep_Sn.

   rewrite as_Moebius_inv_R.
    split; [|split]; try exact (H_rep_Sn).
     rewrite (hd_tl_id (drop (S n) alpha)) in H_rep_Sn; rewrite H_nth in H_rep_Sn.
     destruct d.
      rewrite as_Moebius_L_min_one; rewrite as_Moebius_L_one; apply (rep_L_inv_interval _ _ H_rep_Sn).
      rewrite as_Moebius_R_min_one; rewrite as_Moebius_R_one; apply (rep_R_inv_interval _ _ H_rep_Sn).
      rewrite as_Moebius_M_min_one; rewrite as_Moebius_M_one; apply (rep_M_inv_interval _ _ H_rep_Sn)...
     apply denom_nonvanishing_M_product_inv_R. 
      exact H_denom. 
      rewrite <- as_Moebius_R_one; rewrite <- as_Moebius_R_min_one; split; trivial.
    exact  H_denom.
    rewrite <- as_Moebius_R_one; rewrite <- as_Moebius_R_min_one; split; trivial.
   (* M *)
   rewrite (hd_tl_id (drop n alpha)) in Hind_rep;
   rewrite H_drop_n in Hind_rep;
   rewrite <- (drop_tl_S n alpha) in Hind_rep;
   generalize (rep_M_inv _ _ Hind_rep);
   intros H_rep_Sn.

   rewrite as_Moebius_inv_M.
    split; [|split]; try exact (H_rep_Sn).
     rewrite (hd_tl_id (drop (S n) alpha)) in H_rep_Sn; rewrite H_nth in H_rep_Sn.
     destruct d.
      rewrite as_Moebius_L_min_one; rewrite as_Moebius_L_one; apply (rep_L_inv_interval _ _ H_rep_Sn).
      rewrite as_Moebius_R_min_one; rewrite as_Moebius_R_one; apply (rep_R_inv_interval _ _ H_rep_Sn).
      rewrite as_Moebius_M_min_one; rewrite as_Moebius_M_one; apply (rep_M_inv_interval _ _ H_rep_Sn)...
     apply denom_nonvanishing_M_product_inv_M. 
      exact H_denom. 
      rewrite <- as_Moebius_M_one; rewrite <- as_Moebius_M_min_one; split; trivial.
    exact  H_denom.
    rewrite <- as_Moebius_M_one; rewrite <- as_Moebius_M_min_one; split; trivial.
Qed.


Lemma denom_nonvanishing_product_init: forall (alpha : Reals) (r : R) (n : nat),
       rep alpha r ->   denom_nonvanishing_M (product_init_rev alpha n) r.
Proof.
 intros alpha r n H_rep. 
 decompose record (product_init_rev_rep_drop_denom_nonvanishing alpha n r (Streams.hd (drop n alpha)) H_rep (refl_equal _));  trivial.
Qed.


Lemma rep_drop:forall alpha r n,rep alpha r -> rep (drop n alpha)  (as_Moebius (product_init_rev alpha n) r).
Proof.
 intros alpha r n H_rep. 
 decompose record (product_init_rev_rep_drop_denom_nonvanishing alpha n r (Streams.hd (drop n alpha)) H_rep (refl_equal _));  trivial.
Qed.

Lemma rep_drop_in_range:forall alpha r n, rep alpha r -> (-1<=as_Moebius (product_init_rev alpha n) r<=1)%R.
Proof.
 intros alpha r n H_rep; apply rep_inv_interval with (drop n alpha); apply rep_drop; trivial.
Qed.

