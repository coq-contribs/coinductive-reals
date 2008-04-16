(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)


(** Formalisation of the quadratic algorithm 

<<
quadratic xi (x:xs) (y:ys) | (Incl_T_L_dec xi)  = LL : quadratic (LL_inv o xi) (x:xs) (y:ys)
                           | (Incl_T_R_dec xi)  = RR : quadratic (RR_inv o xi) (x:xs) (y:ys)
                           | (Incl_T_M_dec xi)  = MM : quadratic (MM_inv o xi) (x:xs) (y:ys)
                           | otherwise = quadratic (xi o_l x o_r y) xs ys
>>

*)


Require Import digits.


Inductive emits_q : Tensor -> Reals -> Reals -> Prop :=
  | emits_q_L : forall (xi:Tensor) (alpha beta:Reals), Incl_T xi LL -> emits_q xi alpha beta
  | emits_q_R : forall (xi:Tensor) (alpha beta:Reals), Incl_T xi RR -> emits_q xi alpha beta
  | emits_q_M : forall (xi:Tensor) (alpha beta:Reals), Incl_T xi MM -> emits_q xi alpha beta
  | emits_q_absorbs : forall (xi:Tensor) (alpha beta:Reals), 
              		  emits_q (right_product (left_product xi (hd alpha)) (hd beta)) (tl alpha) (tl beta) ->
                          emits_q xi alpha beta.

Scheme emits_q_ind_dep := Induction for emits_q Sort Prop.

Lemma emits_q_absorbs_inv: forall xi (alpha beta:Reals), ~(Incl_T xi LL)-> ~(Incl_T xi RR) -> ~(Incl_T xi MM) -> 
             emits_q xi alpha beta -> emits_q (right_product (left_product xi (hd alpha)) (hd beta)) (tl alpha) (tl beta).
Proof.
 destruct 4; trivial; contradiction.
Defined.


Fixpoint modulus_q (xi:Tensor) (alpha beta:Reals) (H1:emits_q xi alpha beta) {struct H1}
        : prodT Digit (prodT Tensor (prodT Reals Reals)) :=
   match Incl_T_dec_D xi LL with
   | left _ => pairT LL (pairT (m_product inv_LL xi) (pairT alpha beta))
   | right H_emission_L =>
       match Incl_T_dec_D xi RR with
       | left _ => pairT RR (pairT (m_product inv_RR xi) (pairT alpha beta))
       | right H_emission_R =>
           match Incl_T_dec_D xi MM with
           | left _ => pairT MM (pairT (m_product inv_MM xi) (pairT alpha beta))
           | right H_emission_M =>
               modulus_q (right_product (left_product xi (hd alpha)) (hd beta)) (tl alpha) (tl beta)
                 (emits_q_absorbs_inv xi alpha beta H_emission_L H_emission_R H_emission_M H1)
           end
       end
   end.


Lemma modulus_q_PI:forall xi alpha beta H1 H2,  modulus_q xi alpha beta H1 = modulus_q xi alpha beta H2.
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
	    trivial).
Defined.

Lemma modulus_q_PI_strong:forall xi xi' alpha beta alpha' beta' H1 H2, xi=xi'->alpha=alpha' -> beta = beta' ->
   modulus_q xi alpha beta H1 = modulus_q xi' alpha' beta' H2.
Proof.
 intros; subst; apply modulus_q_PI.
Defined.

Lemma modulus_q_L:forall (xi:Tensor) (alpha beta:Reals) (t: emits_q xi alpha beta),(Incl_T xi LL) ->
                 modulus_q xi alpha beta t=pairT LL (pairT (m_product inv_LL xi) (pairT alpha beta)).
Proof.
 intros xi alpha beta t t_l.
 transitivity (modulus_q xi alpha beta (emits_q_L _ _ _ t_l)).
 apply modulus_q_PI.
 simpl;
  case (Incl_T_dec_D xi LL); try contradiction;
   intros; reflexivity.
Defined.

Lemma modulus_q_R:forall (xi:Tensor) (alpha beta:Reals) (t: emits_q xi alpha beta), ~(Incl_T xi LL) ->  (Incl_T xi RR) ->
                 modulus_q xi alpha beta t=pairT RR (pairT (m_product inv_RR xi) (pairT alpha beta)).
Proof.
 intros xi alpha beta t t_l t_r.
 transitivity (modulus_q xi alpha beta (emits_q_R _ _ _ t_r)).
 apply modulus_q_PI.
 simpl;
   case (Incl_T_dec_D xi LL); try contradiction;
     case (Incl_T_dec_D xi RR); try contradiction;
      intros; reflexivity.
Defined.

Lemma modulus_q_M:forall (xi:Tensor) (alpha beta:Reals) (t: emits_q xi alpha beta),~(Incl_T xi LL)->~(Incl_T xi RR)->(Incl_T xi MM)->
                 modulus_q xi alpha beta t=pairT MM (pairT (m_product inv_MM xi) (pairT alpha beta)).
Proof.
 intros xi alpha beta t t_l t_r t_m.
 transitivity (modulus_q xi alpha beta (emits_q_M _ _ _ t_m)).
 apply modulus_q_PI.
 simpl;
 case (Incl_T_dec_D xi LL); try contradiction;
  case (Incl_T_dec_D xi RR); try contradiction;
   case (Incl_T_dec_D xi MM); try contradiction;
    intros; reflexivity.
Defined.

Lemma modulus_q_absorbs:forall (xi:Tensor) (alpha beta:Reals) (t: emits_q xi alpha beta),~(Incl_T xi LL)->~(Incl_T xi RR)->~(Incl_T xi MM)->
  forall t', modulus_q xi alpha beta t = modulus_q (right_product (left_product xi (hd alpha)) (hd beta)) (tl alpha) (tl beta) t'.
Proof.
 intros xi alpha beta t t_l t_r t_m t'.
 transitivity (modulus_q xi alpha beta (emits_q_absorbs _ _ _ t')).
 apply modulus_q_PI.
 simpl.
 case (Incl_T_dec_D xi LL); try contradiction;
  case (Incl_T_dec_D xi RR); try contradiction;
   case (Incl_T_dec_D xi MM); try contradiction;
    intros _; reflexivity.
Defined.



Inductive step_productive_q : nat -> Tensor -> Reals -> Reals -> Prop :=
 |  step_productive_q_O : forall (xi:Tensor) (alpha beta:Reals), emits_q xi alpha beta -> step_productive_q O xi alpha beta
 |  step_productive_q_S : forall n (xi:Tensor) (alpha beta:Reals) (h:emits_q xi alpha beta), 
             step_productive_q n (fstT (sndT (modulus_q xi alpha beta h)))
              (fstT (sndT (sndT (modulus_q xi alpha beta h)))) (sndT (sndT (sndT (modulus_q xi alpha beta h)))) -> 
              step_productive_q (S n) xi alpha beta.

Lemma step_productive_q_inv_1: forall n (xi:Tensor) (alpha beta:Reals),
     step_productive_q n xi alpha beta -> emits_q xi alpha beta.
Proof.
 intros.
 destruct H; trivial.
Defined.


Lemma step_productive_q_S_inv_2: forall n (xi:Tensor) (alpha beta:Reals) (h:emits_q xi alpha beta),
         step_productive_q (S n) xi alpha beta ->
         step_productive_q n (fstT (sndT (modulus_q xi alpha beta h)))
                 (fstT (sndT (sndT (modulus_q xi alpha beta h)))) (sndT (sndT (sndT (modulus_q xi alpha beta h)))).
Proof.
 exact (
fun (n : nat) (xi : Tensor) (alpha beta : Reals) (h : emits_q xi alpha beta)
  (H : step_productive_q (S n) xi alpha beta) =>
let H0 :=
  match
    H in (step_productive_q n0 t r r0)
    return
      (n0 = S n ->
       t = xi ->
       r = alpha ->
       r0 = beta ->
       step_productive_q n (fstT (sndT (modulus_q xi alpha beta h)))
         (fstT (sndT (sndT (modulus_q xi alpha beta h))))
         (sndT (sndT (sndT (modulus_q xi alpha beta h)))))
  with
  | step_productive_q_O xi0 alpha0 beta0 H0 =>
      fun (H1 : 0 = S n) (H2 : xi0 = xi) (H3 : alpha0 = alpha)
        (H4 : beta0 = beta) =>
      let H :=
        (let H0 :=
           eq_ind 0
             (fun e : nat => match e with
                             | O => True
                             | S _ => False
                             end) I (S n) H1 in
         False_ind
           (xi0 = xi ->
            alpha0 = alpha ->
            beta0 = beta ->
            emits_q xi0 alpha0 beta0 ->
            step_productive_q n (fstT (sndT (modulus_q xi alpha beta h)))
              (fstT (sndT (sndT (modulus_q xi alpha beta h))))
              (sndT (sndT (sndT (modulus_q xi alpha beta h))))) H0) H2 H3
          H4 in
      H H0
  | step_productive_q_S n0 xi0 alpha0 beta0 h0 H0 =>
      fun (H1 : S n0 = S n) (H2 : xi0 = xi) (H3 : alpha0 = alpha)
        (H4 : beta0 = beta) =>
      let H :=
        (let H0 :=
           f_equal (fun e : nat => match e with
                                   | O => n0
                                   | S n => n
                                   end) H1 in
         eq_ind n
           (fun n0 : nat =>
            xi0 = xi ->
            alpha0 = alpha ->
            beta0 = beta ->
            step_productive_q n0
              (fstT (sndT (modulus_q xi0 alpha0 beta0 h0)))
              (fstT (sndT (sndT (modulus_q xi0 alpha0 beta0 h0))))
              (sndT (sndT (sndT (modulus_q xi0 alpha0 beta0 h0)))) ->
            step_productive_q n (fstT (sndT (modulus_q xi alpha beta h)))
              (fstT (sndT (sndT (modulus_q xi alpha beta h))))
              (sndT (sndT (sndT (modulus_q xi alpha beta h)))))
           (fun H2 : xi0 = xi =>
            let H :=
              eq_ind xi
                (fun t : Tensor =>
                 forall h0 : emits_q t alpha0 beta0,
                 alpha0 = alpha ->
                 beta0 = beta ->
                 step_productive_q n
                   (fstT (sndT (modulus_q t alpha0 beta0 h0)))
                   (fstT (sndT (sndT (modulus_q t alpha0 beta0 h0))))
                   (sndT (sndT (sndT (modulus_q t alpha0 beta0 h0)))) ->
                 step_productive_q n
                   (fstT (sndT (modulus_q xi alpha beta h)))
                   (fstT (sndT (sndT (modulus_q xi alpha beta h))))
                   (sndT (sndT (sndT (modulus_q xi alpha beta h)))))
                (fun (h0 : emits_q xi alpha0 beta0) 
                   (H3 : alpha0 = alpha) (H4 : beta0 = beta)
                   (H1 : step_productive_q n
                           (fstT (sndT (modulus_q xi alpha0 beta0 h0)))
                           (fstT
                              (sndT (sndT (modulus_q xi alpha0 beta0 h0))))
                           (sndT
                              (sndT (sndT (modulus_q xi alpha0 beta0 h0))))) =>
                 (let H :=
                    eq_ind_r
                      (fun beta0 : Reals =>
                       forall h0 : emits_q xi alpha0 beta0,
                       step_productive_q n
                         (fstT (sndT (modulus_q xi alpha0 beta0 h0)))
                         (fstT (sndT (sndT (modulus_q xi alpha0 beta0 h0))))
                         (sndT (sndT (sndT (modulus_q xi alpha0 beta0 h0)))) ->
                       step_productive_q n
                         (fstT (sndT (modulus_q xi alpha beta h)))
                         (fstT (sndT (sndT (modulus_q xi alpha beta h))))
                         (sndT (sndT (sndT (modulus_q xi alpha beta h)))))
                      (fun h0 : emits_q xi alpha0 beta =>
                       let H :=
                         eq_ind_r
                           (fun alpha0 : Reals =>
                            forall h0 : emits_q xi alpha0 beta,
                            step_productive_q n
                              (fstT (sndT (modulus_q xi alpha0 beta h0)))
                              (fstT
                                 (sndT (sndT (modulus_q xi alpha0 beta h0))))
                              (sndT
                                 (sndT (sndT (modulus_q xi alpha0 beta h0)))) ->
                            step_productive_q n
                              (fstT (sndT (modulus_q xi alpha beta h)))
                              (fstT
                                 (sndT (sndT (modulus_q xi alpha beta h))))
                              (sndT
                                 (sndT (sndT (modulus_q xi alpha beta h)))))
                           (fun h0 : emits_q xi alpha beta =>
                            eq_ind_r
                              (fun
                                 p : prodT Digit
                                       (prodT Tensor (prodT Reals Reals)) =>
                               step_productive_q n
                                 (fstT (sndT (modulus_q xi alpha beta h0)))
                                 (fstT
                                    (sndT
                                       (sndT (modulus_q xi alpha beta h0))))
                                 (sndT
                                    (sndT
                                       (sndT (modulus_q xi alpha beta h0)))) ->
                               step_productive_q n (fstT (sndT p))
                                 (fstT (sndT (sndT p)))
                                 (sndT (sndT (sndT p))))
                              (fun
                                 H1 : step_productive_q n
                                        (fstT
                                           (sndT
                                              (modulus_q xi alpha beta h0)))
                                        (fstT
                                           (sndT
                                              (sndT
                                                 (modulus_q xi alpha beta
                                                  h0))))
                                        (sndT
                                           (sndT
                                              (sndT
                                                 (modulus_q xi alpha beta
                                                  h0)))) => H1)
                              (modulus_q_PI xi alpha beta h h0)) H3 in
                       H h0) H4 in
                  H h0) H1) xi0 (sym_eq H2) in
            H h0) n0 (sym_eq H0)) H2 H3 H4 in
      H H0
  end in
H0 (refl_equal (S n)) (refl_equal xi) (refl_equal alpha) (refl_equal beta)
).
Defined.


(** #<em>#Productivity predicate#</em># *)

Inductive productive_q : Tensor -> Reals -> Reals ->Prop :=
  |  productive_q_absorbs : forall (xi:Tensor) (alpha beta:Reals), 
      (forall n, step_productive_q n xi alpha beta) -> productive_q xi alpha beta.


Lemma productive_q_emits_q:forall xi alpha beta,productive_q xi alpha beta -> emits_q xi alpha beta.
Proof.
 destruct 1.
 apply step_productive_q_inv_1 with O; trivial.
Defined.


Lemma modulus_q_productive_q: forall xi alpha beta (h:emits_q xi alpha beta), 
  let xi':=fstT (sndT (modulus_q xi alpha beta h)) in
   let alpha':=fstT (sndT (sndT (modulus_q xi alpha beta h))) in
    let beta':=sndT (sndT (sndT (modulus_q xi alpha beta h))) in
      productive_q xi alpha beta -> productive_q xi' alpha' beta'.
Proof.
 intros xi alpha beta h xi' alpha' beta' h_p_alpha_beta.
 constructor.
 intro n.
 inversion h_p_alpha_beta.
 generalize (H (S n)).
 subst xi'.
 subst alpha'.
 subst beta'.
 apply step_productive_q_S_inv_2.
Defined.


(** Definition of the quadratic algorithm *)

CoFixpoint quadratic (xi:Tensor) (alpha beta:Reals) (H :productive_q xi alpha beta) : Reals :=
  Cons (fstT (modulus_q xi alpha beta (productive_q_emits_q xi alpha beta H)))
       (quadratic (fstT (sndT (modulus_q xi alpha beta (productive_q_emits_q xi alpha beta H))))
                  (fstT (sndT (sndT (modulus_q xi alpha beta (productive_q_emits_q xi alpha beta H)))))
		  (sndT (sndT (sndT (modulus_q xi alpha beta (productive_q_emits_q xi alpha beta H)))))
                  (modulus_q_productive_q xi alpha beta (productive_q_emits_q xi alpha beta H) H)).


(** At this point one can uncomment the following two lines in order to extract to Haskell.
<<
Extraction Language Haskell.
Extraction "Xquadratic.hs" quadratic.
>>
*)

(** We now prove the cofixed point equations of the quadratic algorithm *)

Lemma quadratic_unfolded:forall xi alpha beta p, quadratic xi alpha beta p =
    Cons (fstT (modulus_q xi alpha beta (productive_q_emits_q xi alpha beta p)))
       (quadratic (fstT (sndT (modulus_q xi alpha beta (productive_q_emits_q xi alpha beta p))))
                  (fstT (sndT (sndT (modulus_q xi alpha beta (productive_q_emits_q xi alpha beta p)))))
		  (sndT (sndT (sndT (modulus_q xi alpha beta (productive_q_emits_q xi alpha beta p)))))
                  (modulus_q_productive_q xi alpha beta (productive_q_emits_q xi alpha beta p) p)).
Proof.
 intros;
 rewrite (unfold_Stream (quadratic xi alpha beta p));
 reflexivity.
Defined.


Lemma quadratic_EPI_strong:forall xi xi' alpha alpha' beta beta' p p', xi=xi'->alpha=alpha'->beta=beta'->
                bisim (quadratic xi alpha beta p)  (quadratic xi' alpha' beta' p').
Proof.
 cofix.
 intros;
 rewrite quadratic_unfolded;
 rewrite (quadratic_unfolded _ _ _ p');
 constructor; simpl;
 [ idtac
 |  apply quadratic_EPI_strong
 ];
 rewrite (modulus_q_PI_strong _ _ _ _ _ _ (productive_q_emits_q xi alpha beta p) (productive_q_emits_q xi' alpha' beta' p')); trivial.
Defined.

Lemma quadratic_EPI:forall xi alpha beta p p', bisim (quadratic xi alpha beta p)  (quadratic xi alpha beta p').
Proof.
 intros xi alpha beta p p'; apply quadratic_EPI_strong; reflexivity.
Defined.

Lemma quadratic_absorbs :forall xi alpha beta (p:productive_q xi alpha beta), ~(Incl_T xi LL)->~(Incl_T xi RR)->~(Incl_T xi MM)->
                forall p', bisim (quadratic xi alpha beta p)  (quadratic (right_product (left_product xi (hd alpha)) (hd beta)) (tl alpha) (tl beta) p').
Proof.
 intros xi alpha beta p t_l t_r t_m p'.
 rewrite quadratic_unfolded.
 rewrite (quadratic_unfolded (right_product (left_product xi (hd alpha)) (hd beta))).
 generalize (productive_q_emits_q _ _ _ p); intros t.
 generalize (modulus_q_productive_q xi alpha beta t p).
 rewrite (modulus_q_absorbs _ _ _ t t_l t_r t_m (emits_q_absorbs_inv _ _ _ t_l t_r t_m t)).
  rewrite (modulus_q_PI _ _ _ (emits_q_absorbs_inv xi alpha beta t_l t_r t_m t)
                       (productive_q_emits_q (right_product (left_product xi (hd alpha)) (hd beta)) (tl alpha) (tl beta) p')).
 constructor; simpl; trivial; apply quadratic_EPI.
Defined.

Lemma quadratic_emits_L :forall xi alpha beta (p:productive_q xi alpha beta), (Incl_T xi LL) ->
                forall p', bisim (quadratic xi alpha beta p)  (Cons LL (quadratic (m_product inv_LL xi) alpha beta p')).
Proof.
 intros xi alpha beta p t_l p'.
 rewrite quadratic_unfolded.
 rewrite (quadratic_unfolded (m_product inv_LL xi)).
 generalize (productive_q_emits_q _ _ _ p); intros t.
 generalize (modulus_q_productive_q xi alpha beta t p).

 rewrite (modulus_q_L _ _ _ t t_l). 
 intros.
 constructor; simpl; trivial.
 rewrite <- quadratic_unfolded;
 apply quadratic_EPI.
Defined.
 
Lemma quadratic_emits_R :forall xi alpha beta (p:productive_q xi alpha beta), ~(Incl_T xi LL) -> (Incl_T xi RR) ->
                forall p', bisim (quadratic xi alpha beta p)  (Cons RR (quadratic (m_product inv_RR xi) alpha beta p')).
Proof.
 intros xi alpha beta p t_l t_r p'.
 rewrite quadratic_unfolded.
 rewrite (quadratic_unfolded (m_product inv_RR xi)).
 generalize (productive_q_emits_q _ _ _ p); intros t.
 generalize (modulus_q_productive_q xi alpha beta t p).

 rewrite (modulus_q_R _ _ _ t t_l t_r). 
 intros.
 constructor; simpl; trivial.
  rewrite <- quadratic_unfolded;
  apply quadratic_EPI.
Defined.

Lemma quadratic_emits_M :forall xi alpha beta (p:productive_q xi alpha beta), ~(Incl_T xi LL) -> ~(Incl_T xi RR) -> (Incl_T xi MM) ->
                forall p', bisim (quadratic xi alpha beta p)  (Cons MM (quadratic (m_product inv_MM xi) alpha beta p')).
Proof.
 intros xi alpha beta p t_l t_r t_m p'.
 rewrite quadratic_unfolded.
 rewrite (quadratic_unfolded (m_product inv_MM xi)).
 generalize (productive_q_emits_q _ _ _ p); intros t.
 generalize (modulus_q_productive_q xi alpha beta t p).

 rewrite (modulus_q_M _ _ _ t t_l t_r t_m). 
 intros.
 constructor; simpl; trivial.
  rewrite <- quadratic_unfolded;
  apply quadratic_EPI.
Defined.
