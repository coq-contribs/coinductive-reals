(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)


(** Formalisation of the homographic algorithm 

<<
homographic mu (x:xs) | (Incl_M_L_dec mu)  = LL : homographic (LL_inv o mu) (x:xs)
                      | (Incl_M_R_dec mu)  = RR : homographic (RR_inv o mu) (x:xs)
                      | (Incl_M_M_dec mu)  = MM : homographic (MM_inv o mu) (x:xs)
                      | otherwise = homographic (mu o x) xs
>>

*)


Require Import digits.

Inductive emits_h : Matrix -> Reals -> Prop :=
  | emits_h_L : forall (mu:Matrix) (alpha:Reals), Incl_M mu LL -> emits_h mu alpha
  | emits_h_R : forall (mu:Matrix) (alpha:Reals), Incl_M mu RR -> emits_h mu alpha
  | emits_h_M : forall (mu:Matrix) (alpha:Reals), Incl_M mu MM -> emits_h mu alpha
  | emits_h_absorbs : forall (mu:Matrix) (alpha:Reals), 
					  emits_h (product mu (hd alpha)) (tl alpha) -> emits_h mu alpha.

Scheme emits_h_ind_dep := Induction for emits_h Sort Prop.

Lemma emits_h_absorbs_inv: forall mu (alpha:Reals), ~(Incl_M mu LL)-> ~(Incl_M mu RR) ->
                        ~(Incl_M mu MM) -> emits_h mu alpha -> emits_h (product mu (hd alpha)) (tl alpha).
Proof.
 destruct 4; trivial; contradiction.
Defined.

Fixpoint modulus_h (mu:Matrix) (alpha:Reals) (H1:emits_h mu alpha) {struct H1}: prodT Digit (prodT Matrix Reals) :=
   match Incl_M_dec_D mu LL with
   | left _ => pairT LL (pairT (product inv_LL mu) alpha)
   | right H_emission_L =>
       match Incl_M_dec_D mu RR with
       | left _ => pairT RR (pairT (product inv_RR mu) alpha)
       | right H_emission_R =>
           match Incl_M_dec_D mu MM with
           | left _ => pairT MM (pairT (product inv_MM mu) alpha)
           | right H_emission_M =>
               modulus_h (product mu (hd alpha)) (tl alpha)
                 (emits_h_absorbs_inv mu alpha H_emission_L H_emission_R
                    H_emission_M H1)
           end
       end
   end.

Lemma modulus_h_PI:forall mu alpha H1 H2,  modulus_h mu alpha H1 = modulus_h mu alpha H2.
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
	    trivial).
Defined.

Lemma modulus_h_PI_strong:forall mu mu' alpha alpha' H1 H2, mu=mu'->alpha=alpha' ->
   modulus_h mu alpha H1 = modulus_h mu' alpha' H2.
Proof.
 intros; subst; apply modulus_h_PI.
Defined.

Lemma modulus_h_L:forall (mu:Matrix) (alpha:Reals) (t: emits_h mu alpha),(Incl_M mu LL) -> modulus_h mu alpha t = pairT LL (pairT (product inv_LL mu) alpha).
Proof.
 intros mu alpha t t_l.
 transitivity (modulus_h mu alpha (emits_h_L _ _ t_l)).
 apply modulus_h_PI.
 simpl;
  case (Incl_M_dec_D mu LL); try contradiction;
   intros; reflexivity.
Defined.

Lemma modulus_h_R:forall (mu:Matrix) (alpha:Reals) (t: emits_h mu alpha), ~(Incl_M mu LL) ->  (Incl_M mu RR) ->
                             modulus_h mu alpha t = pairT RR (pairT (product inv_RR mu) alpha).
Proof.
 intros mu alpha t t_l t_r.
 transitivity (modulus_h mu alpha (emits_h_R _ _ t_r)).
 apply modulus_h_PI.
 simpl;
   case (Incl_M_dec_D mu LL); try contradiction;
     case (Incl_M_dec_D mu RR); try contradiction;
      intros; reflexivity.
Defined.

Lemma modulus_h_M:forall (mu:Matrix) (alpha:Reals) (t: emits_h mu alpha),~(Incl_M mu LL)->~(Incl_M mu RR)->(Incl_M mu MM)->
                             modulus_h mu alpha t = pairT MM (pairT (product inv_MM mu) alpha).
Proof.
 intros mu alpha t t_l t_r t_m.
 transitivity (modulus_h mu alpha (emits_h_M _ _ t_m)).
 apply modulus_h_PI.
 simpl;
 case (Incl_M_dec_D mu LL); try contradiction;
  case (Incl_M_dec_D mu RR); try contradiction;
   case (Incl_M_dec_D mu MM); try contradiction;
    intros; reflexivity.
Defined.

Lemma modulus_h_absorbs:forall (mu:Matrix) (alpha:Reals) (t: emits_h mu alpha),~(Incl_M mu LL)->~(Incl_M mu RR)->~(Incl_M mu MM)->
  forall t', modulus_h mu alpha t = modulus_h (product mu (hd alpha)) (tl alpha) t'.
Proof.
 intros mu alpha t t_l t_r t_m t'.
 transitivity (modulus_h mu alpha (emits_h_absorbs _ _ t')).
 apply modulus_h_PI.
 simpl.
 case (Incl_M_dec_D mu LL); try contradiction;
  case (Incl_M_dec_D mu RR); try contradiction;
   case (Incl_M_dec_D mu MM); try contradiction;
    intros _; reflexivity.
Defined.


Inductive step_productive_h : nat -> Matrix -> Reals->Prop :=
  |  step_productive_h_O : forall (mu:Matrix) (alpha:Reals), emits_h mu alpha -> step_productive_h O mu alpha
  |  step_productive_h_S : forall n (mu:Matrix) (alpha:Reals) (h:emits_h mu alpha), 
             step_productive_h n (fstT (sndT (modulus_h mu alpha h))) (sndT (sndT (modulus_h mu alpha h))) -> 
              step_productive_h (S n) mu alpha.

Lemma step_productive_h_inv_1: forall n (mu:Matrix) (alpha:Reals), step_productive_h n mu alpha -> emits_h mu alpha.
Proof.
 intros.
 destruct H; trivial.
Defined.


Lemma step_productive_h_S_inv_2: forall n (mu:Matrix)(alpha:Reals) (h:emits_h mu alpha),step_productive_h (S n) mu alpha ->
                     step_productive_h n (fstT (sndT (modulus_h mu alpha h))) (sndT (sndT (modulus_h mu alpha h))).
Proof.
exact(
fun (n : nat) (mu : Matrix) (alpha : Reals) (h : emits_h mu alpha)
  (H : step_productive_h (S n) mu alpha) =>
let H0 :=
  match
    H in (step_productive_h n0 m r)
    return
      (n0 = S n ->
       m = mu ->
       r = alpha ->
       step_productive_h n (fstT (sndT (modulus_h mu alpha h)))
         (sndT (sndT (modulus_h mu alpha h))))
  with
  | step_productive_h_O mu0 alpha0 H0 =>
      fun (H1 : 0 = S n) (H2 : mu0 = mu) (H3 : alpha0 = alpha) =>
      let H :=
        (let H0 :=
           eq_ind 0
             (fun e : nat => match e with
                             | O => True
                             | S _ => False
                             end) I (S n) H1 in
         False_ind
           (mu0 = mu ->
            alpha0 = alpha ->
            emits_h mu0 alpha0 ->
            step_productive_h n (fstT (sndT (modulus_h mu alpha h)))
              (sndT (sndT (modulus_h mu alpha h)))) H0) H2 H3 in
      H H0
  | step_productive_h_S n0 mu0 alpha0 h0 H0 =>
      fun (H1 : S n0 = S n) (H2 : mu0 = mu) (H3 : alpha0 = alpha) =>
      let H :=
        (let H0 :=
           f_equal (fun e : nat => match e with
                                   | O => n0
                                   | S n => n
                                   end) H1 in
         eq_ind n
           (fun n0 : nat =>
            mu0 = mu ->
            alpha0 = alpha ->
            step_productive_h n0 (fstT (sndT (modulus_h mu0 alpha0 h0)))
              (sndT (sndT (modulus_h mu0 alpha0 h0))) ->
            step_productive_h n (fstT (sndT (modulus_h mu alpha h)))
              (sndT (sndT (modulus_h mu alpha h))))
           (fun H2 : mu0 = mu =>
            let H :=
              eq_ind mu
                (fun m : Matrix =>
                 forall h0 : emits_h m alpha0,
                 alpha0 = alpha ->
                 step_productive_h n (fstT (sndT (modulus_h m alpha0 h0)))
                   (sndT (sndT (modulus_h m alpha0 h0))) ->
                 step_productive_h n (fstT (sndT (modulus_h mu alpha h)))
                   (sndT (sndT (modulus_h mu alpha h))))
                (fun (h0 : emits_h mu alpha0) (H3 : alpha0 = alpha)
                   (H1 : step_productive_h n
                           (fstT (sndT (modulus_h mu alpha0 h0)))
                           (sndT (sndT (modulus_h mu alpha0 h0)))) =>
                 (let H :=
                    eq_ind_r
                      (fun alpha0 : Reals =>
                       forall h0 : emits_h mu alpha0,
                       step_productive_h n
                         (fstT (sndT (modulus_h mu alpha0 h0)))
                         (sndT (sndT (modulus_h mu alpha0 h0))) ->
                       step_productive_h n
                         (fstT (sndT (modulus_h mu alpha h)))
                         (sndT (sndT (modulus_h mu alpha h))))
                      (fun h0 : emits_h mu alpha =>
                       eq_ind_r
                         (fun p : prodT Digit (prodT Matrix Reals) =>
                          step_productive_h n
                            (fstT (sndT (modulus_h mu alpha h0)))
                            (sndT (sndT (modulus_h mu alpha h0))) ->
                          step_productive_h n (fstT (sndT p)) (sndT (sndT p)))
                         (fun
                            H1 : step_productive_h n
                                   (fstT (sndT (modulus_h mu alpha h0)))
                                   (sndT (sndT (modulus_h mu alpha h0))) =>
                          H1) (modulus_h_PI mu alpha h h0)) H3 in
                  H h0) H1) mu0 (sym_eq H2) in
            H h0) n0 (sym_eq H0)) H2 H3 in
      H H0
  end in
H0 (refl_equal (S n)) (refl_equal mu) (refl_equal alpha)
).
Defined.

(** #<em>#Productivity predicate#</em># *)

Inductive productive_h : Matrix -> Reals->Prop :=
  |  productive_h_absorbs : forall (mu:Matrix) (alpha:Reals), 
      (forall n, step_productive_h n mu alpha) -> productive_h mu alpha.


Lemma productive_h_emits_h:forall mu alpha,productive_h mu alpha -> emits_h mu alpha.
Proof.
 destruct 1.
 apply step_productive_h_inv_1 with O; trivial.
Defined.


Lemma modulus_h_productive_h: forall mu alpha (h:emits_h mu alpha), 
  let mu':=fstT (sndT (modulus_h mu alpha h)) in
    let alpha':=sndT (sndT (modulus_h mu alpha h)) in productive_h mu alpha -> productive_h mu' alpha'.
Proof.
 intros mu alpha h mu' alpha' h_p_alpha.
 constructor.
 intro n.
 inversion h_p_alpha.
 generalize (H (S n)).
 subst mu'.
 subst alpha'.
 apply step_productive_h_S_inv_2.
Defined.

(** Definition of the homographic algorithm *)

CoFixpoint homographic (mu:Matrix) (alpha : Reals) (H : productive_h mu alpha) : Reals :=
  Cons
    (fstT (modulus_h mu alpha (productive_h_emits_h mu alpha H)))
    (homographic (fstT(sndT(modulus_h mu alpha (productive_h_emits_h mu alpha H))))
                 (sndT(sndT(modulus_h mu alpha (productive_h_emits_h mu alpha H))))
                 (modulus_h_productive_h mu alpha (productive_h_emits_h mu alpha H) H)).



(** At this point one can uncomment the following two lines in order to extract to Haskell.
<<
Extraction Language Haskell.
Extraction "Xhomographic.hs" homographic.
>>
*)

(** We now prove the cofixed point equations of the homographic algorithm *)

Lemma homographic_unfolded:forall mu alpha p, homographic mu alpha p = Cons
    (fstT (modulus_h mu alpha (productive_h_emits_h mu alpha p)))
    (homographic (fstT(sndT(modulus_h mu alpha (productive_h_emits_h mu alpha p))))
                 (sndT(sndT(modulus_h mu alpha (productive_h_emits_h mu alpha p))))
                 (modulus_h_productive_h mu alpha (productive_h_emits_h mu alpha p) p)).
Proof.
 intros;
 rewrite (unfold_Stream (homographic mu alpha p));
 reflexivity.
Defined.


Lemma homographic_EPI_strong:forall mu mu' alpha alpha' p p', mu=mu'->alpha=alpha'->
                bisim (homographic mu alpha p)  (homographic mu' alpha' p').
Proof.
 cofix.
 intros;
 rewrite homographic_unfolded;
 rewrite (homographic_unfolded _ _ p');
 constructor; simpl ;
 [ idtac
 |  apply homographic_EPI_strong
 ];
 rewrite (modulus_h_PI_strong _ _ _ _ (productive_h_emits_h mu alpha p) (productive_h_emits_h mu' alpha' p')); trivial.
Defined.

Lemma homographic_EPI:forall mu alpha p p', bisim (homographic mu alpha p)  (homographic mu alpha p').
Proof.
 intros mu alpha p p'; apply homographic_EPI_strong; reflexivity.
Defined.

Lemma homographic_absorbs :forall mu alpha (p:productive_h mu alpha), ~(Incl_M mu LL)->~(Incl_M mu RR)->~(Incl_M mu MM)->
                forall p', bisim (homographic mu alpha p)  (homographic (product mu (hd alpha)) (tl alpha) p').
Proof.
 intros mu alpha p t_l t_r t_m p'.
 rewrite homographic_unfolded.
 rewrite (homographic_unfolded (product mu (hd alpha))).
 generalize (productive_h_emits_h _ _ p); intros t.
 generalize (modulus_h_absorbs _ _ t t_l t_r t_m (emits_h_absorbs_inv _ _ t_l t_r t_m t)).
 intros H_eq.
 generalize (modulus_h_productive_h mu alpha t p).
 rewrite H_eq.
 rewrite (modulus_h_PI _ _ (emits_h_absorbs_inv mu alpha t_l t_r t_m t) (productive_h_emits_h (product mu (hd alpha)) (tl alpha) p')).
 constructor; simpl; trivial; apply homographic_EPI.
Defined.

Lemma homographic_emits_L :forall mu alpha (p:productive_h mu alpha), (Incl_M mu LL) ->
                forall p', bisim (homographic mu alpha p)  (Cons LL (homographic (product inv_LL mu) alpha p')).
Proof.
 intros mu alpha p t_l p'.
 rewrite homographic_unfolded.
 rewrite (homographic_unfolded (product inv_LL mu)).
 generalize (productive_h_emits_h _ _ p); intros t.
 generalize (modulus_h_productive_h mu alpha t p).

 rewrite (modulus_h_L _ _ t t_l). 
 intros.
 constructor; simpl; trivial.
 rewrite <- homographic_unfolded;
 apply homographic_EPI.
Defined.
 
Lemma homographic_emits_R :forall mu alpha (p:productive_h mu alpha), ~(Incl_M mu LL) -> (Incl_M mu RR) ->
                forall p', bisim (homographic mu alpha p)  (Cons RR (homographic (product inv_RR mu) alpha p')).
Proof.
 intros mu alpha p t_l t_r p'.
 rewrite homographic_unfolded.
 rewrite (homographic_unfolded (product inv_RR mu)).
 generalize (productive_h_emits_h _ _ p); intros t.
 generalize (modulus_h_productive_h mu alpha t p).

 rewrite (modulus_h_R _ _ t t_l t_r). 
 intros.
 constructor; simpl; trivial.
  rewrite <- homographic_unfolded;
  apply homographic_EPI.
Defined.

Lemma homographic_emits_M :forall mu alpha (p:productive_h mu alpha), ~(Incl_M mu LL) -> ~(Incl_M mu RR) -> (Incl_M mu MM) ->
                forall p', bisim (homographic mu alpha p)  (Cons MM (homographic (product inv_MM mu) alpha p')).
Proof.
 intros mu alpha p t_l t_r t_m p'.
 rewrite homographic_unfolded.
 rewrite (homographic_unfolded (product inv_MM mu)).
 generalize (productive_h_emits_h _ _ p); intros t.
 generalize (modulus_h_productive_h mu alpha t p).

 rewrite (modulus_h_M _ _ t t_l t_r t_m). 
 intros.
 constructor; simpl; trivial.
  rewrite <- homographic_unfolded;
  apply homographic_EPI.
Defined.
