(************************************************************************)
(* Copyright 2007 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Import Recdef.
Require Import digits.


(** We prove the LNP (Least Number Principle) for a decidable property
on [nat*Digits] *)

Section LNP_for_nat_digits.

Variable P:nat -> Digit -> Prop.

Variable P_is_decidable:forall n (d:Digit), {P n d}+{~(P n d)}.

Variable there_is_a_bound:{n:nat& {d:Digit |P n d}}.

Let n_bound:= projS1 there_is_a_bound.

Let n_bound_has_d:= projS2 there_is_a_bound.

Let d_of_n_bound_has_d:= proj1_sig n_bound_has_d.

(**
<<
-- the smallest k<=m<=n that has a property p
lnp_next n k p = if k==n || p k then k
                 else lnp_next n (k+1) p
-- the smallest k<=n that has a property p
lnp_all n p = lnp_next n 0 p
>>
*)

Lemma le_neq_S:forall m n, le m n-> ~ n=m -> le (S m) n.
Proof.
 intros; omega.
Qed.

Function f_LNP_dec_next (m:nat) (Hm:le m n_bound) {measure (fun (x:nat)=>(minus n_bound x)) m} : nat * Digit :=
         match Peano_dec.eq_nat_dec n_bound m with
         | left _ =>  (n_bound, d_of_n_bound_has_d)
         | right Hneq => if P_is_decidable m LL then (m, LL)
                         else if P_is_decidable m RR then (m, RR)
                              else if P_is_decidable m MM then (m, MM) 
                              else f_LNP_dec_next (S m) (le_neq_S _ _ Hm Hneq)
         end.
Proof.
 intros; omega.
Qed.


Definition f_LNP_dec_all : (nat*Digit) := f_LNP_dec_next O (le_O_n _).

Lemma result_f_LNP_dec_next_has_property:forall m (Hm:le m n_bound), let (n,d):=f_LNP_dec_next m Hm  in P n d.
Proof.
 intros m Hm.
 remember (f_LNP_dec_next m Hm) as nd; destruct nd.
 functional induction (f_LNP_dec_next m Hm); [ | | | |apply IHp; assumption];
  assert (H_eq:=f_equal (@fst nat Digit) Heqnd); simpl in H_eq; rewrite H_eq; clear H_eq;
  assert (H_eq:=f_equal (@snd nat Digit) Heqnd); simpl in H_eq; rewrite H_eq; trivial.
  exact (proj2_sig n_bound_has_d)...
Qed.

Lemma result_f_LNP_dec_all_has_property: P (fst f_LNP_dec_all) (snd f_LNP_dec_all).
Proof.
 unfold f_LNP_dec_all. 
 generalize (result_f_LNP_dec_next_has_property O (le_O_n n_bound)).
 destruct (f_LNP_dec_next 0 (le_O_n n_bound)).
 trivial.
Qed.   

Lemma result_f_LNP_le_bound: forall m (Hm:le m n_bound), (fst (f_LNP_dec_next m Hm) <= n_bound)%nat.
Proof.
 intros m Hm.
 functional induction (f_LNP_dec_next m Hm); simpl; trivial.
Qed.

Lemma result_f_LNP_dec_next_minimal_property: forall m p (Hm:le m n_bound) (d : Digit), 
  (m<=p)%nat -> (p< fst (f_LNP_dec_next m Hm))%nat -> ~ P p d.
Proof.
 intros m p Hm d Hp1 Hp2.
 assert (Hnbound:=le_not_lt _ _ (result_f_LNP_le_bound m Hm)).
 functional induction (f_LNP_dec_next m Hm); simpl.
  intros _; apply Hnbound; apply le_lt_trans with p; trivial; rewrite <- _x; assumption...
  intros _; simpl in Hp2; apply (lt_irrefl m); apply le_lt_trans with p; assumption...
  intros _; simpl in Hp2; apply (lt_irrefl m); apply le_lt_trans with p; assumption...
  intros _; simpl in Hp2; apply (lt_irrefl m); apply le_lt_trans with p; assumption...
  destruct (le_lt_eq_dec _ _ Hp1) as [Hp3|Hp3]. 
   assert (Hp4:=lt_le_S _ _ Hp3); apply (IHp0 Hp4 Hp2 Hnbound).
   rewrite <- Hp3; destruct d; assumption.
Qed.

Lemma result_f_LNP_dec_all_minimal_property: forall (p : nat) (d : Digit), (p < fst f_LNP_dec_all)%nat -> ~ P p d.
Proof.
 unfold f_LNP_dec_all. 
 intros p d Hp.
 apply (result_f_LNP_dec_next_minimal_property O) with (le_O_n n_bound); trivial; apply le_O_n.  
Qed.

Lemma LNP_sigS_nat_Digit: {n:nat& {d:Digit | P n d/\ forall m d, (lt m n) -> ~(P m d)}}.
Proof.
 remember f_LNP_dec_all as nd.
 exists (fst nd); exists (snd nd); split. 
   subst nd; apply result_f_LNP_dec_all_has_property...
   intros m d Hm; subst nd; apply result_f_LNP_dec_all_minimal_property; assumption...
Qed.

End LNP_for_nat_digits.
