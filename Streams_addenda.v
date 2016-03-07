(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses>                       *)
(************************************************************************)

Require Export List.
Require Export Streams.
Require Import Omega.

(** This file includes some random facts about streams (and lists)
which at the moment of writing this are not found in the standard
library. Some of the lemmas here are not used in the present
development but are rather useful.  *)

Notation " A (=) B " := (EqSt A B) (at level 70).
Notation " x |:| xs " := (Cons x xs) (at level 60, right associativity).


(* tactic for proving cofixpoint equations *)

Ltac LHS :=
match goal with
| |-(?a = _) => constr:(a)
| |-(_ ?a _) => constr:(a)
end.

Ltac decomp_coind := intros; let L := LHS in rewrite (Streams.unfold_Stream L); reflexivity.


Set Implicit Arguments. 

Section Stream_functions_with_one_implicit_argument.

Variable A:Type.


Notation Local Str := (Stream A).

Lemma hd_tl_id:forall xs:Str, xs = hd xs |:| tl xs.
Proof.
 intros [x xs]; trivial.
Defined.

Section replicate.

CoFixpoint replicate (a:A) := Cons a (replicate a).

Lemma replicate_spelled (a:A) : replicate a = Cons a (replicate a).
Proof.
 rewrite (Streams.unfold_Stream (replicate a)) at 1; trivial.
Qed.

End replicate.

Section Str_nth_properties.

Lemma Str_nth_S:forall n x (xs:Stream A), Str_nth (S n) (x|:|xs) = Str_nth n xs. 
Proof.
 intros n x xs.
 unfold Str_nth; reflexivity.
Defined. 

End Str_nth_properties.

Section drop.

(** 

We define the function that drops the first [n] elements of a stream:

<<
drop n [] = []
drop 0 xs = xs
drop n (x:xs) = drop (n-1) xs 
>>

*)


Fixpoint drop (n:nat): Str->Str :=fun s :Str => 
  match n with
  | O   => s
  |(S m) => match s with (Cons x xs) => (drop m xs) end
  end.      

Lemma drop_1:forall x xs n,drop (S n) (Cons x xs)=drop n xs.
Proof.
 trivial.
Defined.

Lemma drop_one_tl : forall xs, drop 1 xs = tl xs.
Proof.
 reflexivity.
Defined.

Lemma drop_n_tl:forall xs n, drop n (tl xs) = drop (n + 1) xs.
Proof.
 intros [x xs];
 induction n.
 reflexivity.
 replace (S n + 1) with (S (S n));
 [reflexivity
 |abstract omega
 ].
Defined.

Lemma drop_plus_tl:forall xs m n, drop m (drop n xs)=drop (m+n) xs.
Proof.
 intros xs m n; generalize xs; clear xs.
 induction n;
 [ simpl; rewrite Plus.plus_0_r
 | replace (m+S n)%nat with ((m+n)+1)%nat; replace (S n) with (n+1)%nat; try abstract omega;
   intros xs;
   repeat rewrite <- drop_n_tl;
   rewrite <- (IHn (tl xs))
 ]; trivial.
Defined.

Lemma drop_Str_nth:forall n (xs:Stream A), hd (drop n xs) = Str_nth n xs.
Proof.
 intros n; induction n; intros [x xs];  trivial.
 rewrite drop_1; rewrite Str_nth_S; trivial.
Qed.

Lemma drop_S_tl:forall (xs:Stream A) n, drop (S n) xs = drop n (tl xs).
Proof.
 intros [x xs] n; trivial.
Qed.

Lemma drop_tl_S: forall n (xs:Stream A), drop (S n) xs = tl (drop n xs).
Proof.
 intros n; induction n; intros [x xs]; trivial.
 transitivity (tl (drop n xs)); trivial.
 rewrite drop_S_tl; trivial.
Qed.


End drop.

Section take.

(** [take] outputs a list containing an initial segment of the input
stream. *)

Fixpoint take (n:nat) (xs: Stream A) {struct n} : List.list A :=
  match n with 
  | 0 => List.nil
  | S n => List.cons (hd xs) (take n (tl xs))
  end.


Lemma take_S_n : forall xs n, take (S n) xs = List.cons (hd xs) (take n (tl xs)).
Proof.
 intros xs [|n]; reflexivity.
Defined.

End take.

Section even_and_odd.

(** [even] takes the elements that are in the even place in a stream. *)
CoFixpoint  even  (s:Str) : Str:= (hd s)|:|(even (tl (tl s))).
    
Lemma  even_spelled:forall x y xs, (even (x|:|(y|:|xs)))=(x|:|(even xs)).
Proof.
 decomp_coind.
Defined.

Lemma even_spelled_2:forall (s:Str), (even s)=(Cons (hd s) (even (tl (tl s)))).
Proof.
 decomp_coind.
Defined.

CoFixpoint odd (s:Str) : Str:= hd (tl s) |:| (odd (tl (tl s))).

Lemma odd_spelled:forall x y xs, (odd (x|:|(y|:|xs)))=(y|:|(odd xs)).
Proof.
 decomp_coind.
Defined.

Lemma odd_even_tl:forall s, odd s (=) (even (tl s)).
Proof.
 cofix.
 intros [x [y xs]].
 rewrite odd_spelled. 
 simpl.
 rewrite even_spelled_2. 
 constructor.
 reflexivity.
 simpl.
 apply odd_even_tl.
Defined.

Lemma even_oddth:forall xs n, Str_nth n (even xs) = Str_nth (2*n) xs.
Proof.
 intros xs n.
 generalize xs.
 clear xs.
 induction n.
 intros xs.
 rewrite even_spelled_2.
 unfold Str_nth.
 reflexivity.

 intros xs.
 unfold Str_nth.
 replace (2 * (S n)) with (S (2*n+1)); try omega.
 simpl.
 replace (n + (n + 0) + 1) with (S (2*n)); try omega.
 simpl.
 replace (n + (n + 0)) with (2*n); try omega.
 apply (IHn (tl (tl xs))).
Defined.

End even_and_odd.

Section combine.

(** [combine], combines two streams by interleaving them alternatively. *)

CoFixpoint combine (x:Str) (y:Str) : Str :=(Cons (hd x) (combine y (tl x))).

Lemma combine_spelled:forall s1 s2, (combine s1 s2)=(Cons (hd s1) (combine s2 (tl s1))).
Proof.
 decomp_coind.
Defined.

Lemma combine_spelled_2: forall x (xs ys:Str), (combine (x|:|xs) ys)=(x|:|(combine ys xs)).
Proof.
 decomp_coind.
Defined.

Lemma combine_spelled_3: forall x y (xs ys:Str), combine (x|:|xs) (y|:|ys) = x|:| y |:| (combine xs ys).
Proof.
 intros x y xs ys.
 rewrite combine_spelled_2.
 apply (@f_equal2 A Str Str (@Cons A)); trivial.
 apply combine_spelled_2.
Defined.


Lemma combine_odd_even_is_id:forall (s:Str), (combine (even s) (odd s))(=)s.
Proof.
 cofix.
 intros [x [y xs]].
 rewrite even_spelled.
 rewrite combine_spelled_2.
 rewrite odd_spelled.
 constructor.
 reflexivity.
 rewrite combine_spelled.
 constructor.
 reflexivity.
 simpl.
 apply combine_odd_even_is_id.
Defined.

Lemma combine_odd: forall (xs ys zs: Stream A), combine xs ys (=) zs -> ys (=) odd zs.
Proof.
 cofix.
 intros [x0 xs] [y0 ys] (z0 & z1 & zs) H_bisim;
 rewrite combine_spelled_3 in H_bisim;
 inversion H_bisim;
 constructor.
  inversion H0; trivial.
  rewrite odd_spelled; apply combine_odd with xs; inversion H0; assumption.
Qed.
  
Lemma combine_even: forall (xs ys zs: Stream A), combine xs ys (=) zs -> xs (=) even zs.
Proof.
 cofix.
 intros [x0 xs] [y0 ys] (z0 & z1 & zs) H_bisim;
 rewrite combine_spelled_3 in H_bisim;
 inversion H_bisim;
 constructor.
  inversion H0; trivial.
  rewrite even_spelled; apply combine_even with ys; inversion H0; assumption.
Qed.

End combine.

Section enumFrom.

(** Stream of consecutive natural numbers: *)
CoFixpoint enumFrom:nat->(Stream nat):=fun n:nat => (Cons n (enumFrom (S n))).

Lemma enumFrom_spelled:forall (n:nat), (enumFrom n)= (Cons n (enumFrom (S n))). 
Proof.
 decomp_coind.
Defined.

Definition nats := enumFrom 0.

End enumFrom.

Section tails.

CoFixpoint tails (xs:Stream A) := Cons (tl xs) (tails (tl xs)).

Lemma tails_spelled (xs:Stream A) : tails xs = Cons (tl xs) (tails (tl xs)).
Proof.
 decomp_coind.
Qed.

End tails.

End Stream_functions_with_one_implicit_argument.

Section Stream_functions_with_two_implicit_argument.

Variable A B:Type.

Section map_properties.

Lemma map_spelled:forall (f:A->B) xs, Streams.map f xs = (f (hd xs)) |:| (Streams.map f (tl xs)).
Proof.
 decomp_coind.
Defined.

Lemma Str_nth_map_pointwise:forall n xs (f:A->B), f (Str_nth n xs) = Str_nth n (Streams.map f xs).
Proof.
 intros n; induction n; intros [x xs] f.
  unfold Str_nth, Str_nth_tl; rewrite map_spelled; trivial. 
  rewrite map_spelled; unfold hd,tl; repeat rewrite Str_nth_S; trivial.
Qed.

End map_properties.

End Stream_functions_with_two_implicit_argument.

(* ****************************** List functions ****************************** *)

Section List_functions_with_one_implicit_argument.

Variable A:Type.

Section rev_properties.

Lemma rev_cons:forall (l:list A) a, rev (a :: l)=  rev l ++ (a :: nil).
Proof.
 intros [|l] a; reflexivity.
Qed.

Lemma rev_take_S_Str_nth:forall n (xs:Stream A), rev (take (S n) xs) =  (Str_nth n xs) :: (rev (take n xs)).
Proof.
 intros n; induction n; intros [x xs];
  [ simpl; unfold Str_nth, Str_nth_tl, hd; reflexivity
  | rewrite take_S_n; unfold hd,tl; rewrite rev_cons; rewrite IHn; trivial].
Qed.

End rev_properties.

Section init.

Section length_properties.

Lemma length_S:forall x xs, length (x::xs)=S (@length A xs).
Proof.
 trivial.
Qed.

Lemma length_O_nil:forall xs, @length A xs=O -> xs = nil.
Proof.
 intros [|x xs] H; trivial; discriminate.
Qed.

End length_properties.

Definition init := removelast.

Lemma init_cons_cons:forall x y xs, init (x::y::xs)=x::(@init A (y::xs)).
Proof.
 trivial.
Qed.

End init.

Section safer_nth.

Definition safer_nth (xs : list A) :=
match xs as l return (forall n : nat, n < length l -> A) with
| nil => fun n Hn => False_rect A (False_ind False (Lt.lt_n_O n Hn))
| x :: xs0 => fun n Hn => let f:=
    (fix safer_nth'' (xs1:list A) (n0:nat) {struct n0}:n0<length (x::xs1)->A :=
       match n0 as n1 return (n1 < length (x :: xs1) -> A) with
       | 0 => fun _ => x
       | S n1 => fun Hn0 => safer_nth'' xs1 n1 (Lt.lt_trans n1 (S n1) (length (x :: xs1)) (Lt.lt_n_Sn n1) Hn0)
       end) in 
    f xs0 n Hn
end.

End safer_nth.

Section safe_last.

Fixpoint safe_last (l:list A) : option A :=
         match l with
         | nil => None
         | x0 :: nil => Some x0
         | x0 :: (x1 :: xs) as l0 => safe_last l0
         end.

End safe_last.

Section List_functions_for_decidable_equality.

Hypothesis eq_dec:forall (x y:A),{x=y}+{~x=y}.

(** We define [nub] that removes duplicate elements from the list,
    keeping only the first occurence of each element.  *)

Fixpoint nub (l:list A) : list A := 
 match l with
 | nil => nil
 | x :: xs => if In_dec eq_dec x xs then nub xs else x :: nub xs
    end. 

Fixpoint nub_append (l ys : list A) {struct l} : list A :=
  match l with
  | nil => ys
  | x :: xs => if In_dec eq_dec x ys then nub_append xs ys else x :: nub_append xs ys
  end.

Lemma nub_In_cons:forall x xs, In x xs -> nub (x :: xs)=nub xs.
Proof.
 intros x [|y ys]; simpl; [intros H_; contradiction H_|];
 intros [H1|H1].
  destruct (eq_dec y x) as [H2|H2];[destruct (In_dec eq_dec y ys) as [H3|H3]; trivial|contradiction H2].
  destruct (eq_dec y x) as [H2|H2];[destruct (In_dec eq_dec y ys) as [H3|H3]; trivial|];
  destruct (In_dec eq_dec x ys) as [H3|H3]; trivial; contradiction H3.
Qed.    


Lemma nub_notIn_cons:forall x xs, ~In x xs -> nub (x :: xs)=x::nub xs.
Proof.
 intros x [|y ys];simpl. 
  intros _; trivial.
  intros H1.
  destruct (eq_dec y x) as [H2|H2];[contradiction H1;left;assumption|destruct (In_dec eq_dec x ys) as [H3|H3]]; trivial.
  contradiction H1; right; assumption.
Qed.

Lemma nub_In: forall (l:list A) x, In x (nub l) -> In x l.
Proof.
 intros l; induction l as [|y ys]; intros x H_nub.
  contradiction H_nub. 
  destruct (In_dec eq_dec y ys) as [H|H].
   apply in_cons; apply IHys; rewrite <- (nub_In_cons y ys H); assumption.
   rewrite (nub_notIn_cons y ys H) in H_nub;
   destruct (in_inv H_nub) as [H1|H1].
    subst y; apply in_eq. 
    apply in_cons; apply IHys; assumption.
Qed.

Lemma incl_dec_inf:forall xs ys, {incl xs ys} + {~(@incl A xs ys)}.
Proof.
 intros xs; induction xs as [|x xs IH]. 
  left; red; simpl; intros a0 H_; contradiction H_.
  intros ys; destruct (IH ys) as [H_ind|H_ind].
   destruct (In_dec eq_dec x ys) as [H_in_dec|H_in_dec].
    left; apply incl_cons; assumption.
    right; intros H_; apply (H_in_dec); apply H_; apply in_eq. 
   right; intros H_; apply H_ind; red; intros a Ha; apply (H_ a); apply in_cons; assumption.
Qed.

Lemma in_inv_inf: forall (a b : A) (l : list A), In b (a :: l) -> {a = b}+{In b l}.
Proof.
 intros a b [|x xs] H_in.
  left; destruct (in_inv H_in); trivial; contradiction H.
  destruct (eq_dec a b) as [H1|H2].
   left; trivial.
   right; destruct H_in; trivial; contradiction H2.
Qed.

End List_functions_for_decidable_equality.



End List_functions_with_one_implicit_argument.

Section List_functions_with_two_implicit_argument.


Variable A B:Type.


Section fold_right_properties.

Lemma fold_right_cons : forall (f:B->A->A) (l:list B) b a0, fold_right f a0 (b::l) = f b (fold_right f a0 l).
Proof.
 intros; reflexivity.
Defined.

End fold_right_properties.

Section fold_left.

Lemma fold_left_cons : forall (f:A->B->A) l b a0, fold_left f (b::l) a0 = fold_left f l (f a0 b).
Proof.
 intros; reflexivity.
Defined.

End fold_left.

Section zipWith.

Fixpoint zipWith (C:Type) (z:A->B->C) (la:list A) (lb:list B) {struct la}: list C:=
         match la, lb  with
         | x :: xs, y::ys  => z x y :: zipWith z xs ys
         | _,_ => nil
         end.

Implicit Arguments zipWith [C].

Definition zip:=zipWith (@pair A B).

End zipWith.

Section concatMap.

Definition concatMap (xs:list A) (f:A->list B):=flat_map f xs.

End concatMap.

End List_functions_with_two_implicit_argument.

Section more_list_functions.

(* This is called prod in the standard library *)
Definition pairs (A B:Type) (xs:list A) (ys:list B) := concatMap xs (fun x=> concatMap ys (fun y=> (x,y)::nil)).

End more_list_functions.

Unset Implicit Arguments.
