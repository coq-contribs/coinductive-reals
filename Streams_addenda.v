(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)

Require Export List.
Require Export Streams.
Require Omega.

Notation " A (=) B " := (EqSt A B) (at level 70).


(* tactic for proving cofixpoint equations *)

Ltac LHS :=
match goal with
| |-(?a = _) => constr: a
| |-(_ ?a _) => constr: a
end.

Ltac decomp_coind := intros; let L := LHS in rewrite (Streams.unfold_Stream L); reflexivity.


Set Implicit Arguments. 

Section Additionial_Functions.

Variable A:Set.


Notation Local Str := (Stream A).

Notation " x |:| xs " := (Cons x xs) (at level 60, right associativity).


Lemma hd_tl_id:forall xs:Str, xs = hd xs |:| tl xs.
Proof.
 intros [x xs]; trivial.
Defined.


Section drop.

(** 

We define the functin [drop] that the first [n] element of a stream:

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

End drop.

Section take.

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

Section fold_left.

Variable B:Set.

Lemma fold_left_cons : forall (f:A->B->A) l b a0, fold_left f (b::l) a0 = fold_left f l (f a0 b).
Proof.
 intros; reflexivity.
Defined.

End fold_left.

Section Str_nth_properties.

Lemma Str_nth_S:forall n x (xs:Stream A), Str_nth (S n) (x|:|xs) = Str_nth n xs. 
Proof.
 intros n x xs.
 unfold Str_nth; reflexivity.
Defined. 

End Str_nth_properties.

Section map_properties.
Variable B:Set.

Lemma map_unfolded:forall (f:A->B) xs, Streams.map f xs = (f (hd xs)) |:| (Streams.map f (tl xs)).
Proof.
 decomp_coind.
Defined.

End map_properties.

Section odd_and_even.

(** odd: takes the elemnts that are in the odd place *)
CoFixpoint  odd  (s:Str) : Str:= (hd s)|:|(odd (tl (tl s))).
    
Lemma  odd_unfolded:forall x y xs, (odd (x|:|(y|:|xs)))=(x|:|(odd xs)).
Proof.
 decomp_coind.
Defined.

Lemma odd_unfolded_2:forall (s:Str), (odd s)=(Cons (hd s) (odd (tl (tl s)))).
Proof.
 decomp_coind.
Defined.

CoFixpoint even (s:Str) : Str:= hd (tl s) |:| (even (tl (tl s))).

Lemma even_unfolded:forall x y xs, (even (x|:|(y|:|xs)))=(y|:|(even xs)).
Proof.
 decomp_coind.
Defined.

Lemma even_odd_tl:forall s, even s (=) (odd (tl s)).
Proof.
 cofix.
 intros [x [y xs]].
 rewrite even_unfolded. 
 simpl.
 rewrite odd_unfolded_2. 
 constructor.
 reflexivity.
 simpl.
 apply even_odd_tl.
Defined.

Lemma odd_eventh:forall xs n, Str_nth n (odd xs) = Str_nth (2*n) xs.
Proof.
 intros xs n.
 generalize xs.
 clear xs.
 induction n.
 intros xs.
 rewrite odd_unfolded_2.
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

End odd_and_even.

Section combine.

(** [combine], combines two streams by interleaving them alternatively. *)

CoFixpoint combine (x:Str) (y:Str) : Str :=(Cons (hd x) (combine y (tl x))).

Lemma combine_unfolded:forall s1 s2, (combine s1 s2)=(Cons (hd s1) (combine s2 (tl s1))).
Proof.
 decomp_coind.
Defined.

Lemma combine_unfolded_2: forall x (xs ys:Str), (combine (x|:|xs) ys)=(x|:|(combine ys xs)).
Proof.
 decomp_coind.
Defined.

Lemma combine_unfolded_3: forall x y (xs ys:Str), combine (x|:|xs) (y|:|ys) = x|:| y |:| (combine xs ys).
Proof.
 intros x y xs ys.
 rewrite combine_unfolded_2.
 apply (@f_equal2 A Str Str (@Cons A)); trivial.
 apply combine_unfolded_2.
Defined.


Lemma combine_even_odd_is_id:forall (s:Str), (combine (odd s) (even s))(=)s.
Proof.
 cofix.
 intros [x [y xs]].
 rewrite odd_unfolded.
 rewrite combine_unfolded_2.
 rewrite even_unfolded.
 constructor.
 reflexivity.
 rewrite combine_unfolded.
 constructor.
 reflexivity.
 simpl.
 apply combine_even_odd_is_id.
Defined.

End combine.


Section enumFrom.

(** stream of natural numbers *)
CoFixpoint enumFrom:nat->(Stream nat):=fun n:nat => (Cons n (enumFrom (S n))).

Lemma enumFrom_unfolded:forall (n:nat), (enumFrom n)= (Cons n (enumFrom (S n))). 
Proof.
 decomp_coind.
Defined.

Definition nats := enumFrom 0.

End enumFrom.

End Additionial_Functions.

Unset Implicit Arguments.

(* Various lemma's with explicit arguments *)

Lemma rev_cons:forall (A : Type) (l:list A) a, rev (a :: l)=  rev l ++ (a :: nil).
Proof.
 intros A [|l] a; reflexivity.
Qed.

Lemma rev_take_S_Str_nth:forall n (A :Set) (xs:Stream A), rev (take (S n) xs) =  (Str_nth n xs) :: (rev (take n xs)).
Proof.
 intros n; induction n; intros A [x xs];
  [ simpl; unfold Str_nth, Str_nth_tl, hd; reflexivity
  | rewrite take_S_n; unfold hd,tl; rewrite rev_cons; rewrite IHn; trivial].
Qed.

Lemma fold_right_cons : forall (A B:Type) (f:B->A->A) (l:list B) b a0, fold_right f a0 (b::l) = f b (fold_right f a0 l).
Proof.
 intros; reflexivity.
Defined.

Lemma Str_nth_map_pointwise:forall (A B:Set) n xs (f:A->B), f (Str_nth n xs) = Str_nth n (Streams.map f xs).
Proof.
 intros A B n; induction n; intros [x xs] f.
  unfold Str_nth, Str_nth_tl; rewrite map_unfolded; trivial.
  rewrite map_unfolded; unfold hd,tl; repeat rewrite Str_nth_S; trivial. 
Qed.

Lemma drop_Str_nth:forall (A:Set) n (xs:Stream A), hd (drop n xs) = Str_nth n xs.
Proof.
 intros A n; induction n; intros [x xs];  trivial.
 rewrite drop_1; rewrite Str_nth_S; trivial.
Qed.

Lemma drop_S_tl:forall (A:Set) (xs:Stream A) n, drop (S n) xs = drop n (tl xs).
Proof.
 intros A [x xs] n; trivial.
Qed.

Lemma drop_tl_S: forall (A:Set) n (xs:Stream A), drop (S n) xs = tl (drop n xs).
Proof.
 intros A n; induction n; intros [x xs]; trivial.
 transitivity (tl (drop n xs)); trivial.
 rewrite drop_S_tl; trivial.
Qed.

