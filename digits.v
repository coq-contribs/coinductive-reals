(************************************************************************)
(* Copyright 2006 Milad Niqui                                           *)
(* This file is distributed under the terms of the                      *)
(* GNU Lesser General Public License Version 2.1                        *)
(* A copy of the license can be found at                                *)
(*                  <http://www.gnu.org/licenses/gpl.txt>               *)
(************************************************************************)


Require Export QArith_Stern_Brocot.   (* Rtional Numbers of QArith package *)
Require Export Streams.   (* Streams from the standard library *)
Require Import Streams_addenda.
Require Import Raxioms.


Unset Printing Notations.

Open Scope type_scope.

Definition Vector := Q*Q.

Definition Matrix := Vector*Vector.

Definition Tensor := Matrix*Matrix.

Set Printing Notations.




Definition EStream:Set := (Stream Matrix).

Inductive Digit : Set := LL : Digit | RR: Digit | MM: Digit.

(* Bisimulation equality is defined in the stanadard library
Coq.Lists.Streams.EqSt. We need that equlaity to prove the cofixed
point equations later on. *)

Definition bisim := @EqSt Digit.

Open Scope Z_scope.
Open Scope Q_scope.


Definition map_digits (d: Digit) : Matrix := 
  match d with 
  | LL =>  (1/2, (-1)/2, (1/2,3/2))
  | RR =>  (1/2, 1/2, ((-1)/2,3/2))
  | MM =>  (1/1, 0/1, (0/1, 3/1))
  end.

Coercion map_digits : Digit >-> Matrix.

Definition inv_LL := ((3/2,1/2),((-1)/2,1/2)). 
Definition inv_RR := ((3/2,(-1)/2),(1/2,1/2)). 
Definition inv_MM := ((1/1,0/1),(0/1,1/3)). 

Definition inv_digit (D : Digit) : Matrix := 
  match D with 
  | LL => inv_LL
  | RR => inv_RR
  | MM => inv_MM
  end.  

(** Product of two matrices *)

Definition product (M N:Matrix):Matrix := 
  let (a1,b1) := (fst (fst M), snd (fst M)) in
    let (c1,d1) := (fst (snd M), snd (snd M)) in
      let (a2,b2) := (fst (fst N), snd (fst N)) in
	let (c2,d2) := (fst (snd N), snd (snd N)) in
	  ((a1 * a2 + b1 * c2, a1 * b2 + b1 * d2),
            (c1 * a2 + d1 * c2, c1 * b2 + d1 * d2)).

(** Product of a matrix and a tensor *)

Definition m_product (M:Matrix) (T:Tensor) : Tensor := 
  let (A,B) := (fst (fst M), snd (fst M)) in
   let (C,D) := (fst (snd M), snd (snd M)) in
    let (a,b) := (fst (fst (fst T)), snd (fst (fst T))) in
     let (c,d) := (fst (snd (fst T)), snd (snd (fst T))) in
      let (e,f) := (fst (fst (snd T)), snd (fst (snd T))) in
       let (g,h) := (fst (snd (snd T)), snd (snd (snd T))) in
          (((A*a + B*e),(A*b + B*f), ((A*c + B*g), (A*d + B*h))),
           ((C*a + D*e),(C*b + D*f), ((C*c + D*g), (C*d + D*h)))).

(** Left product of a tensor and a matrix *)

Definition left_product (T:Tensor) (M:Matrix) : Tensor := 
  let (a,b) := (fst (fst (fst T)), snd (fst (fst T))) in
   let (c,d) := (fst (snd (fst T)), snd (snd (fst T))) in
    let (e,f) := (fst (fst (snd T)), snd (fst (snd T))) in
     let (g,h) := (fst (snd (snd T)), snd (snd (snd T))) in
      let (A,B) := (fst (fst M), snd (fst M)) in
	let (C,D) := (fst (snd M), snd (snd M)) in
          (((a*A + c*C),(b*A + d*C), ((a*B + c*D), (b*B + d*D))),
           ((e*A + g*C),(f*A + h*C), ((e*B + g*D), (f*B + h*D)))).

(** Right product of a tensor and a matrix *)

Definition right_product (T:Tensor) (M:Matrix) : Tensor := 
  let (a,b) := (fst (fst (fst T)), snd (fst (fst T))) in
   let (c,d) := (fst (snd (fst T)), snd (snd (fst T))) in
    let (e,f) := (fst (fst (snd T)), snd (fst (snd T))) in
     let (g,h) := (fst (snd (snd T)), snd (snd (snd T))) in
      let (A,B) := (fst (fst M), snd (fst M)) in
	let (C,D) := (fst (snd M), snd (snd M)) in
          (((a*A + b*C),(a*B + b*D), ((c*A + d*C), (c*B + d*D))),
           ((e*A + f*C),(e*B + f*D), ((g*A + h*C), (g*B + h*D)))).


(** This is the set Digits^{\infty} (stream of elements of Digits). *)

Definition Reals := (Stream Digit).

Definition map_reals  : Reals ->  EStream  := Streams.map map_digits.

Coercion map_reals :Reals >-> EStream.


Definition Bounded_M (M:Matrix):=
  let (a,b) := (fst (fst M), snd (fst M)) in
    let (c,d) := (fst (snd M), snd (snd M)) in
      (Qlt Zero (d+c) /\ Qlt Zero (d-c)) \/  (* 0<cx+d *)
      (Qlt (d+c) Zero /\ Qlt (d-c) Zero).   (* cx+d<0 *)

Lemma Bounded_M_dec: forall (M:Matrix), {Bounded_M M} + {~(Bounded_M M)}.
Proof.
 intros ((a,b),(c,d));
 unfold Bounded_M, fst, snd;
 case (Qlt_dec Zero (d+c)); intros;
  case (Qlt_dec Zero (d-c)); intros;
   case (Qlt_dec (d+c) Zero); intros;
    case (Qlt_dec (d-c) Zero); intros; tauto.
Qed.


(** Our base interval is I_base:=[-1,+1] (Due to choice of digits set,
    and hence the following means:

  M(I_base)\subseteq  D(I_base).

  Note also that 0< dig4-dig3, dig4+dig3 *) 


Definition Incl_M (M:Matrix) (D:Digit) :=
  let (a,b) := (fst (fst M), snd (fst M)) in
    let (c,d) := (fst (snd M), snd (snd M)) in
      let (dig1,dig2) := (fst (fst (map_digits D)), snd (fst (map_digits D))) in
	let (dig3,dig4) := (fst (snd (map_digits D)), snd (snd (map_digits D))) in
	  Bounded_M M /\
              (d-c)*((d-c)*(dig2-dig1))<= (d-c)*((b-a)*(dig4-dig3)) /\           (* D(-1)<=M(-1) *)
              (d-c)*((b-a)*(dig3+dig4))<= (d-c)*((d-c)*(dig1+dig2)) /\           (* M(-1)<=D(+1) *)
              (d+c)*((c+d)*(dig2-dig1))<= (d+c)*((a+b)*(dig4-dig3)) /\           (* D(-1)<=M(+1) *)
              (d+c)*((a+b)*(dig3+dig4))<= (d+c)*((c+d)*(dig1+dig2)).             (* M(+1)<=D(+1) *)



Lemma Incl_M_dec_D: forall (M : Matrix) (D:Digit), {Incl_M M D} + {~(Incl_M M D)}.
Proof.
 intros ((a,b),(c,d)) D;
 unfold Incl_M;
 destruct (map_digits D) as ((dig1,dig2),(dig3,dig4)); simpl;
 case (Bounded_M_dec (a,b,(c,d))); intros ; [| tauto];
    case (Qle_dec ((d-c)*((d-c)*(dig2-dig1))) ((d-c)*((b-a)*(dig4-dig3)))); intros; [|tauto];
     case (Qle_dec ((d-c)*((b-a)*(dig3+dig4))) ((d-c)*((d-c)*(dig1+dig2)))); intros; [|tauto];
      case (Qle_dec ((d+c)*((c+d)*(dig2-dig1))) ((d+c)*((a+b)*(dig4-dig3)))); intros; [|tauto];
        case (Qle_dec ((d+c)*((a+b)*(dig3+dig4))) ((d+c)*((c+d)*(dig1+dig2)))); intros; tauto.
Qed.


Definition Bounded_T (T:Tensor):=
  let (a,b) := (fst (fst (fst T)), snd (fst (fst T))) in
   let (c,d) := (fst (snd (fst T)), snd (snd (fst T))) in
    let (e,f) := (fst (fst (snd T)), snd (fst (snd T))) in
     let (g,h) := (fst (snd (snd T)), snd (snd (snd T))) in
      (Qlt Zero (e+f+g+h) /\ Qlt Zero (e-f-g+h) /\ Qlt Zero (-e-f+g+h) /\ Qlt Zero (-e+f-g+h)) \/  (* 0<exy+fx+gy+h *)
      (Qlt (e+f+g+h) Zero /\ Qlt (e-f-g+h) Zero /\ Qlt (-e-f+g+h) Zero /\ Qlt (-e+f-g+h) Zero).    (* exy+fx+gy+h<0 *)


Lemma Bounded_T_dec: forall (T:Tensor), {Bounded_T T} + {~(Bounded_T T)}.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h)));
 unfold Bounded_T, fst, snd.
 case (Qlt_dec Zero (e+f+g+h)); case (Qlt_dec (e+f+g+h) Zero); intros; [ | | |tauto];
  case (Qlt_dec Zero (e-f-g+h)); case (Qlt_dec (e-f-g+h) Zero); intros; [ | | |tauto| | | |tauto| | | |tauto];
   case (Qlt_dec Zero (-e-f+g+h)); intros;
    case (Qlt_dec Zero (-e+f-g+h)); intros;
	  case (Qlt_dec (-e-f+g+h) Zero); intros;
	    case (Qlt_dec (-e+f-g+h) Zero); intros; tauto.
Qed.

Definition Incl_T (T:Tensor) (D:Digit) :=
  let (a,b) := (fst (fst (fst T)), snd (fst (fst T))) in
   let (c,d) := (fst (snd (fst T)), snd (snd (fst T))) in
    let (e,f) := (fst (fst (snd T)), snd (fst (snd T))) in
     let (g,h) := (fst (snd (snd T)), snd (snd (snd T))) in
      let (dig1,dig2) := (fst (fst (map_digits D)), snd (fst (map_digits D))) in
	let (dig3,dig4) := (fst (snd (map_digits D)), snd (snd (map_digits D))) in
	  Bounded_T T /\
	   ((e-f-g+h)*((e-f-g+h)*(dig2-dig1)))   <= ((e-f-g+h)*((a-b-c+d)*(dig4-dig3)))   /\   (* D(-1)<=T(-1,-1) *)
	   ((e-f-g+h)*((a-b-c+d)*(dig3+dig4)))   <= ((e-f-g+h)*((e-f-g+h)*(dig1+dig2)))   /\   (* T(-1,-1)<=D(+1) *)
	   ((-e-f+g+h)*((-e-f+g+h)*(dig2-dig1))) <= ((-e-f+g+h)*((-a-b+c+d)*(dig4-dig3))) /\   (* D(-1)<=T(-1,+1) *)
	   ((-e-f+g+h)*((-a-b+c+d)*(dig3+dig4))) <= ((-e-f+g+h)*((-e-f+g+h)*(dig1+dig2))) /\   (* T(-1,+1)<=D(+1) *)
	   ((-e+f-g+h)*((-e+f-g+h)*(dig2-dig1))) <= ((-e+f-g+h)*((-a+b-c+d)*(dig4-dig3))) /\   (* D(-1)<=T(+1,-1) *)
	   ((-e+f-g+h)*((-a+b-c+d)*(dig3+dig4))) <= ((-e+f-g+h)*((-e+f-g+h)*(dig1+dig2))) /\   (* T(+1,-1)<=D(+1) *)
	   ((e+f+g+h)*((e+f+g+h)*(dig2-dig1)))   <= ((e+f+g+h)*((a+b+c+d)*(dig4-dig3)))   /\   (* D(-1)<=T(+1,+1) *)
	   ((e+f+g+h)*((a+b+c+d)*(dig3+dig4)))   <= ((e+f+g+h)*((e+f+g+h)*(dig1+dig2))).        (* T(+1,+1)<=D(+1) *) 

Lemma Incl_T_dec_D: forall (T : Tensor) (D:Digit), {Incl_T T D} + {~(Incl_T T D)}.
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))) D.
 unfold Incl_T. 
 destruct (map_digits D) as ((dig1,dig2),(dig3,dig4)); unfold fst, snd.
 case (Bounded_T_dec (a, b, (c, d), (e, f, (g, h)))); intros; [|tauto];
 case (Qle_dec ((e-f-g+h)*((e-f-g+h)*(dig2-dig1))) ((e-f-g+h)*((a-b-c+d)*(dig4-dig3)))); intros; [|tauto];
    case (Qle_dec ((e-f-g+h)*((a-b-c+d)*(dig3+dig4))) ((e-f-g+h)*((e-f-g+h)*(dig1+dig2)))); intros; [|tauto];
      case (Qle_dec ((-e-f+g+h)*((-e-f+g+h)*(dig2-dig1))) ((-e-f+g+h)*((-a-b+c+d)*(dig4-dig3)))); intros; [|tauto];
	case (Qle_dec ((-e-f+g+h)*((-a-b+c+d)*(dig3+dig4))) ((-e-f+g+h)*((-e-f+g+h)*(dig1+dig2)))); intros; [|tauto];
          case (Qle_dec ((-e+f-g+h)*((-e+f-g+h)*(dig2-dig1))) ((-e+f-g+h)*((-a+b-c+d)*(dig4-dig3)))); intros; [|tauto];
	    case (Qle_dec ((-e+f-g+h)*((-a+b-c+d)*(dig3+dig4))) ((-e+f-g+h)*((-e+f-g+h)*(dig1+dig2)))); intros; [|tauto];
              case (Qle_dec ((e+f+g+h)*((e+f+g+h)*(dig2-dig1))) ((e+f+g+h)*((a+b+c+d)*(dig4-dig3)))); intros; [|tauto];
		case (Qle_dec ((e+f+g+h)*((a+b+c+d)*(dig3+dig4))) ((e+f+g+h)*((e+f+g+h)*(dig1+dig2)))); intros;  [|tauto];
                  left; split; trivial; repeat split; assumption.
Qed.



Definition Is_refining_M M:= 
  let (a,b) := (fst (fst M), snd (fst M)) in
    let (c,d) := (fst (snd M), snd (snd M)) in
      Bounded_M M /\
      ((Qle Zero (a+b+c+d) /\ Qle Zero (a-b-c+d) /\ Qle Zero (-a-b+c+d) /\ Qle Zero (-a+b-c+d)) \/  (* 0<axy+bx+cy+d *)
       (Qle (a+b+c+d) Zero /\ Qle (a-b-c+d) Zero /\ Qle (-a-b+c+d) Zero /\ Qle (-a+b-c+d) Zero)).    (* axy+bx+cy+d<0 *)

Definition Is_refining_T T:=
  let (a,b) := (fst (fst (fst T)), snd (fst (fst T))) in
   let (c,d) := (fst (snd (fst T)), snd (snd (fst T))) in
    let (e,f) := (fst (fst (snd T)), snd (fst (snd T))) in
     let (g,h) := (fst (snd (snd T)), snd (snd (snd T))) in
      Bounded_T T /\
      ((Qle Zero (a+b+c+d+e+f+g+h) /\ Qle Zero (-a-b-c-d+e+f+g+h) /\ 
        Qle Zero (a-b-c+d+e-f-g+h) /\ Qle Zero (-a+b+c-d+e-f-g+h) /\ 
        Qle Zero (-a-b+c+d-e-f+g+h) /\ Qle Zero (a+b-c-d-e-f+g+h) /\ 
        Qle Zero (-a+b-c+d-e+f-g+h) /\ Qle Zero (a-b+c-d-e+f-g+h)) \/
       (Qle (a+b+c+d+e+f+g+h) Zero /\ Qle (-a-b-c-d+e+f+g+h) Zero /\ 
        Qle (a-b-c+d+e-f-g+h) Zero /\ Qle (-a+b+c-d+e-f-g+h) Zero /\ 
        Qle (-a-b+c+d-e-f+g+h) Zero /\ Qle (a+b-c-d-e-f+g+h) Zero /\ 
        Qle (-a+b-c+d-e+f-g+h) Zero /\ Qle (a-b+c-d-e+f-g+h) Zero)).
 


(** The iedntity mobius map *)
Definition idM :=  (1 / 1, 0 / 1, (0 / 1, 1 / 1)).

Lemma Is_refining_M_idM:Is_refining_M idM.
Proof.
 red; unfold idM, Bounded_M, fst, snd; qZ_numerals; split; left; repeat split; auto.
Qed.

(** This calculates the product of the inverses of the first n elements of [alpha] (in reverse order) 
    (n=4)   a_0:a_1:a_2:a_3:...  |-------> a_3^ o a_2^ o a_1^ o a_0^: ...
*)
Definition product_init_rev alpha n: Matrix := List.fold_right product idM (List.rev (Streams_addenda.take n (Streams.map inv_digit alpha))).

Definition product_init_pure (alpha:Reals) n := List.fold_right product idM (Streams_addenda.take n (map_reals alpha)).

Lemma product_associative:forall M N P, product M (product N P) = product (product M N) P.
Proof.
 intros ((a0,b0),(c0,d0)) ((a1,b1),(c1,d1)) ((a2,b2),(c2,d2));
 unfold product, fst, snd;
 apply (f_equal2 (@pair Vector Vector));
 apply (f_equal2 (@pair Q Q)); ring; auto.
Qed.

Lemma product_digit_inv_digit_identity_right:forall (d:Digit), product d (inv_digit d) = idM.
Proof.
 intros [ | | ]; unfold map_digits, inv_digit, inv_LL, inv_RR, inv_MM, idM, product, fst, snd;
 apply (f_equal2 (@pair Vector Vector));
 apply (f_equal2 (@pair Q Q)); qZ_numerals. 
Qed.


Lemma product_idM_identity_right:forall M, product M idM = M.
Proof.
  intros ((a,b),(c,d));
  unfold idM, product, fst, snd, Qdiv at 2 3 6 7; rewrite Qmult_zero; repeat rewrite Qmult_zero_right;
  repeat rewrite Qplus_zero_right; repeat rewrite Qplus_zero_left; qZ_numerals; rewrite Qdiv_Qone_Qone; 
  repeat rewrite Qmult_one_right; trivial.
Qed.

Lemma product_idM_identity_left:forall M, product idM M = M.
Proof.
  intros ((a,b),(c,d));
  unfold idM, product, fst, snd, Qdiv at 2 4 5 7; rewrite Qmult_zero; repeat rewrite Qmult_zero_right;
  repeat rewrite Qplus_zero_right; repeat rewrite Qplus_zero_left; qZ_numerals; rewrite Qdiv_Qone_Qone; 
  repeat rewrite Qmult_one_left; trivial.
Qed.


Lemma product_inv_L:forall mu, mu = (product (map_digits LL) (product inv_LL mu)).
Proof.
 intro mu; rewrite product_associative;
 replace inv_LL with (inv_digit LL); trivial;
 rewrite product_digit_inv_digit_identity_right;
 rewrite product_idM_identity_left; reflexivity.
Qed.

Lemma product_inv_R:forall mu, mu = (product (map_digits RR) (product inv_RR mu)).
Proof.
 intro mu; rewrite product_associative;
 replace inv_RR with (inv_digit RR); trivial;
 rewrite product_digit_inv_digit_identity_right;
 rewrite product_idM_identity_left; reflexivity.
Qed.

Lemma product_inv_M:forall mu, mu = (product MM (product inv_MM mu)).
Proof.
 intro mu; rewrite product_associative;
 replace inv_MM with (inv_digit MM); trivial;
 rewrite product_digit_inv_digit_identity_right;
 rewrite product_idM_identity_left; reflexivity.
Qed.

Lemma right_left_product_idM_identity_right:forall T, right_product (left_product T idM) idM = T.
Proof.
  intros (((a,b),(c,d)),((e,f),(g,h)));
  unfold idM, left_product, right_product, fst, snd, Qdiv at 2 3 6 7; rewrite Qmult_zero; repeat rewrite Qmult_zero_right;
  repeat rewrite Qplus_zero_right; repeat rewrite Qplus_zero_left; qZ_numerals; rewrite Qdiv_Qone_Qone; 
  repeat rewrite Qmult_one_right; trivial.
Qed.

Lemma m_product_left_right_product_associative: forall M T N P,
        m_product M (right_product (left_product T N) P)=right_product (left_product (m_product M T) N) P.
Proof.
  intros ((A,B),(C,D)) (((a,b),(c,d)),((e,f),(g,h)))  ((E,F),(G,H)) ((I,J),(K,L)).
  unfold m_product, left_product, right_product, fst, snd. 
  apply (f_equal2 (@pair Matrix Matrix));
  apply (f_equal2 (@pair Vector Vector));
  apply (f_equal2 (@pair Q Q)); ring.
Qed.


Lemma product_left_right_product_associative: forall T M1 M2 N1 N2,
     right_product (left_product (right_product (left_product T M1) N1) M2) N2=
     right_product (left_product T (product M1 M2)) (product N1 N2).
Proof.
  intros (((a,b),(c,d)),((e,f),(g,h)))  ((A1,B1),(C1,D1)) ((A2,B2),(C2,D2)) ((E1,F1),(G1,H1)) ((E2,F2),(G2,H2));
  unfold product, left_product, right_product, fst, snd. 
  apply (f_equal2 (@pair Matrix Matrix));
  apply (f_equal2 (@pair Vector Vector));
  apply (f_equal2 (@pair Q Q)); ring.
Qed.

Lemma m_product_inv_L: forall xi, xi = m_product LL (m_product inv_LL xi).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))); unfold map_digits, inv_digit, inv_LL, m_product, fst, snd;
 apply (f_equal2 (@pair Matrix Matrix));
 apply (f_equal2 (@pair Vector Vector));
 apply (f_equal2 (@pair Q Q)); qZ_numerals; field; auto.
Qed.

Lemma m_product_inv_R: forall xi, xi = m_product RR (m_product inv_RR xi).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))); unfold map_digits, inv_digit, inv_RR, m_product, fst, snd;
 apply (f_equal2 (@pair Matrix Matrix));
 apply (f_equal2 (@pair Vector Vector));
 apply (f_equal2 (@pair Q Q));
 qZ_numerals; field ;auto.
Qed.

Lemma m_product_inv_M: forall xi, xi = m_product MM (m_product inv_MM xi).
Proof.
 intros (((a,b),(c,d)),((e,f),(g,h))); unfold map_digits, inv_digit, inv_MM, m_product, fst, snd;
 apply (f_equal2 (@pair Matrix Matrix));
 apply (f_equal2 (@pair Vector Vector));
 apply (f_equal2 (@pair Q Q));
 qZ_numerals; field ;auto.
Qed.

Definition as_Moebius_Q (M:Matrix) := 
  let (a,b) := (fst (fst M), snd (fst M)) in 
    let (c,d) := (fst (snd M), snd (snd M)) in
      fun (x:Q) => ((a*x+b)/(c*x+d)).

Definition as_Tensor_Q (T:Tensor) := 
  let (a,b) := (fst (fst (fst T)), snd (fst (fst T))) in
   let (c,d) := (fst (snd (fst T)), snd (snd (fst T))) in
    let (e,f) := (fst (fst (snd T)), snd (fst (snd T))) in
     let (g,h) := (fst (snd (snd T)), snd (snd (snd T))) in
      fun (x y:Q)=> (a*x*y+b*x+c*y+d)/(e*x*y+f*x+g*y+h).

Lemma as_Moebius_Q_L: forall x, Zero<x+3->as_Moebius_Q LL x= (x-1)/(x+3).
Proof.
 intros x H_x;
 (* TP:  x * 2 + 3 * 2 <> Zero *)
 assert (H_x':x * 2 + 3 * 2 <> Zero); [stepl (2*(x+3)); auto; ring|];
 unfold as_Moebius_Q, map_digits, fst, snd, Qdiv at 2 4;
 rewrite <- Qmult_assoc; rewrite Qmult_one_left; rewrite Qmult_sym;
 fold (Qdiv x 2); rewrite Qplus_Qdiv; auto; rewrite Qplus_Qdiv; auto;
 rewrite Qdiv_Qdiv_simplify; auto; qZ_numerals; field; auto. 
Qed.

Lemma as_Moebius_Q_R: forall x, Zero<(-x)+3->as_Moebius_Q RR x= (x+1)/((-x)+3).
Proof.
 intros x H_x;
 (* TP:  (-x) * 2 + 3 * 2 <> Zero *)
 assert (H_x':(-x) * 2 + 3 * 2 <> Zero); [stepl (2*((-x)+3)); auto; ring|];
 unfold as_Moebius_Q, map_digits, fst, snd, Qdiv at 2;
 replace ((-1)%Z/2*x) with (-x/2); [|rewrite Z_to_Q_min_one; field; auto];
 rewrite <- Qmult_assoc; rewrite Qmult_one_left; rewrite Qmult_sym;
 fold (Qdiv x 2); rewrite Qplus_Qdiv; auto; rewrite Qplus_Qdiv; auto;
 rewrite Qdiv_Qdiv_simplify; auto; field; auto.
Qed.

Lemma as_Moebius_Q_M: forall x, as_Moebius_Q MM x= (x/3).
Proof.
 intros x; unfold as_Moebius_Q, map_digits, fst, snd; qZ_numerals; field; auto.
Qed.

Lemma as_Moebius_Q_L_nondecreasing:forall x y, (Qopp Qone) <= x -> y<= Qone -> x<=y ->
                                                as_Moebius_Q LL x <= as_Moebius_Q LL y.
Proof.
 intros x y Hx Hy Hxy.
 unfold as_Moebius_Q, map_digits, fst, snd.
 (* TP: Zero <= x+ 1 *)
 assert (H_x_one_nonneg: Zero <= x+1).
 stepr (x-(Qopp 1)); try ring; apply Qle_Qminus_Zero; auto. 
 (* TP: Zero < x+3 *)
 assert (H_x_three_pos: Zero < x+3).
 apply Qle_lt_trans with (x+1); auto;
 apply Qlt_Zero_Qminus; stepr 2; auto; qZ_numerals; ring.
 (* TP: Zero < 1 * x * 2 + 3 * 2 *)
 assert (H:Zero < 1 * x * 2 + 3 * 2).
  stepr (2*(x+3)); [|qZ_numerals; ring].
  apply Qlt_mult_pos_pos; auto.
 (* TP: Zero <= y+ 1 *)
 assert (H_y_one_nonneg: Zero <= y+1).
 stepr (y-(Qopp 1)); try ring; apply Qle_Qminus_Zero; auto; apply Qle_trans with x; auto.
 (* TP: Zero < y+3 *)
 assert (H_y_three_pos: Zero < y+3).
 apply Qle_lt_trans with (y+1); auto;
 apply Qlt_Zero_Qminus; stepr 2; auto; qZ_numerals; ring.
 (* TP: Zero < 1 * y * 2 + 3 * 2 *)
 assert (H':Zero < 1 * y * 2 + 3 * 2).
  stepr (2*(y+3)); [|qZ_numerals; ring].
  apply Qlt_mult_pos_pos; auto.

 repeat rewrite Qdiv_Qmult_numerator_r; auto.
 repeat rewrite Qplus_Qdiv; auto.
 repeat rewrite Qdiv_Qdiv_simplify; auto.
 apply Qmult_Qdiv_pos_Qle; auto.
 apply Qle_Zero_Qminus.
 stepr (16*(y-x)); qZ_numerals; [|qZ_numerals; ring].
 apply Qle_mult_nonneg_nonneg; auto.
 apply Qle_Qminus_Zero; auto.
Qed.


Lemma as_Moebius_Q_R_nondecreasing:forall x y, (Qopp Qone) <= x -> y<= Qone -> x<=y ->
                                                as_Moebius_Q RR x <= as_Moebius_Q RR y.
Proof.
 intros x y Hx Hy Hxy.
 unfold as_Moebius_Q, map_digits, fst, snd.
 (* TP: Zero <= -y+ 1 *)
 assert (H_min_y_one_nonneg: Zero <= -y+1).
 stepr (1-y); try ring; apply Qle_Qminus_Zero; auto. 
 (* TP: Zero < -y+3 *)
 assert (H_min_y_three_pos: Zero < -y+3).
 apply Qle_lt_trans with ((-y)+1); auto.
 apply Qlt_Zero_Qminus; stepr 2; auto; qZ_numerals; ring.
 (* TP: Zero < (-1) * y * 2 + 3 * 2 *)
 assert (H':Zero < (-1)%Z * y * 2 + 3 * 2).
  rewrite Z_to_Q_min_one;
  stepr (2*(-y+3)); [|ring].
  apply Qlt_mult_pos_pos; auto.
 (* TP: Zero <= -x+ 1 *)
 assert (H_min_x_one_nonneg: Zero <= -x+1).
 stepr (1-x); try ring; apply Qle_Qminus_Zero; auto; apply Qle_trans with y; auto.
 (* TP: Zero < -x+3 *)
 assert (H_min_x_three_pos: Zero < -x+3).
 apply Qle_lt_trans with ((-x)+1); auto.
 apply Qlt_Zero_Qminus; stepr 2; auto; qZ_numerals; ring.
 (* TP: Zero < (-1) * x * 2 + 3 * 2 *)
 assert (H:Zero < (-1)%Z * x * 2 + 3 * 2).
  rewrite Z_to_Q_min_one;
  stepr (2*(-x+3)); [|ring].
  apply Qlt_mult_pos_pos; auto.

 repeat rewrite Qdiv_Qmult_numerator_r; auto.
 repeat rewrite Qplus_Qdiv; auto.
 repeat rewrite Qdiv_Qdiv_simplify; auto.
 apply Qmult_Qdiv_pos_Qle; auto.
 apply Qle_Zero_Qminus; 
 stepr (16*(y-x)); 
 qZ_numerals; [|ring].
 apply Qle_mult_nonneg_nonneg; auto.
 apply Qle_Qminus_Zero; auto.
Qed.


Lemma as_Moebius_Q_M_nondecreasing:forall x y, (Qopp Qone) <= x -> y<= Qone -> x<=y ->
                                                as_Moebius_Q MM x <= as_Moebius_Q MM y.
Proof.
 intros x y Hx Hy Hxy.
 unfold as_Moebius_Q, map_digits, fst, snd.

 repeat rewrite Qdiv_Qmult_numerator_r; auto.
 repeat rewrite Qplus_Qdiv; auto.
 repeat rewrite Qdiv_Qdiv_simplify; auto.
 apply Qmult_Qdiv_pos_Qle; auto.
 apply Qle_Zero_Qminus.
 stepr (3*(y-x)); [|qZ_numerals; ring].
 apply Qle_mult_nonneg_nonneg; auto; apply Qle_Qminus_Zero; auto.
Qed.

Definition Determinant M :=   
  let (a,b) := (fst (fst M), snd (fst M)) in
    let (c,d) := (fst (snd M), snd (snd M)) in
	  (a * d - b * c).

Definition diameter mu (H_refining:Is_refining_M mu) : Q := Qabs (as_Moebius_Q mu Qone - as_Moebius_Q mu (-Qone)).

Lemma diameter_PI:forall mu H1 H2, diameter mu H1 = diameter mu H2.
Proof.
 intros mu H1 H2; unfold diameter; reflexivity.
Qed.

Definition min_one_is_in_base_interval_Q := conj (Qle_reflexive (-Qone)) (Qlt_le_weak (-Qone) Qone Qopp_Qone_Qlt_Qone).
Definition one_is_in_base_interval_Q :=conj (Qlt_le_weak (- Qone) Qone Qopp_Qone_Qlt_Qone) (Qle_reflexive Qone).

Definition redundancy := 1/3.

Lemma redundancy_pos:Zero < redundancy.
Proof.
 auto.
Qed.

(* I_1=[x_1,x_2], I_2=[y_1,y_2] *)
Definition diameter2 xi (H_xi: Is_refining_T xi) x1 y1 x2 y2 (Hx1:-Qone<=x1/\x1<=Qone) (Hy1:-Qone<=y1/\y1<=Qone)
   (Hx2:-Qone<=x2/\x2<=Qone) (Hy2:-Qone<=y2/\y2<=Qone) :=
 let xi_ll:= as_Tensor_Q xi x1 y1 in
  let xi_lr:= as_Tensor_Q xi x1 y2 in
   let xi_rl:= as_Tensor_Q xi x2 y1 in
    let xi_rr:= as_Tensor_Q xi x2 y2 in
     (Qmax4 xi_ll xi_lr xi_rl xi_rr) - (Qmin4 xi_ll xi_lr xi_rl xi_rr).

(** The following map can be used in estimating the maximum of the
diameter. *)
Definition eta_discriminant (M:Matrix) :=
  let (c,d) := (fst (snd M), snd (snd M)) in
	  ((0/1,1/1),(c,d)).

Definition denom_nonvanishing_M (mu:Matrix) r:= 
  let (a,b) := (fst (fst mu), snd (fst mu)) in
    let (c,d) := (fst (snd mu), snd (snd mu)) in
      (c*r+d<>0)%R.

Definition denom_nonvanishing_T (xi:Tensor) r1 r2:= 
  let (a,b) := (fst (fst (fst xi)), snd (fst (fst xi))) in
   let (c,d) := (fst (snd (fst xi)), snd (snd (fst xi))) in
    let (e,f) := (fst (fst (snd xi)), snd (fst (snd xi))) in
     let (g,h) := (fst (snd (snd xi)), snd (snd (snd xi))) in
      (e*r1*r2+f*r1+g*r2+h<>0)%R.

Definition as_Moebius (M:Matrix) := 
  let (a,b) := (fst (fst M), snd (fst M)) in 
    let (c,d) := (fst (snd M), snd (snd M)) in
      fun (x:R) => ((a*x+b)/(c*x+d))%R.

Definition as_Tensor (T:Tensor) := 
  let (a,b) := (fst (fst (fst T)), snd (fst (fst T))) in
   let (c,d) := (fst (snd (fst T)), snd (snd (fst T))) in
    let (e,f) := (fst (fst (snd T)), snd (fst (snd T))) in
     let (g,h) := (fst (snd (snd T)), snd (snd (snd T))) in
      fun x y=> ((a*x*y+b*x+c*y+d)/(e*x*y+f*x+g*y+h))%R.

Definition Tensor_Moebius_Q_l (xi:Tensor) x := 
  let (a,b) := (fst (fst (fst xi)), snd (fst (fst xi))) in
   let (c,d) := (fst (snd (fst xi)), snd (snd (fst xi))) in
    let (e,f) := (fst (fst (snd xi)), snd (fst (snd xi))) in
     let (g,h) := (fst (snd (snd xi)), snd (snd (snd xi))) in
        ((a*x+c,b*x+d),(e*x+g,f*x+h)).

Definition Tensor_Moebius_Q_r (xi:Tensor) y := 
  let (a,b) := (fst (fst (fst xi)), snd (fst (fst xi))) in
   let (c,d) := (fst (snd (fst xi)), snd (snd (fst xi))) in
    let (e,f) := (fst (fst (snd xi)), snd (fst (snd xi))) in
     let (g,h) := (fst (snd (snd xi)), snd (snd (snd xi))) in
        ((a*y+b,c*y+d),(e*y+f,g*y+h)).

Definition as_Tensor_Moebius_Q_l xi x:= as_Moebius_Q (Tensor_Moebius_Q_l xi x).

Definition as_Tensor_Moebius_Q_r xi x:= as_Moebius_Q (Tensor_Moebius_Q_r xi x).


Lemma Q_to_R_as_Moebius:forall mu q, denom_nonvanishing_M mu (Q_to_R.Q_to_R q)->
  Q_to_R.Q_to_R (as_Moebius_Q mu q) = as_Moebius mu (Q_to_R.Q_to_R q).
Proof.
 intros ((a,b),(c,d)) q;
 unfold denom_nonvanishing_M, as_Moebius_Q, as_Moebius, fst, snd;
 intro Hcd; Q_to_R.realify_Q; trivial;
 apply Q_to_R.Q_to_R_Qneq; Q_to_R.realify_Q; trivial.
Qed.

Close Scope Z_scope.