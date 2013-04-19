Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import prelude prefix xfind heaps terms reflection.
Require Import Program.
Require Import Cybele.
Import Monad.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Obligation Tactic := idtac.


(** * Heap congruencer *)

(** This file contains the congruence algorithm for heaps. A heap is
a map from pointers to values. They can be constructed with three functions:
- [empty] : the constant function for creating an empty map.
- [x :-> v] : the singleton heap containing only pointer [x] pointing to value [v].
- [h1 :+ h2] : the disjoint union operator for merging heaps [h1] or [h2].

The algorithm works with a syntactical representation of heaps. [x :-> v] is 
reflected into syntax as [Pts i v], where [i] is an index in a context 
containing a list of pointers. A heap variable [h] is reflected as [Var j], 
where [j] is an index into a list of heaps in the context. Then, instead of
having a disjoint union, a heap is reflected as a list of Pts's or Var's.
For instance, the heap 

  [x :-> v :+ h :+ empty]

is reflected as

  [[Pts 0 v ; Var 0 ; nil]]

under context [ ([x], [h]) ]. For interpreting a (syntactic) heap [h] in a 
context [g] we use the function [interp g h].

The files not described here are part of the Hoare Type Theory development, and
they are described in [1] and [2].

** Requirements

- CoqEpsilon
- ReleasedSsreflect


** Compilation

$ coq_makefile *.v > Makefile
$ make


[[1]] Georges Gonthier, Beta Ziliani, Aleksandar Nanevski, Derek Dreyer: How to
    make ad hoc proof automation less ad hoc. ICFP 2011: 163-175.
[[2]] Aleksandar Nanevski, Viktor Vafeiadis, Josh Berdine: Structuring the 
    verification of heap-manipulating programs. POPL 2010: 261-274

*)

(** A transparent existential. *)
Structure Sigma A (P : A -> Prop) := sigma_intro { 
  elem : A; 
  prop : P elem 
}. 
Implicit Arguments sigma_intro [A P].

(** A bind from [option] to [M sig A]. *)
Notation "x '<-' f ';' t" := 
  (match f with
   | None => error ""
   | Some x => t
   end) 
(at level 60, right associativity).

(** The input of the fixpoint is packed into one record *)
Record pack := Pack {
  heap1 : synheap;
  heap2 : synheap;
  rest  : synheap
}.

(** Additional lemma for points-to congruence. *)
Lemma cong_ptrs (i : ctx) (t r : synheap) (x x' : nat) (d d' : dynamic) (p1 p2 : ptr)
  (Heq_r : [:: Pts x d] = r)
  (Heq_t : [:: Pts x' d'] = t)
  (filtered_var := onth (ptr_ctx i) x)
  (Heq_anonymous : Some p1 = filtered_var)
  (filtered_var0 := onth (ptr_ctx i) x')
  (Heq_anonymous0 : Some p2 = filtered_var0)
  (H : [/\ p1 = p2 /\ d = d', def (interp i ([:: Pts x d]))
        & def (interp i [Pts x' d']%list)]) :
   interp i ([::Pts x d]) = interp i [:: Pts x' d'].
Proof.
  rewrite /filtered_var in Heq_anonymous.
  rewrite /filtered_var0 in Heq_anonymous0.
  simpl. rewrite -Heq_anonymous0 -Heq_anonymous.
  by move: H=>[[-> ->] _].
Qed.

(**
** Algorithm

The congruence algorithm solves goals of the form [h1 = h2] (for two heaps [h1]
and [h2]), by cancelling common subheaps form both heaps, and equating values
pointed by the same pointer. For instance, the goal

  [x :-> v1 :+ h  =  x :-> v2]

is changed by the congruencer with the goal

  [v1 = v2 /\ h = empty]

If we have the following hypotheses:

  [H1 : v1 = v2]
  [H2 : h = empty]

then the new goal is easy to prove.

The algorithm proceeds by decomposing the heap on the left. For the description,
we are using [x :-> v] and [h] to mean [Pts i v] and [Var j], respectively, for 
some [i] and [j]. 

If the subheap
on the left-outer position of the heap is a singleton pointer [x :-> v1],
it searches for an element [x :-> v2] in the heap on the right. If it finds
the element, it adds the goal [v1 = v2] to the goal produced by equating the
remaining parts of both heaps.

If instead the heap on the left is a variable (like [h] in the equation above)
then it proceeds in the same way, but without creating any new goal (i.e.,
the subheap is cancelled from both sides of the equation). 

If the subheap is not found, then it is added to the accumulator [rest].

The type of the congruencer can be understood as 

[forall (i : ctx) (t1 t2 r : heap), M (exists (p:Prop), 
  p /\ def (t1 :+ r) /\ t2 -> t1 :+ r = t2)]

but where instead of [heap]s we use their syntactic representation [synheap], and
instead of using the opaque existential [exists], we use a transparent one [Sigma].
*)
Program
Definition congruence (i : ctx) (t1 t2 r : synheap) : 
  M Sig.empty (Sigma (fun p:Prop=>
    [/\ p , def (interp i (t1 ++ r)) & def (interp i t2)] -> 
    interp i (t1 ++ r) = interp i t2)) := 
  letrec! f [fun c : pack=>
    let: Pack t1 t2 r := c in
    Sigma (fun p:Prop=>
      [/\ p , def (interp i (t1 ++ r)) & def (interp i t2)] -> 
      interp i (t1 ++ r) = interp i (t2))] :=
  fun c : pack =>
  let: Pack t1 t2 r := c in
  match t1 with 
  | [::] =>
      match r, t2 with
      | [::], [::] => ret (sigma_intro True (fun _=>erefl _))
      | [:: Pts x d], [:: Pts x' d'] => 
        p1 <- onth (ptr_ctx i) x;
        p2 <- onth (ptr_ctx i) x';
        ret (sigma_intro (p1 = p2 /\ d = d') _)
      | _ , _ => ret (sigma_intro (interp i r = interp i t2) _)
      end
  | Pts x d :: t1' => 
      match x \in ptrs t2 with
      | true =>  
        let! res := f (Pack t1' (pfree x t2) r) in
        ret (sigma_intro (d = (pread' x t2) /\ elem res) _)
      | false =>
        let! res := f (Pack t1' t2 [:: Pts x d & r]) in 
        ret (sigma_intro (elem res) _)
      end
  | Var h :: t1' => 
      match h \in vars t2 with
      | true =>
        let! res := f (Pack t1' (hfree h t2) r) in
        ret (sigma_intro (elem res) _)
      | false => 
        let! res := f (Pack t1' t2 [:: Var h & r]) in
        ret (sigma_intro (elem res) _)
      end
  end
  in f (Pack t1 t2 r).
Next Obligation.
Proof.
  move => i _ _ _ _ _ t1 t2 r _ _.
  move=>x d x' d' Heq_r Heq_t fv1 p1 Heq_anon1 fv2 p2 Heq_anon2 H.
  by apply: (cong_ptrs Heq_r Heq_t  Heq_anon1 Heq_anon2 H).
Qed.
Next Obligation.
Proof.
  move=> i _ _ _ _ _ t1 t2 r _ _.
  move=> w1 w2 _ Heq_r Heq_t H.
  by move:H; rewrite Heq_r Heq_t=>[[->]].
Qed.
Next Obligation. Proof. by try split ; program_simpl. Qed.
Next Obligation. Proof. by try split ; program_simpl. Qed.
Next Obligation. Proof. by try split ; program_simpl. Qed.
Next Obligation. Proof. by try split ; program_simpl. Qed.
Next Obligation. Proof. by try split ; program_simpl. Qed.
Next Obligation. Proof. by try split ; program_simpl. Qed.
Next Obligation. 
Proof.
  rewrite (lock interp).
  move=>/= i _ _ _ _ _ _ t2 r _ x d t1 _ Heq_anon res e.
  move: e=>[[H1 H2] D1 D2].
  case: res H2=>p H2.
  rewrite [elem _]/= =>proof_of_p.
  symmetry in Heq_anon.
  rewrite -lock in D1 D2 H2 *.
  apply: (cong_pts Heq_anon _ H1 D1 D2).
  apply: H2.
  split; first by [].
    by rewrite interp_cons in D1; apply: (defUnr D1).
  by apply: pfree_def.
Qed.
Next Obligation.
Proof.
  rewrite (lock interp).
  move=>/= i _ _ _ _ _ _ t2 r _ x d t1 _ Heq_anon res e.
  move: e=>[H2 D1 D2].
  case: res H2=>p H2.
  rewrite [elem _]/= =>proof_of_p.
  rewrite -lock in D1 D2 H2 *.
  rewrite interp_unCA in D1 *.
  by apply: H2.
Qed.
Next Obligation.
Proof.
  rewrite (lock interp).
  move=>/= i _ _ _ _ _ _ t2 r _ h t1 _ Heq_anon res [H2 D1 D2].
  case: res H2=>p H2.
  rewrite [elem _]/= =>proof_of_p.
  rewrite -lock in D1 D2 H2 *.
  symmetry in Heq_anon.
  rewrite (free_heap D2 Heq_anon).
  rewrite interp_cons in D1 *.
  rewrite unC [_ :+ interp _ (hfree _ _)]unC.
  apply congeqUh.
  apply: H2.
  split; first by [].
    by apply (defUnr D1).
  by apply: hfree_def.
Qed.
Next Obligation.
Proof.
  rewrite (lock interp).
  move=>/= i _ _ _ _ _ _ t2 r _ h t1 _ Heq_anon res [H2 D1 D2].
  case: res H2=>p H2.
  rewrite [elem _]/= =>proof_of_p.
  rewrite -lock in D1 D2 H2 *.
  rewrite interp_unCA in D1 *.
  by apply: H2.
Qed.

Notation congruencer c hl hr i := 
  (prop (proof_by_reflection (congruence c hl hr [::]) (Prophecy.of_nat _ i) (erefl _))).


(** ** Examples reflecting the heaps manually into syntax. *)
Example ex1 x y : 
  def (x :-> 1 :+ y :-> 2) -> 
  def (y :-> 2 :+ x :-> 1) ->
  x :-> 1 :+ y :-> 2 = y :-> 2 :+ x :-> 1.
Proof.
  move=>D1 D2.
  set c := Context [::] [:: x ; y].
  set hl := [:: Pts 0 (dyn 1); Pts 1 (dyn 2)].
  set hr := [:: Pts 1 (dyn 2); Pts 0 (dyn 1)].
  apply: (congruencer c hl hr 3).
  simpl; by [].
Qed.


Example ex2 x y h : 
  def (x :-> 1 :+ y :-> 2) -> 
  def (y :-> 2 :+ x :-> 1 :+ h) ->
  h = empty ->
  x :-> 1 :+ y :-> 2 = y :-> 2 :+ x :-> 1 :+ h.
Proof.
  move=>D1 D2 h0.
  set c := Context [:: h] [:: x ; y].
  set hl := [:: Pts 0 (dyn 1); Pts 1 (dyn 2)].
  set hr := [:: Pts 1 (dyn 2); Pts 0 (dyn 1); Var 0].
  rewrite -!unA in D1 D2 *.
  apply: (congruencer c hl hr 4); simpl. do ![split; try by []].
Qed.


Example ex3 x y h : 
  def (h :+ x :-> 1 :+ y :-> 2) -> 
  def (y :-> 2 :+ x :-> 1 :+ h) ->
  h :+ x :-> 1 :+ y :-> 2 = y :-> 2 :+ x :-> 1 :+ h.
Proof.
  move=>D1 D2.
  set c := Context [:: h] [:: x ; y].
  set hl := [:: Var 0; Pts 0 (dyn 1); Pts 1 (dyn 2)].
  set hr := [:: Pts 1 (dyn 2); Pts 0 (dyn 1); Var 0].
  rewrite -!unA in D1 D2 *.
  apply: (congruencer c hl hr 4); simpl. 
  do ![split; try by []].
Qed.

(** This lemma reflects a heap equality into syntax. *)
Lemma reflect j k t1 t2 (f1 : ast empc j t1) (f2 : ast j k t2) :
        interp k t1 = interp k t2 ->
        untag (heap_of f1) = untag (heap_of f2).
Proof.
  case: f1 f2=>hp1 /= [<- _ I] [hp2 /= [<- S _]].
  by rewrite -(interp_subctx I S).
Qed.

(** Congruence algorithm reflecting heaps into syntax. *)
Definition r_congruence j k t1 t2 (f1 : ast empc j t1) (f2 : ast j k t2) 
  (D1 : def f1) (D2 : def f2) :=
  congruence k t1 t2 [::].

(** Example using full reflection. *)
Example ex3' x y h : 
  def (h :+ x :-> 1 :+ y :-> 2) -> 
  def (y :-> 2 :+ x :-> 1 :+ h) ->
  h :+ x :-> 1 :+ y :-> 2 = y :-> 2 :+ x :-> 1 :+ h.
rewrite -!unA.
move=>D1 D2.
apply: (prop (proof_by_reflection (r_congruence D1 D2) 
  (Prophecy.of_nat _ 20) (erefl _))).
simpl.
do ![split; by []].
Qed.
