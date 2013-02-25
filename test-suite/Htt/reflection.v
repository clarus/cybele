(*
    Copyright (C) 2012  G. Gonthier, B. Ziliani, A. Nanevski, D. Dreyer

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*)

Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import prelude prefix xfind heaps terms.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

  
(******************************************************************************)
(* cancelR :                                                                  *)
(*   Lemma automated with Canonical Structures to cancel heap expressions.    *)
(*   Usage:                                                                   *)
(*     apply (cancelR D) in H                                                 *)
(*   where D : def h1 and H : h1 = h2                                         *)
(******************************************************************************)

(* Syntactification of heaps *)
Section HeapReflection.

(* The algorithm works as follow:
   - if the heap is h1 :+ h2 then recurse over both and concatenate the results
   - if the heap is the empty heap, return []
   - if the heap is p :-> v then add p to the context, and return [Pts x v], 
     where x is the deBruijn index for p in the context
   - if the heap is whatever else, add the heap to the context and return
     [Var n], where n is the deBruijn index for the heap in the context
 *)

(* a tagging structure to control the flow of computation *)
Structure tagged_heap := Tag {untag :> heap}.

(* in reversed order; first test for unions, then empty, pts and vars *)
Definition var_tag := Tag.
Definition pts_tag := var_tag.
Definition empty_tag := pts_tag.
Canonical Structure union_tag hc := empty_tag hc. 

Definition invariant i j t h := [/\ interp j t = h, subctx i j & valid j t].

(* Main structure
   i : input context
   j : output context
   t : syntactification of heap_of using context j *) 
Structure ast (i j : ctx) (t : synheap) := 
  Ast {heap_of :> tagged_heap; 
       _ : invariant i j t heap_of}.

Implicit Arguments Ast [].

Lemma union_pf i j k t1 t2 (f1 : ast i j t1) (f2 : ast j k t2) :
        invariant i k (t1 ++ t2) (union_tag (f1 :+ f2)).
Proof.
case: f1 f2=>h1 /= [<- S1 D1] [h2 /= [<- S2 D2]].
split; first by rewrite interp_cat (interp_subctx D1 S2).
- by apply: (subctx_trans S1 S2).
by rewrite valid_cat D2 andbT; apply: (valid_subctx S2).
Qed.

(* pass output context of f1 as input of f2 *)
Canonical Structure 
  union_struct i j k t1 t2 (f1 : ast i j t1) (f2 : ast j k t2) := 
  Ast i k _ (union_tag (f1 :+ f2)) (union_pf f1 f2).

Lemma empty_pf i : invariant i i [::] (empty_tag empty).
Proof. split; by [|apply: subctx_refl|]. Qed.

Canonical Structure empty_struct i := 
  Ast i i [::] (empty_tag empty) (empty_pf i).
 
Lemma pts_pf A hs xs1 xs2 x (d : A) (xs : xfind xs1 xs2 x):
        invariant (Context hs xs1) (Context hs xs2) 
                  [:: Pts x (dyn d)] (pts_tag (xuntag xs :-> d)).
Proof.
case: xs=>[p /= [H P]]; split; first by rewrite /= H.
- by split; [apply: prefix_refl|].
by apply/andP; rewrite /= (onth_size H). 
Qed.

Canonical Structure 
  pts_struct A hs xs1 xs2 x (d : A)
           (xs : xfind xs1 xs2 x) :=
  Ast (Context hs xs1) (Context hs xs2) 
       [:: Pts x (dyn d)]
       (pts_tag (xuntag xs :-> d))
       (pts_pf hs _ xs).


Lemma var_pf hs1 hs2 xs n (f : xfind hs1 hs2 n) : 
        invariant (Context hs1 xs) (Context hs2 xs) [:: Var n] (var_tag (xuntag f)).
Proof.
case:f=>p [H1 H2]; split; first by rewrite /= /hlook H1.
- by split; [|apply: prefix_refl].
by apply/andP; rewrite /= (onth_size H1).
Qed.

Canonical Structure var_struct hs1 hs2 xs n (f : xfind hs1 hs2 n) := 
  Ast (Context hs1 xs) (Context hs2 xs) _ 
      (var_tag (xuntag f)) 
      (var_pf xs f). 

End HeapReflection.
