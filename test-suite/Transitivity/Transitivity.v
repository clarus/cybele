Require Import Setoid Morphisms Basics Equalities OrdersFacts.
Require Import OrdersEx.
Require Import String.

Require Import Program.
Require Import List.
Require Import Cybele.
Import Monad.
Require Import FMapAVL Int.
Require Import Int.

Open Scope type.

Set Extraction AccessOpaque.

(* FIXME: To be commented. *)

Module Transitivity (Import O: OrderedTypeFull').

Notation "x =?= y" := (O.eq_dec x y) (at level 100).

Module OF := OrderedTypeFacts (O).
Import OF.
Include OrderedTypeTest (O).

Open Scope order.

Definition T : Type := O.t.

Record formula : Type := mkFormula {
  hypothesis : list (T * T);
  goal : T * T
}.

Definition interpret_pair (e : T * T) : Prop := 
  (fst e) <= (snd e).

Fixpoint interpret_hypothesis_list h : Prop := 
  match h with
    | nil => True
    | e :: nil => interpret_pair e
    | e :: es => interpret_pair e /\ interpret_hypothesis_list es
  end.

Notation "▹ e" := ((fun x => x) (_ e)) (at level 200). 

Lemma weak_list : forall A (P Q : A -> Prop), 
                    list { x : A & P x } ->
                    (forall x, P x -> Q x) ->
                    list { x : A & Q x }.
Proof.
 intros. induction X. exact nil.
 constructor 2. destruct a. exists x. apply H. auto. exact IHX.
Defined.

Program Fixpoint successors (x : T) (hs : list (T * T)) { struct hs }
: list { y : T & interpret_hypothesis_list hs -> x <= y } :=
  match hs with
    | nil => nil
    | (x', y) :: hs' =>
        if eq_dec x x' then 
          (▹ y) :: ▹ (successors x hs')
        else 
          ▹ (successors x hs')
  end.
Next Obligation. 
Proof.
  unfold interpret_pair. destruct hs'; simpl; exists x0; intuition; order.
Defined.
Next Obligation.
Proof. 
  unfold interpret_pair.  simpl. eapply (weak_list _ _ _ x0). intros. 
  destruct hs'. simpl in * |- *. auto. intuition.
Defined.
Next Obligation.
Proof. 
  unfold interpret_pair.  simpl. eapply (weak_list _ _ _ x0). intros. 
  destruct hs'. simpl in * |- *. auto. intuition.
Defined.

Definition interpret f : Prop := 
  interpret_hypothesis_list (hypothesis f) -> interpret_pair (goal f).

Definition interpret_hypotheses f : Prop := 
  interpret_hypothesis_list (hypothesis f).

Module OOF <: OrderedType.OrderedType.
  Definition t := O.t.
  Definition eq := O.eq.
  Definition eq_refl := OF.eq_refl.
  Definition eq_sym := OF.eq_sym.
  Definition eq_trans := OF.eq_trans.
  Definition lt_trans := OF.lt_trans.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y. OF.order. Qed.
  Ltac compare_spec_auto x y Heq := 
    generalize (compare_spec x y); 
    rewrite <- Heq; intro Hspec; inversion Hspec; auto.

  Program Definition compare (x y :T) : OrderedType.Compare lt eq x y :=
    match O.compare x y with
    | Eq => OrderedType.EQ _
    | Lt => OrderedType.LT _
    | Gt => OrderedType.GT _
    end.
  Next Obligation. Proof. compare_spec_auto x y Heq_anonymous. Qed.
  Next Obligation. Proof. compare_spec_auto x y Heq_anonymous. Qed.
  Next Obligation. Proof. compare_spec_auto x y Heq_anonymous. Qed.

  Definition lt := O.lt.
  Definition eq_dec := O.eq_dec.
End OOF.

Print Module Z_as_Int.

Module Type Table.
  Definition key := O.t.
  Inductive tree elt :=
  | Leaf : tree elt 
  | Node : tree elt -> key -> elt -> tree elt -> Z_as_Int.t -> tree elt.

  Parameter mem : forall elt, key -> tree elt -> bool.
  Parameter add : forall elt, key -> elt -> tree elt -> tree elt.
End Table.

Module MarksTable <: Table := Raw Z_as_Int (OOF).
  
Definition Marks := MarksTable.t bool.

Definition Σ := Sig.Make nil [ Marks ].

Fixpoint choice A {T} (cs : list T) (pred : T -> M Σ A) : M Σ A :=
  match cs with
    | nil => error "Not found"
    | c :: cs => 
        try! 
          pred c 
        with  _ => choice A cs pred
    end.

(* FIXME: Why does Program notation for ! has priority over our notation 
       for dereferencing? *)

Program Definition decide : forall f:formula, M Σ (interpret f) :=
  fun f =>
  let a := fst (goal f) in
  let b := snd (goal f) in
  let! marks_ref := tmp_ref Σ 0 (MarksTable.empty bool) in
  let marked (x : T) : M Σ bool := 
    let! marks : Marks := ! marks_ref in 
    ret (MarksTable.mem x marks) 
  in 
  let mark (x : T) : M Σ unit :=
      let! marks : Marks := ! marks_ref in
      marks_ref :=! (MarksTable.add x true marks)
  in  
  letrec! traverse
  [ (fun (x : T) => (interpret_hypotheses f) -> x <= b) ] :=
    (fun x => 
      if x =?= b then ret (▹ eq_refl x)
      else if! marked x then error "Not Found"  
      else do! mark x in
          choice ((interpret_hypotheses f) -> x <= b) (successors x (hypothesis f))
          (fun (s : { y : T & interpret_hypotheses f -> x <= y }) =>
             let! Hyb := traverse (projT1 s) in
             ret (▹ (fun (hs : interpret_hypotheses f) => le_trans (x := x) (y := projT1 s) (z := b)))
          )
    )
  in
    ▹ (traverse a).

End Transitivity.

(* Tests *)

Module Import TNat := Transitivity (Nat_as_OT).
Import TNat.OF.
Import Nat_as_OT.

Ltac reify_pair f :=
  match f with
      |  ?X <= ?Y =>
           constr: (X, Y)
      | _ => fail
  end.

Ltac reify_hypothesis hs :=
  match hs with
      | ?X <= ?Y => constr: ((X, Y) :: nil)
      | ?X <= ?Y /\ ?H => 
          let h := reify_hypothesis H in
          constr: ((X, Y) :: h)
      | _ =>
          constr: nil
  end.

Ltac reify_formula f :=
  match f with
      |  ?H -> ?G => 
           let h := reify_hypothesis H in
           let g := reify_pair G in
           constr: (TNat.mkFormula h g)
      | ?G =>
           reify_pair G
  end.

Ltac decide_goal_formula :=
  match goal with | |- ?G => 
     let f := reify_formula G in let x := constr:(TNat.decide f) in cybele x
  end.

(* FIXME: Benchmark each step of the 'cybele' tactic, because I find it too slow. *)
Example f1 : (0 <= 1 -> 0 <= 1). decide_goal_formula. Defined.
Example f2 : (0 <= 1 /\ 1 <= 2) -> 0 <= 2. decide_goal_formula. Defined.
Example f3 : (0 <= 1 /\ 1 <= 2 /\ 2 <= 3) -> 0 <= 3. decide_goal_formula. Defined.
Example f4 : (0 <= 1 /\ 1 <= 0 /\ 2 <= 3) -> (2 <= 3). decide_goal_formula. Defined.
Example f5 : (2 <= 5 /\ 5 <= 100 /\ 5 <= 50 /\ 50 <= 70) -> (50 <= 70). decide_goal_formula. Defined.


  

