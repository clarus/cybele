Require Import Setoid Morphisms Basics Equalities OrdersFacts.
Require Import OrdersEx.
Require Import String.

Require Import Program.
Require Import List.
Require Import Coqbottom.
Require Import Reifiable.
Import Monad.
Require Import FMapAVL Int.
Require Import Int.

Open Scope type.

Set Extraction AccessOpaque.

(* FIXME: To be commented. *)

Module Type ReifiableOrderedType.
  Include OrderedTypeFull'.
  Parameter reify : Reifiable.t t.
End ReifiableOrderedType.

Module Transitivity (Import O: ReifiableOrderedType).

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

Fixpoint interpret_hypothesis h : Prop := 
  match h with
    | nil => True
    | e :: nil => interpret_pair e
    | e :: es => interpret_pair e /\ interpret_hypothesis es
  end.

Lemma weak_list : forall A (P Q : A -> Prop), 
                    list { x : A & P x } ->
                    (forall x, P x -> Q x) ->
                    list { x : A & Q x }.
Proof.
 intros. induction X. exact nil.
 constructor 2. destruct a. exists x. apply H. auto. exact IHX.
Defined.

Program Fixpoint successors (x : T) (hs : list (T * T)) { struct hs }
: list { y : T & interpret_hypothesis hs -> x <= y } :=
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
  interpret_hypothesis (hypothesis f) -> interpret_pair (goal f).

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

Module MemoTable := FMapAVL.Make (OOF).

Module ReifiableMap := Reifiable.Map (MemoTable).

Module InputMemoTable := Monad.InputMemo (MemoTable).

Definition memo_type := 
  existT _ (MemoTable.t nat) (ReifiableMap.Map O.reify Reifiable.Nat).

Definition Σ := Sig.Make [ memo_type ] [ Marks ]. 

Fixpoint nth sig {A} (cs : list A) (n : nat) : Monad.t sig A :=
  match cs with
      | nil => Error "Not found"
      | x :: xs => match n with O => Return x | S k => nth sig xs k end
  end.

Definition precompute (table : Ref.t Σ (MemoTable.t nat))
                      (f : T -> Monad.t Σ nat) 
: T -> Monad.t Σ nat :=
    fun x => 
      Select 
        (* Coq *)
        (fun _ =>
           let! map := Read table in  
           ExtractSome (MemoTable.find x map))
        (* OCaml *)
        (fun _ => 
           let! y := f x in
           let! map := !table in  
           let! u := Write table (MemoTable.add x y map) in
           Return y).
           
Program Definition choice A 
  (table : Ref.t Σ (MemoTable.t nat))
  (input : T)
  (choices : list (unit -> Monad.t Σ A)) 
: Monad.t Σ A :=
  let choice_idx := 
    fix choice_idx k cs { struct cs } : Monad.t Σ nat := 
    match cs with
      | nil => Error "Not found"
      | c :: cs => 
          try! 
             let! y := c tt in 
             Return k
          with _ => choice_idx (S k) cs 
    end
  in
(*  let precompute_choice_idx := precompute table (fun _ => choice_idx O choices) in
  let! k := precompute_choice_idx input in *)
  let! k := choice_idx O choices in
  let! y := nth Σ choices k in
    y tt.

(* FIXME: Why does Program notation for ! has priority over our notation 
       for dereferencing? *)

Program Definition decide : forall f:formula, Monad.t Σ (interpret f) :=
  fun f =>
  let a := fst (goal f) in
  let b := snd (goal f) in
  let! marks_ref := TmpRef Σ 0 (MarksTable.empty bool) in
  let marked (x : T) : Monad.t Σ bool := 
    let! marks : Marks := Read marks_ref in 
    Return (MarksTable.mem x marks) 
  in 
  let mark (x : T) : Monad.t Σ unit :=
      let! marks : Marks := Read marks_ref in
      marks_ref :=! (MarksTable.add x true marks)
  in  
  let table := InputRef Σ 0 (MemoTable.empty nat) in
  letrec! traverse
  [ (fun (x : T) => (interpret_hypothesis (hypothesis f)) -> x <= b) ] :=
    (fun x => 
      if O.eq_dec x b then
        Return (▹ eq_refl x)
      else if! marked x then
        Error "Not Found"  
      else 
        do! mark x in
        let s := successors x (hypothesis f) in
        let choices := 
            List.map 
              (fun (s: { y : T & interpret_hypothesis (hypothesis f) -> x <= y }) (_ : unit) => 
                 let! Hyb := traverse (projT1 s) in
                   Return (▹ (fun (hs : interpret_hypothesis (hypothesis f)) => 
                                le_trans (x := x) (y := projT1 s) (z := b)))) s
        in
          choice ((interpret_hypothesis (hypothesis f)) -> x <= b) table x choices
    )
  in
    ▹ (traverse a).

End Transitivity.

(* Tests *)

Module NatObject.
  Include Nat_as_OT.
  Definition reify := Reifiable.Nat.
End NatObject.

Module Import TNat := Transitivity (NatObject).
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
     let f := reify_formula G in coq (TNat.decide f) 
  end.

(* FIXME: Benchmark each step of the 'coq' tactic, because I find it too slow. *)
Example f1 : (0 <= 1 -> 0 <= 1). decide_goal_formula. Defined.
Example f2 : (0 <= 1 /\ 1 <= 2) -> 0 <= 2. decide_goal_formula. Defined.
Example f3 : (0 <= 1 /\ 1 <= 2 /\ 2 <= 3) -> 0 <= 3. decide_goal_formula. Defined.
Example f4 : (0 <= 1 /\ 1 <= 0 /\ 2 <= 3) -> (2 <= 3). decide_goal_formula. Defined.
Example f5 : (2 <= 5 /\ 5 <= 100 /\ 5 <= 50 /\ 50 <= 70) -> (50 <= 70). decide_goal_formula. Defined.


  

