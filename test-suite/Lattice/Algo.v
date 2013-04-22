Require Import Arith.
Require Import OrderedType.
Require Import OrderedTypeEx.
Require Import Lattice.
Require Import Cybele.
Require Import Cybele.Map.
Require Import Cybele.Reifiable.

Import Lattice Monad.

Set Implicit Arguments.

(** * Module [Term]
  A [Term.t] represents a reified formula. *)
Module Term.
  (** A variable is an index to a value in an environment. *)
  Inductive t: Type :=
  | Var  : nat -> t
  | Meet : t -> t -> t
  | Join : t -> t -> t.
  
  (** We define a complete order on [t], so they can be used as keys
      for map tables. *)
  Module MiniOrdered <: MiniOrderedType.
    Definition t := t.
    
    Definition eq := eq (A := t).
    
    Definition eq_refl := eq_refl (A := t).
    Definition eq_sym := eq_sym (A := t).
    Definition eq_trans := eq_trans (A := t).
    
    Fixpoint lt (t1 t2: t): Prop :=
      match (t1, t2) with
      | (Var i1, Var i2) => i1 < i2
      | (Var _, _) => True
      | (_, Var _) => False
      | (Meet t11 t12, Meet t21 t22) => lt t11 t21 \/ (t11 = t21 /\ lt t12 t22)
      | (Meet _ _, _) => True
      | (_, Meet _ _) => False
      | (Join t11 t12, Join t21 t22) => lt t11 t21 \/ (t11 = t21 /\ lt t12 t22)
      end.
    
    Lemma lt_trans: forall (t1 t2 t3: t),
      lt t1 t2 -> lt t2 t3 -> lt t1 t3.
      intros t1; induction t1; intros t2 t3 Ht1t2 Ht2t3;
      destruct t2; destruct t3;
        simpl; simpl in Ht1t2, Ht2t3;
        trivial; try omega; (
        (destruct Ht1t2 as [Ht1t2 | Ht1t2];
          try destruct Ht1t2 as [Ht1t2eq Ht1t2lt];
        destruct Ht2t3 as [Ht2t3 | Ht2t3];
          try destruct Ht2t3 as [Ht2t3eq Ht2t3lt]);
        [left | left | left | right]; [
          now apply IHt1_1 with (t2 := t2_1) |
          
          now rewrite <- Ht2t3eq |
          
          now rewrite Ht1t2eq |
          
          split; [congruence |];
          now apply IHt1_2 with (t2 := t2_2)]).
    Qed.
    
    Definition lt_not_eq: forall (t1 t2: t),
      lt t1 t2 -> t1 <> t2.
      intro t1; induction t1; intros t2 Hlt; destruct t2;
        simpl in Hlt; try congruence;
        try (assert (n <> n0); [omega |]; congruence);
        (intro;
        destruct Hlt as [Hlt | Hlt];
          [apply IHt1_1 with (t2 := t2_1) | apply IHt1_2 with (t2 := t2_2)];
          intuition congruence).
    Qed.
    
    Fixpoint compare (t1 t2: t): Compare lt eq t1 t2.
      destruct t1 as [i1 | t11 t12 | t11 t12];
      destruct t2 as [i2 | t21 t22 | t21 t22];
        try (now apply LT); try (now apply GT);
        try (
          destruct (lt_eq_lt_dec i1 i2) as [Hlteq | Hgt];
            [destruct Hlteq as [Hlt | Heq] |];
            [apply LT | apply EQ | apply GT]; trivial; congruence);
        (destruct (compare t11 t21) as [Hlt1 | Heq1 | Hgt1];
          [apply LT; simpl; tauto |
          
          destruct (compare t12 t22) as [Hlt2 | Heq2 | Hgt2]; [
            apply LT; simpl; tauto |
            
            apply EQ; congruence |
            
            apply GT; simpl; auto] |
          
          apply GT; simpl; auto]).
    Defined.
  End MiniOrdered.
  
  Module Ordered <: OrderedType := MOT_to_OT MiniOrdered.
  
  Import SExpr.
  
  (** A term can be reified from OCaml to Coq. *)
  Definition Reifiable := Reifiable.New
    (fix export t :=
      match t with
      | Var n => B I (Reifiable.Export Reifiable.Nat n)
      | Meet t1 t2 => B (B I I) (B (export t1) (export t2))
      | Join t1 t2 => B (B (B I I) I) (B (export t1) (export t2))
      end)
    (fix import r :=
      match r with
      | B I r' => Var (Reifiable.Import Reifiable.Nat r')
      | B (B I I) (B r1 r2) => Meet (import r1) (import r2)
      | B (B (B I I) I) (B r1 r2) => Join (import r1) (import r2)
      | _ => Var 0
      end).
End Term.

(** * Module [Algo]
 Module with the main algorithm. It is parametrized with a lattice type *)
Module Algo (P: Param).
  Module Lattice := Lattice.Instance P.
  Import P Term
    Lattice.Definitions Lattice.Notations Lattice.Facts.
  Local Open Scope lattice_scope.
  
  (** Evaluation of a [Term.t] in an environment. *)
  Fixpoint Eval (t : Term.t) (env : nat -> A): A :=
    match t with
    | Var n => env n
    | Meet t1 t2 => (Eval t1 env) /*\ (Eval t2 env)
    | Join t1 t2 => (Eval t1 env) \*/ (Eval t2 env)
    end.
  
  (** The predicate the algorithm proves: [leq] for reflected terms. *)
  Definition Leq (p: Term.t * Term.t) :=
    forall env, Eval (fst p) env <= Eval (snd p) env.
  
  (** Lemmas used to generate the final proof in our algorithm.
      They are proofs on lattices lift to the [Leq] predicate. *)
  Module Facts.
    Ltac lift lemma :=
      intros; intro env; simpl; apply lemma; intuition.
    
    Lemma CompareToMeetRight (t u1 u2: Term.t):
      Leq (t, u1) -> Leq (t, u2) -> Leq (t, Meet u1 u2).
      lift CompareToMeetRight.
    Qed.
    
    Lemma CompareToMeetLeft (t1 t2 u: Term.t):
      Leq (t1, u) \/ Leq (t2, u) -> Leq (Meet t1 t2, u).
      lift CompareToMeetLeft.
    Qed.
    
    Lemma CompareToJoinLeft (t1 t2 u: Term.t):
      Leq (t1, u) -> Leq (t2, u) -> Leq (Join t1 t2, u).
      lift CompareToJoinLeft.
    Qed.
    
    Lemma CompareToJoinRight (t u1 u2: Term.t):
      Leq (t, u1) \/ Leq (t, u2) -> Leq (t, Join u1 u2).
      lift CompareToJoinRight.
    Qed.
  End Facts.
  
  Module OrderedTermPair := PairOrderedType Term.Ordered Term.Ordered.
  
  (** Map from pairs of terms to natural numbers.
      Usefull for memoization of branches. *)
  Module TermPairMap := Map OrderedTermPair.
  
  (** A map that can be reifiable from Ocaml to Coq. *)
  Module ReifiableTermPairMap := Reifiable.Map TermPairMap.
  Definition ReifiableMap: Reifiable.t (TermPairMap.t nat) :=
    ReifiableTermPairMap.Map
      (Reifiable.Product Term.Reifiable Term.Reifiable)
      Reifiable.Nat.
  (*
  Module TmpMemo := Monad.TmpMemo TermPairMap.
  *)
  (** The memory is split in two:
     - The part that is written in Ocaml and read in Coq, and
     - The part that is used only in Ocaml.
     The first part is used to remember the path taken by the Ocaml
     algorithm. Coq replays the successful path only. The second
     part is used only when using memoization (see [ProveLeqMemo] below).
     *)
  Definition Sig: Sig.t := Sig.Make
    (existT _ _ ReifiableMap :: nil)
    (TermPairMap.t {p: Term.t * Term.t & Leq p} :: nil).
  
  (** In order to compare the effectiveness of our method, we provide two 
     versions of the choice operator: one that tries blindly all branches
     and another that uses the data memoized in Ocaml. Here is the slow version
     that perform no optimization.*)
  Fixpoint tryBranchesSlow (k : TermPairMap.key) 
    B (branches: list (unit -> M Sig B))
    : M Sig B :=
    match branches with
    | nil => error "No branch left to try"
    | (b :: branches') =>
      try! (b tt)
      with _ =>
        tryBranchesSlow k branches'
    end.

  (** Optimized version of the previous function: it tries everything in OCaml
     until no exception is raised, remembers the index of the branch and uses the
     index in Coq to directly find the successful branch. *)
  Fixpoint tryBranchesFast (ref: Ref.t Sig _) (n_branch: nat) 
    (k : TermPairMap.key) B (branches: list (unit -> M Sig B))
    : M Sig B :=
    select
      (* Coq *)
      (fun _ =>
        let! map := !ref in
        let! n_branch := extract_some (TermPairMap.find k map) in
        let! branch := extract_some (nth_error branches n_branch) in
        branch tt)
      (* OCaml *)
      (fun _ =>
        let! map := !ref in
        match TermPairMap.find k map with
        | Some n => 
          let! branch := extract_some (nth_error branches n) in
          branch tt
        | None =>
          match branches with
          | nil => 
            error "No branch left to try"
          | (branch :: branches') =>
            try!
              let! r := branch tt in
              let! map := !ref in
              do! ref :=! TermPairMap.add k n_branch map in
              ret r
            with _ =>
              tryBranchesFast ref (S n_branch) k branches'
          end
        end).

  Notation "[ x ||| .. ||| y ]" := (cons (fun _=>x) .. (cons (fun _=>y) nil) ..).

  (** The main decision procedure. It takes two terms and returns the proof
      of their inequality. The [fast] flag activates branch memoization. *)
  Program
  Definition ProveLeq (fast: bool)
    : forall (p : Term.t * Term.t), M Sig (Leq p)
    :=
      let ref := input_ref Sig 0 (TermPairMap.empty _) in
      let tryBranches :=
        if fast 
          then tryBranchesFast ref 0
          else tryBranchesSlow
      in
      letrec! leq [fun p: Term.t * Term.t => Leq p] := 
      (fun p =>
        match p as p' return M Sig (Leq p') with
        | (Var m, Var n) =>
          match eq_nat_dec m n with
            | left Heq => ret _
            | right _ => error "not equal"
          end
        | (t, Meet u1 u2) =>
          let! r1 := leq (t, u1) in
          let! r2 := leq (t, u2) in
          ret (Facts.CompareToMeetRight r1 r2)
        | (Join t1 t2, u) =>
          let! r1 := leq (t1, u) in
          let! r2 := leq (t2, u) in
          ret (Facts.CompareToJoinLeft r1 r2)
        | (Var m, Join u1 u2) as p =>
            tryBranches p _ [
              let! r := leq (Var m, u1) in
              ret (Facts.CompareToJoinRight (or_introl r)) 
            |||
              let! r := leq (Var m, u2) in
              ret (Facts.CompareToJoinRight (or_intror r))
            ]
        | (Meet t1 t2, Var n) as p =>
            tryBranches p _ [
              let! r := leq (t1, Var n) in
              ret (Facts.CompareToMeetLeft (or_introl r))
            |||
              let! r := leq (t2, Var n) in
              ret (Facts.CompareToMeetLeft (or_intror r))
            ]
        | (Meet t1 t2, Join u1 u2) as p =>
            tryBranches p _ [
              let! r := leq (t1, Join u1 u2) in
              ret (Facts.CompareToMeetLeft (or_introl r))
            |||
              let! r := leq (t2, Join u1 u2) in
              ret (Facts.CompareToMeetLeft (or_intror r))
            |||
              let! r := leq (Meet t1 t2, u1) in
              ret (Facts.CompareToJoinRight (or_introl r))
            |||
              let! r := leq (Meet t1 t2, u2) in
              ret (Facts.CompareToJoinRight (or_intror r))
            ]
        end)
      in leq.
  Next Obligation.
    intros. unfold Leq. intro. apply LeReflexive.
  Defined.
   
  (*
  (** Memoize the results of [ProveLeq] in a map in the hope of being faster
      (no significant result yet). *)
  Definition ProveLeqMemo (fast: bool) (p: Term.t * Term.t)
    : M Sig (Leq p).
    refine (
      let! memo := TmpRef Sig 0 (TermPairMap.empty _) in
      let leq_aux p :=
        let! proof := ProveLeq fast p in
        Return (existT _ p proof) in
      let! result := TmpMemo.Memoize memo leq_aux p in
      _).
    destruct result as [p' proof].
    destruct (OrderedTermPair.eq_dec p p') as [Heq | Hneq].
      replace p with (fst p, snd p); [ | now destruct p].
      destruct Heq as [Heq1 Heq2]; rewrite Heq1; rewrite Heq2.
      exact (Return proof).
      
      exact (Error "p' expected to be equal to p").
  Defined.
  *)
  (** ** Tactics to reifiy a goal. *)
  (** Checks whether an element is in the environment. *)
  Ltac isMember x env :=
    let rec member' ls :=
      match ls with
      | nil => constr:false
      | ?h :: ?t =>
        match constr:(x = h) with
        | (?X = ?X) => constr:true
        | _ => member' t
        end
      end in
      member' env.
  
  (** Returns the position of [v] in [env], starting from [n]. *)
  Ltac rank env n v :=
    match env with
    | (cons ?X1 ?X2) =>
        let env' := constr:X2 in
          match constr:(X1 = v) with
          | (?X1 = ?X1) => n
          | _ => rank env' (S n) v
          end
    end.
  
  (** Performs the reflection of [v] using environment [env]. *)
  Ltac reflect env v :=
    match v with
    | (?X1 /*\ ?X2) =>
        let r1 := reflect env X1
        with r2 := reflect env X2 in
          constr:(Meet r1 r2)
    | (?X1 \*/ ?X2) =>
        let r1 := reflect env X1
        with r2 := reflect env X2 in
          constr:(Join r1 r2)
    | ?X1 =>
        let n := rank env 0 X1 in
          constr:(Var n)
    | _ => constr:(Var 0)
    end.
  
  (** Creates an environment by scanning the variables in [t] *)
  Ltac variables env t :=
    match t with
    | (?X1 /*\ ?X2) =>
      let env' := variables env X1 in
      variables env' X2
    | (?X1 \*/ ?X2) =>
      let env' := variables env X1 in
      variables env' X2
    | ?X =>
      match isMember X env with
      | true => env
      | false => constr:(cons X env)
      end
    end.
  
  (** Reify a goal and takes a continuation for the next thing to do. *)
  Ltac Reify k :=
    match goal with
    | [ |- (?le ?X1 ?X2) ] =>
      let vars := variables (@nil P.A) X1 in
      let vars := variables vars X2 in
      let env_ := constr:(fun n => nth n vars X1) in
      let term1_ := reflect vars X1 in
      let term2_ := reflect vars X2 in
      k env_ term1_ term2_
    end.
  
  (** A continuation to [Reify] doing nothing except presentation. *)
  Ltac Only env_ term1_ term2_ :=
    set (env := env_); set (term1 := term1_); set (term2 := term2_);
    change (Eval term1 env <= Eval term2 env).
  
  (** A continuation to [Reify] to call the [coq] tactic. *)
  Ltac Solve env_ term1_ term2_ :=
    set (env := env_);
    change (Eval term1_ env <= Eval term2_ env);
    generalize env;
    cybele (ProveLeq true (term1_, term2_)).

  (** A continuation to [Reify] to call the [coq] tactic using [ProveLeqMemo]. *)
  (*
  Ltac SolveMemo env_ term1_ term2_ :=
    set (env := env_);
    change (Eval term1_ env <= Eval term2_ env);
    generalize env;
    cybele (ProveLeqMemo true (term1_, term2_)).
   *)
End Algo.
