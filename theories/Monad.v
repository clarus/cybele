(** Effectful monad with extraction. *)
Require Import Program.
Require Import String.
Require Import List.
Require Import Reifiable.

Notation "▹ e" := ((fun x => x) (_ e)) (at level 200).

Set Implicit Arguments.

Extract Inductive string =>
  "ascii list" [ "[]" "(::)" ].

(** At some point, we will have to forget about the type of some values that
    have different types to store them in the same container. *)
Module Dynamic.
  Record t: Type := New {
    T: Type;
    Value: T}.
End Dynamic.

(** A memory signature [MemSig.t] is a list of types. Signatures are used to
    assign types to the cells that compose the state of a monadic program. *)
Module MemSig.
  Definition t: Type := list Type.
  
  Definition nth (sig: t) (n: nat): Type :=
    nth n sig unit.
End MemSig.

(** A memory of type [Mem.t sig] is the union of cells whose type is specified
    by [sig]. Each cell is an option type, initially with an empty value. *)
Module Mem.
  Inductive t : MemSig.t -> Type :=
  | Nil : t nil
  | Cons : forall (T : Type), option T -> forall (sig: MemSig.t), t sig ->
    t (T :: sig).
  
  (** A new memory with empty cells. *)
  Fixpoint init (sig: MemSig.t): t sig :=
    match sig with
    | nil => Nil
    | cons T sig' => Cons (None (A := T)) (init sig')
    end.
  Arguments init [sig].
  
  (** Extend the memory with empty cells to fit a bigger signature. *)
  Definition extend sig ext (M : t sig) : t (sig ++ ext).
    induction sig.
    simpl.
    apply (init (sig := ext)).
    simpl.
    inversion M; subst.
    constructor; auto.
  Defined.
  
  (** Truncate a signature to fit a smaller signature. *)
  Definition weaken sig ext (M : t (sig ++ ext)) : t sig.
    induction sig.
    simpl.
    apply (init (sig := nil)).
    simpl in M.
    inversion M; subst.
    constructor; auto.
  Defined.
End Mem.

(** A reference of type [RawRef.t sig T] is an element of the cell [sig]
    of type [T]. *)
Module RawRef.
  Inductive t: MemSig.t -> Type -> Type :=
  | Make: forall (sig: MemSig.t) (index: nat),
    t sig (MemSig.nth sig index).
  
  (** [read sig T r m] returns the value of type [T] held by the reference [r] in
      memory [m]. If no such value exists, returns [None]. *)
  Fixpoint read (sig: MemSig.t) (T: Type) (ref: t sig T) (mem: Mem.t sig)
    : option T.
    destruct ref as [sig index].
    destruct mem as [| T x sig' mem'].
      exact None.
      
      destruct index as [| index'].
        exact x.
        
        apply (read _ _ (Make _ index') mem').
  Defined.
  
  (** [write sig T r m v] returns a new memory [m] in which [r] is
      now assigned to the value [v] of type [T]. If [r] has not the
      type [T] then [None] is returned. *)
  Fixpoint write (sig: MemSig.t) (T: Type) (ref: t sig T) (mem: Mem.t sig)
    (value: T) {struct mem}: option (Mem.t sig).
    destruct ref as [sig index].
    destruct mem as [| T x sig' mem'].
      exact None.
      
      destruct index as [| index'].
        exact (Some (Mem.Cons (Some value) mem')).
        
        destruct (write _ _ (Make _ index') mem' value) as [mem'' |].
          exact (Some (Mem.Cons x mem'')).
          
          exact None.
  Defined.
End RawRef.

(** A signature contains the list of types for both the input and temporay
    memories. The contents of the input memory are saved after the execution in
    OCaml and given as an input to Coq. *)
Module Sig.
  Record t := Make {
    InputTypes: list {T: Type & Reifiable.t T};
    TmpTypes: list Type
  }.
  
  (** An empty signature. Use it if you do not need references. *)
  Definition empty: t := Make nil nil.
  
  Definition input_mem_sig (sig: t): MemSig.t.
    refine (map _ (InputTypes sig)).
    apply projT1.
  Defined.
  
  Definition tmp_mem_sig (sig: t): MemSig.t :=
    TmpTypes sig.
  
  Definition nth_input (sig: t) (n: nat): {T: Type & Reifiable.t T} :=
    nth n (InputTypes sig) (existT _ _ Reifiable.Unit).
  
  Definition nth_input_type (sig: t) (n: nat): Type :=
    projT1 (nth_input sig n).
  
  Fixpoint mem_sig_nth_eq_nth_input_type (sig: t) (n: nat)
    : MemSig.nth (input_mem_sig sig) n = nth_input_type sig n.
    destruct sig as [input_types tmp_types].
    destruct input_types.
      destruct n; reflexivity.
      
      destruct n; try reflexivity.
      unfold MemSig.nth, input_mem_sig, nth_input_type, nth_input in *.
      simpl.
      apply (mem_sig_nth_eq_nth_input_type
        (Sig.Make input_types tmp_types) n).
  Defined.
  
  Definition nth_tmp (sig: t) (n: nat): Type :=
    MemSig.nth (tmp_mem_sig sig) n.

  Definition extend_tmp (s: t) ext := Make (InputTypes s) (TmpTypes s ++ ext).
End Sig.

(** The oracle produces:
    - a natural number that corresponds to the maximum number of recursion
      needed to perform the simulation;
    - the content of the input memory. *)
Module Prophecy.
  Record t (sig: Sig.t) := Make {
    NbSteps: nat;
    InputMem: Mem.t (Sig.input_mem_sig sig) }.
  
  (** The prophecy with an empty input memory. *)
  Definition of_nat (sig: Sig.t) (nb_steps: nat): t sig :=
    Make sig nb_steps Mem.init.
  
  Fixpoint input_mem_of_sexprs (sig: list {T: Type & Reifiable.t T})
    (sexprs: list (option SExpr.t))
    : Mem.t (map (projT1 (P := Reifiable.t)) sig).
    destruct sig as [| T sig'].
      exact Mem.Nil.
      
      destruct sexprs as [| sexpr sexprs'].
        exact (Mem.Cons None (input_mem_of_sexprs _ nil)).
        
        destruct sexpr as [sexpr |].
          destruct T as [T r].
          exact (Mem.Cons (Some (Reifiable.Import r sexpr))
            (input_mem_of_sexprs _ sexprs')).
          exact (Mem.Cons None (input_mem_of_sexprs _ sexprs')).
  Defined.
  
  (** Generate the prophecy from the reified expression given by the
      OCaml program. *)
  Definition of_sexprs (sig: Sig.t) (nb_steps: nat)
    (sexprs: list (option SExpr.t)): t sig :=
    Make sig nb_steps (input_mem_of_sexprs (Sig.InputTypes sig) sexprs).
End Prophecy.

(** A state encapsulates:
    - a natural number that corresponds to the maximum number of
    recursion steps;
    - the input memory;
    - the output memory;
    - A debugging trace. See [print] below. *)
Module State.
  Record t (sig: Sig.t) := Make {
    NbSteps: nat;
    InputMem: Mem.t (Sig.input_mem_sig sig);
    TmpMem: Mem.t (Sig.tmp_mem_sig sig);
    Output: list Dynamic.t }.
  
  (** The initial state deduced from a prophecy. *)
  Definition of_prophecy (sig: Sig.t) (p: Prophecy.t sig): t sig :=
    Make sig (Prophecy.NbSteps p) (Prophecy.InputMem p) Mem.init nil.
  
  Definition set_input_mem (sig: Sig.t) (s: t sig)
    (mem: Mem.t (Sig.input_mem_sig sig)): t sig :=
    Make sig (NbSteps s) mem (TmpMem s) (Output s).
  
  Definition set_tmp_mem (sig: Sig.t) (s: t sig)
    (mem: Mem.t (Sig.tmp_mem_sig sig)): t sig :=
    Make sig (NbSteps s) (InputMem s) mem (Output s).
  
  Definition set_output (sig: Sig.t) (s: t sig) (output: list Dynamic.t): t sig :=
    Make sig (NbSteps s) (InputMem s) (TmpMem s) output.
  
  Definition extend (sig: Sig.t) ext (s: t sig) : t (Sig.extend_tmp sig ext) :=
    Make (Sig.extend_tmp sig ext)
         (NbSteps s)
         (InputMem s)
         (Mem.extend (sig := Sig.TmpTypes sig) ext (TmpMem s)) 
         (Output s).

  Definition weaken (sig: Sig.t) ext (s: t (Sig.extend_tmp sig ext)) : t sig :=
    Make sig
         (NbSteps s)
         (InputMem s)
         (Mem.weaken (Sig.TmpTypes sig) ext (TmpMem s))
         (Output s).
End State.

(** A reference to a cell in the input or the temporary memory. *)
Module Ref.
  Inductive t (sig: Sig.t) (T: Type): Type :=
  | Input: RawRef.t (Sig.input_mem_sig sig) T -> t sig T
  | Tmp: RawRef.t (Sig.tmp_mem_sig sig) T -> t sig T.
  
  Arguments Input [sig T] _.
  Arguments Tmp [sig T] _.
  
  (** A new reference in the input memory to the cell of index [index]. *)
  Definition new_input (sig: Sig.t) (index: nat)
    : t sig (Sig.nth_input_type sig index).
    rewrite <- Sig.mem_sig_nth_eq_nth_input_type.
    exact (Input (RawRef.Make _ index)).
  Defined.
  
  (** A new reference in the temporary memory to the cell of index [index]. *)
  Definition new_tmp (sig: Sig.t) (index: nat)
    : t sig (Sig.nth_tmp sig index) :=
    Tmp (RawRef.Make _ index).
  
  (** Read the value of a reference. *)
  Definition read (sig: Sig.t) (T: Type) (ref: t sig T) (s: State.t sig)
    : option T :=
    match ref with
    | Input ref' => RawRef.read ref' (State.InputMem s)
    | Tmp ref' => RawRef.read ref' (State.TmpMem s)
    end.
  
  (** Write to a reference. *)
  Definition write (sig: Sig.t) (T: Type) (ref: t sig T) (s: State.t sig)
    (value: T): option (State.t sig) :=
    match ref with
    | Input ref' =>
      option_map (State.set_input_mem s)
        (RawRef.write ref' (State.InputMem s) value)
    | Tmp ref' =>
      option_map (State.set_tmp_mem s)
        (RawRef.write ref' (State.TmpMem s) value)
    end.
End Ref.

(** Define the simulable monad with effects. *)
Module Monad.
  (** The underlying implementation of the monad:
      a state and exception monad, returning either a valid result or
      an error message. *)
  Definition M (sig: Sig.t) (A: Type) :=
    State.t sig -> (A + string) * State.t sig.
  
  (** To produce the oracle, we simply remove the monadic layout and directly
      work with the OCaml (effectful) computational model. *)
  Extract Constant M "'a" => "'a".
  
  Program Definition extend_signature
               (sig: Sig.t) (A : Type) (B : Type)
               (c : forall x:nat, Sig.nth_tmp (Sig.extend_tmp sig [B]) x = B ->
                                  M (Sig.extend_tmp sig [B]) A)
    : M sig A :=
    fun (s : State.t sig) =>
      let s' := State.extend (sig:=sig) [B] s in
      let (r, s'') := c (List.length (Sig.TmpTypes sig)) _ s' in
        (r, State.weaken (sig:=sig) (ext := [B]) s'').
  Next Obligation. Proof.
    unfold Sig.nth_tmp. unfold MemSig.nth.
    destruct sig; simpl in * |- *.
    clear c. clear s.
    induction TmpTypes. simpl. auto.
    simpl. apply IHTmpTypes.
  Defined.

  (** * Monadic basic combinators. *)
  (** The classic return. *)
  Definition ret (sig: Sig.t) (A: Type) (x: A): M sig A :=
    fun s =>
      (inl x, s).
  Extract Constant ret => "fun _ x -> x".
  
  (** The classic bind. *)
  Definition bind (sig: Sig.t) (A B: Type) (x: M sig A) (f: A -> M sig B)
    : M sig B :=
    fun s =>
    match x s with
    | (inl x', s') => f x' s'
    | (inr error, s') => (inr error, s')
    end.
  Extract Constant bind => "(fun _ x f -> f x)".
  
  Notation "'do!' A 'in' B" := (bind A (fun _ => B))
    (at level 200, B at level 200).
  
  Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
  
  Notation "'let!' X ':' T ':=' A 'in' B" := (bind (A := T) A (fun X => B))
    (at level 200, X ident, A at level 100, T at level 200, B at level 200).
  
  Notation "'if!' X 'then' A 'else' B" := (bind X (fun b => if b then A else B))
    (at level 200, X at level 100, A at level 100, B at level 200).

  (** [prophecy_run t p] simulates [t] with prophecy [p]. *)
  Definition prophecy_run (sig: Sig.t) (A : Type) (x : M sig A) (p : Prophecy.t sig) :=
    x (State.of_prophecy p).
  
  (** Simple run for the case there is no input memory. *)
  Definition run (sig: Sig.t) (A : Type) (x : M sig A) (nb_steps: nat) :=
    prophecy_run x (Prophecy.of_nat _ nb_steps).
  
  (** [is_computable sig A x p = true] if [x] is a converging computation,
      which means that it is equivalent to [ret v] for some value [v]
      of type [A]. *)
  Definition is_computable (sig: Sig.t) (A: Type) (x: M sig A) (p: Prophecy.t sig)
    : bool :=
    match prophecy_run x p with
    | (inl _, _) => true
    | (inr _, _) => false
    end.
  
  (** Extract an element of type [A] from the proof that [x] is computable. *)
  Lemma proof_by_reflection (sig: Sig.t) (A: Type) (x: M sig A) (p: Prophecy.t sig)
    : is_computable x p = true -> A.
    unfold is_computable.
    destruct (prophecy_run x p) as [x'].
    destruct x'; congruence.
  Defined.

  (* FIXME: Guillaume, why do we have to extract [proof_by_reflection]? *)
  Extract Constant proof_by_reflection => "fun _ _ _ _ -> ()".
  
  (** [select f g] executes [f] in Coq but [g] in OCaml *)
  Definition select (T: Type) (f g: unit -> T): T :=
    f tt.
  Extract Constant select => "fun f g -> g ()".
  
  (** Raise an error with the message [msg]. *)
  Definition error (sig: Sig.t) (A: Type) (msg: string): M sig A :=
    fun s =>
      (inr msg, s).
  (* TODO: extract Coq strings to OCaml strings *)
  Extract Constant error => "fun _ _ -> failwith ""error""".
  Arguments error [sig A] msg _.
  
  (** Catch an exception. *)
  Definition try (sig: Sig.t) (A: Type) (x: unit -> M sig A)
    (handler: string -> M sig A): M sig A :=
    fun s =>
      match x tt s with
      | (inl _, _) as x' => x'
      | (inr msg, s') => handler msg s'
      end.
  Extract Constant try => "fun _ x handler ->
    try x () with _ -> handler ""error""".
  Notation "'try!' a 'with' '_' '=>' b" :=
    (try (fun _ => a) (fun _=> b)) (at level 100).
  
  (** A dependently typed general fixpoint. *)
  Definition dependent_fix (sig: Sig.t) (A: Type) (B: A -> Type)
    (F: (forall (x: A), M sig (B x)) -> forall (x: A), M sig (B x))
    : forall (x: A), M sig (B x) :=
    let fix rec (n: nat) (x: A) (s: State.t sig) :=
      match n with
      | O => (inr "Not terminated" % string, s)
      | S n' => F (rec n') x s
      end in
    fun x s =>
      rec (State.NbSteps s) x s.
  Extract Constant dependent_fix => "
    let rec fix f =
      fun x ->
        CybeleState.observe_recursive_call ();
        f (fix f) x
    in fun _ -> fix".
  
  Notation "'letrec!' X '[' F ']' ':=' A 'in' B" :=
  (let X := dependent_fix F (fun X => A) in B)
  (at level 200, X ident, A at level 100, B at level 200).

  (** A simply typed general fixpoint. *)
  Definition fix_ (sig: Sig.t) (A B: Type) (F: (A -> M sig B) -> A -> M sig B)
    : A -> M sig B :=
    dependent_fix (fun _ => B) F.
  
  (** Read in a reference. *)
  Definition read (sig: Sig.t) (T: Type) (ref: Ref.t sig T)
    : M sig T :=
    fun s =>
      match Ref.read ref s with
      | None => (inr "Invalid reference read" % string, s)
      | Some x => (inl x, s)
      end.
  Notation "! ref" := (read ref) (at level 100).
  Extract Constant read => "fun _ r -> !r".
  
  (** Write in a reference. *)
  Definition write (sig: Sig.t) (T: Type) (ref: Ref.t sig T) (value: T)
    : M sig unit :=
    fun s =>
      match Ref.write ref s value with
      | None => (inr "Invalid reference write" % string, s)
      | Some s' => (inl tt, s')
      end.
  Notation "ref ':=!' x" := (write ref x) (at level 180).
  Extract Constant write => "fun _ r x -> r := x".
  
  Definition register_input_ref (sig: Sig.t) (index: nat)
    (init: Sig.nth_input_type sig index)
    (getter: Ref.t sig (Sig.nth_input_type sig index) -> M sig SExpr.t)
    : Ref.t sig _ :=
    Ref.new_input sig index.
  Extract Constant register_input_ref => "fun _ index init getter ->
    let rec int_of_nat = function
      | O -> 0
      | S n' -> 1 + int_of_nat n' in
    let rec ocaml_sexpr_of_sexpr = function
      | SExpr.I -> CybeleState.I
      | SExpr.B (r1, r2) -> CybeleState.B
        (ocaml_sexpr_of_sexpr r1, ocaml_sexpr_of_sexpr r2) in
    let r = ref init in
    CybeleState.register_input_ref
      (int_of_nat index) (fun () -> ocaml_sexpr_of_sexpr (getter r));
    r".
  
  (** Allocate a reference in the input memory. *)
  Unset Implicit Arguments.
  Definition input_ref (sig: Sig.t) (index: nat)
    (init: Sig.nth_input_type sig index)
    : Ref.t sig (Sig.nth_input_type sig index).
    refine (register_input_ref index init (fun ref =>
      let! v := !ref in
      ret (Reifiable.Export _ v))).
    unfold Sig.nth_input_type.
    destruct (Sig.nth_input sig index) as [T r].
    exact r.
  Defined.
  Set Implicit Arguments.
  
  (** Allocate a reference in the temporary memory. *)
  Unset Implicit Arguments.
  Definition tmp_ref (sig: Sig.t) (index: nat) (init: (Sig.nth_tmp sig index))
    : M sig (Ref.t sig _) :=
    fun s =>
      let ref := Ref.new_tmp sig index in
      match Ref.read ref s with
      | Some _ => error "The reference is already allocated" s
      | None =>
        match Ref.write ref s init with
        | None => error "Impossible to initialize reference" s
        | Some s' => ret ref s'
        end
      end.
  Set Implicit Arguments.
  Extract Constant tmp_ref => "fun _ _ init -> ref init".
  
  (** Print a value in the debugging trace. *)
  Definition print (sig: Sig.t) (T: Type) (value: T): M sig unit :=
    fun s =>
      (inl tt, State.set_output s (Dynamic.New value :: State.Output s)).
  Extract Constant print => "fun _ _ -> ()".
  
  (** * Derived combinators. **)
  (** Print a string in the debugging trace. *)
  Definition print_string (sig: Sig.t) (msg: string): M sig unit :=
    print msg.
  
  (** The while loop. *)
  Definition while (sig: Sig.t)
    (condition: unit -> M sig bool) (body: unit -> M sig unit)
    : M sig unit :=
    fix_ (fun f x =>
      let! b := condition tt in
      if b then
        (do! body tt in
        f x)
      else
        ret tt)
      tt.
  
  (** Return the content of [o] assuming it is not [None]. *)
  Definition extract_some (sig: Sig.t) (T: Type) (o: option T)
    : M sig T :=
    match o with
    | None => error """Some"" expected"
    | Some x => ret x
    end.
End Monad.
