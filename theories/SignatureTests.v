(** Experiments on a memory with automatic and compositional signatures.
      We want the allocating scheme to be determined statically. We need to
    compute at typing time the types of values in the memory and the addresses
    of the pointers. It enforces a finite number of references in the program,
    but each reference can point to an extensible datastructure such as a list.
      Our approach works well but breaks the type inference and requires a lot
    of annotations. This is due to the limited unification algorithm which
    cannot use the associativity of list concatenation. Thus the user has to
    solve many equations by hand.
    TODO: try type classes *)
Require Import List.

Set Implicit Arguments.

(** A signature is a list of types to type the values in a memory *)
Module Sig.
  Definition t: Type := list Type.
End Sig.

(** A memory is a list of one value for each type of the signature *)
Module Mem.
  Inductive t: Sig.t -> Type :=
  | Nil: t nil
  | Cons: forall (T: Type), T -> forall (sig: Sig.t), t sig ->
    t (T :: sig).

  Definition Destruct (T: Type) (sig: Sig.t) (mem: t (T :: sig))
    : T * t sig.
    inversion_clear mem as [|T' x sig' mem'].
    exact (x, mem').
  Defined.

  Fixpoint Split (sig1 sig2: Sig.t) (mem: t (sig1 ++ sig2))
    : t sig1 * t sig2.
    destruct sig1 as [|T sig1].
      exact (Nil, mem).

      simpl in mem.
      refine (let (x, mem') := Destruct mem in _).
      destruct (Split _ _ mem') as [mem1 mem2].
      exact (Cons x mem1, mem2).
  Defined.

  Fixpoint Append (sig1 sig2: Sig.t) (mem1: t sig1) (mem2: t sig2)
    : t (sig1 ++ sig2).
    destruct sig1 as [|T sig1].
      exact mem2.

      refine (let (x, mem1') := Destruct mem1 in _).
      exact (Cons x (Append _ _ mem1' mem2)).
  Defined.
End Mem.

(** A reference is a statically computed pointer ; it contains no data,
    only type informations *)
Module Ref.
  (** Points to an element of type [T] located after a list of elements
      of types [sig] *)
  Inductive t (sig: Sig.t) (T: Type): Type :=
  | Make: t sig T.

  (** Dereference a pointer *)
  Definition Read (sig1 sig2: Sig.t) (T: Type) (ref: t sig1 T)
    (mem: Mem.t (sig2 ++ T :: sig1)): T :=
    fst (Mem.Destruct (snd (Mem.Split sig2 _ mem))).

  (** Write at a pointer address *)
  Definition Write (sig1 sig2: Sig.t) (T: Type) (ref: t sig1 T)
    (mem: Mem.t (sig2 ++ T :: sig1)) (x: T)
    : Mem.t (sig2 ++ T :: sig1) :=
    let (mem1, mem2) := Mem.Split sig2 _ mem in
    let (_, mem2') := Mem.Destruct mem2 in
    Mem.Append mem1 (Mem.Cons x mem2').
End Ref.

(** The state monad *)
Module Monad.
  (** [sig_in] is the type of the input memory,
      [sig_out] the type of the allocated elements *)
  Definition t (sig_in sig_out: Sig.t) (T: Type): Type :=
    Mem.t sig_in ->
    T * Mem.t (sig_out ++ sig_in).

  (** The return combinator *)
  Definition Return (sig_in: Sig.t) (A: Type) (x: A): t sig_in nil A :=
    fun s =>
      (x, s).

  (** Same as [app_assoc] but with non-opaque proof *)
  Fixpoint appAssoc (A: Type) (l1 l2 l3: list A)
    : l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
    destruct l1 as [|x l1].
      reflexivity.

      simpl.
      now rewrite appAssoc.
  Defined.

  (** The bind combinator *)
  Definition Bind (A B: Type)
    (sig_in_x sig_out_x sig_out_f: Sig.t)
    (x: t sig_in_x sig_out_x A)
    (f: A -> t (sig_out_x ++ sig_in_x) sig_out_f B)
    : t sig_in_x (sig_out_f ++ sig_out_x) B.
    intros s.
    destruct (x s) as [x' s'].
    rewrite <- appAssoc.
    exact (f x' s').
  Defined.

  (** A pointer to a new memory cell *)
  Definition Alloc (sig: Sig.t) (A: Type) (x: A)
    : t sig (A :: nil) (Ref.t sig A) :=
    fun s =>
      (Ref.Make sig A, Mem.Cons x s).

  (** Read at a pointer address *)
  Definition Read (sig1 sig2: Sig.t) (A: Type) (ref: Ref.t sig1 A)
    : t (sig2 ++ A :: sig1) nil A :=
    fun s =>
      (Ref.Read sig2 ref s, s).

  (** Write at a pointer address *)
  Definition Write (sig1 sig2: Sig.t) (A: Type) (ref: Ref.t sig1 A)
    (x: A): t (sig2 ++ A :: sig1) nil unit :=
      fun s =>
        (tt, Ref.Write sig2 ref s x).

  (** To type the examples we enforce the input signature to be [nil]
      and add annotations when the type inference fails. *)
  Module Examples.
    Definition Five: t nil _ nat := Return 5.
    Compute Five Mem.Nil.

    Definition RefReadTwo: t nil _ nat :=
      Bind (Alloc 2) (fun ref2 =>
      Read nil ref2).
    Compute RefReadTwo Mem.Nil.

    Definition RefReadReturnTwo: t nil _ nat :=
      Bind (Alloc 5) (fun ref5 =>
      Bind (Alloc 2) (fun ref2 =>
      Bind (Read nil ref2) (fun v2 =>
      Return v2))).
    Compute RefReadReturnTwo Mem.Nil.

    Definition RefSeven: t nil _ nat :=
      Bind (Alloc 2) (fun ref2 =>
      Bind (Alloc 5) (fun ref5 =>
      Bind (Read nil ref5) (fun v5 =>
      Bind (Read ((nat: Type) :: nil) ref2) (fun v2 =>
      Return (v2 + v5))))).
    Compute RefSeven Mem.Nil.

    Definition RefWriteReadNine: t nil _ nat :=
      Bind (Alloc 2) (fun ref2 =>
      Bind (Write _ ref2 9) (fun _ =>
      Read nil ref2)).
    Compute RefWriteReadNine Mem.Nil.
  End Examples.
End Monad.
