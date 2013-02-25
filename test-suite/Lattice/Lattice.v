Require Import Setoid.

Set Implicit Arguments.

(** * Module [Lattice]  *)
Module Lattice.
  (** A set is a lattice if it has a meet and a join following the standard
     lattice equations. *)
  Record t (A: Type) := New {
    Meet: A -> A -> A;
    Join: A -> A -> A;
    
    MeetIdempotent: forall a, Meet a a = a;
    MeetCommutative: forall a b, Meet a b = Meet b a;
    MeetAssociative: forall a b c, Meet (Meet a b) c = Meet a (Meet b c);
    MeetAbsorptive: forall a b, Meet a (Join a b) = a;
    
    JoinIdempotent: forall a, Join a a = a;
    JoinCommutative: forall a b, Join a b = Join b a;
    JoinAssociative: forall a b c, Join (Join a b) c = Join a (Join b c);
    JoinAbsorptive: forall a b, Join a (Meet a b) = a}.
  
  (** Implicit parameters used for most of the developments. *)
  Module Type Param.
    (** The current set. *)
    Parameter A: Type.
    
    (** The current lattice description. *)
    Parameter Lattice: t A.
  End Param.
  
  Module Instance (P: Param).
    Import P.
    
    Module Definitions.
      (** Orderering relation: less or equal. *)
      Definition Le a b := Meet Lattice a b = a.
    End Definitions.
    Import Definitions.
    
    Module Notations.
      Infix "/*\" := (Meet P.Lattice)
        (at level 40, left associativity): lattice_scope.
      Infix "\*/" := (Join P.Lattice)
        (at level 50, left associativity): lattice_scope.
      Infix "<=" := Le : lattice_scope.
    End Notations.
    Import Notations.
    Local Open Scope lattice_scope.
    
    (** ** Lemmas about lattices. *)
    Module Facts.
      (** *** [a <= b] is an order. *)
      Lemma LeReflexive: forall a, a <= a.
        apply MeetIdempotent.
      Qed.
      
      Lemma LeAntiSymmetric: forall a b,
        a <= b -> b <= a -> a = b.
        intros a b Ha Hb.
        unfold Le in Hb.
        rewrite MeetCommutative in Hb.
        congruence.
      Qed.
      
      Lemma LeTransitive: forall a b c,
        a <= b -> b <= c -> a <= c.
        intros a b c Hab Hbc.
        unfold Le in *.
        rewrite <- Hab at 2.
        rewrite <- Hbc.
        rewrite <- MeetAssociative.
        congruence.
      Qed.
      
      (** *** Some properties relating the ordering and the lattice operators. *)
      Lemma MeetJoinEq: forall a b,
        a /*\ b = a <-> a \*/ b = b.
        split; intro H; rewrite <- H.
          rewrite JoinCommutative.
          rewrite MeetCommutative.
          rewrite JoinAbsorptive.
          reflexivity.
          rewrite MeetAbsorptive.
          reflexivity.
      Qed.
      
      Lemma ConsistentMeet: forall a b,
        a <= b <-> a /*\ b = a.
        tauto.
      Qed.
      
      Lemma ConsistentJoin: forall a b,
        a <= b <-> a \*/ b = b.
        intros a b.
        rewrite <- MeetJoinEq.
        apply ConsistentMeet.
      Qed.
      
      Lemma MeetLeLeft : forall a b, a /*\ b <= a.
        intros a b.
        rewrite ConsistentMeet.
        rewrite MeetCommutative.
        rewrite <- MeetAssociative.
        now rewrite MeetIdempotent.
      Qed.
      
      Lemma MeetLeRight : forall a b, a /*\ b <= b.
        intros a b.
        rewrite ConsistentMeet.
        rewrite MeetAssociative.
        now rewrite MeetIdempotent.
      Qed.
      
      Lemma JoinLeLeft : forall a b, a <= a \*/ b.
        intros a b.
        rewrite ConsistentJoin.
        rewrite <- JoinAssociative.
        now rewrite JoinIdempotent.
      Qed.
      
      Lemma JoinLeRight : forall a b, b <= a \*/ b.
        intros a b.
        rewrite ConsistentJoin.
        rewrite JoinCommutative.
        rewrite JoinAssociative.
        now rewrite JoinIdempotent.
      Qed.
      
      Lemma CompareToMeetRight: forall u a b,
        u <= a -> u <= b -> u <= a /*\ b.
        intros u a b Ha Hb.
        rewrite <- (proj1 (ConsistentMeet u b)); trivial.
        rewrite <- (proj1 (ConsistentMeet u a)); trivial.
        rewrite MeetAssociative.
        apply MeetLeRight.
      Qed.
      
      Lemma CompareToMeetLeft: forall u a b,
        a <= u \/ b <= u -> a /*\ b <= u.
        intros u a b [Ha | Hb].
          apply LeTransitive with (b := a); trivial.
          apply MeetLeLeft.
          
          apply LeTransitive with (b := b); trivial.
          apply MeetLeRight.
      Qed.
      
      Lemma CompareToJoinLeft: forall u a b,
        a <= u -> b <= u -> a \*/ b <= u.
        intros u a b Ha Hb.
        rewrite <- (proj1 (ConsistentJoin a u)); trivial.
        rewrite <- (proj1 (ConsistentJoin b u)); trivial.
        rewrite <- JoinAssociative.
        apply JoinLeLeft.
      Qed.
      
      Lemma CompareToJoinRight: forall u a b,
        u <= a \/ u <= b -> u <= a \*/ b.
        intros u a b [Ha | Hb].
          apply LeTransitive with (b := a); trivial.
          apply JoinLeLeft.
          
          apply LeTransitive with (b := b); trivial.
          apply JoinLeRight.
      Qed.
    End Facts.
  End Instance.
End Lattice.