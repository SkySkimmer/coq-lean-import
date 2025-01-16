Declare ML Module "coq-lean-import.plugin".

Set Universe Polymorphism.
Set Printing Universes.
Set Primitive Projections.

Declare Scope lean_scope.
Global Open Scope lean_scope.

Global Set Definitional UIP.

Inductive eq@{u|} {α:Type@{u}} (a:α) : α -> SProp
  := eq_refl : eq a a.
Notation "x = y" := (eq x y) : lean_scope.

Register eq as lean.eq.

Inductive eq_inst1@{|} {α:SProp} (a:α) : α -> SProp
  := eq_refl_inst1 : eq_inst1 a a.

Register eq_inst1 as lean.eq_inst1.

Module Quot.

  Private Inductive quot@{u|} {α : Type@{u}} (r : α -> α -> SProp) : Type@{u}
    := mk (a:α).

  Register quot as lean.quot.
  Register mk as lean.quot.mk.

  Definition lift@{u v|} {α : Type@{u}} {r:α -> α -> SProp} {β : Type@{v}} (f : α -> β)
    : (forall a b : α, r a b -> eq (f a) (f b)) -> quot r -> β
    := fun H q => match q with mk _ x => fun _ => f x end H.

  Register lift as lean.quot.lift.

  Definition lift_inst2@{u|} {α : Type@{u}} {r:α -> α -> SProp} {β : SProp} (f : α -> β)
    : (forall a b : α, r a b -> eq_inst1 (f a) (f b)) -> quot r -> β
    := fun H q => match q with mk _ x => fun _ => f x end H.

  Register lift_inst2 as lean.quot.lift_inst2.

  Definition ind@{u|} {α : Type@{u}} {r:α -> α -> SProp} {β : quot r -> SProp}
    : (forall a : α, β (mk r a)) -> forall q : quot r, β q
    := fun f q => match q with mk _ x => f x end.

  Register ind as lean.quot.ind.

  (* Because quot_inst1 is SProp we don't need to make it Private: the
     axiom declared by lean about it is a tautology. *)
  Inductive quot_inst1@{|} {α : SProp} (r : α -> α -> SProp) : SProp
    := mk_inst1 (a:α).

  Register quot_inst1 as lean.quot_inst1.
  Register mk_inst1 as lean.quot.mk_inst1.

  (* This non-uniform translation avoids breaking SR ;) *)
  Definition lift_inst1@{v|} {α : SProp} {r:α -> α -> SProp} {β : Type@{v}} (f : α -> β)
    : (forall a b : α, r a b -> eq (f a) (f b)) -> quot_inst1 r -> β
    := fun _ q => f (match q with mk_inst1 _ x => x end).

  Register lift_inst1 as lean.quot.lift_inst1.

  Definition lift_inst3@{|} {α : SProp} {r:α -> α -> SProp} {β : SProp} (f : α -> β)
    : (forall a b : α, r a b -> eq_inst1 (f a) (f b)) -> quot_inst1 r -> β
    := fun _ q => f (match q with mk_inst1 _ x => x end).

  Register lift_inst3 as lean.quot.lift_inst3.

  Definition ind_inst1@{|} {α : SProp} {r:α -> α -> SProp} {β : quot_inst1 r -> SProp}
    : (forall a : α, β (mk_inst1 r a)) -> forall q : quot_inst1 r, β q
    := fun f q => match q with mk_inst1 _ x => f x end.

  Register ind_inst1 as lean.quot.ind_inst1.

End Quot.

Inductive Nat := Nat_zero : Nat | Nat_succ : Nat -> Nat.

Register Nat as lean.Nat.

Fixpoint double (n : Nat) : Nat :=
  match n with
  | Nat_zero => Nat_zero
  | Nat_succ n => Nat_succ (Nat_succ (double n))
  end.

Register double as lean.Nat_double.