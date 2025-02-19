From Stdlib Require ZArith Lia ZifyBool Uint63.
Declare ML Module "coq-lean-import.plugin".

Set Universe Polymorphism.
Set Printing Universes.
Set Primitive Projections.

Declare Scope lean_scope.
Global Open Scope lean_scope.

Global Set Definitional UIP.

Cumulative
Inductive eq@{u|} {α:Type@{u}} (a:α) : α -> SProp
  := eq_refl : eq a a.
Notation "x = y" := (eq x y) : lean_scope.

Register eq as lean.eq.

Inductive eq_inst1@{|} {α:SProp} (a:α) : α -> SProp
  := eq_refl_inst1 : eq_inst1 a a.

Register eq_inst1 as lean.eq_inst1.

(* Inductive List@{u Lean.u+1.0} (α : Type@{Lean.u+1.0}) : Type@{Lean.u+1.0} :=
    List_nil : List@{u Lean.u+1.0} α
  | List_cons : α -> List@{u Lean.u+1.0} α -> List@{u Lean.u+1.0} α. *)

Monomorphic Universe set.
Inductive List_inst1@{} (α : Type@{set}) : Type@{set} :=
| List_nil_inst1 : List_inst1 α
| List_cons_inst1 : α -> List_inst1 α -> List_inst1 α.

Register List_inst1 as lean.List_inst1.

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

Declare Scope Nat_scope.
Delimit Scope Nat_scope with Nat.
Open Scope Nat_scope.
Bind Scope Nat_scope with Nat.

Inductive Nat_le@{} (n : Nat) : Nat -> SProp :=
| Nat_le_refl : Nat_le n n
| Nat_le_step : forall m : Nat, Nat_le n m -> Nat_le n (Nat_succ m).

Register Nat_le as lean.Nat_le.

Notation "n <= m" := (Nat_le n m) : Nat_scope.
Notation "n < m" := (Nat_le (Nat_succ n) m) (only parsing) : Nat_scope.
(*
Definition Nat_pred (n : Nat) : Nat :=
  match n with
  | Nat_zero => Nat_zero
  | Nat_succ n => n
  end. *)

Variant Or@{} (a a0 : SProp) : SProp :=
| Or_inl : a -> Or a a0
| Or_inr : a0 -> Or a a0.
Register Or as lean.Or.
Record And@{} (a a0 : SProp) : SProp := And_intro
  { left : a;  right : a0 }.
Register And as lean.And.

Inductive sEmpty : SProp := .

Section nat_notation.
  Import ZifyClasses ZArith NArith.
  Fixpoint nat_of_Nat (n : Nat) : nat :=
    match n with
    | Nat_zero => 0
    | Nat_succ n => S (nat_of_Nat n)
    end%nat.
  Fixpoint Nat_of_nat (n : nat) : Nat :=
    match n with
    | O => Nat_zero
    | S n => Nat_succ (Nat_of_nat n)
    end.

  Definition Nat_of_N (n : N) : Nat := Nat_of_nat (N.to_nat n).
  Definition N_of_Nat (n : Nat) : N := N.of_nat (nat_of_Nat n).
  Definition Nat_of_num_uint n : Nat := Nat_of_N (N.of_num_uint n).
  Definition Nat_to_num_uint (n : Nat) := N.to_num_uint (N_of_Nat n).

  Lemma nat2Natid (n : nat) : nat_of_Nat (Nat_of_nat n) = n.
  Proof. induction n as [|n IHn]; cbn; rewrite ?IHn; reflexivity. Qed.
  Lemma Nat2natid (n : Nat) : Nat_of_nat (nat_of_Nat n) = n.
  Proof. induction n as [|n IHn]; cbn; rewrite ?IHn; reflexivity. Qed.

  #[global]
  Monomorphic Instance Inj_Nat_Z : InjTyp Nat Z :=
    mkinj _ _ (fun n => Z.of_nat (nat_of_Nat n)) (fun x =>  0 <= x )%Z (fun n => Nat2Z.is_nonneg _).

  Lemma nat_le_Nat_le' (n m : nat) : (n <= m)%nat -> (Nat_of_nat n <= Nat_of_nat m)%Nat.
  Proof. induction 1; cbn; constructor; assumption. Defined.

  Lemma nat_le_Nat_le (n m : Nat) : (nat_of_Nat n <= nat_of_Nat m)%nat -> (n <= m)%Nat.
  Proof.
    intro H; apply nat_le_Nat_le' in H.
    rewrite !Nat2natid in H; assumption.
  Qed.

  Definition Nat_le_ind (n : Nat) (P : forall m, n <= m -> Prop)
              (H0 : P n (Nat_le_refl n))
              (HS : forall m (H : n <= m), P m H -> P (Nat_succ m) (Nat_le_step n m H))
              m (H : n <= m) : P m H.
  Proof.
    revert m H; fix IH 1; intros [|m] H; [ clear IH | specialize (IH m) ].
    { clear HS.
      revert n P H0 H.
      fix IH 1; intros [|n] P H0 H; [ clear IH | specialize (IH n) ].
      { exact H0. }
      { cut sEmpty; [ destruct 1 | ].
        inversion H. } }
    { specialize (fun H => HS m _ (IH H)).
      clear IH.
      destruct (Nat.eqb (nat_of_Nat n) (nat_of_Nat (Nat_succ m))) eqn:E; [ clear HS | clear H0 ].
      { apply Nat.eqb_eq in E.
        apply (f_equal Nat_of_nat) in E.
        rewrite !Nat2natid in E.
        subst.
        exact H0. }
      { refine (HS _); clear HS.
        inversion H; subst; rewrite ?Nat.eqb_refl in E.
        { congruence. }
        { assumption. } } }
  Qed.

  Definition Nat_le_rect (n : Nat) (P : forall m, n <= m -> Type)
              (H0 : P n (Nat_le_refl n))
              (HS : forall m (H : n <= m), P m H -> P (Nat_succ m) (Nat_le_step n m H))
              m (H : n <= m) : P m H.
  Proof.
    revert m H; fix IH 1; intros [|m] H; [ clear IH | specialize (IH m) ].
    { clear HS.
      revert n P H0 H.
      fix IH 1; intros [|n] P H0 H; [ clear IH | specialize (IH n) ].
      { exact H0. }
      { cut sEmpty; [ destruct 1 | ].
        inversion H. } }
    { specialize (fun H => HS m _ (IH H)).
      clear IH.
      destruct (Nat.eqb (nat_of_Nat n) (nat_of_Nat (Nat_succ m))) eqn:E; [ clear HS | clear H0 ].
      { apply Nat.eqb_eq in E.
        apply (f_equal Nat_of_nat) in E.
        rewrite !Nat2natid in E.
        subst.
        exact H0. }
      { refine (HS _); clear HS.
        inversion H; subst; rewrite ?Nat.eqb_refl in E.
        { congruence. }
        { assumption. } } }
  Defined.

  Lemma Nat_le_nat_le' (n m : Nat) : (n <= m)%Nat -> (nat_of_Nat n <= nat_of_Nat m)%nat.
  Proof. induction 1; cbn; constructor; assumption. Defined.

  Lemma Nat_le_nat_le (n m : nat) : (Nat_of_nat n <= Nat_of_nat m)%Nat -> (n <= m)%nat.
  Proof.
    intro H; apply Nat_le_nat_le' in H.
    rewrite !nat2Natid in H; assumption.
  Qed.
End nat_notation.
Add Zify InjTyp Inj_Nat_Z.

Number Notation Nat Nat_of_num_uint Nat_to_num_uint (abstract after 5000) : Nat_scope.
(* Tell the kernel to unfold these wrappers early, to speed things up *)
#[global] Strategy -10000 [Nat_of_num_uint Nat_to_num_uint].

#[local] Set Warnings "-abstract-large-number".
Definition UInt32_size : Nat := 0x100000000%Nat.
Register UInt32_size as lean.UInt32_size.

Record Fin@{} (n : Nat) := Fin_mk { val : Nat; isLt : (val < n)%Nat }.
Register Fin as lean.Fin.
Record UInt32@{} := UInt32_mk { val0 : Fin UInt32_size }.
Register UInt32 as lean.UInt32.


Section strings.
  Import ZArith NArith Lia Zify ZifyBool.
  Variant InvalidUInt32 (n : N) : Set := invalid_uint32.
  Variant InvalidChar (n : N) : Set := invalid_char.
  #[local] Set Warnings "-abstract-large-number".

  Lemma Nat_lt_to_N (n : N) (m : N) : (n <? m)%N = true -> Nat_of_N n < Nat_of_N m.
  Proof.
    cbv [N_of_Nat Nat_of_N].
    intro H; apply nat_le_Nat_le.
    cbn [nat_of_Nat].
    rewrite ?nat2Natid.
    lia.
  Qed.

  Lemma Nat_lt_to_N_l (n : Nat) (m : N) : (N_of_Nat n <? m)%N = true -> n < Nat_of_N m.
  Proof.
    cbv [N_of_Nat Nat_of_N].
    intro H; apply nat_le_Nat_le.
    cbn [nat_of_Nat].
    rewrite nat2Natid.
    lia.
  Qed.

  Lemma Nat_lt_to_N_r (n : N) (m : Nat) : (n <? N_of_Nat m)%N = true -> Nat_of_N n < m.
  Proof.
    cbv [N_of_Nat Nat_of_N].
    intro H; apply nat_le_Nat_le.
    cbn [nat_of_Nat].
    rewrite nat2Natid.
    lia.
  Qed.

  (* Section with_or. *)
    (* Context (Or : SProp -> SProp -> SProp)
            (Or_inl : forall P Q, P -> Or P Q)
            (Or_inr : forall P Q, Q -> Or P Q)
            (And : SProp -> SProp -> SProp)
            (And_intro : forall P Q, P -> Q -> And P Q). *)
  #[local] Set Warnings "-notation-overridden".
  #[local] Infix "\/" := Or : type_scope.
  #[local] Infix "/\" := And : type_scope.
  #[local] Open Scope Nat_scope.

  Definition Nat_isValidChar (n : Nat) : SProp
    := n < 0xd800 \/ (0xdfff < n /\ n < 0x110000).

  Record Char@{} := Char_mk
  { val1 : UInt32; valid : Nat_isValidChar val1.(val0).(val _) }.

  Definition check_N_isValidChar (n : N) : bool
    := ((n <? 0xd800) || ((0xdfff <? n) && (n <? 0x110000)))%N%bool.

  Definition Fin_mk_N (n : N) (val : N) (isLt : (val <? n)%N = true) : Fin (Nat_of_N n)
    := Fin_mk (Nat_of_N n) (Nat_of_N val) (Nat_lt_to_N val n isLt).

  Definition UInt32_mk_N (val : N) (isLt : (val <? 0x100000000)%N = true) : UInt32
    := UInt32_mk (Fin_mk_N 0x100000000 val isLt).

  Lemma Nat_isValidChar_mk_N (n : N) (isLt : check_N_isValidChar n = true)
    : Nat_isValidChar (Nat_of_N n).
  Proof.
    cbv [Nat_isValidChar Nat_of_num_uint check_N_isValidChar] in *.
    pose proof (Nat_lt_to_N n 0xd800) as H1.
    pose proof (Nat_lt_to_N 0xdfff n) as H2.
    pose proof (Nat_lt_to_N n 0x110000) as H3.
    destruct N.ltb; cbn [orb] in *;
    [ | destruct N.ltb; cbn [andb] in *; [ | exfalso; congruence ] ];
    [ | destruct N.ltb; cbn [andb] in *; [ | exfalso; congruence ] ];
    [ apply Or_inl, nat_le_Nat_le; revert H1 | apply Or_inr, And_intro; apply nat_le_Nat_le; [ revert H2 | revert H3 ] ];
    clear.
    all: cbv [Nat_of_N Nat_of_num_uint].
    all: intro H; specialize (H Logic.eq_refl).
    all: apply Nat_le_nat_le' in H.
    1: etransitivity; [ exact H | ].
    2: etransitivity; [ | exact H ].
    3: etransitivity; [ exact H | ].
    all: clear.
    all: zify; clear.
    all: cbn [nat_of_Nat]; rewrite ?nat2Natid, ?Nat2Z.inj_succ, ?N_nat_Z.
    all: vm_compute; congruence.
  Qed.

  Definition Char_mk_N (val : N) (isLt : ((val <? 0x100000000)%N && check_N_isValidChar val)%bool = true) : Char
    := Char_mk (UInt32_mk_N val (proj1 (andb_prop _ _ isLt))) (Nat_isValidChar_mk_N val (proj2 (andb_prop _ _ isLt))).

  Definition reflective_Char_mk (val : N)
    : if ((val <? 0x100000000)%N && check_N_isValidChar val)%bool
      then Char
      else InvalidChar val
    := let isLt := ((val <? 0x100000000)%N && check_N_isValidChar val)%bool in
       match isLt return ((val <? 0x100000000)%N && check_N_isValidChar val)%bool = isLt -> if isLt then Char else InvalidChar val with
       | true => fun H => Char_mk_N val H
       | false => fun _ => invalid_char val
       end Logic.eq_refl.

  Definition reflective_Char_mk_prim (val : Uint63.int)
    := reflective_Char_mk (Z.to_N (Uint63.to_Z val)).


  (* Definition reflective_UInt32_mk (val : N) : if (val <? 0x100000000)%N
                                              then UInt32
                                              else InvalidUInt32 val
    := let isLt := (val <? 0x100000000)%N in
       match isLt return (val <? 0x100000000)%N = isLt -> if isLt then UInt32 else InvalidUInt32 val with
       | true => fun H => UInt32_mk_N val H
       | false => fun _ => invalid_uint32 val
       end Logic.eq_refl.

  Definition reflective_UInt32_mk_prim (val : Uint63.int)
    := reflective_UInt32_mk (Z.to_N (Uint63.to_Z val)).


  Definition check_isValidChar (n : Nat) : bool
    := let n := N_of_Nat n in
        ((n <? 0xd800) || ((0xdfff <? n) && (n <? 0x110000)))%N%bool.

  Definition reflective_isValidChar_mk (n : Nat)
    : if check_isValidChar n
      then n < 0xd800 \/ (0xdfff < n /\ n < 0x110000)
      else InvalidChar n.
  Proof.
    cbv [check_isValidChar].
    pose proof (Nat_lt_to_N_l n 0xd800) as H1.
    pose proof (Nat_lt_to_N_r 0xdfff n) as H2.
    pose proof (Nat_lt_to_N_l n 0x110000) as H3.
    destruct N.ltb; cbn [orb];
    [ | destruct N.ltb; cbn [andb]; [ | constructor ] ];
    [ | destruct N.ltb; cbn [andb]; [ | constructor ] ];
    [ apply Or_inl, nat_le_Nat_le; revert H1 | apply Or_inr, And_intro; apply nat_le_Nat_le; [ revert H2 | revert H3 ] ];
    clear.
    all: cbv [Nat_of_N Nat_of_num_uint].
    all: intro H; specialize (H Logic.eq_refl).
    all: apply Nat_le_nat_le' in H.
    1: etransitivity; [ exact H | ].
    2: etransitivity; [ | exact H ].
    3: etransitivity; [ exact H | ].
    all: clear.
    all: zify; clear.
    all: cbn [nat_of_Nat]; rewrite ?nat2Natid, ?Nat2Z.inj_succ, ?N_nat_Z.
    all: vm_compute; congruence.
  Qed.
  End with_or. *)


End strings.

Register Nat_isValidChar as lean.Nat_isValidChar.
Register Char as lean.Char.
Register reflective_Char_mk_prim as lean.Char.mk.reflective_prim.
