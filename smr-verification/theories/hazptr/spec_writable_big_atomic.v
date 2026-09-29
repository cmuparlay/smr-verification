From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.hazptr Require Import spec_hazptr.
From iris.prelude Require Import options.

(** Logically atomic specification of Load/Store/CAS (writable) big atomics.
    The abstract state is the value. Load returns a fresh buffer with it. *)

Definition WritableBigAtomicT Σ : Type :=
  ∀ (γ : gname) (vs : list val), iProp Σ.

Definition IsWritableBigAtomicT Σ (N : namespace) : Type :=
  ∀ (γ : gname) (l : val) (n : nat), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (writableN : namespace) (hazptrN : namespace) (DISJN : writableN ## hazptrN).
Variables
  (writable_new : nat → val)
  (writable_load : nat → val)
  (writable_store : nat → val)
  (writable_cas : nat → val).
Variables
  (hazptr : hazard_pointer_spec Σ hazptrN)
  (WritableBigAtomic : WritableBigAtomicT Σ)
  (IsWritableBigAtomic : IsWritableBigAtomicT Σ writableN).

Definition writable_new_spec' : Prop :=
  ∀ γd d n l dq vs,
    n > 0 → length vs = n → Forall val_is_unboxed vs →
      {{{ hazptr.(IsHazardDomain) γd d ∗ l ↦∗{dq} vs }}}
        writable_new n #l #d
      {{{ γ ba, RET ba; IsWritableBigAtomic γ ba n ∗ WritableBigAtomic γ vs ∗ l ↦∗{dq} vs }}}.

Definition writable_load_spec' : Prop :=
  ⊢ ∀ γ ba n,
    IsWritableBigAtomic γ ba n -∗
      <<{ ∀∀ vs, WritableBigAtomic γ vs }>>
        writable_load n ba @ ⊤,(↑writableN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
      <<{ ∃∃ l, WritableBigAtomic γ vs | RET #l; l ↦∗ vs }>>.

Definition writable_store_spec' : Prop :=
  ∀ γ ba n (l_desired : loc) (dq : dfrac) (desired : list val),
    length desired = n → Forall val_is_unboxed desired →
      IsWritableBigAtomic γ ba n -∗ l_desired ↦∗{dq} desired -∗
        <<{ ∀∀ vs, WritableBigAtomic γ vs }>>
          writable_store n ba #l_desired @ ⊤,(↑writableN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
        <<{ WritableBigAtomic γ desired | RET #(); l_desired ↦∗{dq} desired }>>.

Definition writable_cas_spec' : Prop :=
  ∀ γ ba n (l_expected l_desired : loc) (dq dq' : dfrac) (expected desired : list val),
    length expected = n → length desired = n →
      Forall val_is_unboxed expected → Forall val_is_unboxed desired →
        IsWritableBigAtomic γ ba n -∗ l_expected ↦∗{dq} expected -∗ l_desired ↦∗{dq'} desired -∗
          <<{ ∀∀ actual, WritableBigAtomic γ actual }>>
            writable_cas n ba #l_expected #l_desired @ ⊤,(↑writableN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
          <<{ if bool_decide (actual = expected) then
                WritableBigAtomic γ desired
              else
                WritableBigAtomic γ actual
            | RET #(bool_decide (actual = expected)); l_expected ↦∗{dq} expected ∗ l_desired ↦∗{dq'} desired }>>.

End spec.

Record writable_big_atomic_code : Type := WritableBigAtomicCode {
  writable_big_atomic_new : nat → val;
  writable_big_atomic_load : nat → val;
  writable_big_atomic_store : nat → val;
  writable_big_atomic_cas : nat → val;
}.

Record writable_big_atomic_spec {Σ} `{!heapGS Σ} {writableN hazptrN : namespace}
    {DISJN : writableN ## hazptrN}
    {hazptr : hazard_pointer_spec Σ hazptrN}
  : Type := WritableBigAtomicSpec {
  writable_big_atomic_spec_code :> writable_big_atomic_code;

  WritableBigAtomic : WritableBigAtomicT Σ;
  IsWritableBigAtomic : IsWritableBigAtomicT Σ writableN;

  WritableBigAtomic_Timeless : ∀ γ vs, Timeless (WritableBigAtomic γ vs);
  IsWritableBigAtomic_Persistent : ∀ γ l n, Persistent (IsWritableBigAtomic γ l n);

  writable_big_atomic_new_spec :
    writable_new_spec' writableN hazptrN writable_big_atomic_spec_code.(writable_big_atomic_new) hazptr
      WritableBigAtomic IsWritableBigAtomic;
  writable_big_atomic_load_spec :
    writable_load_spec' writableN hazptrN writable_big_atomic_spec_code.(writable_big_atomic_load)
      WritableBigAtomic IsWritableBigAtomic;
  writable_big_atomic_store_spec :
    writable_store_spec' writableN hazptrN writable_big_atomic_spec_code.(writable_big_atomic_store)
      WritableBigAtomic IsWritableBigAtomic;
  writable_big_atomic_cas_spec :
    writable_cas_spec' writableN hazptrN writable_big_atomic_spec_code.(writable_big_atomic_cas)
      WritableBigAtomic IsWritableBigAtomic;
}.

Global Arguments writable_big_atomic_spec : clear implicits.
Global Arguments writable_big_atomic_spec _ {_} _ _ _ _ : assert.
Global Existing Instances WritableBigAtomic_Timeless IsWritableBigAtomic_Persistent.
