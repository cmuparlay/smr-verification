From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.hazptr Require Import spec_hazptr.
From iris.prelude Require Import options.

(** Logically atomic specification of LL/SC big atomics.

    In the paper's sequential specification, the abstract state of a big atomic
    is a pair of its value and the set of threads that have it linked. We encode
    this set by a version, which counts the successful SCs on the big atomic,
    together with a per-thread link recording the big atomic and version at the
    thread's last LL: a thread has [γ] linked iff its link is [(γ, ver)] where
    [ver] is the current version of [γ]. Hence an LL unlinks all other big
    atomics, and a successful SC unlinks all threads by incrementing the
    version.

    The thread-local state is shared by all big atomics, and SC compares the
    header against it without knowing which big atomic it came from, so SC is
    only specified for the big atomic of the thread's last LL.

    LL returns a fresh buffer with the value, together with the permission to
    free it and the fact that the value has the size [n] of the big atomic. *)

Definition BigAtomicLLSCT Σ : Type :=
  ∀ (γ : gname) (vs : list val) (ver : nat), iProp Σ.

Definition IsBigAtomicLLSCT Σ (N : namespace) : Type :=
  ∀ (γ γd : gname) (l : val) (n : nat), iProp Σ.

Definition LLSCThreadT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (ctx : val) (link : option (gname * nat)), iProp Σ.

Section spec.
Context `{!heapGS Σ}.
Context (big_atomicN : namespace) (hazptrN : namespace) (DISJN : big_atomicN ## hazptrN).
Variables
  (big_atomic_new : nat → val)
  (big_atomic_thread_new : val)
  (big_atomic_thread_drop : val)
  (big_atomic_ll : nat → val)
  (big_atomic_sc : nat → val).
Variables
  (hazptr : hazard_pointer_spec Σ hazptrN)
  (BigAtomic : BigAtomicLLSCT Σ)
  (IsBigAtomic : IsBigAtomicLLSCT Σ big_atomicN)
  (LLSCThread : LLSCThreadT Σ big_atomicN).

Definition big_atomic_llsc_new_spec' : Prop :=
  ∀ γd d n l dq vs,
    n > 0 → length vs = n →
      {{{ hazptr.(IsHazardDomain) γd d ∗ l ↦∗{dq} vs }}}
        big_atomic_new n #l #d
      {{{ γ ba, RET ba; IsBigAtomic γ γd ba n ∗ BigAtomic γ vs 0 ∗ l ↦∗{dq} vs }}}.

Definition big_atomic_llsc_thread_new_spec' : Prop :=
  ∀ γd d,
    {{{ hazptr.(IsHazardDomain) γd d }}}
      big_atomic_thread_new #d
    {{{ ctx, RET ctx; LLSCThread γd ctx None }}}.

Definition big_atomic_llsc_thread_drop_spec' : Prop :=
  ∀ γd ctx link,
    {{{ LLSCThread γd ctx link }}}
      big_atomic_thread_drop ctx
    {{{ RET #(); True }}}.

Definition big_atomic_llsc_ll_spec' : Prop :=
  ⊢ ∀ γ γd ba n ctx link,
    IsBigAtomic γ γd ba n -∗ LLSCThread γd ctx link -∗
      <<{ ∀∀ vs ver, BigAtomic γ vs ver }>>
        big_atomic_ll n ba ctx @ ⊤,(↑big_atomicN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
      <<{ ∃∃ l, BigAtomic γ vs ver
        | RET #l; l ↦∗ vs ∗ †l…n ∗ ⌜length vs = n⌝ ∗ LLSCThread γd ctx (Some (γ, ver)) }>>.

Definition big_atomic_llsc_sc_spec' : Prop :=
  ∀ γ γd ba n ctx ver (l_desired : loc) (dq : dfrac) (desired : list val),
    length desired = n →
      IsBigAtomic γ γd ba n -∗ LLSCThread γd ctx (Some (γ, ver)) -∗ l_desired ↦∗{dq} desired -∗
        <<{ ∀∀ actual ver', BigAtomic γ actual ver' }>>
          big_atomic_sc n ba ctx #l_desired @ ⊤,(↑big_atomicN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
        <<{ if bool_decide (ver' = ver) then
              BigAtomic γ desired (S ver')
            else
              BigAtomic γ actual ver'
          | RET #(bool_decide (ver' = ver));
              LLSCThread γd ctx (Some (γ, ver)) ∗ l_desired ↦∗{dq} desired }>>.

End spec.

Record big_atomic_llsc_code : Type := BigAtomicLLSCCode {
  big_atomic_llsc_new : nat → val;
  big_atomic_llsc_thread_new : val;
  big_atomic_llsc_thread_drop : val;
  big_atomic_llsc_ll : nat → val;
  big_atomic_llsc_sc : nat → val;
}.

Record big_atomic_llsc_spec {Σ} `{!heapGS Σ} {big_atomicN hazptrN : namespace}
    {DISJN : big_atomicN ## hazptrN}
    {hazptr : hazard_pointer_spec Σ hazptrN}
  : Type := BigAtomicLLSCSpec {
  big_atomic_llsc_spec_code :> big_atomic_llsc_code;

  BigAtomicLLSC : BigAtomicLLSCT Σ;
  IsBigAtomicLLSC : IsBigAtomicLLSCT Σ big_atomicN;
  LLSCThread : LLSCThreadT Σ big_atomicN;

  BigAtomicLLSC_Timeless : ∀ γ vs ver, Timeless (BigAtomicLLSC γ vs ver);
  IsBigAtomicLLSC_Persistent : ∀ γ γd l n, Persistent (IsBigAtomicLLSC γ γd l n);

  big_atomic_llsc_new_spec :
    big_atomic_llsc_new_spec' big_atomicN hazptrN
      big_atomic_llsc_spec_code.(big_atomic_llsc_new) hazptr BigAtomicLLSC IsBigAtomicLLSC;
  big_atomic_llsc_thread_new_spec :
    big_atomic_llsc_thread_new_spec' big_atomicN hazptrN
      big_atomic_llsc_spec_code.(big_atomic_llsc_thread_new) hazptr LLSCThread;
  big_atomic_llsc_thread_drop_spec :
    big_atomic_llsc_thread_drop_spec' big_atomicN
      big_atomic_llsc_spec_code.(big_atomic_llsc_thread_drop) LLSCThread;
  big_atomic_llsc_ll_spec :
    big_atomic_llsc_ll_spec' big_atomicN hazptrN
      big_atomic_llsc_spec_code.(big_atomic_llsc_ll) BigAtomicLLSC IsBigAtomicLLSC LLSCThread;
  big_atomic_llsc_sc_spec :
    big_atomic_llsc_sc_spec' big_atomicN hazptrN
      big_atomic_llsc_spec_code.(big_atomic_llsc_sc) BigAtomicLLSC IsBigAtomicLLSC LLSCThread;
}.

Global Arguments big_atomic_llsc_spec : clear implicits.
Global Arguments big_atomic_llsc_spec _ {_} _ _ _ _ : assert.
Global Existing Instances BigAtomicLLSC_Timeless IsBigAtomicLLSC_Persistent.
