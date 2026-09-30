From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.hazptr Require Import spec_hazptr_sp spec_big_atomic_llsc.
From iris.prelude Require Import options.

(** * LL/SC big atomics with space costs

    The specification of [spec_big_atomic_llsc], in a heap that may count
    space, on top of hazard pointers with bounded space ([spec_hazptr_sp]).
    Every operation says what it costs in space credits:

    - [new] costs [llsc_new_cost n] for a big atomic of size [n], which must fit
      in the blocks the hazard domain can retire ([n ≤ hp_kmax]);
    - [thread_new] costs [llsc_thread_cost], and [thread_drop] gives back
      [llsc_thread_refund] of it;
    - [LL] costs [n], the size of the buffer it returns, which the caller gets
      back by freeing it;
    - [SC] needs [llsc_sc_cost n] credits while it runs, and gives them all
      back.

    So the space held by [n'] big atomics of size [n] and [p] threads is at most
    [n' * llsc_new_cost n + p * llsc_thread_cost], plus what the operations in
    progress hold, plus the domain's [hp_domain_cost]. *)

Section spec.
Context `{!heapGS_gen HasLc hsp Σ}.
Context (big_atomicN : namespace) (hazptrN : namespace) (DISJN : big_atomicN ## hazptrN).
Variables
  (big_atomic_new : nat → val)
  (big_atomic_thread_new : val)
  (big_atomic_thread_drop : val)
  (big_atomic_ll : nat → val)
  (big_atomic_sc : nat → val).
Variables
  (hazptr : hazard_pointer_sp_spec Σ hazptrN)
  (new_cost sc_cost : nat → nat) (thread_cost thread_refund : nat)
  (BigAtomic : BigAtomicLLSCT Σ)
  (IsBigAtomic : IsBigAtomicLLSCT Σ big_atomicN)
  (LLSCThread : LLSCThreadT Σ big_atomicN).

Definition big_atomic_llsc_sp_new_spec' : Prop :=
  ∀ γd d n l dq vs,
    0 < n → n ≤ hazptr.(hp_kmax) → length vs = n →
      {{{ hazptr.(IsHazardDomainSp) γd d ∗ l ↦∗{dq} vs ∗ ♢ (new_cost n) }}}
        big_atomic_new n #l #d
      {{{ γ ba, RET ba; IsBigAtomic γ γd ba n ∗ BigAtomic γ vs 0 ∗ l ↦∗{dq} vs }}}.

Definition big_atomic_llsc_sp_thread_new_spec' : Prop :=
  ∀ γd d,
    {{{ hazptr.(IsHazardDomainSp) γd d ∗ ♢ thread_cost }}}
      big_atomic_thread_new #d
    {{{ ctx, RET ctx; LLSCThread γd ctx None }}}.

Definition big_atomic_llsc_sp_thread_drop_spec' : Prop :=
  ∀ γd ctx link,
    {{{ LLSCThread γd ctx link }}}
      big_atomic_thread_drop ctx
    {{{ RET #(); ♢ thread_refund }}}.

Definition big_atomic_llsc_sp_ll_spec' : Prop :=
  ⊢ ∀ γ γd ba n ctx link,
    IsBigAtomic γ γd ba n -∗ LLSCThread γd ctx link -∗ ♢ n -∗
      <<{ ∀∀ vs ver, BigAtomic γ vs ver }>>
        big_atomic_ll n ba ctx @ ⊤,(↑big_atomicN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
      <<{ ∃∃ l, BigAtomic γ vs ver
        | RET #l; l ↦∗ vs ∗ †l…n ∗ ⌜length vs = n⌝ ∗ LLSCThread γd ctx (Some (γ, ver)) }>>.

Definition big_atomic_llsc_sp_sc_spec' : Prop :=
  ∀ γ γd ba n ctx ver (l_desired : loc) (dq : dfrac) (desired : list val),
    length desired = n →
      IsBigAtomic γ γd ba n -∗ LLSCThread γd ctx (Some (γ, ver)) -∗ l_desired ↦∗{dq} desired -∗
      ♢ (sc_cost n) -∗
        <<{ ∀∀ actual ver', BigAtomic γ actual ver' }>>
          big_atomic_sc n ba ctx #l_desired @ ⊤,(↑big_atomicN ∪ ↑(ptrsN hazptrN)),↑(mgmtN hazptrN)
        <<{ if bool_decide (ver' = ver) then
              BigAtomic γ desired (S ver')
            else
              BigAtomic γ actual ver'
          | RET #(bool_decide (ver' = ver));
              LLSCThread γd ctx (if bool_decide (ver' = ver) then None else Some (γ, ver)) ∗
              l_desired ↦∗{dq} desired ∗ ♢ (sc_cost n) }>>.

End spec.

Record big_atomic_llsc_sp_spec {Σ} `{!heapGS_gen HasLc hsp Σ} {big_atomicN hazptrN : namespace}
    {DISJN : big_atomicN ## hazptrN}
    {hazptr : hazard_pointer_sp_spec Σ hazptrN}
  : Type := BigAtomicLLSCSpSpec {
  big_atomic_llsc_sp_spec_code :> big_atomic_llsc_code;

  llsc_new_cost : nat → nat;
  llsc_sc_cost : nat → nat;
  llsc_thread_cost : nat;
  llsc_thread_refund : nat;

  BigAtomicLLSCSp : BigAtomicLLSCT Σ;
  IsBigAtomicLLSCSp : IsBigAtomicLLSCT Σ big_atomicN;
  LLSCThreadSp : LLSCThreadT Σ big_atomicN;

  BigAtomicLLSCSp_Timeless : ∀ γ vs ver, Timeless (BigAtomicLLSCSp γ vs ver);
  IsBigAtomicLLSCSp_Persistent : ∀ γ γd l n, Persistent (IsBigAtomicLLSCSp γ γd l n);

  big_atomic_llsc_sp_new_spec :
    big_atomic_llsc_sp_new_spec' big_atomicN hazptrN
      big_atomic_llsc_sp_spec_code.(big_atomic_llsc_new) hazptr llsc_new_cost
      BigAtomicLLSCSp IsBigAtomicLLSCSp;
  big_atomic_llsc_sp_thread_new_spec :
    big_atomic_llsc_sp_thread_new_spec' big_atomicN hazptrN
      big_atomic_llsc_sp_spec_code.(big_atomic_llsc_thread_new) hazptr llsc_thread_cost
      LLSCThreadSp;
  big_atomic_llsc_sp_thread_drop_spec :
    big_atomic_llsc_sp_thread_drop_spec' big_atomicN
      big_atomic_llsc_sp_spec_code.(big_atomic_llsc_thread_drop) llsc_thread_refund LLSCThreadSp;
  big_atomic_llsc_sp_ll_spec :
    big_atomic_llsc_sp_ll_spec' big_atomicN hazptrN
      big_atomic_llsc_sp_spec_code.(big_atomic_llsc_ll) BigAtomicLLSCSp IsBigAtomicLLSCSp
      LLSCThreadSp;
  big_atomic_llsc_sp_sc_spec :
    big_atomic_llsc_sp_sc_spec' big_atomicN hazptrN
      big_atomic_llsc_sp_spec_code.(big_atomic_llsc_sc) llsc_sc_cost BigAtomicLLSCSp
      IsBigAtomicLLSCSp LLSCThreadSp;
}.

Global Arguments big_atomic_llsc_sp_spec : clear implicits.
Global Arguments big_atomic_llsc_sp_spec _ {_ _} _ _ _ _ : assert.
Global Existing Instances BigAtomicLLSCSp_Timeless IsBigAtomicLLSCSp_Persistent.
