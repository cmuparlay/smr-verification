From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr hazptr.spec_big_atomic_llsc.
From smr Require Import hazptr.code_llsc_thread hazptr.code_cached_me.

(** Stub: the representation predicates of the Cached-MemoryEfficient LL/SC big atomic are
    [True] and its specifications are admitted. *)

Section cached_me.
  Context (cached_meN hazptrN : namespace) (DISJN : cached_meN ## hazptrN).
  Context `{!heapGS Σ}.

  Variable (hazptr : hazard_pointer_spec Σ hazptrN).

  Definition CachedME (γ : gname) (vs : list val) (ver : nat) : iProp Σ := True.

  Global Instance CachedME_Timeless γ vs ver : Timeless (CachedME γ vs ver).
  Proof. rewrite /CachedME. apply _. Qed.

  Definition IsCachedME (γ γd : gname) (v : val) (n : nat) : iProp Σ := True.

  Global Instance IsCachedME_Persistent γ γd v n : Persistent (IsCachedME γ γd v n).
  Proof. rewrite /IsCachedME. apply _. Qed.

  Definition CachedMEThread (γd : gname) (ctx : val) (link : option (gname * nat)) : iProp Σ := True.

  Lemma cached_me_new_spec :
    big_atomic_llsc_new_spec' cached_meN hazptrN cached_me_new hazptr CachedME IsCachedME.
  Proof. Admitted.

  Lemma cached_me_thread_new_spec :
    big_atomic_llsc_thread_new_spec' cached_meN hazptrN (llsc_thread_new hazptr) hazptr CachedMEThread.
  Proof. Admitted.

  Lemma cached_me_thread_drop_spec :
    big_atomic_llsc_thread_drop_spec' cached_meN (llsc_thread_drop hazptr) CachedMEThread.
  Proof. Admitted.

  Lemma cached_me_ll_spec :
    big_atomic_llsc_ll_spec' cached_meN hazptrN (cached_me_ll hazptr) CachedME IsCachedME CachedMEThread.
  Proof. Admitted.

  Lemma cached_me_sc_spec :
    big_atomic_llsc_sc_spec' cached_meN hazptrN (cached_me_sc hazptr) CachedME IsCachedME CachedMEThread.
  Proof. Admitted.

  Definition cached_me_code : big_atomic_llsc_code := {|
    big_atomic_llsc_new := cached_me_new;
    big_atomic_llsc_thread_new := llsc_thread_new hazptr;
    big_atomic_llsc_thread_drop := llsc_thread_drop hazptr;
    big_atomic_llsc_ll := cached_me_ll hazptr;
    big_atomic_llsc_sc := cached_me_sc hazptr;
  |}.

  Definition cached_me_impl : big_atomic_llsc_spec Σ cached_meN hazptrN DISJN hazptr := {|
    big_atomic_llsc_spec_code := cached_me_code;

    BigAtomicLLSC := CachedME;
    IsBigAtomicLLSC := IsCachedME;
    LLSCThread := CachedMEThread;

    BigAtomicLLSC_Timeless := CachedME_Timeless;
    IsBigAtomicLLSC_Persistent := IsCachedME_Persistent;

    big_atomic_llsc_new_spec := cached_me_new_spec;
    big_atomic_llsc_thread_new_spec := cached_me_thread_new_spec;
    big_atomic_llsc_thread_drop_spec := cached_me_thread_drop_spec;
    big_atomic_llsc_ll_spec := cached_me_ll_spec;
    big_atomic_llsc_sc_spec := cached_me_sc_spec;
  |}.

End cached_me.
