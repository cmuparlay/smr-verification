From iris.base_logic.lib Require Import invariants.
From smr.program_logic Require Import atomic.
From smr.lang Require Import adequacy notation proofmode lib.array.
From smr.hazptr Require Import spec_hazptr_sp code_hazptr_sp proof_hazptr_sp.
From smr.hazptr Require Import spec_big_atomic_llsc spec_big_atomic_llsc_sp.
From smr.hazptr Require Import code_llsc_thread code_cached_wf_llsc_sp.
From smr.hazptr Require Import proof_cached_wf_llsc proof_cached_wf_llsc_sp.
From iris.prelude Require Import options.

Local Set Default Proof Using "All".

(** * An end-to-end space bound

    [p] threads LL/SC a Cached-WaitFree big atomic of size [n] forever, on
    hazard pointers with [H = 2 p] slots (two per thread) and retirers of
    [R = H + 1] entries. Every reachable heap has at most [client_bound p n]
    cells, a bound in [O(p² n)]: the domain ([H]), the source buffer and the
    big atomic ([n + (2 n + 2)]), and per thread its state and retirer (which
    holds at most [R] blocks of [n] cells) plus its LL buffer and SC backup
    ([2 n]). *)

Section code.
  Variables (p n : nat).

  Definition cH : nat := 2 * p.
  Definition cR : nat := S cH.
  Definition chp : hazard_pointer_sp_code := hazptr_sp_code cH cR.

  Definition worker : val :=
    rec: "loop" "ba" "ctx" :=
      let: "v" := cached_wf_llsc_ll_sp chp n "ba" "ctx" in
      cached_wf_llsc_sc_sp chp n "ba" "ctx" "v";;
      Free #n "v";;
      "loop" "ba" "ctx".

  Definition start_worker : val :=
    λ: "ba" "dom",
      let: "ctx" := llsc_thread_new_sp chp "dom" in
      worker "ba" "ctx".

  Definition spawn : val :=
    rec: "spawn" "k" "ba" "dom" :=
      if: "k" = #0 then #()
      else
        Fork (start_worker "ba" "dom");;
        "spawn" ("k" - #1) "ba" "dom".

  Definition client : val :=
    λ: <>,
      let: "dom" := hazard_domain_new_sp cH #() in
      let: "src" := AllocN #n #0 in
      let: "ba" := cached_wf_llsc_new_sp n "src" "dom" in
      Free #n "src";;
      spawn #p "ba" "dom".

  (** The bound *)
  Definition thread_space : nat := (4 + (hp_retirer_size cH cR + cR * n)) + 2 * n.
  Definition client_bound : nat := cH + n + (S (S n) + n) + p * thread_space.
End code.

Definition clhpN := nroot .@ "hazptr_sp".
Definition clbaN := nroot .@ "cwf_sp".
Definition clientN := nroot .@ "client_sp".

Section proof.
  Context `{!heapGS_gen HasLc hsp Σ, !hazptr_spG Σ, !cached_wf_llscG Σ}.
  Context (p n : nat) (Hp : 0 < p) (Hn : 0 < n).

  Lemma cHR : cH p < cR p. Proof. rewrite /cR. lia. Qed.
  Lemma cH0 : 0 < cH p. Proof. rewrite /cH. lia. Qed.

  Definition hz : hazard_pointer_sp_spec Σ clhpN :=
    hazptr_sp_impl clhpN (cH p) (cR p) n cHR cH0.

  Lemma DISJ : clbaN ## clhpN. Proof. solve_ndisj. Qed.

  Definition cba := cached_wf_llsc_sp_impl clbaN clhpN DISJ hz.

  Definition BA_inv (γ : gname) : iProp Σ :=
    inv clientN (∃ vs ver, cba.(BigAtomicLLSCSp) γ vs ver).

  Lemma worker_spec γ γd (l : val) ctx link :
    {{{ BA_inv γ ∗ cba.(IsBigAtomicLLSCSp) γ γd l n ∗ cba.(LLSCThreadSp) γd ctx link ∗ ♢ (2 * n) }}}
      worker p n l ctx
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hba & Hth & Hc) HΦ".
    iLöb as "IH" forall (link).
    wp_lam. wp_pures.
    rewrite (_ : (2 * n)%nat = (n + n)%nat); last lia.
    iDestruct "Hc" as "[Hc1 Hc2]".
    awp_apply (cba.(big_atomic_llsc_sp_ll_spec) with "Hba Hth Hc1").
    iInv "Hinv" as (vs ver) ">Hγ".
    iAaccIntro with "Hγ".
    { iIntros "Hγ !>". iSplitL "Hγ"; first by iExists _, _. iFrame. }
    iIntros (lv) "Hγ !>". iSplitL "Hγ"; first by iExists _, _.
    iIntros "(Hv & †v & %Hlen & Hth)".
    wp_pures.
    awp_apply (cba.(big_atomic_llsc_sp_sc_spec) with "Hba Hth Hv Hc2"); first done.
    iInv "Hinv" as (vs' ver') ">Hγ".
    iAaccIntro with "Hγ".
    { iIntros "Hγ !>". iSplitL "Hγ"; first by iExists _, _. iFrame. }
    iIntros "Hγ !>". iSplitL "Hγ".
    { case_bool_decide; by iExists _, _. }
    iIntros "(Hth & Hv & Hc2)".
    wp_pures.
    wp_apply (wp_free_cred with "[$Hv †v]") as "Hc1"; first by rewrite Hlen.
    { by rewrite Hlen. }
    wp_pures. rewrite Hlen.
    iCombine "Hc1 Hc2" as "Hc". iApply ("IH" with "Hth Hc HΦ").
  Qed.

  Lemma start_worker_spec γ γd (l : val) (d : loc) :
    {{{ BA_inv γ ∗ cba.(IsBigAtomicLLSCSp) γ γd l n ∗ hz.(IsHazardDomainSp) γd d ∗
        ♢ (thread_space p n) }}}
      start_worker p n l #d
    {{{ RET #(); False }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hba & #Hdom & Hc) HΦ".
    wp_lam. wp_pures.
    rewrite /thread_space. iDestruct "Hc" as "[Ht Hc]".
    wp_apply (cba.(big_atomic_llsc_sp_thread_new_spec) with "[$Hdom $Ht]") as (ctx) "Hth".
    wp_pures.
    wp_apply (worker_spec with "[$Hinv $Hba $Hth $Hc] HΦ").
  Qed.

  Lemma spawn_spec γ γd (l : val) (d : loc) (k : nat) :
    {{{ BA_inv γ ∗ cba.(IsBigAtomicLLSCSp) γ γd l n ∗ hz.(IsHazardDomainSp) γd d ∗
        ♢ (k * thread_space p n) }}}
      spawn p n #k l #d
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Hba & #Hdom & Hc) HΦ".
    iInduction k as [|k] "IH".
    { wp_lam. wp_pures. by iApply "HΦ". }
    wp_lam. wp_pures.
    rewrite (_ : (S k * thread_space p n)%nat = (thread_space p n + k * thread_space p n)%nat);
      last lia.
    iDestruct "Hc" as "[Hc1 Hc]".
    wp_apply (wp_fork with "[Hc1]").
    { iNext. wp_apply (start_worker_spec with "[$Hinv $Hba $Hdom $Hc1]"). by iIntros. }
    wp_pures.
    replace (Z.of_nat (S k) - 1)%Z with (Z.of_nat k) by lia.
    iApply ("IH" with "Hc HΦ").
  Qed.

  Lemma client_spec :
    {{{ ♢ (client_bound p n) }}} client p n #() {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". rewrite /client_bound.
    iDestruct "Hc" as "[[[HcH Hcsrc] Hcba] Hcth]".
    wp_lam.
    wp_apply (hz.(hazard_domain_new_sp_spec) with "HcH") as (γd d) "#Hdom".
    wp_pures.
    wp_apply (wp_allocN_cred with "[Hcsrc]") as (src) "[†src Hsrc]"; first lia.
    { by rewrite Nat2Z.id. }
    wp_pures. rewrite Nat2Z.id.
    wp_apply (cba.(big_atomic_llsc_sp_new_spec) with "[$Hdom $Hsrc $Hcba]")
      as (γ ba) "(#Hba & Hγ & Hsrc)"; [lia|simpl; lia|by rewrite length_replicate|].
    wp_pures.
    iMod (inv_alloc clientN _ (∃ vs ver, cba.(BigAtomicLLSCSp) γ vs ver) with "[Hγ]") as "#Hinv".
    { iNext. by iExists _, _. }
    wp_free; [by rewrite length_replicate|by rewrite length_replicate|].
    wp_pures.
    wp_apply (spawn_spec with "[$Hinv $Hba $Hdom $Hcth] HΦ").
  Qed.
End proof.

Definition clientΣ : gFunctors := #[heapΣ; hazptr_spΣ; cached_wf_llscΣ].

(** Every heap that [client p n] reaches from the empty heap has at most
    [client_bound p n] cells. *)
Theorem client_space_bound (p n : nat) σ :
  0 < p → 0 < n → σ.(heap) = ∅ →
  ∀ t2 σ2, rtc erased_step ([client p n #()], σ) (t2, σ2) →
    size σ2.(heap) ≤ client_bound p n.
Proof.
  intros Hp Hn Hσ.
  apply (heap_space_adequacy clientΣ NotStuck (client p n #()) σ (λ _, True)).
  { rewrite Hσ map_size_empty. lia. }
  iIntros (?) "_ Hc". rewrite Hσ map_size_empty Nat.sub_0_r.
  iApply (client_spec with "Hc"); [done|done|by iIntros].
Qed.
