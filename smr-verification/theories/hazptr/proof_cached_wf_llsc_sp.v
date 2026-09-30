From iris.algebra Require Import auth gmap gset agree.
From iris.base_logic.lib Require Import invariants ghost_var mono_nat token.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation lib.array.
From smr.base_logic Require Import lib.mono_list.
From iris.prelude Require Import options.
From Stdlib Require Import ZArith.Zquot.

From smr Require Import hazptr.spec_hazptr_sp hazptr.spec_big_atomic_llsc hazptr.spec_big_atomic_llsc_sp.
From smr Require Import hazptr.code_llsc_thread hazptr.code_cached_wf_llsc_sp.
From smr Require Import hazptr.proof_cached_wf_llsc.

(** * Cached-WaitFree LL/SC with space credits

    The proof of [proof_cached_wf_llsc], redone in a heap that may count space
    ([hsp]), on hazard pointers with bounded space ([spec_hazptr_sp]). The
    history, the invariant and the ghost state are those of
    [proof_cached_wf_llsc] (whose pure lemmas and ghost lemmas are reused). The
    space costs:

    - A big atomic of size [n] is [n + 2] words (sequence number, backup
      pointer, cache) plus its installed backup of [n] words, so [new] costs
      [2 * n + 2]. The invariant holds no credits: the installed backup was
      paid for by the SC that allocated it.
    - An SC needs [n] credits for its new backup. If the backup is installed,
      the retirer gives back the [n] credits of the backup it replaces;
      otherwise it frees its own backup. Either way the SC returns [n]
      credits.
    - An LL costs [n], the buffer it returns.
    - The thread-local state is four words and a retirer. *)

Local Existing Instances cached_wf_llsc_absG cached_wf_llsc_histG cached_wf_llsc_seqG
  cached_wf_llsc_valG cached_wf_llsc_unlG cached_wf_llsc_lkG cached_wf_llsc_tokenG.

Section cached_wf_llsc_sp.
  Context (cached_wf_llscN hazptrN : namespace) (DISJN : cached_wf_llscN ## hazptrN).
  Context `{!heapGS_gen HasLc hsp Σ, !cached_wf_llscG Σ}.
  Notation iProp := (iProp Σ).

  Variable (hazptr : hazard_pointer_sp_spec Σ hazptrN).

  (** ** The invariant *)

  Definition llsc_inv (γs : llsc_names) (γd : gname) (l : loc) (n : nat) : iProp :=
    ∃ (sq t : nat) (hist : list entry) (ec : entry) (c : list val) (lk : nat)
      (validated : gset nat) (unlocks : gmap nat nat),
      (l +ₗ seqnum_off) ↦ #sq ∗
      (l +ₗ backup_off) ↦ #(Some (Loc.blk_to_loc ec.(e_blk)) &ₜ t) ∗
      γs.(γ_abs) ↪VAR{#1/2} (ec.(e_val), length hist - 1) ∗
      hazptr.(ManagedSp) γd ec.(e_blk) ec.(e_name) n (node ec.(e_val)) ∗
      mono_list_auth_own γs.(γ_hist) 1 hist ∗
      ([∗ list] e ∈ hist, token e.(e_name)) ∗
      γs.(γ_seq) ↪●MN sq ∗
      (l +ₗ cache_off) ↦∗{#1/2} c ∗
      γs.(γ_lk) ↪VAR{#1/2} lk ∗
      (if Nat.even sq then γs.(γ_lk) ↪VAR{#1/2} lk ∗ (l +ₗ cache_off) ↦∗{#1/2} c
       else ⌜sq = S lk⌝) ∗
      validated_auth γs.(γ_val) validated ∗
      unlocks_auth γs.(γ_unl) unlocks ∗
      ⌜llsc_wf n sq t hist ec c validated unlocks⌝.

  (** ** Representation predicates *)

  Definition CachedWFLLSC (γ : gname) (vs : list val) (ver : nat) : iProp :=
    ∃ γs, ⌜γ = encode γs⌝ ∗ γs.(γ_abs) ↪VAR{#1/2} (vs, ver).

  Global Instance CachedWFLLSC_Timeless γ vs ver : Timeless (CachedWFLLSC γ vs ver).
  Proof. apply _. Qed.

  (** The big atomic records that its backups can be retired. *)
  Definition IsCachedWFLLSC (γ γd : gname) (v : val) (n : nat) : iProp :=
    ∃ γs (l : loc), ⌜γ = encode γs⌝ ∗ ⌜v = #l⌝ ∗ ⌜0 < n⌝ ∗ ⌜n ≤ hazptr.(hp_kmax)⌝ ∗
      inv cached_wf_llscN (llsc_inv γs γd l n).

  Global Instance IsCachedWFLLSC_Persistent γ γd v n : Persistent (IsCachedWFLLSC γ γd v n).
  Proof. apply _. Qed.

  (** What an LL leaves for the next SC: the version it read, and either the
      sequence number of that version (fast path) or its protected backup
      pointer (slow path). In both cases, it knows that the version has been
      validated if it read an unmarked backup pointer. *)
  Definition link_wit (γ : gname) (ver : nat) (et : val) (st1 : shield_state Σ) : iProp :=
    ∃ γs e, ⌜γ = encode γs⌝ ∗ mono_list_idx_own γs.(γ_hist) ver e ∗
      ((⌜et = #(None &ₜ e.(e_seq))⌝ ∗ validated_frag γs.(γ_val) ver) ∨
       (∃ (tp : nat) sz, ⌜et = #(Some (Loc.blk_to_loc e.(e_blk)) &ₜ tp)⌝ ∗
          ⌜st1 = Validated e.(e_blk) e.(e_name) (node e.(e_val)) sz⌝ ∗
          (⌜tp = 1⌝ ∨ ⌜tp = 0⌝ ∗ validated_frag γs.(γ_val) ver))).

  Definition CachedWFLLSCThread (γd : gname) (ctx : val) (link : option (gname * nat)) : iProp :=
    ∃ (c h1 h2 d r : loc) (et : val) (st1 st2 : shield_state Σ),
      ⌜ctx = #c⌝ ∗ c ↦∗ [ #h1; #h2; et; #r ] ∗ †c…4 ∗ hazptr.(IsHazardDomainSp) γd d ∗
      hazptr.(ShieldSp) γd h1 st1 ∗ hazptr.(ShieldSp) γd h2 st2 ∗ hazptr.(Retirer) γd r ∗
      match link with None => True | Some (γ, ver) => link_wit γ ver et st1 end.

  (** ** Copying the cache *)

  (** What an LL knows about the cache when it reads [seqnum] at [s1]: if [s1]
      is even, the unlock at [s1] copied the value of version [cv] into the
      cache. *)
  Definition cache_snap (γs : llsc_names) (s1 : nat) (oc : option (nat * entry)) : iProp :=
    match oc with
    | Some (cv, e) =>
        ⌜Nat.even s1 = true⌝ ∗ unlocks_frag γs.(γ_unl) s1 cv ∗ mono_list_idx_own γs.(γ_hist) cv e
    | None => True
    end.

  Global Instance cache_snap_persistent γs s1 oc : Persistent (cache_snap γs s1 oc).
  Proof. destruct oc as [[??]|]; apply _. Qed.

  (** After copying [vs] from offset [i] of the cache: either [seqnum] changed
      since [s1], or [vs] is (the corresponding part of) the value of [cv]. *)
  Definition cache_good (γs : llsc_names) (s1 : nat) (oc : option (nat * entry)) (i : nat) (vs : list val) : iProp :=
    match oc with
    | Some (cv, e) => γs.(γ_seq) ↪◯MN (S s1) ∨ ⌜vs = take (length vs) (drop i e.(e_val))⌝
    | None => True
    end.

  Lemma wp_copy_cache γs γd l n (dst : loc) (i : nat) vdst s1 oc :
    i + length vdst = n →
    inv cached_wf_llscN (llsc_inv γs γd l n) -∗
    γs.(γ_seq) ↪◯MN s1 -∗
    cache_snap γs s1 oc -∗
    {{{ dst ↦∗ vdst }}}
      array_copy_to #dst #(l +ₗ cache_off +ₗ i) #(length vdst)
    {{{ vs', RET #(); dst ↦∗ vs' ∗ ⌜length vs' = length vdst⌝ ∗ cache_good γs s1 oc i vs' }}}.
  Proof.
    iIntros (Hlen) "#Hinv #Hlb #Hsnap %Φ !> Hdst HΦ".
    iInduction vdst as [|v0 vdst] "IH" forall (dst i Hlen Φ).
    - wp_rec. wp_pures. iApply ("HΦ" $! []). iModIntro. iFrame. iSplit; first done.
      destruct oc as [[cv e]|]; last done. by iRight.
    - wp_rec. wp_pures.
      iDestruct (array_cons with "Hdst") as "[Hv0 Hdst]".
      wp_bind (! _)%E.
      iInv "Hinv" as (sq t hist ec c lk validated unlocks)
        "(Hseq & Hbk & Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & Hlk & Hif & >Hval & >Hunl & >%Hwf)" "Hcl".
      simpl in Hlen.
      assert (is_Some (c !! i)) as [v Hv].
      { apply lookup_lt_is_Some. rewrite (wf_cache_len _ _ _ _ _ _ _ _ Hwf). lia. }
      wp_apply (wp_load_offset with "Hcache") as "Hcache"; first done.
      iDestruct (mono_nat_auth_lb_own_valid with "Hsq Hlb") as %[_ Hle].
      iAssert (match oc with
               | Some (cv, e) => γs.(γ_seq) ↪◯MN (S s1) ∨ ⌜e.(e_val) !! i = Some v⌝
               | None => True
               end)%I as "#Hgood".
      { destruct oc as [[cv e]|]; last done.
        destruct (decide (sq = s1)) as [->|Hne].
        - iDestruct "Hsnap" as "(%Heven & Hfrag & Hidx)".
          iDestruct (unlocks_lookup with "Hunl Hfrag") as %Hcv.
          iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He.
          destruct (wf_cache _ _ _ _ _ _ _ _ Hwf Heven) as (cv' & e' & Hcv' & He' & ->).
          simplify_eq. iRight. done.
        - iLeft. iApply (mono_nat_lb_own_le with "[Hsq]"); last by iApply mono_nat_lb_own_get.
          lia. }
      iMod ("Hcl" with "[-Hv0 Hdst HΦ]") as "_".
      { iExists sq, t, hist, ec, c, lk, validated, unlocks. by iFrame. }
      iModIntro. wp_store. wp_pures.
      rewrite Loc.add_assoc.
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_sub /=; last lia.
      rewrite Nat.sub_0_r -Nat2Z.inj_add.
      wp_apply ("IH" with "[] Hdst"); first (iPureIntro; lia).
      iIntros (vs') "(Hdst & %Hlen' & #Hgood')".
      iApply ("HΦ" $! (v :: vs')). iFrame.
      iSplit; first (iPureIntro; simpl; lia).
      destruct oc as [[cv e]|]; last done.
      iDestruct "Hgood" as "[$|%Hvi]".
      iDestruct "Hgood'" as "[$|%Hvs']".
      iRight. iPureIntro. simpl.
      rewrite Nat.add_1_r in Hvs'.
      rewrite (drop_S _ _ _ Hvi) /=. by rewrite -Hvs'.
  Qed.

  Lemma wp_clone_cache γs γd l n s1 oc :
    0 < n →
    inv cached_wf_llscN (llsc_inv γs γd l n) -∗
    γs.(γ_seq) ↪◯MN s1 -∗
    cache_snap γs s1 oc -∗
    {{{ ♢ n }}}
      array_clone #(l +ₗ cache_off) #n
    {{{ (dst : blk) vs', RET #dst;
        dst ↦∗ vs' ∗ †dst…n ∗ ⌜length vs' = n⌝ ∗ cache_good γs s1 oc 0 vs' }}}.
  Proof.
    iIntros (Hpos) "#Hinv #Hlb #Hsnap %Φ !> Hc HΦ".
    wp_lam. wp_pures.
    wp_apply (wp_allocN_cred with "[Hc]") as (dst) "[†dst Hdst]"; first lia.
    { by rewrite Nat2Z.id. }
    wp_pures. rewrite Nat2Z.id.
    rewrite -{1}(Loc.add_0 (l +ₗ cache_off)).
    assert (Z.of_nat n = Z.of_nat (length (replicate n #()))) as ->
      by rewrite length_replicate //.
    change 0%Z with (Z.of_nat 0).
    wp_apply (wp_copy_cache with "Hinv Hlb Hsnap Hdst").
    { by rewrite length_replicate. }
    iIntros (vs') "(Hdst & %Hlen & Hgood)".
    wp_pures. iApply "HΦ". iFrame "Hdst †dst Hgood".
    iPureIntro. by rewrite Hlen length_replicate.
  Qed.

  (** ** Copying a protected backup *)

  Lemma wp_copy_protected_off (dst : loc) (src : blk) vdst vsrc γd s γ_src (i : nat) :
    i + length vdst = length vsrc →
    {{{ dst ↦∗ vdst ∗ hazptr.(ShieldSp) γd s (Validated src γ_src (node vsrc) (length vsrc)) }}}
      array_copy_to #dst #(src +ₗ i) #(length vdst)
    {{{ RET #(); dst ↦∗ drop i vsrc ∗ hazptr.(ShieldSp) γd s (Validated src γ_src (node vsrc) (length vsrc)) }}}.
  Proof.
    iIntros (Hlen Φ) "[Hdst S] HΦ".
    iInduction vdst as [|v vdst] "IH" forall (dst i Hlen Φ).
    { simplify_list_eq. wp_rec. wp_pures. iApply "HΦ".
      iModIntro. replace i with (length vsrc) in * by lia.
      rewrite drop_all. iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv Hvdst]".
    simplify_list_eq. wp_rec. wp_pures.
    wp_bind (! _)%E.
    wp_apply (shield_read_sp with "S") as (? v') "(S & -> & %EQ)"; [solve_ndisj|lia|].
    wp_store. wp_pures.
    rewrite Loc.add_assoc.
    change 1%Z with (Z.of_nat 1).
    rewrite -Nat2Z.inj_sub /=; last lia.
    rewrite Nat.sub_0_r -Nat2Z.inj_add Nat.add_1_r.
    wp_apply ("IH" with "[] [$Hvdst] [$S]").
    { iPureIntro. lia. }
    iIntros "[Hvdst S]".
    iApply "HΦ".
    iPoseProof (array_cons with "[$Hv $Hvdst]") as "Hvdst".
    assert (v' :: drop (S i) vsrc = drop i vsrc) as ->.
    { by rewrite (drop_S _ _ _ EQ). }
    iFrame.
  Qed.

  Lemma wp_copy_protected (dst : loc) (src : blk) vdst vsrc γd s γ_src n :
    length vdst = n → length vsrc = n →
    {{{ dst ↦∗ vdst ∗ hazptr.(ShieldSp) γd s (Validated src γ_src (node vsrc) n) }}}
      array_copy_to #dst #src #n
    {{{ RET #(); dst ↦∗ vsrc ∗ hazptr.(ShieldSp) γd s (Validated src γ_src (node vsrc) n) }}}.
  Proof.
    iIntros (Hlen_dst Hlen_src Φ) "[Hdst S] HΦ".
    rewrite -(Loc.add_0 src). change 0%Z with (Z.of_nat O). subst n.
    iEval (rewrite -Hlen_src) in "S HΦ".
    wp_apply (wp_copy_protected_off with "[$Hdst $S]"); first lia.
    iIntros "[Hdst S]".
    rewrite drop_0.
    iApply ("HΦ" with "[$]").
  Qed.

  (** ** Writing the cache while holding the lock *)

  Lemma lk_excl γ (a b c : nat) :
    γ ↪VAR{#1/2} a -∗ γ ↪VAR{#1/2} b -∗ γ ↪VAR{#1/2} c -∗ False.
  Proof.
    iIntros "Ha Hb Hc".
    iCombine "Ha Hb" as "Hab".
    iDestruct (ghost_var_valid_2 with "Hab Hc") as %[Hv _].
    rewrite dfrac_op_own dfrac_valid_own in Hv.
    by apply Qp.not_add_le_l in Hv.
  Qed.

  Lemma wp_write_cache γs γd l n (src : loc) dq (vs : list val) (i k s : nat) c :
    length vs = n → i + k = n → length c = n → take i c = take i vs →
    inv cached_wf_llscN (llsc_inv γs γd l n) -∗
    {{{ γs.(γ_lk) ↪VAR{#1/2} s ∗ (l +ₗ cache_off) ↦∗{#1/2} c ∗ src ↦∗{dq} vs }}}
      array_copy_to #(l +ₗ cache_off +ₗ i) #(src +ₗ i) #k
    {{{ RET #(); γs.(γ_lk) ↪VAR{#1/2} s ∗ (l +ₗ cache_off) ↦∗{#1/2} vs ∗ src ↦∗{dq} vs }}}.
  Proof.
    iIntros (Hlen Hik Hlenc Htake) "#Hinv %Φ !> (Hlk & Hc & Hsrc) HΦ".
    iInduction k as [|k] "IH" forall (i c Hik Hlenc Htake).
    { wp_rec. wp_pures. iApply "HΦ". iModIntro. iFrame.
      rewrite !take_ge in Htake; [|lia..]. by subst c. }
    wp_rec. wp_pures.
    assert (is_Some (vs !! i)) as [v Hv] by (apply lookup_lt_is_Some; lia).
    wp_apply (wp_load_offset with "Hsrc") as "Hsrc"; first done.
    wp_bind (_ <- _)%E.
    iInv "Hinv" as (sq t hist ec c' lk validated unlocks)
      "(Hseq & Hbk & Habs & Hman & Hhist & Htoks & Hsq & >Hcache & >Hlk' & Hif & Hval & Hunl & >%Hwf)" "Hcl".
    destruct (Nat.even sq) eqn:Heven.
    { iDestruct "Hif" as "[>Hlk'' _]".
      iDestruct (lk_excl with "Hlk Hlk' Hlk''") as %[]. }
    iDestruct "Hif" as ">%Hsq".
    iDestruct (array_agree with "Hc Hcache") as %<-.
    { by rewrite (wf_cache_len _ _ _ _ _ _ _ _ Hwf). }
    iCombine "Hc Hcache" as "Hc".
    wp_apply (wp_store_offset with "Hc") as "Hc".
    { apply lookup_lt_is_Some. lia. }
    iDestruct "Hc" as "[Hc Hcache]".
    iMod ("Hcl" with "[-Hlk Hc Hsrc HΦ]") as "_".
    { iExists sq, t, hist, ec, (<[i:=v]> c), lk, validated, unlocks.
      rewrite Heven. iFrame. iPureIntro. split; first done.
      apply (wf_write _ _ _ _ _ c); [done| |by rewrite length_insert].
      by rewrite -Nat.negb_even Heven. }
    iModIntro. wp_pures.
    rewrite Loc.add_assoc (Loc.add_assoc src).
    change 1%Z with (Z.of_nat 1).
    rewrite -!Nat2Z.inj_add.
    replace (Z.of_nat (S k) - Z.of_nat 1)%Z with (Z.of_nat k) by lia.
    wp_apply ("IH" with "[%] [%] [%] Hlk Hc Hsrc HΦ").
    - lia.
    - by rewrite length_insert.
    - rewrite Nat.add_1_r (take_S_r _ _ v); last by rewrite list_lookup_insert_eq; [|lia].
      rewrite (take_S_r vs _ v) //.
      rewrite take_insert decide_False; last lia.
      by rewrite Htake.
  Qed.

  Lemma wp_write_cache0 γs γd l n (src : loc) dq (vs : list val) (s : nat) c :
    length vs = n → length c = n →
    inv cached_wf_llscN (llsc_inv γs γd l n) -∗
    {{{ γs.(γ_lk) ↪VAR{#1/2} s ∗ (l +ₗ cache_off) ↦∗{#1/2} c ∗ src ↦∗{dq} vs }}}
      array_copy_to #(l +ₗ cache_off) #src #n
    {{{ RET #(); γs.(γ_lk) ↪VAR{#1/2} s ∗ (l +ₗ cache_off) ↦∗{#1/2} vs ∗ src ↦∗{dq} vs }}}.
  Proof.
    iIntros (Hlen Hlenc) "#Hinv".
    iPoseProof (wp_write_cache γs γd l n src dq vs 0 n s c with "Hinv") as "Hwp"; [done..|].
    by rewrite /= !Loc.add_0.
  Qed.

  Lemma tagged_blk_eq (b b' : blk) (t t' : Z) :
    Some (Loc.blk_to_loc b) &ₜ t = Some (Loc.blk_to_loc b') &ₜ t' ↔ b = b' ∧ t = t'.
  Proof.
    split.
    - rewrite /Loc.to_tagged_loc. intros H. by injection H as -> ->.
    - by intros [-> ->].
  Qed.

  (** ** Validating an installed backup *)

  Lemma wp_try_validate γs γd l n (seq : nat) (l_desired : loc) dq desired (ptr : blk) γp τ v h2 sz :
    length desired = n → seq + 2 ≤ τ →
    inv cached_wf_llscN (llsc_inv γs γd l n) -∗
    mono_list_idx_own γs.(γ_hist) v (Entry γp ptr desired τ) -∗
    {{{ l_desired ↦∗{dq} desired ∗ hazptr.(ShieldSp) γd h2 (Validated ptr γp (node desired) sz) }}}
      try_validate_sp n #l #seq #l_desired #(Some (Loc.blk_to_loc ptr) &ₜ 1)
    {{{ RET #(); l_desired ↦∗{dq} desired ∗ hazptr.(ShieldSp) γd h2 (Validated ptr γp (node desired) sz) }}}.
  Proof.
    iIntros (Hlen Hτ) "#Hinv #Hidx %Φ !> [Hdes S] HΦ".
    wp_lam. wp_pures.
    rewrite Z_rem_2_of_nat.
    destruct (Nat.even seq) eqn:Heven; last first.
    { wp_pures. by iApply "HΦ"; iFrame. }
    wp_pures.
    (* [seq = !seqnum] *)
    wp_bind (! _)%E.
    iInv "Hinv" as (sq t hist ec c lk validated unlocks)
      "(>Hseq & Hbk & Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf)" "Hcl".
    rewrite Loc.add_0. wp_load.
    iMod ("Hcl" with "[-Hdes S HΦ]") as "_".
    { iExists sq, t, hist, ec, c, lk, validated, unlocks. rewrite Loc.add_0. by iFrame. }
    iModIntro.
    destruct (decide (sq = seq)) as [->|Hne]; last first.
    { wp_pures. rewrite bool_decide_eq_false_2; last (intros [=]; lia).
      wp_pures. iApply "HΦ". by iFrame. }
    clear t hist ec c lk validated unlocks Hwf.
    wp_pures.
    (* Take the lock *)
    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as (sq1 t1 hist1 ec1 c1 lk1 validated1 unlocks1)
      "(>Hseq & Hbk & Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf1)" "Hcl".
    rewrite Loc.add_0.
    destruct (decide (sq1 = seq)) as [->|Hne]; last first.
    { wp_cmpxchg_fail.
      iMod ("Hcl" with "[-Hdes S HΦ]") as "_".
      { iExists sq1, t1, hist1, ec1, c1, lk1, validated1, unlocks1. rewrite Loc.add_0. by iFrame. }
      iModIntro. wp_pures. iApply "HΦ". by iFrame. }
    wp_cmpxchg_suc.
    iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %Hv.
    destruct (wf_lock_cond _ _ _ _ _ _ _ _ _ _ Hwf1 Hv) as (-> & Hτeq & Hecseq); first (simpl; lia).
    simpl in Hτeq.
    rewrite Heven.
    iDestruct "Hif" as "[Hlk' Hcache']".
    iMod (ghost_var_update_halves seq with "Hlk Hlk'") as "[Hlk Hlk']".
    iMod (mono_nat_own_update (seq + 1) with "Hsq") as "[Hsq _]"; first lia.
    iMod ("Hcl" with "[-Hdes S HΦ Hlk' Hcache']") as "_".
    { iExists (seq + 1), 1, hist1, ec1, c1, seq, validated1, unlocks1.
      rewrite Loc.add_0 Nat2Z.inj_add Nat.even_add Heven /=. iFrame.
      iPureIntro. split; [lia|by apply wf_lock]. }
    iModIntro. wp_pures.
    (* Copy [desired] into the cache *)
    wp_apply (wp_write_cache0 with "Hinv [$Hlk' $Hcache' $Hdes]").
    { done. }
    { by rewrite (wf_cache_len _ _ _ _ _ _ _ _ Hwf1). }
    iIntros "(Hlk' & Hcache' & Hdes)".
    wp_pures.
    (* Unlock *)
    wp_bind (_ <- _)%E.
    iInv "Hinv" as (sq2 t2 hist2 ec2 c2 lk2 validated2 unlocks2)
      "(>Hseq & Hbk & Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf2)" "Hcl".
    destruct (Nat.even sq2) eqn:Heven2.
    { iDestruct "Hif" as "[>Hlk'' _]". iDestruct (lk_excl with "Hlk Hlk' Hlk''") as %[]. }
    iDestruct "Hif" as ">%Hsq2".
    iDestruct (ghost_var_agree with "Hlk Hlk'") as %->.
    subst sq2.
    iDestruct (array_agree with "Hcache Hcache'") as %->.
    { by rewrite (wf_cache_len _ _ _ _ _ _ _ _ Hwf2). }
    rewrite Loc.add_0. wp_store.
    iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %Hv2.
    replace (S seq) with (seq + 1) in Hwf2 by lia.
    destruct (wf_unlock _ _ _ _ _ _ _ _ _ _ Hwf2 Heven Hv2 eq_refl) as [-> Hwf2']; first (simpl; lia).
    iMod (unlocks_insert _ _ (seq + 2) v with "Hunl") as "[Hunl #Hunl_frag]".
    { apply not_elem_of_dom. intros ?%(wf_unl_dom _ _ _ _ _ _ _ _ Hwf2). lia. }
    iMod (mono_nat_own_update (seq + 2) with "Hsq") as "[Hsq #Hlb2]"; first lia.
    iMod ("Hcl" with "[-Hdes S HΦ]") as "_".
    { iExists (seq + 2), 1, hist2, ec2, desired, seq, validated2, _.
      assert (Nat.even (seq + 2) = true) as Heven2' by (rewrite Nat.even_add Heven //).
      rewrite Loc.add_0 Nat2Z.inj_add Heven2' /=. by iFrame. }
    iModIntro. wp_pures.
    (* Unmark the backup pointer *)
    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as (sq3 t3 hist3 ec3 c3 lk3 validated3 unlocks3)
      "(>Hseq & >Hbk & Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf3)" "Hcl".
    destruct (decide (Some (Loc.blk_to_loc ec3.(e_blk)) &ₜ t3 = Some (Loc.blk_to_loc ptr) &ₜ 1))
      as [[Hblk Ht3]%tagged_blk_eq|Hne]; last first.
    { wp_cmpxchg_fail.
      iMod ("Hcl" with "[-Hdes S HΦ]") as "_".
      { iExists sq3, t3, hist3, ec3, c3, lk3, validated3, unlocks3. by iFrame. }
      iModIntro. wp_pures. iApply "HΦ". by iFrame. }
    wp_cmpxchg_suc.
    rewrite Hblk.
    iDestruct (hazptr.(shield_managed_agree_sp) with "S Hman") as %Hγ.
    iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %Hv3.
    pose proof (wf_current _ _ _ _ _ _ _ _ Hwf3) as Hcur3.
    assert (v = length hist3 - 1) as ->.
    { eapply (NoDup_lookup (e_name <$> hist3)); [apply Hwf3| |].
      - by rewrite list_lookup_fmap Hv3.
      - rewrite list_lookup_fmap Hcur3 /=. by rewrite Hγ. }
    rewrite Hcur3 in Hv3. injection Hv3 as ->.
    simpl in *.
    iDestruct (mono_nat_auth_lb_own_valid with "Hsq Hlb2") as %[_ Hle3].
    pose proof (wf_seq_bound _ _ _ _ _ _ _ _ Hwf3) as Hbound3. simpl in Hbound3.
    assert (sq3 = seq + 2) as -> by lia.
    iDestruct (unlocks_lookup with "Hunl Hunl_frag") as %Hunl3.
    iMod (validated_insert _ _ (length hist3 - 1) with "Hval") as "[Hval _]".
    assert (t3 = 1) as -> by lia.
    iMod ("Hcl" with "[-Hdes S HΦ]") as "_".
    { iExists (seq + 2), 0, hist3, (Entry γp ptr desired τ), c3, lk3,
        ({[length hist3 - 1]} ∪ validated3), unlocks3. simpl. iFrame.
      iPureIntro. apply wf_unmark; [done|done|simpl; lia|by rewrite Nat.even_add Heven]. }
    iModIntro. wp_pures. iApply "HΦ". by iFrame.
  Qed.

  Definition proph_int (pvs : list (val * val)) : option Z :=
    match pvs with
    | (LitV (LitInt (FinInt i)), _) :: _ => Some i
    | _ => None
    end.

  (** ** Installing a new backup *)

  Lemma tokens_fresh (γ : gname) (hist : list entry) :
    token γ -∗ ([∗ list] e ∈ hist, token e.(e_name)) -∗ ⌜γ ∉ e_name <$> hist⌝.
  Proof.
    iIntros "Htok Htoks" ((e & -> & He)%list_elem_of_fmap).
    iDestruct (big_sepL_elem_of with "Htoks") as "Htok'"; first done.
    iDestruct (token_exclusive with "Htok Htok'") as %[].
  Qed.

  (** The atomic update of SC *)
  Definition AU_sc (γ : gname) (ver : nat) (desired : list val) (Q : bool → iProp) (Φ : val → iProp) : iProp :=
    AU <{ ∃∃ actual ver', CachedWFLLSC γ actual ver' }>
       @ ⊤ ∖ (↑cached_wf_llscN ∪ ↑ptrsN hazptrN), ↑mgmtN hazptrN
       <{ if bool_decide (ver' = ver) then CachedWFLLSC γ desired (S ver') else CachedWFLLSC γ actual ver',
          COMM Q (bool_decide (ver' = ver)) -∗ Φ #(bool_decide (ver' = ver)) }>.

  (** A successful installation of the backup [ptr] by an SC that linked version
      [ver] (protected by [h1]). This is the linearization point of the SC. *)
  Lemma sc_commit_success γs γd l n (d : loc) (sq t : nat) hist ec c lk validated unlocks
      (ptr : blk) γ_new desired ver e sz (h1 h2 : loc) (Q : bool → iProp) Φ :
    llsc_wf n sq t hist ec c validated unlocks →
    length desired = n →
    ec.(e_blk) = e.(e_blk) →
    hazptr.(IsHazardDomainSp) γd d -∗
    mono_list_idx_own γs.(γ_hist) ver e -∗
    hazptr.(ShieldSp) γd h1 (Validated e.(e_blk) e.(e_name) (node e.(e_val)) sz) -∗
    hazptr.(ShieldSp) γd h2 (NotValidated ptr) -∗
    token γ_new -∗ ptr ↦∗ desired -∗ †ptr…n -∗
    AU_sc (encode γs) ver desired Q Φ -∗
    (* The invariant, with the new backup installed *)
    (l +ₗ seqnum_off) ↦ #sq -∗
    (l +ₗ backup_off) ↦ #(Some (Loc.blk_to_loc ptr) &ₜ 1) -∗
    γs.(γ_abs) ↪VAR{#1/2} (ec.(e_val), length hist - 1) -∗
    hazptr.(ManagedSp) γd ec.(e_blk) ec.(e_name) n (node ec.(e_val)) -∗
    mono_list_auth_own γs.(γ_hist) 1 hist -∗
    ([∗ list] e ∈ hist, token e.(e_name)) -∗
    γs.(γ_seq) ↪●MN sq -∗
    (l +ₗ cache_off) ↦∗{#1/2} c -∗
    γs.(γ_lk) ↪VAR{#1/2} lk -∗
    (if Nat.even sq then γs.(γ_lk) ↪VAR{#1/2} lk ∗ (l +ₗ cache_off) ↦∗{#1/2} c else ⌜sq = S lk⌝) -∗
    validated_auth γs.(γ_val) validated -∗
    unlocks_auth γs.(γ_unl) unlocks -∗
    (▷ llsc_inv γs γd l n ={⊤ ∖ ↑cached_wf_llscN, ⊤}=∗ emp) -∗
    |={⊤ ∖ ↑cached_wf_llscN, ⊤}=>
      hazptr.(ShieldSp) γd h1 (Validated e.(e_blk) e.(e_name) (node e.(e_val)) sz) ∗
      hazptr.(ManagedSp) γd e.(e_blk) e.(e_name) n (node e.(e_val)) ∗
      hazptr.(ShieldSp) γd h2 (Validated ptr γ_new (node desired) n) ∗
      mono_list_idx_own γs.(γ_hist) (S ver) (Entry γ_new ptr desired (sq + 2)) ∗
      (Q true -∗ Φ #true).
  Proof using DISJN.
    iIntros (Hwf Hlen Hblk) "#Hdom #Hidx S1 S2 Htok Hptr †ptr AU Hseq Hbk Habs Hman Hhist Htoks Hsq
      Hcache Hlk Hif Hval Hunl Hcl".
    (* The protected backup is the current one *)
    rewrite Hblk.
    iDestruct (hazptr.(shield_managed_agree_sp) with "S1 Hman") as %Hname.
    iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He.
    pose proof (wf_current _ _ _ _ _ _ _ _ Hwf) as Hcur.
    assert (ver = length hist - 1) as ->.
    { eapply (NoDup_lookup (e_name <$> hist)); [apply Hwf| |].
      - by rewrite list_lookup_fmap He.
      - by rewrite list_lookup_fmap Hcur /= Hname. }
    rewrite Hcur in He. injection He as ->.
    (* Register the new backup *)
    iDestruct (tokens_fresh with "Htok Htoks") as %Hfresh.
    iMod (hazptr.(hazard_domain_register_sp) (node desired) with "Hdom [$Hptr †ptr]") as "Hman'";
      first solve_ndisj.
    { rewrite /node Hlen. by iFrame. }
    iMod (hazptr.(shield_validate_sp) with "Hdom Hman' S2") as "[Hman' S2]"; first solve_ndisj.
    set e_new := Entry γ_new ptr desired (sq + 2).
    iMod (mono_list_auth_own_update_app [e_new] with "Hhist") as "[Hhist #Hhist_lb]".
    iPoseProof (mono_list_idx_own_get (length hist) e_new with "Hhist_lb") as "#Hidx_new".
    { by rewrite lookup_app_r // Nat.sub_diag. }
    (* Commit *)
    iMod "AU" as (actual ver') "[(%γs' & %Henc & Hba) [_ Hcommit]]".
    apply (inj encode) in Henc as <-.
    iDestruct (ghost_var_agree with "Habs Hba") as %[= <- <-].
    iMod (ghost_var_update_halves (desired, S (length hist - 1)) with "Habs Hba") as "[Habs Hba]".
    rewrite bool_decide_eq_true_2 //.
    iMod ("Hcommit" with "[Hba]") as "HΦ".
    { iExists γs. by iFrame. }
    iMod ("Hcl" with "[-S1 Hman S2 HΦ]") as "_".
    { iNext. iExists sq, 1, (hist ++ [e_new]), e_new, c, lk, validated, unlocks.
      pose proof (wf_length_pos _ _ _ _ _ _ _ _ Hwf).
      rewrite length_app /=. replace (length hist + 1 - 1) with (S (length hist - 1)) by lia.
      rewrite big_sepL_snoc Hlen /=. iFrame.
      iPureIntro. eapply wf_install; [exact Hwf|done|done|done]. }
    iModIntro. rewrite Hlen.
    pose proof (wf_length_pos _ _ _ _ _ _ _ _ Hwf).
    replace (S (length hist - 1)) with (length hist) by lia.
    by iFrame "∗ #".
  Qed.

  (** A failing SC, when the version has changed since its LL. *)
  Lemma sc_commit_fail γs ver desired (Q : bool → iProp) Φ (vs : list val) (cur : nat) :
    cur ≠ ver →
    γs.(γ_abs) ↪VAR{#1/2} (vs, cur) -∗
    AU_sc (encode γs) ver desired Q Φ ={⊤ ∖ ↑cached_wf_llscN}=∗
    γs.(γ_abs) ↪VAR{#1/2} (vs, cur) ∗ (Q false -∗ Φ #false).
  Proof using DISJN.
    iIntros (Hne) "Habs AU".
    iMod "AU" as (actual ver') "[(%γs' & %Henc & Hba) [_ Hcommit]]".
    apply (inj encode) in Henc as <-.
    iDestruct (ghost_var_agree with "Habs Hba") as %[= <- <-].
    rewrite bool_decide_eq_false_2 //.
    iMod ("Hcommit" with "[Hba]") as "HΦ"; first (iExists γs; by iFrame).
    by iFrame.
  Qed.

  Lemma wp_try_install γs γd l n (c h1 h2 d r : loc) (et : val) (st2 : shield_state Σ) (tp seq ver sz : nat)
      (e : entry) (l_desired : loc) (dq : dfrac) (desired : list val) (Q : bool → iProp) (Φ : val → iProp) :
    length desired = n → 0 < n → n ≤ hazptr.(hp_kmax) →
    inv cached_wf_llscN (llsc_inv γs γd l n) -∗
    hazptr.(IsHazardDomainSp) γd d -∗
    mono_list_idx_own γs.(γ_hist) ver e -∗
    (⌜tp = 1⌝ ∨ ⌜tp = 0⌝ ∗ validated_frag γs.(γ_val) ver) -∗
    γs.(γ_seq) ↪◯MN seq -∗
    c ↦∗ [ #h1; #h2; et; #r ] -∗
    hazptr.(ShieldSp) γd h1 (Validated e.(e_blk) e.(e_name) (node e.(e_val)) sz) -∗
    hazptr.(ShieldSp) γd h2 st2 -∗
    hazptr.(Retirer) γd r -∗
    l_desired ↦∗{dq} desired -∗
    ♢ n -∗
    AU_sc (encode γs) ver desired Q Φ -∗
    (∀ st2' b, c ↦∗ [ #h1; #h2; et; #r ] -∗
       hazptr.(ShieldSp) γd h1 (Validated e.(e_blk) e.(e_name) (node e.(e_val)) sz) -∗
       hazptr.(ShieldSp) γd h2 st2' -∗ hazptr.(Retirer) γd r -∗
       l_desired ↦∗{dq} desired -∗ ♢ n -∗ Q b) -∗
    WP try_install_sp hazptr n #l #c #(Some (Loc.blk_to_loc e.(e_blk)) &ₜ tp) #seq #l_desired {{ Φ }}.
  Proof using DISJN.
    iIntros (Hlen Hpos Hkmax) "#Hinv #Hdom #Hidx #Htp #Hlb Hc S1 S2 Hret Hdes Hcred AU HQ".
    wp_lam. wp_pures.
    wp_apply (wp_array_clone_cred with "[$Hdes $Hcred]"); [done|lia|].
    iIntros (ptr) "(Hdes & Hptr & †ptr)".
    wp_pures.
    wp_apply (wp_load_offset _ _ _ _ 1 with "Hc") as "Hc"; first done.
    wp_apply (hazptr.(shield_set_sp_spec) (Some ptr) with "Hdom S2") as "S2"; first solve_ndisj.
    wp_pures.
    (* The first [cmp_xch] *)
    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as (sq t hist ec cc lk validated unlocks)
      "(>Hseq & >Hbk & >Habs & Hman & >Hhist & >Htoks & >Hsq & >Hcache & >Hlk & >Hif & >Hval & >Hunl & >%Hwf)" "Hcl".
    iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He.
    iDestruct (mono_nat_auth_lb_own_valid with "Hsq Hlb") as %[_ Hseq_le].
    pose proof (wf_current _ _ _ _ _ _ _ _ Hwf) as Hcur.
    destruct (decide (Some (Loc.blk_to_loc ec.(e_blk)) &ₜ t = Some (Loc.blk_to_loc e.(e_blk)) &ₜ tp))
      as [[Hblk Ht]%tagged_blk_eq|Hne].
    { (* Success *)
      apply (inj Z.of_nat) in Ht as ->.
      iMod token_alloc as (γ_new) "Htok".
      wp_cmpxchg_suc.
      iMod (sc_commit_success with "Hdom Hidx S1 S2 Htok Hptr †ptr AU Hseq Hbk Habs Hman Hhist Htoks
        Hsq Hcache Hlk Hif Hval Hunl Hcl") as "(S1 & Hman_old & S2 & #Hidx_new & HΦ)"; [done..|].
      iModIntro. wp_pures.
      wp_apply (wp_load_offset _ _ _ _ 3 with "Hc") as "Hc"; first done.
      wp_apply (hazptr.(hazard_retire_spec) with "[$Hret $Hman_old]") as "[Hret Hcred]";
        [solve_ndisj|done|].
      wp_pures.
      wp_apply (wp_try_validate with "Hinv Hidx_new [$Hdes $S2]"); [done|simpl; lia|].
      iIntros "[Hdes S2]". wp_pures.
      iApply "HΦ". iApply ("HQ" with "Hc S1 S2 Hret Hdes Hcred"). }
    wp_cmpxchg_fail.
    destruct (decide (ec.(e_blk) = e.(e_blk) ∧ t = 0)) as [[Hblk ->]|Hnot].
    - (* The backup is the validated version of the one we protected: retry *)
      iAssert ⌜tp = 1⌝%I as %->.
      { iDestruct "Htp" as "[%Htp|[%Htp _]]"; [done|]. subst tp. by rewrite Hblk in Hne. }
      iPoseProof (mono_list_lb_own_get with "Hhist") as "#Hhist_lb".
      iMod (validated_get _ _ (length hist - 1) with "Hval") as "[Hval #Hvcur]".
      { by destruct (wf_tag _ _ _ _ _ _ _ _ Hwf) as [[_ ?]|[? _]]. }
      iMod ("Hcl" with "[-AU HQ Hc S1 S2 Hret Hdes Hptr †ptr]") as "_".
      { iExists sq, 0, hist, ec, cc, lk, validated, unlocks. by iFrame. }
      iModIntro. wp_pures.
      rewrite Hblk bool_decide_eq_true_2 //. wp_pures.
      (* The second [cmp_xch], with the unmarked pointer *)
      wp_bind (CmpXchg _ _ _).
      iInv "Hinv" as (sq2 t2 hist2 ec2 cc2 lk2 validated2 unlocks2)
        "(>Hseq & >Hbk & >Habs & Hman & >Hhist & >Htoks & >Hsq & >Hcache & >Hlk & >Hif & >Hval & >Hunl & >%Hwf2)" "Hcl".
      iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He2.
      iDestruct (mono_list_auth_lb_valid with "Hhist Hhist_lb") as %[_ Hpre].
      iDestruct (mono_nat_auth_lb_own_valid with "Hsq Hlb") as %[_ Hseq_le2].
      pose proof (wf_current _ _ _ _ _ _ _ _ Hwf2) as Hcur2.
      destruct (decide (Some (Loc.blk_to_loc ec2.(e_blk)) &ₜ t2 = Some (Loc.blk_to_loc e.(e_blk)) &ₜ 0))
        as [[Hblk2 Ht2]%tagged_blk_eq|Hne2].
      + assert (t2 = 0) as -> by lia.
        iMod token_alloc as (γ_new) "Htok".
        wp_cmpxchg_suc.
        iMod (sc_commit_success with "Hdom Hidx S1 S2 Htok Hptr †ptr AU Hseq Hbk Habs Hman Hhist Htoks
          Hsq Hcache Hlk Hif Hval Hunl Hcl") as "(S1 & Hman_old & S2 & #Hidx_new & HΦ)"; [done..|].
        iModIntro. wp_pures.
        wp_apply (wp_load_offset _ _ _ _ 3 with "Hc") as "Hc"; first done.
        wp_apply (hazptr.(hazard_retire_spec) with "[$Hret $Hman_old]") as "[Hret Hcred]";
          [solve_ndisj|done|].
        wp_pures.
        wp_apply (wp_try_validate with "Hinv Hidx_new [$Hdes $S2]"); [done|simpl; lia|].
        iIntros "[Hdes S2]". wp_pures.
        iApply "HΦ". iApply ("HQ" with "Hc S1 S2 Hret Hdes Hcred").
      + wp_cmpxchg_fail.
        iAssert ⌜length hist2 - 1 ≠ ver⌝%I as %Hchanged.
        { iIntros (Heq).
          pose proof (prefix_length _ _ Hpre) as Hlen12.
          apply lookup_lt_Some in He.
          assert (length hist - 1 = ver) as Hcur_ver by lia.
          iDestruct (validated_elem with "Hval Hvcur") as %Hv2.
          rewrite Hcur_ver -Heq in Hv2.
          destruct (wf_validated_current _ _ _ _ _ _ _ _ Hwf2 Hv2) as (-> & _).
          rewrite -Heq Hcur2 in He2. injection He2 as ->. done. }
        iMod (sc_commit_fail with "Habs AU") as "[Habs HΦ]"; first done.
        iMod ("Hcl" with "[-HΦ HQ Hc S1 S2 Hret Hdes Hptr †ptr]") as "_".
        { iExists sq2, t2, hist2, ec2, cc2, lk2, validated2, unlocks2. by iFrame. }
        iModIntro. wp_pures.
        wp_apply (wp_free_cred _ _ n with "[$Hptr †ptr]"); [lia|by rewrite Hlen|].
        iIntros "Hcred". wp_pures. rewrite Hlen.
        iApply "HΦ". iApply ("HQ" with "Hc S1 S2 Hret Hdes Hcred").
    - (* The version has changed *)
      iAssert ⌜length hist - 1 ≠ ver⌝%I as %Hchanged.
      { iIntros (Heq). rewrite -Heq Hcur in He. injection He as ->.
        destruct (wf_tag _ _ _ _ _ _ _ _ Hwf) as [[-> _]|[-> Hnval]]; first naive_solver.
        iDestruct "Htp" as "[->|[-> Hv]]"; first done.
        iDestruct (validated_elem with "Hval Hv") as %?. by rewrite Heq in Hnval. }
      iMod (sc_commit_fail with "Habs AU") as "[Habs HΦ]"; first done.
      iMod ("Hcl" with "[-HΦ HQ Hc S1 S2 Hret Hdes Hptr †ptr]") as "_".
      { iExists sq, t, hist, ec, cc, lk, validated, unlocks. by iFrame. }
      iModIntro. wp_pures.
      rewrite bool_decide_eq_false_2; last first.
      { intros [= Hb Ht]. apply Hnot. split; [done|lia]. }
      wp_pures.
      wp_apply (wp_free_cred _ _ n with "[$Hptr †ptr]"); [lia|by rewrite Hlen|].
      iIntros "Hcred". wp_pures. rewrite Hlen.
      iApply "HΦ". iApply ("HQ" with "Hc S1 S2 Hret Hdes Hcred").
  Qed.

  (** ** Specifications *)

  (** The costs *)
  Definition cwf_new_cost (n : nat) : nat := S (S n) + n.
  Definition cwf_sc_cost (n : nat) : nat := n.
  Definition cwf_thread_cost : nat := 4 + hazptr.(hp_retirer_cost).
  Definition cwf_thread_refund : nat := 4.

  Lemma cached_wf_llsc_new_spec :
    big_atomic_llsc_sp_new_spec' cached_wf_llscN hazptrN cached_wf_llsc_new_sp hazptr cwf_new_cost
      CachedWFLLSC IsCachedWFLLSC.
  Proof.
    iIntros (γd d n src dq vs Hpos Hkmax Hlen Φ) "(#Hdom & Hsrc & [Hc1 Hc2]) HΦ".
    wp_rec. wp_pures.
    wp_apply (wp_allocN_cred with "[Hc1]") as (l) "[†Hl Hl]"; first lia.
    { by rewrite Nat2Z.id. }
    wp_pures.
    rewrite Nat2Z.id /= array_cons array_cons.
    iDestruct "Hl" as "(Hseq & Hbackup & Hcache)".
    rewrite !Loc.add_assoc /=.
    wp_apply (wp_array_clone_cred with "[$Hsrc $Hc2]"); [done|lia|].
    iIntros (backup) "(Hsrc & Hb & †Hb)".
    wp_pures.
    change (1 + 1)%Z with 2%Z.
    wp_store. wp_pures.
    wp_apply (wp_array_copy_to with "[$Hcache $Hsrc]").
    { by rewrite length_replicate. }
    { done. }
    iIntros "[[Hcache Hcache'] Hsrc]".
    wp_pures.
    subst n.
    iMod token_alloc as "[%γ0 Hγ0]".
    iMod (hazptr.(hazard_domain_register_sp) (node vs) with "Hdom [$Hb $†Hb //]") as "Hmanaged";
      first solve_ndisj.
    set e0 := Entry γ0 backup vs 0.
    iMod (mono_list_own_alloc [e0]) as (γh) "[Hγh _]".
    iMod (ghost_var_alloc (vs, 0)) as (γa) "[Hγa Hγa']".
    iMod (mono_nat_own_alloc 0) as (γq) "[Hγq _]".
    iMod (validated_alloc 0) as (γv) "Hγv".
    iMod (unlocks_alloc 0 0) as (γu) "Hγu".
    iMod (ghost_var_alloc 0) as (γk) "[Hγk Hγk']".
    set γs := LLSCNames γa γh γq γv γu γk.
    iMod (inv_alloc cached_wf_llscN _ (llsc_inv γs γd l (length vs))
      with "[-HΦ Hγa' Hsrc]") as "#Hinv".
    { iNext. iExists 0, 0, [e0], e0, vs, 0, {[0]}, {[0 := 0]}.
      rewrite Loc.add_0 /=. iFrame.
      iPureIntro. constructor; simpl.
      - done.
      - by rewrite Forall_singleton.
      - done.
      - apply NoDup_singleton.
      - left. split; [done|set_solver].
      - intros i j ei ej _ Hi Hj.
        apply list_lookup_singleton_Some in Hi as [-> <-].
        apply list_lookup_singleton_Some in Hj as [-> <-]. done.
      - lia.
      - intros _. split_and!; [done|by rewrite lookup_singleton_eq|done].
      - intros v ->%elem_of_singleton. by exists e0.
      - intros v e v' e' ->%elem_of_singleton _ He' Hlt.
        apply lookup_lt_Some in He'. simpl in *. lia.
      - intros _. exists 0, e0. by rewrite lookup_singleton_eq.
      - intros k. rewrite dom_singleton_L elem_of_singleton. lia. }
    iModIntro. iApply "HΦ". iFrame "Hsrc".
    iSplitR.
    - iExists γs, l. iFrame "#". iPureIntro. split_and!; [done|done|lia|lia].
    - iExists γs. by iFrame.
  Qed.

  Lemma cached_wf_llsc_thread_new_spec :
    big_atomic_llsc_sp_thread_new_spec' cached_wf_llscN hazptrN (llsc_thread_new_sp hazptr) hazptr
      cwf_thread_cost CachedWFLLSCThread.
  Proof.
    iIntros (γd d Φ) "[#Hdom [Hc4 Hcr]] HΦ".
    wp_lam.
    wp_apply (wp_allocN_cred _ _ _ 4 with "[Hc4]") as (c) "[†c Hc]"; first lia.
    { done. }
    wp_pures.
    rewrite /= !array_cons array_nil.
    iDestruct "Hc" as "(Hc0 & Hc1 & Hc2 & Hc3 & _)".
    wp_apply (hazptr.(shield_new_sp_spec) with "Hdom [//]") as (s1) "S1"; first solve_ndisj.
    wp_pures. rewrite Loc.add_0. wp_store. wp_pures.
    wp_apply (hazptr.(shield_new_sp_spec) with "Hdom [//]") as (s2) "S2"; first solve_ndisj.
    wp_pures. wp_store. wp_pures. rewrite !Loc.add_assoc /=. wp_store. wp_pures.
    wp_apply (hazptr.(hazard_retirer_new_spec) with "Hdom Hcr") as (r) "Hret"; first solve_ndisj.
    wp_pures. wp_store.
    iModIntro. iApply "HΦ".
    iExists c, s1, s2, d, r, _, _, _. iFrame "∗ #". iSplit; first done.
    by rewrite array_nil.
  Qed.

  Lemma cached_wf_llsc_thread_drop_spec :
    big_atomic_llsc_sp_thread_drop_spec' cached_wf_llscN (llsc_thread_drop_sp hazptr)
      cwf_thread_refund CachedWFLLSCThread.
  Proof.
    iIntros (γd ctx link Φ)
      "(%c & %h1 & %h2 & %d & %r & %et & %st1 & %st2 & -> & Hc & †c & #Hdom & S1 & S2 & _) HΦ".
    wp_lam. wp_pures.
    wp_apply (wp_load_offset _ _ _ _ 0 with "Hc") as "Hc"; first done.
    wp_apply (hazptr.(shield_drop_sp_spec) with "Hdom S1") as "_"; first solve_ndisj.
    wp_pures.
    wp_apply (wp_load_offset _ _ _ _ 1 with "Hc") as "Hc"; first done.
    wp_apply (hazptr.(shield_drop_sp_spec) with "Hdom S2") as "_"; first solve_ndisj.
    wp_pures.
    wp_apply (wp_free_cred with "[$Hc $†c]") as "Hc"; first done.
    by iApply "HΦ".
  Qed.

  Lemma cached_wf_llsc_ll_spec :
    big_atomic_llsc_sp_ll_spec' cached_wf_llscN hazptrN (cached_wf_llsc_ll_sp hazptr) CachedWFLLSC
      IsCachedWFLLSC CachedWFLLSCThread.
  Proof using DISJN.
    iIntros (γ γd ba n ctx link)
      "(%γs & %l & -> & -> & %Hpos & %Hkmax & #Hinv)
       (%c & %h1 & %h2 & %d' & %r & %et & %st1 & %st2 & -> & Hc & †c & #Hdom' & S1 & S2 & Hret & _)
       Hcred".
    iIntros (Φ) "AU".
    wp_lam. wp_pures.
    (* [seq := seqnum] *)
    wp_bind (! _)%E.
    iInv "Hinv" as (sq t hist ec cc lk validated unlocks)
      "(>Hseq & Hbk & Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf)" "Hcl".
    rewrite Loc.add_0. wp_load.
    iPoseProof (mono_nat_lb_own_get with "Hsq") as "#Hlb1".
    iAssert (|==> ∃ oc, cache_snap γs sq oc ∗
               ⌜Nat.even sq = true → is_Some oc⌝ ∗ unlocks_auth γs.(γ_unl) unlocks ∗
               mono_list_auth_own γs.(γ_hist) 1 hist)%I
      with "[Hunl Hhist]" as ">(%oc & #Hsnap & %Hoc & Hunl & Hhist)".
    { destruct (Nat.even sq) eqn:Heven; last first.
      { iModIntro. iExists None. by iFrame. }
      destruct (wf_cache _ _ _ _ _ _ _ _ Hwf Heven) as (cv & e & Hcv & He & _).
      iMod (unlocks_get with "Hunl") as "[Hunl #Hfrag]"; first done.
      iPoseProof (mono_list_lb_own_get with "Hhist") as "#Hhist_lb".
      iModIntro. iExists (Some (cv, e)). iFrame "Hunl Hhist".
      iSplit; last (iPureIntro; by eauto).
      iFrame "Hfrag". iSplit; first done.
      by iApply (mono_list_idx_own_get _ _ He with "Hhist_lb"). }
    iMod ("Hcl" with "[-Hc †c S1 S2 Hret Hcred AU]") as "_".
    { iExists sq, t, hist, ec, cc, lk, validated, unlocks. rewrite Loc.add_0. by iFrame. }
    clear t hist ec cc lk validated unlocks Hwf.
    iModIntro. wp_pures.
    wp_apply (wp_clone_cache with "Hinv Hlb1 Hsnap Hcred"); first done.
    iIntros (dst vs') "(Hdst & †dst & %Hlen' & #Hgood)".
    wp_pures.
    wp_apply wp_new_proph; first done.
    iIntros (pvs p) "Hp".
    wp_pures.
    (* [p := backup_ptr]: the linearization point of the fast path *)
    wp_bind (! _)%E.
    iInv "Hinv" as (sq2 t2 hist2 ec2 c2 lk2 validated2 unlocks2)
      "(>Hseq & >Hbk & >Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf2)" "Hcl".
    wp_load.
    destruct (decide (t2 = 0 ∧ proph_int pvs = Some (Z.of_nat sq))) as [[-> Hproph]|Hslow].
    - (* Fast path: commit now *)
      destruct (wf_valid _ _ _ _ _ _ _ _ Hwf2) as (Hsq2 & Hunl2 & Heven2); first done.
      assert (length hist2 - 1 ∈ validated2) as Hval2.
      { by destruct (wf_tag _ _ _ _ _ _ _ _ Hwf2) as [[_ ?]|[? _]]. }
      iMod (validated_get with "Hval") as "[Hval #Hvfrag]"; first done.
      iMod (unlocks_get with "Hunl") as "[Hunl #Hufrag]"; first done.
      iPoseProof (mono_list_lb_own_get with "Hhist") as "#Hhist_lb".
      iPoseProof (mono_list_idx_own_get _ _ (wf_current _ _ _ _ _ _ _ _ Hwf2) with "Hhist_lb") as "#Hidx2".
      iPoseProof (mono_nat_lb_own_get with "Hsq") as "#Hlb2".
      iDestruct (mono_nat_auth_lb_own_valid with "Hsq Hlb1") as %[_ Hle12].
      iMod "AU" as (vs ver) "[(%γs' & %Henc & Hba) [_ Hcommit]]".
      apply (inj encode) in Henc as <-.
      iDestruct (ghost_var_agree with "Habs Hba") as %[= <- <-].
      iMod ("Hcommit" $! dst with "[Hba]") as "HΦ".
      { iExists γs. by iFrame. }
      iMod ("Hcl" with "[-Hc †c S1 S2 Hret HΦ Hdst †dst Hp]") as "_".
      { iExists sq2, 0, hist2, ec2, c2, lk2, validated2, unlocks2. by iFrame. }
      iModIntro.
      rewrite /is_valid_sp. wp_pures.
      (* [seqnum] again, resolving the prophecy *)
      wp_bind (Resolve _ _ _)%E.
      iInv "Hinv" as (sq3 t3 hist3 ec3 c3 lk3 validated3 unlocks3)
        "(>Hseq & Hbk & Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf3)" "Hcl".
      rewrite Loc.add_0.
      wp_apply (wp_resolve_load with "[$Hp $Hseq]").
      iIntros (pvs') "(-> & Hp & Hseq)".
      iDestruct (mono_nat_auth_lb_own_valid with "Hsq Hlb2") as %[_ Hle3].
      simpl in Hproph. injection Hproph as <-%(inj Z.of_nat).
      assert (sq2 = sq3) as -> by lia.
      (* The copy of the cache is the current value *)
      iAssert ⌜vs' = e_val ec2⌝%I as %->.
      { destruct oc as [[cv e]|]; last by destruct Hoc.
        iDestruct "Hsnap" as "(_ & Hfrag & Hidx)".
        iDestruct (own_valid_2 with "Hfrag Hufrag") as %Hvalid.
        rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hvalid.
        apply to_agree_op_inv_L in Hvalid as <-.
        iDestruct (mono_list_idx_agree with "Hidx Hidx2") as %<-.
        iDestruct "Hgood" as "[Hlb'|%Hgood]".
        - iDestruct (mono_nat_auth_lb_own_valid with "Hsq Hlb'") as %[_ ?]. lia.
        - iPureIntro. rewrite Hgood drop_0 take_ge //.
          pose proof (wf_current _ _ _ _ _ _ _ _ Hwf2) as Hc2.
          pose proof (Forall_lookup_1 _ _ _ _ (wf_len _ _ _ _ _ _ _ _ Hwf2) Hc2) as Hl2.
          simpl in Hl2. lia. }
      iMod ("Hcl" with "[-Hc †c S1 S2 Hret HΦ Hdst †dst]") as "_".
      { iExists sq3, t3, hist3, ec3, c3, lk3, validated3, unlocks3. rewrite Loc.add_0. by iFrame. }
      iModIntro. wp_pures.
      wp_apply (wp_store_offset with "Hc") as "Hc"; first done.
      wp_pures. iModIntro.
      iApply "HΦ". iFrame "Hdst †dst". iSplit; first done.
      iExists c, h1, h2, d', r, _, st1, st2. iFrame "∗ #". iSplit; first done.
      iSplit; first done. iLeft. iPureIntro. by rewrite Hsq2.
    - (* No commit here *)
      iMod ("Hcl" with "[-AU Hc †c S1 S2 Hret Hdst †dst Hp]") as "_".
      { iExists sq2, t2, hist2, ec2, c2, lk2, validated2, unlocks2. by iFrame. }
      iModIntro.
      (* The slow path, which linearizes at the protected load of the backup pointer *)
      iAssert (WP (let: "p" := hazptr.(hpsp_shield_protect_tagged) ! #(c +ₗ Z.of_nat h1_off) #(l +ₗ Z.of_nat backup_off) in
                   #c +ₗ #expected_tag_off <- "p";; array_copy_to #dst (untag "p") #n;; #dst)
               {{ v, Φ v }})%I with "[AU Hc †c S1 S2 Hret Hdst †dst]" as "Hslow".
      { wp_pures.
        wp_apply (wp_load_offset _ _ _ _ 0 with "Hc") as "Hc"; first done.
        awp_apply (hazptr.(shield_protect_tagged_sp_spec) with "Hdom' S1"); first solve_ndisj.
        rewrite /atomic_acc /=.
        iInv "Hinv" as (sq4 t4 hist4 ec4 c4 lk4 validated4 unlocks4)
          "(>Hseq & >Hbk & >Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf4)" "Hcl".
        iMod "AU" as (vs ver) "[(%γs' & %Henc & Hba) Hlin]".
        apply (inj encode) in Henc as <-.
        iDestruct (ghost_var_agree with "Habs Hba") as %[= <- <-].
        iModIntro. iExists ec4.(e_blk), t4, ec4.(e_name), n, (node ec4.(e_val)). iFrame "Hbk Hman".
        iSplit.
        { iIntros "[Hbk Hman]". iDestruct "Hlin" as "[Habort _]".
          iMod ("Habort" with "[Hba]") as "AU"; first (iExists γs; by iFrame).
          iMod ("Hcl" with "[-AU Hc †c S2 Hret Hdst †dst]") as "_".
          { iExists sq4, t4, hist4, ec4, c4, lk4, validated4, unlocks4. by iFrame. }
          by iFrame. }
        iIntros "(Hbk & Hman & S1)".
        iDestruct "Hlin" as "[_ Hcommit]".
        iMod ("Hcommit" $! dst with "[Hba]") as "HΦ"; first (iExists γs; by iFrame).
        iPoseProof (mono_list_lb_own_get with "Hhist") as "#Hhist_lb".
        pose proof (wf_current _ _ _ _ _ _ _ _ Hwf4) as Hcur4.
        iPoseProof (mono_list_idx_own_get _ _ Hcur4 with "Hhist_lb") as "#Hidx4".
        iAssert (|==> validated_auth γs.(γ_val) validated4 ∗
                   (⌜t4 = 1⌝ ∨ ⌜t4 = 0⌝ ∗ validated_frag γs.(γ_val) (length hist4 - 1)))%I
          with "[Hval]" as ">[Hval #Htag]".
        { destruct (wf_tag _ _ _ _ _ _ _ _ Hwf4) as [[-> Hv]|[-> _]].
          - iMod (validated_get _ _ (length hist4 - 1) with "Hval") as "[$ #Hv]"; first done.
            iModIntro. iRight. by iFrame "Hv".
          - iModIntro. iFrame. by iLeft. }
        iMod ("Hcl" with "[-HΦ Hc †c S1 S2 Hret Hdst †dst]") as "_".
        { iExists sq4, t4, hist4, ec4, c4, lk4, validated4, unlocks4. by iFrame. }
        iModIntro. wp_pures.
        wp_apply (wp_store_offset with "Hc") as "Hc"; first done.
        wp_pures.
        change #(Some (Loc.blk_to_loc ec4.(e_blk)) &ₜ 0) with #(ec4.(e_blk)).
        wp_apply (wp_copy_protected with "[$Hdst $S1]").
        { done. }
        { exact (Forall_lookup_1 _ _ _ _ (wf_len _ _ _ _ _ _ _ _ Hwf4) Hcur4). }
        iIntros "[Hdst S1]". wp_pures.
        iModIntro. iApply "HΦ". iFrame "Hdst †dst".
        iSplit; first (iPureIntro; exact (Forall_lookup_1 _ _ _ _ (wf_len _ _ _ _ _ _ _ _ Hwf4) Hcur4)).
        iExists c, h1, h2, d', r, _, _, st2. iFrame "∗ #". iSplit; first done.
        iSplit; first done. iRight. iExists n. by iSplit. }
      rewrite /is_valid_sp. wp_pures.
      destruct (decide (t2 = 0)) as [->|Ht2]; last first.
      { rewrite bool_decide_eq_false_2; last (intros [= ?]; lia).
        wp_pures. iApply "Hslow". }
      wp_pures.
      wp_bind (Resolve _ _ _)%E.
      iInv "Hinv" as (sq3 t3 hist3 ec3 c3 lk3 validated3 unlocks3)
        "(>Hseq & Hbk & Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf3)" "Hcl".
      wp_apply (wp_resolve_load with "[$Hp $Hseq]").
      iIntros (pvs') "(-> & Hp & Hseq)".
      iMod ("Hcl" with "[-Hslow]") as "_".
      { iExists sq3, t3, hist3, ec3, c3, lk3, validated3, unlocks3. by iFrame. }
      iModIntro. wp_pures.
      rewrite bool_decide_eq_false_2; last first.
      { intros [= ->%(inj Z.of_nat)]. apply Hslow. done. }
      wp_pures. iApply "Hslow".
  Qed.


  Lemma cached_wf_llsc_sc_spec :
    big_atomic_llsc_sp_sc_spec' cached_wf_llscN hazptrN (cached_wf_llsc_sc_sp hazptr) cwf_sc_cost
      CachedWFLLSC IsCachedWFLLSC CachedWFLLSCThread.
  Proof using DISJN.
    iIntros (γ γd ba n ctx ver l_desired dq desired Hlen)
      "(%γs & %l & -> & -> & %Hpos & %Hkmax & #Hinv)
       (%c & %h1 & %h2 & %d' & %r & %et & %st1 & %st2 & -> & Hc & †c & #Hdom' & S1 & S2 & Hret & #Hlink)
       Hdes Hcred".
    iIntros (Φ) "AU".
    iDestruct "Hlink" as (γs' e) "(%Henc & #Hidx & #Hcase)".
    apply (inj encode) in Henc as <-.
    iAssert (AU_sc (encode γs) ver desired
               (λ b, CachedWFLLSCThread γd #c (if b then None else Some (encode γs, ver)) ∗
                     l_desired ↦∗{dq} desired ∗ ♢ (cwf_sc_cost n))%I Φ) with "[AU]" as "AU".
    { rewrite /AU_sc /=. iExact "AU". }
    (* How to rebuild the thread-local state at the end *)
    iAssert (∀ st1' st2' (b : bool), c ↦∗ [ #h1; #h2; et; #r ] -∗ hazptr.(ShieldSp) γd h1 st1' -∗
               hazptr.(ShieldSp) γd h2 st2' -∗ hazptr.(Retirer) γd r -∗
               l_desired ↦∗{dq} desired -∗ ♢ n -∗
               ⌜∀ tp sz, et = #(Some (Loc.blk_to_loc e.(e_blk)) &ₜ tp) →
                  st1 = Validated e.(e_blk) e.(e_name) (node e.(e_val)) sz →
                  st1' = st1⌝ -∗
               CachedWFLLSCThread γd #c (if b then None else Some (encode γs, ver)) ∗
               l_desired ↦∗{dq} desired ∗ ♢ (cwf_sc_cost n))%I
      with "[†c]" as "HQ".
    { iIntros (st1' st2' b) "Hc S1 S2 Hret Hdes Hcred %Hst1". iFrame "Hdes Hcred".
      iExists c, h1, h2, d', r, et, st1', st2'. iFrame "∗ #". iSplit; first done.
      destruct b; first done.
      iExists γs, e. iFrame "Hidx". iSplit; first done.
      iDestruct "Hcase" as "[Hcase|(%tp & %sz & %Het & %Hst & Htp)]"; first by iLeft.
      iRight. iExists tp, sz. rewrite (Hst1 tp sz Het Hst). by iFrame "Htp". }
    wp_lam. wp_pures.
    wp_apply (wp_load_offset _ _ _ _ 2 with "Hc") as "Hc"; first done.
    wp_pures.
    iDestruct "Hcase" as "[[-> #Hvver] | (%tp & %sz & -> & -> & #Htp)]"; last first.
    { (* Slow path: [expected_tag] is the protected pointer *)
      rewrite /is_seqnum_sp. wp_pures.
      wp_bind (! _)%E.
      iInv "Hinv" as (sq t hist ec cc lk validated unlocks)
        "(>Hseq & Hbk & Habs & Hman & >Hhist & Htoks & >Hsq & >Hcache & >Hlk & Hif & >Hval & >Hunl & >%Hwf)" "Hcl".
      wp_load.
      iPoseProof (mono_nat_lb_own_get with "Hsq") as "#Hlb".
      iMod ("Hcl" with "[-AU HQ Hc S1 S2 Hret Hdes Hcred]") as "_".
      { iExists sq, t, hist, ec, cc, lk, validated, unlocks. by iFrame. }
      iModIntro.
      wp_apply (wp_try_install with "Hinv Hdom' Hidx Htp Hlb Hc S1 S2 Hret Hdes Hcred AU"); [done..|].
      iIntros (st2' b) "Hc S1 S2 Hret Hdes Hcred".
      iApply ("HQ" $! _ _ b with "Hc S1 S2 Hret Hdes Hcred"). iPureIntro. naive_solver. }
    (* Fast path: [expected_tag] is the sequence number of version [ver] *)
    rewrite /is_seqnum_sp. wp_pures.
    wp_apply (wp_load_offset _ _ _ _ 0 with "Hc") as "Hc"; first done.
    awp_apply (hazptr.(shield_protect_tagged_sp_spec) with "Hdom' S1"); first solve_ndisj.
    rewrite /atomic_acc /=.
    iInv "Hinv" as (sq1 t1 hist1 ec1 cc1 lk1 validated1 unlocks1)
      "(>Hseq & >Hbk & >Habs & Hman & >Hhist & >Htoks & >Hsq & >Hcache & >Hlk & >Hif & >Hval & >Hunl & >%Hwf1)" "Hcl".
    iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first solve_ndisj.
    iModIntro.
    iExists ec1.(e_blk), t1, ec1.(e_name), n, (node ec1.(e_val)). iFrame "Hbk Hman".
    iSplit.
    { iIntros "[Hbk Hman]". iMod "Hclose" as "_".
      iMod ("Hcl" with "[-AU HQ Hc S2 Hret Hdes Hcred]") as "_".
      { iExists sq1, t1, hist1, ec1, cc1, lk1, validated1, unlocks1. by iFrame. }
      by iFrame. }
    iIntros "(Hbk & Hman & S1)". iMod "Hclose" as "_".
    (* What we learn from the protected load *)
    iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He1.
    iDestruct (validated_elem with "Hval Hvver") as %Hvver1.
    pose proof (wf_current _ _ _ _ _ _ _ _ Hwf1) as Hcur1.
    assert (ver ≤ length hist1 - 1) as Hle1 by (apply lookup_lt_Some in He1; lia).
    assert (length hist1 - 1 = ver → t1 = 0) as Hcur_t1.
    { intros Heq. rewrite -Heq in Hvver1.
      by destruct (wf_validated_current _ _ _ _ _ _ _ _ Hwf1 Hvver1). }
    assert (t1 = 0 → sq1 = ec1.(e_seq)) as Hsq1.
    { intros Ht. by destruct (wf_valid _ _ _ _ _ _ _ _ Hwf1 Ht). }
    assert (ver < length hist1 - 1 → e.(e_seq) + 2 ≤ ec1.(e_seq)) as Hlater1.
    { intros Hlt. by eapply (wf_val_later _ _ _ _ _ _ _ _ Hwf1). }
    iPoseProof (mono_nat_lb_own_get with "Hsq") as "#Hlb1".
    iPoseProof (mono_list_lb_own_get with "Hhist") as "#Hhist_lb1".
    iPoseProof (mono_list_idx_own_get _ _ Hcur1 with "Hhist_lb1") as "#Hidx1".
    iMod ("Hcl" with "[-AU HQ Hc S1 S2 Hret Hdes Hcred]") as "_".
    { iExists sq1, t1, hist1, ec1, cc1, lk1, validated1, unlocks1. by iFrame. }
    iModIntro. wp_pures.
    (* [seq := seqnum] *)
    wp_bind (! _)%E.
    iInv "Hinv" as (sq2 t2 hist2 ec2 cc2 lk2 validated2 unlocks2)
      "(>Hseq & >Hbk & >Habs & Hman & >Hhist & >Htoks & >Hsq & >Hcache & >Hlk & >Hif & >Hval & >Hunl & >%Hwf2)" "Hcl".
    wp_load.
    iDestruct (mono_nat_auth_lb_own_valid with "Hsq Hlb1") as %[_ Hsq12].
    iDestruct (mono_list_auth_lb_valid with "Hhist Hhist_lb1") as %[_ Hpre12].
    iPoseProof (mono_nat_lb_own_get with "Hsq") as "#Hlb2".
    destruct (decide (t1 = 0 ∧ sq2 = e.(e_seq))) as [[-> ->]|Hfail].
    - (* The check succeeds: the protected pointer is version [ver] *)
      iMod ("Hcl" with "[-AU HQ Hc S1 S2 Hret Hdes Hcred]") as "_".
      { iExists _, t2, hist2, ec2, cc2, lk2, validated2, unlocks2. by iFrame. }
      assert (length hist1 - 1 = ver) as Hver1.
      { destruct (decide (ver < length hist1 - 1)) as [Hlt|]; last lia.
        specialize (Hlater1 Hlt). specialize (Hsq1 eq_refl). lia. }
      rewrite Hver1 He1 in Hcur1. injection Hcur1 as ->.
      iModIntro. rewrite /is_valid_sp. wp_pures.
      wp_apply (wp_try_install _ _ _ _ _ _ _ _ _ _ _ 0 _ _ n
        with "Hinv Hdom' Hidx [] Hlb2 Hc S1 S2 Hret Hdes Hcred AU"); [done|done|done| |].
      { iRight. by iFrame "Hvver". }
      iIntros (st2' b) "Hc S1 S2 Hret Hdes Hcred".
      iApply ("HQ" $! _ _ b with "Hc S1 S2 Hret Hdes Hcred"). iPureIntro. intros ?? [=]. 
    - (* The check fails: the version has changed *)
      iAssert ⌜length hist2 - 1 ≠ ver⌝%I as %Hchanged.
      { iIntros (Heq).
        pose proof (prefix_length _ _ Hpre12).
        assert (length hist1 - 1 = ver) as Hver1 by lia.
        specialize (Hcur_t1 Hver1).
        iDestruct (validated_elem with "Hval Hvver") as %Hvver2.
        rewrite -Heq in Hvver2.
        destruct (wf_validated_current _ _ _ _ _ _ _ _ Hwf2 Hvver2) as (_ & Hsq2 & _).
        iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He2.
        pose proof (wf_current _ _ _ _ _ _ _ _ Hwf2) as Hcur2.
        rewrite -Heq Hcur2 in He2. injection He2 as ->.
        iPureIntro. by apply Hfail. }
      iMod (sc_commit_fail with "Habs AU") as "[Habs HΦ]"; first done.
      iMod ("Hcl" with "[-HΦ HQ Hc S1 S2 Hret Hdes Hcred]") as "_".
      { iExists sq2, t2, hist2, ec2, cc2, lk2, validated2, unlocks2. by iFrame. }
      iModIntro. rewrite /is_valid_sp. wp_pures.
      destruct (decide (t1 = 0)) as [->|Ht1].
      + rewrite bool_decide_eq_true_2 //. wp_pures.
        rewrite bool_decide_eq_false_2; last first.
        { intros Heq. apply Hfail. split; [reflexivity|lia]. }
        wp_pures. iApply "HΦ".
        iApply ("HQ" $! _ _ false with "Hc S1 S2 Hret Hdes Hcred"). iPureIntro. intros ?? [=].
      + rewrite bool_decide_eq_false_2; last (intros [=]; lia).
        wp_pures. iApply "HΦ".
        iApply ("HQ" $! _ _ false with "Hc S1 S2 Hret Hdes Hcred"). iPureIntro. intros ?? [=].
  Qed.

  Definition cached_wf_llsc_sp_code : big_atomic_llsc_code := {|
    big_atomic_llsc_new := cached_wf_llsc_new_sp;
    big_atomic_llsc_thread_new := llsc_thread_new_sp hazptr;
    big_atomic_llsc_thread_drop := llsc_thread_drop_sp hazptr;
    big_atomic_llsc_ll := cached_wf_llsc_ll_sp hazptr;
    big_atomic_llsc_sc := cached_wf_llsc_sc_sp hazptr;
  |}.

  Definition cached_wf_llsc_sp_impl :
      big_atomic_llsc_sp_spec Σ cached_wf_llscN hazptrN DISJN hazptr := {|
    big_atomic_llsc_sp_spec_code := cached_wf_llsc_sp_code;

    llsc_new_cost := cwf_new_cost;
    llsc_sc_cost := cwf_sc_cost;
    llsc_thread_cost := cwf_thread_cost;
    llsc_thread_refund := cwf_thread_refund;

    BigAtomicLLSCSp := CachedWFLLSC;
    IsBigAtomicLLSCSp := IsCachedWFLLSC;
    LLSCThreadSp := CachedWFLLSCThread;

    BigAtomicLLSCSp_Timeless := CachedWFLLSC_Timeless;
    IsBigAtomicLLSCSp_Persistent := IsCachedWFLLSC_Persistent;

    big_atomic_llsc_sp_new_spec := cached_wf_llsc_new_spec;
    big_atomic_llsc_sp_thread_new_spec := cached_wf_llsc_thread_new_spec;
    big_atomic_llsc_sp_thread_drop_spec := cached_wf_llsc_thread_drop_spec;
    big_atomic_llsc_sp_ll_spec := cached_wf_llsc_ll_spec;
    big_atomic_llsc_sp_sc_spec := cached_wf_llsc_sc_spec;
  |}.

End cached_wf_llsc_sp.
