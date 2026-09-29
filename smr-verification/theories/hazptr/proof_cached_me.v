From iris.base_logic.lib Require Import invariants ghost_var mono_nat token.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation lib.array.
From smr.base_logic Require Import lib.mono_list.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr hazptr.spec_big_atomic_llsc.
From smr Require Import hazptr.code_llsc_thread hazptr.code_cached_me.

(** * Proof of the Cached-MemoryEfficient LL/SC big atomic

    The abstract state of the big atomic is its current value and its version,
    the number of successful SCs. Every successful SC installs a fresh backup
    whose sequence number is the new version, so the history [hist] of values
    is indexed by version, and each entry records the gname (unique, as it is
    backed by a token) and block of the backup that installed it. The initial
    version has no backup, so its block is arbitrary.

    The header is either the sequence number of the current version [V], or a
    pointer to the backup of [V]. A header that is a sequence number only
    changes to a pointer, and a pointer changes either to another pointer (a
    successful SC) or to the sequence number of its own version. So the header
    only moves forward through the index [k], where the sequence number [s] has
    index [2 s] and the backup of version [v] has index [2 v - 1].

    An SC that replaces a sequence number with a pointer becomes the owner of
    the cache (the token [γ_own] and one half of the cache), until it replaces
    the header with the sequence number of the backup whose value it copied into
    the cache. While the header is a sequence number, the invariant owns the
    cache and it holds the current value. *)

Record entry := Entry {
  e_name : gname;
  e_blk : blk;
  e_val : list val;
}.

Global Instance entry_inhabited : Inhabited entry.
Proof. constructor. exact (Entry inhabitant inhabitant []). Qed.

Record me_names := MENames {
  γ_abs : gname;
  γ_hist : gname;
  γ_idx : gname;
  γ_own : gname;
}.

Global Instance me_names_eq_dec : EqDecision me_names.
Proof. solve_decision. Qed.

Global Instance me_names_countable : Countable me_names.
Proof.
  refine (inj_countable'
    (λ γs, (γs.(γ_abs), γs.(γ_hist), γs.(γ_idx), γs.(γ_own)))
    (λ '(a, b, c, d), MENames a b c d) _); by intros [].
Qed.

Class cached_meG Σ := CachedMEG {
  #[local] cached_me_absG :: ghost_varG Σ (list val * nat);
  #[local] cached_me_histG :: mono_listG entry Σ;
  #[local] cached_me_idxG :: mono_natG Σ;
  #[local] cached_me_tokenG :: tokenG Σ;
}.

Definition cached_meΣ : gFunctors := #[
  ghost_varΣ (list val * nat);
  mono_listΣ entry;
  mono_natΣ;
  tokenΣ
].

Global Instance subG_cached_meΣ {Σ} :
  subG cached_meΣ Σ → cached_meG Σ.
Proof. solve_inG. Qed.

(** ** Pure facts of the invariant *)

(** [k] is the index of the header, [hist] the history, [ec] its last entry,
    and [c] the contents of the cache. *)
Record me_wf (n k : nat) (hist : list entry) (ec : entry) (c : list val) : Prop := {
  wf_last : last hist = Some ec;
  wf_len : Forall (λ e, length e.(e_val) = n) hist;
  wf_cache_len : length c = n;
  wf_nodup : NoDup (e_name <$> hist);
  wf_idx : if Nat.even k then k = 2 * (length hist - 1) else k + 1 = 2 * (length hist - 1);
  wf_cache : Nat.even k = true → c = ec.(e_val);
}.

Section wf.
  Implicit Types (hist : list entry) (e ec : entry).

  Lemma even_double (s : nat) : Nat.even (2 * s) = true.
  Proof. rewrite Nat.even_mul. done. Qed.

  Lemma wf_current n k hist ec c :
    me_wf n k hist ec c → hist !! (length hist - 1) = Some ec.
  Proof.
    intros Hwf. pose proof (wf_last _ _ _ _ _ Hwf) as Hl. rewrite last_lookup in Hl.
    by replace (length hist - 1) with (pred (length hist)) by lia.
  Qed.

  Lemma wf_length_pos n k hist ec c :
    me_wf n k hist ec c → 0 < length hist.
  Proof.
    intros Hwf. pose proof (wf_last _ _ _ _ _ Hwf) as Hl.
    destruct hist; [done|simpl; lia].
  Qed.

  Lemma wf_ec_len n k hist ec c :
    me_wf n k hist ec c → length ec.(e_val) = n.
  Proof.
    intros Hwf. exact (Forall_lookup_1 _ _ _ _ (wf_len _ _ _ _ _ Hwf) (wf_current _ _ _ _ _ Hwf)).
  Qed.

  Lemma wf_even n k hist ec c :
    me_wf n k hist ec c → Nat.even k = true →
    k = 2 * (length hist - 1) ∧ c = ec.(e_val).
  Proof.
    intros Hwf Heven. pose proof (wf_idx _ _ _ _ _ Hwf) as Hidx. rewrite Heven in Hidx.
    split; first done. by apply (wf_cache _ _ _ _ _ Hwf).
  Qed.

  Lemma wf_odd n k hist ec c :
    me_wf n k hist ec c → Nat.even k = false →
    k + 1 = 2 * (length hist - 1).
  Proof.
    intros Hwf Hodd. pose proof (wf_idx _ _ _ _ _ Hwf) as Hidx. by rewrite Hodd in Hidx.
  Qed.

  (** A successful SC appends its entry to the history. *)
  Lemma wf_install n k hist ec c e_new :
    me_wf n k hist ec c →
    length e_new.(e_val) = n →
    e_new.(e_name) ∉ e_name <$> hist →
    me_wf n (if Nat.even k then S k else S (S k)) (hist ++ [e_new]) e_new c.
  Proof.
    intros Hwf Hlen Hfresh.
    pose proof (wf_length_pos _ _ _ _ _ Hwf).
    pose proof (wf_idx _ _ _ _ _ Hwf) as Hidx.
    destruct Hwf as [Hlast Hlens Hclen Hnodup _ _].
    constructor.
    - by rewrite last_app.
    - rewrite Forall_app Forall_singleton. done.
    - done.
    - rewrite fmap_app /=. apply NoDup_app. split_and!; [done| |apply NoDup_singleton].
      intros x Hx ->%list_elem_of_singleton. done.
    - rewrite length_app /=.
      destruct (Nat.even k) eqn:Heven.
      + rewrite Nat.even_succ -Nat.negb_even Heven /=. lia.
      + rewrite !Nat.even_succ Nat.odd_succ Heven /=. lia.
    - destruct (Nat.even k) eqn:Heven.
      + rewrite Nat.even_succ -Nat.negb_even Heven. done.
      + rewrite !Nat.even_succ Nat.odd_succ Heven. done.
  Qed.

  (** The owner writes the cache while the header is a pointer. *)
  Lemma wf_write n k hist ec c c' :
    me_wf n k hist ec c → Nat.even k = false → length c' = n →
    me_wf n k hist ec c'.
  Proof.
    intros Hwf Hodd Hlen'.
    destruct Hwf as [Hlast Hlens Hclen Hnodup Hidx Hcache].
    constructor; try done. by rewrite Hodd.
  Qed.

  (** The owner replaces the pointer to the current backup by its sequence
      number, after copying its value into the cache. *)
  Lemma wf_unmark n k hist ec c :
    me_wf n k hist ec c → Nat.even k = false → c = ec.(e_val) →
    me_wf n (S k) hist ec c.
  Proof.
    intros Hwf Hodd Hc.
    pose proof (wf_odd _ _ _ _ _ Hwf Hodd) as Hk.
    destruct Hwf as [Hlast Hlens Hclen Hnodup Hidx Hcache].
    constructor; try done.
    - rewrite Nat.even_succ -Nat.negb_even Hodd /=. lia.
  Qed.

  (** If the header is not the sequence number of [ver] and its index is at
      least that of this sequence number, the version is not [ver]. *)
  Lemma wf_ver_ne_seq n k hist ec c ver :
    me_wf n k hist ec c → 2 * ver ≤ k →
    ¬ (Nat.even k = true ∧ length hist - 1 = ver) → length hist - 1 ≠ ver.
  Proof.
    intros Hwf Hle Hno Heq. destruct (Nat.even k) eqn:Heven.
    - by apply Hno.
    - pose proof (wf_odd _ _ _ _ _ Hwf Heven). lia.
  Qed.

  (** Same, if the header is also not the backup [e] of [ver]. *)
  Lemma wf_ver_ne_ptr n k hist ec c ver e :
    me_wf n k hist ec c → 2 * ver - 1 ≤ k → hist !! ver = Some e →
    ¬ (Nat.even k = true ∧ length hist - 1 = ver) →
    ¬ (Nat.even k = false ∧ ec.(e_blk) = e.(e_blk)) → length hist - 1 ≠ ver.
  Proof.
    intros Hwf Hle He Hno1 Hno2 Heq. destruct (Nat.even k) eqn:Heven.
    - by apply Hno1.
    - apply Hno2. split; first done.
      rewrite -Heq (wf_current _ _ _ _ _ Hwf) in He. by injection He as ->.
  Qed.

End wf.

Section ghost.
  Context `{!heapGS Σ, !cached_meG Σ}.
  Notation iProp := (iProp Σ).

  (** The resource of a backup: its value followed by its sequence number,
      which never change. *)
  Definition node (vs : list val) (s : nat) (_ : blk) (lv : list val) (_ : gname) : iProp :=
    ⌜lv = vs ++ [ #s ]⌝.

  Lemma tokens_fresh (γ : gname) (hist : list entry) :
    token γ -∗ ([∗ list] e ∈ hist, token e.(e_name)) -∗ ⌜γ ∉ e_name <$> hist⌝.
  Proof.
    iIntros "Htok Htoks" ((e & -> & He)%list_elem_of_fmap).
    iDestruct (big_sepL_elem_of with "Htoks") as "Htok'"; first done.
    iDestruct (token_exclusive with "Htok Htok'") as %[].
  Qed.

End ghost.

Section cached_me.
  Context (cached_meN hazptrN : namespace) (DISJN : cached_meN ## hazptrN).
  Context `{!heapGS Σ, !cached_meG Σ}.
  Notation iProp := (iProp Σ).

  Variable (hazptr : hazard_pointer_spec Σ hazptrN).

  (** ** The invariant *)

  Definition llsc_inv (γs : me_names) (γd : gname) (l : loc) (n : nat) : iProp :=
    ∃ (k : nat) (hist : list entry) (ec : entry) (c : list val),
      γs.(γ_abs) ↪VAR{#1/2} (ec.(e_val), length hist - 1) ∗
      mono_list_auth_own γs.(γ_hist) 1 hist ∗
      ([∗ list] e ∈ hist, token e.(e_name)) ∗
      γs.(γ_idx) ↪●MN k ∗
      (l +ₗ cache_off) ↦∗{#1/2} c ∗
      (if Nat.even k then
         (l +ₗ header_off) ↦ #(None &ₜ (length hist - 1)%nat) ∗
         token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} c
       else
         (l +ₗ header_off) ↦ #(Some (Loc.blk_to_loc ec.(e_blk)) &ₜ 0) ∗
         hazptr.(Managed) γd ec.(e_blk) ec.(e_name) (S n) (node ec.(e_val) (length hist - 1))) ∗
      ⌜me_wf n k hist ec c⌝.

  (** ** Representation predicates *)

  Definition CachedME (γ : gname) (vs : list val) (ver : nat) : iProp :=
    ∃ γs, ⌜γ = encode γs⌝ ∗ γs.(γ_abs) ↪VAR{#1/2} (vs, ver).

  Global Instance CachedME_Timeless γ vs ver : Timeless (CachedME γ vs ver).
  Proof. apply _. Qed.

  Definition IsCachedME (γ γd : gname) (v : val) (n : nat) : iProp :=
    ∃ γs (l d : loc), ⌜γ = encode γs⌝ ∗ ⌜v = #l⌝ ∗ ⌜0 < n⌝ ∗
      (l +ₗ domain_off) ↦□ #d ∗ hazptr.(IsHazardDomain) γd d ∗
      inv cached_meN (llsc_inv γs γd l n).

  Global Instance IsCachedME_Persistent γ γd v n : Persistent (IsCachedME γ γd v n).
  Proof. apply _. Qed.

  (** What an LL leaves for the next SC: the version [ver] it read, and either
      the sequence number of [ver] (fast path) or the protected backup of [ver]
      (slow path), together with a lower bound on the index of the header at
      the LL. *)
  Definition link_wit (γ : gname) (ver : nat) (et : val) (st1 : shield_state Σ) : iProp :=
    ∃ γs e, ⌜γ = encode γs⌝ ∗ mono_list_idx_own γs.(γ_hist) ver e ∗
      ((⌜et = #(None &ₜ ver)⌝ ∗ γs.(γ_idx) ↪◯MN (2 * ver)) ∨
       (⌜et = #(Some (Loc.blk_to_loc e.(e_blk)) &ₜ 0)⌝ ∗ ⌜1 ≤ ver⌝ ∗
          ⌜st1 = Validated e.(e_blk) e.(e_name) (node e.(e_val) ver) (S (length e.(e_val)))⌝ ∗
          γs.(γ_idx) ↪◯MN (2 * ver - 1))).

  Definition CachedMEThread (γd : gname) (ctx : val) (link : option (gname * nat)) : iProp :=
    ∃ (c h1 h2 d : loc) (et : val) (st1 st2 : shield_state Σ),
      ⌜ctx = #c⌝ ∗ c ↦∗ [ #h1; #h2; et ] ∗ †c…3 ∗ hazptr.(IsHazardDomain) γd d ∗
      hazptr.(Shield) γd h1 st1 ∗ hazptr.(Shield) γd h2 st2 ∗
      match link with None => True | Some (γ, ver) => link_wit γ ver et st1 end.

  (** ** Reading the cache *)

  (** What an LL knows about the cache when it read the sequence number [s]
      of the entry [e] in the header. *)
  Definition cache_snap (γs : me_names) (oc : option (nat * entry)) : iProp :=
    match oc with
    | Some (s, e) => γs.(γ_idx) ↪◯MN (2 * s) ∗ mono_list_idx_own γs.(γ_hist) s e
    | None => True
    end.

  Global Instance cache_snap_persistent γs oc : Persistent (cache_snap γs oc).
  Proof. destruct oc as [[??]|]; apply _. Qed.

  (** After copying [vs] from offset [i] of the cache: either the header moved
      on, or [vs] is (the corresponding part of) the value of [e]. *)
  Definition cache_good (γs : me_names) (oc : option (nat * entry)) (i : nat) (vs : list val) : iProp :=
    match oc with
    | Some (s, e) => γs.(γ_idx) ↪◯MN (S (2 * s)) ∨ ⌜vs = take (length vs) (drop i e.(e_val))⌝
    | None => True
    end.

  Lemma wp_copy_cache γs γd l n (dst : loc) (i : nat) vdst oc :
    i + length vdst = n →
    inv cached_meN (llsc_inv γs γd l n) -∗
    cache_snap γs oc -∗
    {{{ dst ↦∗ vdst }}}
      array_copy_to #dst #(l +ₗ cache_off +ₗ i) #(length vdst)
    {{{ vs', RET #(); dst ↦∗ vs' ∗ ⌜length vs' = length vdst⌝ ∗ cache_good γs oc i vs' }}}.
  Proof.
    iIntros (Hlen) "#Hinv #Hsnap %Φ !> Hdst HΦ".
    iInduction vdst as [|v0 vdst] "IH" forall (dst i Hlen Φ).
    - wp_rec. wp_pures. iApply ("HΦ" $! []). iModIntro. iFrame. iSplit; first done.
      destruct oc as [[s e]|]; last done. by iRight.
    - wp_rec. wp_pures.
      iDestruct (array_cons with "Hdst") as "[Hv0 Hdst]".
      wp_bind (! _)%E.
      iInv "Hinv" as (k hist ec c) "(Habs & >Hhist & Htoks & >Hk & >Hcache & Hif & >%Hwf)" "Hcl".
      simpl in Hlen.
      assert (is_Some (c !! i)) as [v Hv].
      { apply lookup_lt_is_Some. rewrite (wf_cache_len _ _ _ _ _ Hwf). lia. }
      wp_apply (wp_load_offset with "Hcache") as "Hcache"; first done.
      iAssert (match oc with
               | Some (s, e) => γs.(γ_idx) ↪◯MN (S (2 * s)) ∨ ⌜e.(e_val) !! i = Some v⌝
               | None => True
               end)%I as "#Hgood".
      { destruct oc as [[s e]|]; last done.
        iDestruct "Hsnap" as "[Hlb Hidx]".
        iDestruct (mono_nat_auth_lb_own_valid with "Hk Hlb") as %[_ Hle].
        destruct (decide (k = 2 * s)) as [->|Hne].
        - iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He.
          destruct (wf_even _ _ _ _ _ Hwf (even_double s)) as [Hs ->].
          assert (s = length hist - 1) as -> by lia.
          rewrite (wf_current _ _ _ _ _ Hwf) in He. injection He as ->.
          iRight. done.
        - iLeft. iApply (mono_nat_lb_own_le with "[Hk]"); last by iApply mono_nat_lb_own_get.
          lia. }
      iMod ("Hcl" with "[-Hv0 Hdst HΦ]") as "_".
      { iExists k, hist, ec, c. by iFrame. }
      iModIntro. wp_store. wp_pures.
      rewrite Loc.add_assoc.
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_sub /=; last lia.
      rewrite Nat.sub_0_r -Nat2Z.inj_add.
      wp_apply ("IH" with "[] Hdst"); first (iPureIntro; lia).
      iIntros (vs') "(Hdst & %Hlen' & #Hgood')".
      iApply ("HΦ" $! (v :: vs')). iFrame.
      iSplit; first (iPureIntro; simpl; lia).
      destruct oc as [[s e]|]; last done.
      iDestruct "Hgood" as "[$|%Hvi]".
      iDestruct "Hgood'" as "[$|%Hvs']".
      iRight. iPureIntro. simpl.
      rewrite Nat.add_1_r in Hvs'.
      rewrite (drop_S _ _ _ Hvi) /=. by rewrite -Hvs'.
  Qed.

  Lemma wp_clone_cache γs γd l n oc :
    0 < n →
    inv cached_meN (llsc_inv γs γd l n) -∗
    cache_snap γs oc -∗
    {{{ True }}}
      array_clone #(l +ₗ cache_off) #n
    {{{ (dst : blk) vs', RET #dst;
        dst ↦∗ vs' ∗ †dst…n ∗ ⌜length vs' = n⌝ ∗ cache_good γs oc 0 vs' }}}.
  Proof.
    iIntros (Hpos) "#Hinv #Hsnap %Φ !> _ HΦ".
    wp_lam. wp_alloc dst as "Hdst" "†dst"; first lia.
    wp_pures. rewrite Nat2Z.id.
    rewrite -{1}(Loc.add_0 (l +ₗ cache_off)).
    assert (Z.of_nat n = Z.of_nat (length (replicate n #()))) as ->
      by rewrite length_replicate //.
    change 0%Z with (Z.of_nat 0).
    wp_apply (wp_copy_cache with "Hinv Hsnap Hdst").
    { by rewrite length_replicate. }
    iIntros (vs') "(Hdst & %Hlen & Hgood)".
    wp_pures. iApply "HΦ". iFrame "Hdst †dst Hgood".
    iPureIntro. by rewrite Hlen length_replicate.
  Qed.

  (** ** Reading a protected backup *)

  Lemma wp_copy_backup_off (dst : loc) (q : blk) vdst vs (s : nat) γd h γq (i : nat) :
    i + length vdst = length vs →
    {{{ dst ↦∗ vdst ∗ hazptr.(Shield) γd h (Validated q γq (node vs s) (S (length vs))) }}}
      array_copy_to #dst #(q +ₗ i) #(length vdst)
    {{{ RET #(); dst ↦∗ drop i vs ∗ hazptr.(Shield) γd h (Validated q γq (node vs s) (S (length vs))) }}}.
  Proof.
    iIntros (Hlen Φ) "[Hdst S] HΦ".
    iInduction vdst as [|v vdst] "IH" forall (dst i Hlen Φ).
    { simplify_list_eq. wp_rec. wp_pures. iApply "HΦ".
      iModIntro. replace i with (length vs) in * by lia.
      rewrite drop_all. iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv Hvdst]".
    simplify_list_eq. wp_rec. wp_pures.
    wp_bind (! _)%E.
    wp_apply (shield_read with "S") as (? v') "(S & -> & %EQ)"; [solve_ndisj|lia|].
    rewrite lookup_app_l in EQ; last lia.
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
    assert (v' :: drop (S i) vs = drop i vs) as ->.
    { by rewrite (drop_S _ _ _ EQ). }
    iFrame.
  Qed.

  Lemma wp_copy_backup (dst : loc) (q : blk) vdst vs (s : nat) γd h γq n :
    length vdst = n → length vs = n →
    {{{ dst ↦∗ vdst ∗ hazptr.(Shield) γd h (Validated q γq (node vs s) (S n)) }}}
      array_copy_to #dst #q #n
    {{{ RET #(); dst ↦∗ vs ∗ hazptr.(Shield) γd h (Validated q γq (node vs s) (S n)) }}}.
  Proof.
    iIntros (Hlen_dst Hlen_src Φ) "[Hdst S] HΦ".
    rewrite -(Loc.add_0 q). change 0%Z with (Z.of_nat O). subst n.
    iEval (rewrite -Hlen_src) in "S HΦ".
    wp_apply (wp_copy_backup_off with "[$Hdst $S]"); first lia.
    iIntros "[Hdst S]".
    rewrite drop_0.
    iApply ("HΦ" with "[$]").
  Qed.

  Lemma wp_read_seqnum (q : blk) vs (s : nat) γd h γq n :
    length vs = n →
    {{{ hazptr.(Shield) γd h (Validated q γq (node vs s) (S n)) }}}
      ! #(q +ₗ n)
    {{{ RET #s; hazptr.(Shield) γd h (Validated q γq (node vs s) (S n)) }}}.
  Proof.
    iIntros (Hlen Φ) "S HΦ".
    wp_apply (shield_read with "S") as (? v') "(S & -> & %EQ)"; [solve_ndisj|lia|].
    rewrite lookup_app_r in EQ; last lia.
    rewrite Hlen Nat.sub_diag /= in EQ. injection EQ as <-.
    by iApply "HΦ".
  Qed.

  (** ** Writing the cache as its owner *)

  Lemma wp_write_cache γs γd l n (src : loc) dq (vs : list val) (i j : nat) c :
    length vs = n → i + j = n → length c = n → take i c = take i vs →
    inv cached_meN (llsc_inv γs γd l n) -∗
    {{{ token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} c ∗ src ↦∗{dq} vs }}}
      array_copy_to #(l +ₗ cache_off +ₗ i) #(src +ₗ i) #j
    {{{ RET #(); token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} vs ∗ src ↦∗{dq} vs }}}.
  Proof.
    iIntros (Hlen Hij Hlenc Htake) "#Hinv %Φ !> (Hown & Hc & Hsrc) HΦ".
    iInduction j as [|j] "IH" forall (i c Hij Hlenc Htake).
    { wp_rec. wp_pures. iApply "HΦ". iModIntro. iFrame.
      rewrite !take_ge in Htake; [|lia..]. by subst c. }
    wp_rec. wp_pures.
    assert (is_Some (vs !! i)) as [v Hv] by (apply lookup_lt_is_Some; lia).
    wp_apply (wp_load_offset with "Hsrc") as "Hsrc"; first done.
    wp_bind (_ <- _)%E.
    iInv "Hinv" as (k hist ec c') "(Habs & Hhist & Htoks & Hk & >Hcache & Hif & >%Hwf)" "Hcl".
    destruct (Nat.even k) eqn:Heven.
    { iDestruct "Hif" as "(_ & >Hown' & _)".
      iDestruct (token_exclusive with "Hown Hown'") as %[]. }
    iDestruct (array_agree with "Hc Hcache") as %<-.
    { by rewrite (wf_cache_len _ _ _ _ _ Hwf). }
    iCombine "Hc Hcache" as "Hc".
    wp_apply (wp_store_offset with "Hc") as "Hc".
    { apply lookup_lt_is_Some. lia. }
    iDestruct "Hc" as "[Hc Hcache]".
    iMod ("Hcl" with "[-Hown Hc Hsrc HΦ]") as "_".
    { iExists k, hist, ec, (<[i:=v]> c).
      rewrite Heven. iFrame. iPureIntro.
      apply (wf_write _ _ _ _ c); [done|done|by rewrite length_insert]. }
    iModIntro. wp_pures.
    rewrite Loc.add_assoc (Loc.add_assoc src).
    change 1%Z with (Z.of_nat 1).
    rewrite -!Nat2Z.inj_add.
    replace (Z.of_nat (S j) - Z.of_nat 1)%Z with (Z.of_nat j) by lia.
    wp_apply ("IH" with "[%] [%] [%] Hown Hc Hsrc HΦ").
    - lia.
    - by rewrite length_insert.
    - rewrite Nat.add_1_r (take_S_r _ _ v); last by rewrite list_lookup_insert_eq; [|lia].
      rewrite (take_S_r vs _ v) //.
      rewrite take_insert decide_False; last lia.
      by rewrite Htake.
  Qed.

  Lemma wp_write_cache0 γs γd l n (src : loc) dq (vs : list val) c :
    length vs = n → length c = n →
    inv cached_meN (llsc_inv γs γd l n) -∗
    {{{ token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} c ∗ src ↦∗{dq} vs }}}
      array_copy_to #(l +ₗ cache_off) #src #n
    {{{ RET #(); token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} vs ∗ src ↦∗{dq} vs }}}.
  Proof.
    iIntros (Hlen Hlenc) "#Hinv".
    iPoseProof (wp_write_cache γs γd l n src dq vs 0 n c with "Hinv") as "Hwp"; [done..|].
    by rewrite /= !Loc.add_0.
  Qed.

  Lemma wp_write_cache_backup γs γd l n (q : blk) γq (vs : list val) (s : nat) h (i j : nat) c :
    length vs = n → i + j = n → length c = n → take i c = take i vs →
    inv cached_meN (llsc_inv γs γd l n) -∗
    {{{ token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} c ∗
        hazptr.(Shield) γd h (Validated q γq (node vs s) (S n)) }}}
      array_copy_to #(l +ₗ cache_off +ₗ i) #(q +ₗ i) #j
    {{{ RET #(); token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} vs ∗
        hazptr.(Shield) γd h (Validated q γq (node vs s) (S n)) }}}.
  Proof.
    iIntros (Hlen Hij Hlenc Htake) "#Hinv %Φ !> (Hown & Hc & S) HΦ".
    iInduction j as [|j] "IH" forall (i c Hij Hlenc Htake).
    { wp_rec. wp_pures. iApply "HΦ". iModIntro. iFrame.
      rewrite !take_ge in Htake; [|lia..]. by subst c. }
    wp_rec. wp_pures.
    wp_bind (! _)%E.
    wp_apply (shield_read with "S") as (? v) "(S & -> & %Hv)"; [solve_ndisj|lia|].
    rewrite lookup_app_l in Hv; last lia.
    wp_bind (_ <- _)%E.
    iInv "Hinv" as (k hist ec c') "(Habs & Hhist & Htoks & Hk & >Hcache & Hif & >%Hwf)" "Hcl".
    destruct (Nat.even k) eqn:Heven.
    { iDestruct "Hif" as "(_ & >Hown' & _)".
      iDestruct (token_exclusive with "Hown Hown'") as %[]. }
    iDestruct (array_agree with "Hc Hcache") as %<-.
    { by rewrite (wf_cache_len _ _ _ _ _ Hwf). }
    iCombine "Hc Hcache" as "Hc".
    wp_apply (wp_store_offset with "Hc") as "Hc".
    { apply lookup_lt_is_Some. lia. }
    iDestruct "Hc" as "[Hc Hcache]".
    iMod ("Hcl" with "[-Hown Hc S HΦ]") as "_".
    { iExists k, hist, ec, (<[i:=v]> c).
      rewrite Heven. iFrame. iPureIntro.
      apply (wf_write _ _ _ _ c); [done|done|by rewrite length_insert]. }
    iModIntro. wp_pures.
    rewrite (Loc.add_assoc (l +ₗ cache_off)) (Loc.add_assoc (Loc.blk_to_loc q)).
    change 1%Z with (Z.of_nat 1).
    rewrite -!Nat2Z.inj_add.
    replace (Z.of_nat (S j) - Z.of_nat 1)%Z with (Z.of_nat j) by lia.
    wp_apply ("IH" with "[%] [%] [%] Hown Hc S HΦ").
    - lia.
    - by rewrite length_insert.
    - rewrite Nat.add_1_r (take_S_r _ _ v); last by rewrite list_lookup_insert_eq; [|lia].
      rewrite (take_S_r vs _ v) //.
      rewrite take_insert decide_False; last lia.
      by rewrite Htake.
  Qed.

  Lemma wp_write_cache_backup0 γs γd l n (q : blk) γq (vs : list val) (s : nat) h c :
    length vs = n → length c = n →
    inv cached_meN (llsc_inv γs γd l n) -∗
    {{{ token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} c ∗
        hazptr.(Shield) γd h (Validated q γq (node vs s) (S n)) }}}
      array_copy_to #(l +ₗ cache_off) #q #n
    {{{ RET #(); token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} vs ∗
        hazptr.(Shield) γd h (Validated q γq (node vs s) (S n)) }}}.
  Proof.
    iIntros (Hlen Hlenc) "#Hinv".
    iPoseProof (wp_write_cache_backup γs γd l n q γq vs s h 0 n c with "Hinv") as "Hwp"; [done..|].
    by rewrite /= !Loc.add_0.
  Qed.

  (** ** Allocating a backup *)

  Lemma wp_backup_new n (src : loc) dq (vs : list val) (s : Z) :
    length vs = n →
    {{{ src ↦∗{dq} vs }}}
      backup_new n #src #s
    {{{ (b : blk), RET #b; b ↦∗ (vs ++ [ #s ]) ∗ †b…(S n) ∗ src ↦∗{dq} vs }}}.
  Proof.
    iIntros (Hlen Φ) "Hsrc HΦ".
    wp_lam. wp_pures.
    wp_alloc b as "Hb" "†b".
    wp_pures. rewrite Nat2Z.id replicate_S_end.
    iDestruct (array_app with "Hb") as "[Hb Hlast]".
    wp_apply (wp_array_copy_to with "[$Hb $Hsrc]"); [by rewrite length_replicate|done|].
    iIntros "[Hb Hsrc]". wp_pures.
    rewrite length_replicate array_singleton.
    rewrite -/(Loc.loc_to_tagged_loc _).
    wp_store. iModIntro.
    iApply "HΦ". iFrame "Hsrc †b".
    iApply array_app. rewrite array_singleton Hlen. iFrame.
  Qed.

  (** ** Installing the cache as its owner *)

  (** The owner holds the cache, which holds the value of the backup [q] of
      version [s], protected by one of its shields. *)
  Lemma wp_install_cache γs γd l n (d h1 h2 : loc) (q : blk) γq (vs : list val) (s : nat) st1 st2 :
    0 < n → length vs = n →
    (st1 = Validated q γq (node vs s) (S n) ∨ st2 = Validated q γq (node vs s) (S n)) →
    inv cached_meN (llsc_inv γs γd l n) -∗
    hazptr.(IsHazardDomain) γd d -∗
    mono_list_idx_own γs.(γ_hist) s (Entry γq q vs) -∗
    {{{ token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} vs ∗
        hazptr.(Shield) γd h1 st1 ∗ hazptr.(Shield) γd h2 st2 }}}
      install_cache hazptr n #l #d #h1 #q #s
    {{{ st1' st2', RET #(); hazptr.(Shield) γd h1 st1' ∗ hazptr.(Shield) γd h2 st2' }}}.
  Proof using DISJN.
    iIntros (Hpos Hlen Hprot) "#Hinv #Hdom #Hidx %Φ !> (Hown & Hc & S1 & S2) HΦ".
    iLöb as "IH" forall (q γq vs s st1 st2 Hlen Hprot) "Hidx".
    wp_lam. wp_pures.
    (* The slow path: protect the current backup and copy it into the cache *)
    iAssert (□ ∀ st1' st2', token γs.(γ_own) -∗ (l +ₗ cache_off) ↦∗{#1/2} vs -∗
               hazptr.(Shield) γd h1 st1' -∗ hazptr.(Shield) γd h2 st2' -∗
               (∀ st1' st2', hazptr.(Shield) γd h1 st1' ∗ hazptr.(Shield) γd h2 st2' -∗ Φ #()) -∗
               WP (let: "new_backup" := hazptr.(shield_protect_tagged) #h1 #(l +ₗ header_off) in
                   array_copy_to (#l +ₗ #cache_off) "new_backup" #n;;
                   install_cache hazptr n #l #d #h1 "new_backup" !("new_backup" +ₗ #n)) {{ Φ }})%I
      as "#Hslow".
    { iIntros "!>" (st1' st2') "Hown Hc S1 S2 HΦ".
      wp_pures.
      awp_apply (hazptr.(shield_protect_tagged_spec) with "Hdom S1"); first solve_ndisj.
      rewrite /atomic_acc /=.
      iInv "Hinv" as (k hist ec c) "(Habs & Hhist & Htoks & Hk & Hcache & Hif & >%Hwf)" "Hcl".
      destruct (Nat.even k) eqn:Heven.
      { iDestruct "Hif" as "(_ & >Hown' & _)".
        iDestruct (token_exclusive with "Hown Hown'") as %[]. }
      iDestruct "Hif" as "[>Hhdr Hman]".
      iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first solve_ndisj.
      iModIntro. iExists ec.(e_blk), 0, ec.(e_name), (S n), (node ec.(e_val) (length hist - 1)).
      rewrite Loc.add_0. iFrame "Hhdr Hman".
      iSplit.
      { iIntros "[Hhdr Hman]". iMod "Hclose" as "_".
        iMod ("Hcl" with "[-Hown Hc S2 HΦ]") as "_".
        { iExists k, hist, ec, c. rewrite Heven Loc.add_0. by iFrame. }
        by iFrame. }
      iIntros "(Hhdr & Hman & S1)". iMod "Hclose" as "_".
      iDestruct (mono_list_lb_own_get with "Hhist") as "#Hlb".
      iPoseProof (mono_list_idx_own_get _ _ (wf_current _ _ _ _ _ Hwf) with "Hlb") as "#Hidx'".
      pose proof (wf_ec_len _ _ _ _ _ Hwf) as Heclen.
      iMod ("Hcl" with "[-Hown Hc S1 S2 HΦ]") as "_".
      { iExists k, hist, ec, c. rewrite Heven Loc.add_0. by iFrame. }
      iModIntro. wp_pures.
      destruct ec as [γe qe ve]. simpl in *.
      wp_apply (wp_write_cache_backup0 with "Hinv [$Hown $Hc $S1]"); [done|done|].
      iIntros "(Hown & Hc & S1)". wp_pures.
      rewrite -/(Loc.loc_to_tagged_loc _).
      wp_apply (wp_read_seqnum with "S1") as "S1"; first done.
      wp_apply ("IH" with "[%] [%] Hown Hc S1 S2 HΦ Hidx'"); [done|by left]. }
    wp_bind (! _)%E.
    iInv "Hinv" as (k hist ec c) "(Habs & Hhist & Htoks & Hk & Hcache & Hif & >%Hwf)" "Hcl".
    destruct (Nat.even k) eqn:Heven.
    { iDestruct "Hif" as "(_ & >Hown' & _)".
      iDestruct (token_exclusive with "Hown Hown'") as %[]. }
    iDestruct "Hif" as "[>Hhdr Hman]".
    rewrite -/(Loc.loc_to_tagged_loc _).
    wp_load.
    iMod ("Hcl" with "[-Hown Hc S1 S2 HΦ]") as "_".
    { iExists k, hist, ec, c. rewrite Heven. by iFrame. }
    iModIntro.
    destruct (decide (ec.(e_blk) = q)) as [Hq|Hne]; last first.
    { wp_pures. rewrite bool_decide_eq_false_2; last first.
      { intros [= Heq]. apply Hne. by apply (inj Loc.blk_to_loc), (inj Some). }
      wp_pures. iApply ("Hslow" with "Hown Hc S1 S2 HΦ"). }
    subst q. wp_pures.
    (* Replace the pointer by its sequence number *)
    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as (k2 hist2 ec2 c2) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf2)" "Hcl".
    destruct (Nat.even k2) eqn:Heven2.
    { iDestruct "Hif" as "(_ & >Hown' & _)".
      iDestruct (token_exclusive with "Hown Hown'") as %[]. }
    iDestruct "Hif" as "[>Hhdr Hman]".
    rewrite -/(Loc.loc_to_tagged_loc _).
    destruct (decide (ec2.(e_blk) = ec.(e_blk))) as [Hq2|Hne2]; last first.
    { wp_cmpxchg_fail.
      iMod ("Hcl" with "[-Hown Hc S1 S2 HΦ]") as "_".
      { iExists k2, hist2, ec2, c2. rewrite Heven2. by iFrame. }
      iModIntro. wp_pures. iApply ("Hslow" with "Hown Hc S1 S2 HΦ"). }
    rewrite Hq2. wp_cmpxchg_suc.
    (* The backup of version [s] is the current one *)
    iAssert ⌜γq = ec2.(e_name)⌝%I as %Hγ.
    { destruct Hprot as [-> | ->].
      - iApply (hazptr.(shield_managed_agree) with "S1 Hman").
      - iApply (hazptr.(shield_managed_agree) with "S2 Hman"). }
    iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %Hs.
    pose proof (wf_current _ _ _ _ _ Hwf2) as Hcur.
    assert (s = length hist2 - 1) as ->.
    { eapply (NoDup_lookup (e_name <$> hist2)); [apply Hwf2| |].
      - by rewrite list_lookup_fmap Hs.
      - by rewrite list_lookup_fmap Hcur /= Hγ. }
    rewrite Hcur in Hs. injection Hs as ->.
    iDestruct (array_agree with "Hc Hcache") as %<-.
    { by rewrite (wf_cache_len _ _ _ _ _ Hwf2). }
    iMod (mono_nat_own_update (S k2) with "Hk") as "[Hk _]"; first lia.
    iMod ("Hcl" with "[-Hman S1 S2 HΦ]") as "_".
    { iExists (S k2), hist2, (Entry γq ec.(e_blk) vs), vs.
      rewrite Nat.even_succ -Nat.negb_even Heven2 /=. iFrame.
      iPureIntro. by apply wf_unmark. }
    iModIntro. wp_pures.
    wp_apply (hazptr.(hazard_domain_retire_spec) with "Hdom Hman") as "_"; first solve_ndisj.
    iApply "HΦ". iFrame.
  Qed.

  (** ** Linearization points of SC *)

  (** The atomic update of SC *)
  Definition AU_sc (γ : gname) (ver : nat) (desired : list val) (Q : bool → iProp) (Φ : val → iProp) : iProp :=
    AU <{ ∃∃ actual ver', CachedME γ actual ver' }>
       @ ⊤ ∖ (↑cached_meN ∪ ↑ptrsN hazptrN), ↑mgmtN hazptrN
       <{ if bool_decide (ver' = ver) then CachedME γ desired (S ver') else CachedME γ actual ver',
          COMM Q (bool_decide (ver' = ver)) -∗ Φ #(bool_decide (ver' = ver)) }>.

  (** A failing SC, when the version has changed since its LL. *)
  Lemma sc_commit_fail γs ver desired (Q : bool → iProp) Φ (vs : list val) (cur : nat) :
    cur ≠ ver →
    γs.(γ_abs) ↪VAR{#1/2} (vs, cur) -∗
    AU_sc (encode γs) ver desired Q Φ ={⊤ ∖ ↑cached_meN}=∗
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

  (** A successful SC, when the version is [ver]: it installs the backup [b]
      and appends its entry to the history. *)
  Lemma sc_commit_success γs γd (d : loc) n hist ec desired (Q : bool → iProp) Φ
      (b : blk) γ_new (h2 : loc) :
    length desired = n → 0 < length hist →
    γ_new ∉ e_name <$> hist →
    hazptr.(IsHazardDomain) γd d -∗
    hazptr.(Shield) γd h2 (NotValidated b) -∗
    b ↦∗ (desired ++ [ #(S (length hist - 1)) ]) -∗ †b…(S n) -∗
    γs.(γ_abs) ↪VAR{#1/2} (ec.(e_val), length hist - 1) -∗
    mono_list_auth_own γs.(γ_hist) 1 hist -∗
    AU_sc (encode γs) (length hist - 1) desired Q Φ ={⊤ ∖ ↑cached_meN}=∗
    γs.(γ_abs) ↪VAR{#1/2} (desired, length (hist ++ [Entry γ_new b desired]) - 1) ∗
    mono_list_auth_own γs.(γ_hist) 1 (hist ++ [Entry γ_new b desired]) ∗
    mono_list_idx_own γs.(γ_hist) (length hist) (Entry γ_new b desired) ∗
    hazptr.(Managed) γd b γ_new (S n) (node desired (length (hist ++ [Entry γ_new b desired]) - 1)) ∗
    hazptr.(Shield) γd h2 (Validated b γ_new (node desired (length (hist ++ [Entry γ_new b desired]) - 1)) (S n)) ∗
    (Q true -∗ Φ #true).
  Proof using DISJN.
    iIntros (Hlen Hpos Hfresh) "#Hdom S2 Hb †b Habs Hhist AU".
    assert (length (hist ++ [Entry γ_new b desired]) - 1 = length hist) as ->.
    { rewrite length_app /=. lia. }
    replace (S (length hist - 1)) with (length hist) by lia.
    iMod (hazptr.(hazard_domain_register) (node desired (length hist)) with "Hdom [$Hb †b]") as "Hman";
      first solve_ndisj.
    { rewrite length_app /= Hlen Nat.add_1_r. by iFrame. }
    rewrite length_app /= Hlen Nat.add_1_r.
    iMod (hazptr.(shield_validate) with "Hdom Hman S2") as "[Hman S2]"; first solve_ndisj.
    iMod (mono_list_auth_own_update_app [Entry γ_new b desired] with "Hhist") as "[Hhist #Hhist_lb]".
    iPoseProof (mono_list_idx_own_get (length hist) (Entry γ_new b desired) with "Hhist_lb") as "#Hidx_new".
    { by rewrite lookup_app_r // Nat.sub_diag. }
    iMod "AU" as (actual ver') "[(%γs' & %Henc & Hba) [_ Hcommit]]".
    apply (inj encode) in Henc as <-.
    iDestruct (ghost_var_agree with "Habs Hba") as %[= <- <-].
    iMod (ghost_var_update_halves (desired, length hist) with "Habs Hba") as "[Habs Hba]".
    rewrite bool_decide_eq_true_2 //.
    iMod ("Hcommit" with "[Hba]") as "HΦ".
    { iExists γs. replace (S (length hist - 1)) with (length hist) by lia. by iFrame. }
    by iFrame "∗ #".
  Qed.

  (** The atomic update of LL *)
  Definition AU_ll (γ γd : gname) (c : loc) (n : nat) (Φ : val → iProp) : iProp :=
    AU <{ ∃∃ vs ver, CachedME γ vs ver }>
       @ ⊤ ∖ (↑cached_meN ∪ ↑ptrsN hazptrN), ↑mgmtN hazptrN
       <{ ∀∀ l : loc, CachedME γ vs ver,
          COMM l ↦∗ vs ∗ †l…n ∗ ⌜length vs = n⌝ ∗ CachedMEThread γd #c (Some (γ, ver)) -∗ Φ #l }>.

  (** ** Reading the header in LL *)

  Lemma wp_read_hdr1 γs γd l n :
    inv cached_meN (llsc_inv γs γd l n) -∗
    {{{ True }}}
      ! #(l +ₗ header_off)
    {{{ (x : Loc.tagged_loc) oc, RET #x; cache_snap γs oc ∗
        ⌜(∃ (s : nat) e, oc = Some (s, e) ∧ x = None &ₜ s) ∨
         (oc = None ∧ ∃ p : blk, x = Some (Loc.blk_to_loc p) &ₜ 0)⌝ }}}.
  Proof.
    iIntros "#Hinv %Φ !> _ HΦ".
    iInv "Hinv" as (k hist ec c) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf)" "Hcl".
    destruct (Nat.even k) eqn:Heven.
    - iDestruct "Hif" as "(>Hhdr & Hown & Hc)".
      wp_load.
      iPoseProof (mono_nat_lb_own_get with "Hk") as "#Hlb".
      iPoseProof (mono_list_lb_own_get with "Hhist") as "#Hhist_lb".
      iPoseProof (mono_list_idx_own_get _ _ (wf_current _ _ _ _ _ Hwf) with "Hhist_lb") as "#Hidx".
      destruct (wf_even _ _ _ _ _ Hwf Heven) as [Hk _].
      iMod ("Hcl" with "[-HΦ]") as "_".
      { iExists k, hist, ec, c. rewrite Heven. by iFrame. }
      iModIntro. iApply ("HΦ" $! _ (Some (length hist - 1, ec))).
      iSplit; first (iSplit; [by rewrite -Hk|done]).
      iPureIntro. left. by eexists _, _.
    - iDestruct "Hif" as "(>Hhdr & Hman)".
      wp_load.
      iMod ("Hcl" with "[-HΦ]") as "_".
      { iExists k, hist, ec, c. rewrite Heven. by iFrame. }
      iModIntro. iApply ("HΦ" $! _ None). iSplit; first done.
      iPureIntro. right. split; first done. by eexists.
  Qed.

  (** A successful SC that replaced the sequence number of the current version
      by its backup [b]: linearize it and close the invariant. The SC becomes
      the owner of the cache. *)
  Lemma sc_commit_seq γs γd l n (d h2 : loc) k hist ec cc desired (b : blk) (Q : bool → iProp) Φ :
    me_wf n k hist ec cc → Nat.even k = true → length desired = n →
    hazptr.(IsHazardDomain) γd d -∗
    hazptr.(Shield) γd h2 (NotValidated b) -∗
    b ↦∗ (desired ++ [ #(S (length hist - 1)) ]) -∗ †b…(S n) -∗
    AU_sc (encode γs) (length hist - 1) desired Q Φ -∗
    γs.(γ_abs) ↪VAR{#1/2} (ec.(e_val), length hist - 1) -∗
    mono_list_auth_own γs.(γ_hist) 1 hist -∗
    ([∗ list] e ∈ hist, token e.(e_name)) -∗
    γs.(γ_idx) ↪●MN k -∗
    (l +ₗ cache_off) ↦∗{#1/2} cc -∗
    (l +ₗ header_off) ↦ #b -∗
    (▷ llsc_inv γs γd l n ={⊤ ∖ ↑cached_meN, ⊤}=∗ emp) ={⊤ ∖ ↑cached_meN, ⊤}=∗
    ∃ γ_new, ⌜length cc = n⌝ ∗
      hazptr.(Shield) γd h2 (Validated b γ_new (node desired (S (length hist - 1))) (S n)) ∗
      mono_list_idx_own γs.(γ_hist) (S (length hist - 1)) (Entry γ_new b desired) ∗
      (Q true -∗ Φ #true).
  Proof using DISJN.
    iIntros (Hwf Heven Hlen) "#Hdom S2 Hb †b AU Habs Hhist Htoks Hk Hcache Hhdr Hcl".
    iMod token_alloc as (γ_new) "Htok".
    iDestruct (tokens_fresh with "Htok Htoks") as %Hfresh.
    pose proof (wf_length_pos _ _ _ _ _ Hwf).
    iMod (sc_commit_success with "Hdom S2 Hb †b Habs Hhist AU")
      as "(Habs & Hhist & #Hidx_new & Hman & S2 & HΦ)"; [done|done|done|].
    iMod (mono_nat_own_update (S k) with "Hk") as "[Hk _]"; first lia.
    iMod ("Hcl" with "[-HΦ S2]") as "_".
    { iExists (S k), (hist ++ [Entry γ_new b desired]), (Entry γ_new b desired), cc.
      rewrite Nat.even_succ -Nat.negb_even Heven big_sepL_snoc /=. iFrame.
      iPureIntro. pose proof (wf_install _ _ _ _ _ (Entry γ_new b desired) Hwf) as Hwf'.
      rewrite Heven in Hwf'. by apply Hwf'. }
    assert (length (hist ++ [Entry γ_new b desired]) - 1 = S (length hist - 1)) as Hlen'.
    { rewrite length_app /=. lia. }
    rewrite Hlen'. iModIntro. iExists γ_new. iFrame "S2 HΦ".
    iSplit; first (iPureIntro; apply (wf_cache_len _ _ _ _ _ Hwf)).
    by replace (S (length hist - 1)) with (length hist) by lia.
  Qed.

  (** Stage 3 of SC, as the owner of the cache *)
  Lemma wp_sc_stage3 γs γd l n (d c h1 h2 : loc) (et : val) st1 (b : blk) γ_new (s : nat)
      desired (l_desired : loc) dq cc :
    length desired = n → length cc = n → 0 < n →
    inv cached_meN (llsc_inv γs γd l n) -∗
    hazptr.(IsHazardDomain) γd d -∗
    mono_list_idx_own γs.(γ_hist) s (Entry γ_new b desired) -∗
    {{{ token γs.(γ_own) ∗ (l +ₗ cache_off) ↦∗{#1/2} cc ∗ l_desired ↦∗{dq} desired ∗
        c ↦∗ [ #h1; #h2; et ] ∗ hazptr.(Shield) γd h1 st1 ∗
        hazptr.(Shield) γd h2 (Validated b γ_new (node desired s) (S n)) }}}
      array_copy_to #(l +ₗ cache_off) #l_desired #n;;
      install_cache hazptr n #l #d !(#c +ₗ #h1_off) #b #s
    {{{ st1' st2', RET #(); l_desired ↦∗{dq} desired ∗ c ↦∗ [ #h1; #h2; et ] ∗
        hazptr.(Shield) γd h1 st1' ∗ hazptr.(Shield) γd h2 st2' }}}.
  Proof using DISJN.
    iIntros (Hlen Hcc Hpos) "#Hinv #Hdom #Hidx %Φ !> (Hown & Hcc & Hdes & Hc & S1 & S2) HΦ".
    wp_apply (wp_write_cache0 with "Hinv [$Hown $Hcc $Hdes]"); [done|done|].
    iIntros "(Hown & Hcc & Hdes)". wp_pures.
    wp_apply (wp_load_offset _ _ _ _ 0 with "Hc") as "Hc"; first done.
    wp_apply (wp_install_cache with "Hinv Hdom Hidx [$Hown $Hcc $S1 $S2]"); [done|done|by right|].
    iIntros (st1' st2') "[S1 S2]".
    iApply "HΦ". iFrame.
  Qed.

  (** The second [cmp_xch] of SC, after it saw the sequence number of the
      version [ver] of its LL. *)
  Lemma wp_sc_cas2 γs γd l n (d c h1 h2 : loc) (et : val) st1 ver desired (l_desired : loc) dq
      (b : blk) (Q : bool → iProp) Φ :
    length desired = n → 0 < n →
    inv cached_meN (llsc_inv γs γd l n) -∗
    hazptr.(IsHazardDomain) γd d -∗
    γs.(γ_idx) ↪◯MN (2 * ver) -∗
    AU_sc (encode γs) ver desired Q Φ -∗
    (∀ st1' st2' (bb : bool), c ↦∗ [ #h1; #h2; et ] -∗ hazptr.(Shield) γd h1 st1' -∗
       hazptr.(Shield) γd h2 st2' -∗ l_desired ↦∗{dq} desired -∗ ⌜bb = false → st1' = st1⌝ -∗ Q bb) -∗
    c ↦∗ [ #h1; #h2; et ] -∗ hazptr.(Shield) γd h1 st1 -∗ hazptr.(Shield) γd h2 (NotValidated b) -∗
    l_desired ↦∗{dq} desired -∗ b ↦∗ (desired ++ [ #(S ver) ]) -∗ †b…(S n) -∗
    WP (if: Snd (CmpXchg #(l +ₗ header_off) #(None &ₜ ver) #b) then
          (if: is_pointer #(None &ₜ ver)
           then hazptr.(hazard_domain_retire) #d et #(S n)
           else array_copy_to (#l +ₗ #cache_off) #l_desired #n;;
                install_cache hazptr n #l #d !(#c +ₗ #h1_off) #b #(S ver));; #true
        else Free #(S n) #b;; #false) {{ Φ }}.
  Proof using DISJN.
    iIntros (Hlen Hpos) "#Hinv #Hdom #Hlb AU HQ Hc S1 S2 Hdes Hb †b".
    wp_bind (CmpXchg _ _ _).
    iInv "Hinv" as (k hist ec cc) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf)" "Hcl".
    iDestruct (mono_nat_auth_lb_own_valid with "Hk Hlb") as %[_ Hk].
    destruct (decide (Nat.even k = true ∧ length hist - 1 = ver)) as [[Heven Hv]|Hno].
    - (* Success: linearize *)
      rewrite Heven. iDestruct "Hif" as "(>Hhdr & Hown & Hcc)".
      rewrite Hv. wp_cmpxchg_suc.
      subst ver.
      iMod (sc_commit_seq with "Hdom S2 Hb †b AU Habs Hhist Htoks Hk Hcache Hhdr Hcl")
        as (γ_new) "(%Hcclen & S2 & #Hidx_new & HΦ)"; [done..|].
      iModIntro. rewrite /is_pointer. wp_pures.
      wp_apply (wp_sc_stage3 with "Hinv Hdom Hidx_new [$Hown $Hcc $Hdes $Hc $S1 $S2]"); [done..|].
      iIntros (st1' st2') "(Hdes & Hc & S1 & S2)". wp_pures.
      iModIntro. iApply "HΦ". iApply ("HQ" $! _ _ true with "Hc S1 S2 Hdes"). done.
    - (* Failure: the version has changed *)
      iAssert (⌜length hist - 1 ≠ ver⌝)%I as %Hne.
      { iPureIntro. eapply wf_ver_ne_seq; [done|lia|done]. }
      iMod (sc_commit_fail with "Habs AU") as "[Habs HΦ]"; first done.
      destruct (Nat.even k) eqn:Heven;
        iDestruct "Hif" as "(>Hhdr & Hif)";
        (wp_cmpxchg_fail; try (intros [= ?]; apply Hno; split; [done|lia]));
        (iMod ("Hcl" with "[-HΦ HQ Hc S1 S2 Hdes Hb †b]") as "_";
         [iExists k, hist, ec, cc; rewrite Heven; by iFrame|]);
        iModIntro; wp_pures;
        (wp_free; try (rewrite length_app /= Hlen; lia));
        iModIntro; iApply "HΦ"; by iApply ("HQ" $! _ _ false with "Hc S1 S2 Hdes").
  Qed.

  (** ** Specifications *)

  Lemma cached_me_new_spec :
    big_atomic_llsc_new_spec' cached_meN hazptrN cached_me_new hazptr CachedME IsCachedME.
  Proof.
    iIntros (γd d n src dq vs Hpos Hlen Φ) "[#Hdom Hsrc] HΦ".
    wp_rec. wp_pures.
    wp_alloc l as "Hl" "†Hl". wp_pures.
    rewrite Nat2Z.id /= array_cons array_cons.
    iDestruct "Hl" as "(Hhdr & Hdomain & Hcache)".
    rewrite !Loc.add_assoc /=.
    rewrite -{1}(Loc.add_0 l).
    wp_store. wp_pures. wp_store. wp_pures.
    wp_apply (wp_array_copy_to with "[$Hcache $Hsrc]"); [by rewrite length_replicate|done|].
    iIntros "[[Hcache Hcache'] Hsrc]". wp_pures.
    subst n.
    iMod token_alloc as (γ0) "Hγ0".
    iMod token_alloc as (γo) "Hγo".
    set e0 := Entry γ0 inhabitant vs.
    iMod (mono_list_own_alloc [e0]) as (γh) "[Hγh _]".
    iMod (ghost_var_alloc (vs, 0)) as (γa) "[Hγa Hγa']".
    iMod (mono_nat_own_alloc 0) as (γk) "[Hγk _]".
    set γs := MENames γa γh γk γo.
    iMod (inv_alloc cached_meN _ (llsc_inv γs γd l (length vs))
      with "[-HΦ Hdomain Hγa' Hsrc]") as "#Hinv".
    { iNext. iExists 0, [e0], e0, vs. rewrite /=. iFrame.
      iPureIntro. constructor; simpl.
      - done.
      - by rewrite Forall_singleton.
      - done.
      - apply NoDup_singleton.
      - done.
      - done. }
    iMod (pointsto_persist with "Hdomain") as "#Hdomain".
    iModIntro. iApply "HΦ". iFrame "Hsrc".
    iSplitR.
    - iExists γs, l, d. iFrame "#". iPureIntro. split_and!; [done|done|lia].
    - iExists γs. by iFrame.
  Qed.

  Lemma cached_me_thread_new_spec :
    big_atomic_llsc_thread_new_spec' cached_meN hazptrN (llsc_thread_new hazptr) hazptr CachedMEThread.
  Proof.
    iIntros (γd d Φ) "#Hdom HΦ".
    wp_lam. wp_alloc c as "Hc" "†c". wp_pures.
    rewrite /= !array_cons array_nil.
    iDestruct "Hc" as "(Hc0 & Hc1 & Hc2 & _)".
    wp_apply (hazptr.(shield_new_spec) with "Hdom [//]") as (s1) "S1"; first solve_ndisj.
    wp_pures. rewrite Loc.add_0. wp_store. wp_pures.
    wp_apply (hazptr.(shield_new_spec) with "Hdom [//]") as (s2) "S2"; first solve_ndisj.
    wp_pures. wp_store. wp_pures. rewrite Loc.add_assoc /=. wp_store.
    iModIntro. iApply "HΦ".
    iExists c, s1, s2, d, _, _, _. iFrame "∗ #". iSplit; first done.
    by rewrite array_nil.
  Qed.

  Lemma cached_me_thread_drop_spec :
    big_atomic_llsc_thread_drop_spec' cached_meN (llsc_thread_drop hazptr) CachedMEThread.
  Proof.
    iIntros (γd ctx link Φ) "(%c & %h1 & %h2 & %d & %et & %st1 & %st2 & -> & Hc & †c & #Hdom & S1 & S2 & _) HΦ".
    wp_lam. wp_pures.
    wp_apply (wp_load_offset _ _ _ _ 0 with "Hc") as "Hc"; first done.
    wp_apply (hazptr.(shield_drop_spec) with "Hdom S1") as "_"; first solve_ndisj.
    wp_pures.
    wp_apply (wp_load_offset _ _ _ _ 1 with "Hc") as "Hc"; first done.
    wp_apply (hazptr.(shield_drop_spec) with "Hdom S2") as "_"; first solve_ndisj.
    wp_pures. wp_free; first done.
    by iApply "HΦ".
  Qed.

  Lemma cached_me_ll_spec :
    big_atomic_llsc_ll_spec' cached_meN hazptrN (cached_me_ll hazptr) CachedME IsCachedME CachedMEThread.
  Proof using DISJN.
    iIntros (γ γd ba n ctx link)
      "(%γs & %l & %d & -> & -> & %Hpos & #Hdomloc & #Hdom & #Hinv)
       (%c & %h1 & %h2 & %d' & %et & %st1 & %st2 & -> & Hc & †c & #Hdom' & S1 & S2 & _)".
    iIntros (Φ) "AU".
    iAssert (AU_ll (encode γs) γd c n Φ) with "[AU]" as "AU".
    { rewrite /AU_ll /=. iExact "AU". }
    iLöb as "IH" forall (et st1).
    wp_lam. wp_pures.
    wp_apply (wp_read_hdr1 with "Hinv [//]") as (x1 oc) "[#Hsnap %Hx1]".
    wp_pures.
    wp_apply (wp_clone_cache with "Hinv Hsnap [//]"); first done.
    iIntros (dst vs') "(Hdst & †dst & %Hlen' & #Hgood)".
    wp_pures.
    (* The slow path, which linearizes at the protected load of the header if
       it is a pointer, and retries otherwise *)
    iAssert (AU_ll (encode γs) γd c n Φ -∗ c ↦∗ [ #h1; #h2; et ] -∗ †c…3 -∗
             hazptr.(Shield) γd h1 st1 -∗ hazptr.(Shield) γd h2 st2 -∗ dst ↦∗ vs' -∗ †dst…n -∗
             WP (let: "hdr" := hazptr.(shield_protect_tagged) !#(c +ₗ h1_off) #(l +ₗ header_off) in
                 if: is_pointer "hdr" then
                   #c +ₗ #expected_tag_off <- "hdr";; array_copy_to #dst "hdr" #n;; #dst
                 else Free #n #dst;; cached_me_ll hazptr n #l #c) {{ Φ }})%I as "Hslow".
    { iIntros "AU Hc †c S1 S2 Hdst †dst".
      wp_apply (wp_load_offset _ _ _ _ 0 with "Hc") as "Hc"; first done.
      awp_apply (hazptr.(shield_protect_tagged_opt_spec) with "Hdom' S1"); first solve_ndisj.
      rewrite /atomic_acc /=.
      iInv "Hinv" as (k hist ec cc) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf)" "Hcl".
      iMod "AU" as (vs ver) "[(%γs' & %Henc & Hba) Hlin]".
      apply (inj encode) in Henc as <-.
      iDestruct (ghost_var_agree with "Habs Hba") as %[= <- <-].
      destruct (Nat.even k) eqn:Heven.
      - (* A sequence number: retry *)
        iDestruct "Hif" as "(>Hhdr & Hown & Hcc)".
        iModIntro. iExists None, (length hist - 1), inhabitant, 0, (λ _ _ _, True)%I.
        iFrame "Hhdr". iSplit.
        { iIntros "[Hhdr _]". iDestruct "Hlin" as "[Habort _]".
          iMod ("Habort" with "[Hba]") as "AU"; first (iExists γs; by iFrame).
          iMod ("Hcl" with "[-AU Hc †c S2 Hdst †dst]") as "_".
          { iExists k, hist, ec, cc. rewrite Heven. by iFrame. }
          by iFrame. }
        iIntros "[Hhdr S1]". iDestruct "Hlin" as "[Habort _]".
        iMod ("Habort" with "[Hba]") as "AU"; first (iExists γs; by iFrame).
        iMod ("Hcl" with "[-AU Hc †c S1 S2 Hdst †dst]") as "_".
        { iExists k, hist, ec, cc. rewrite Heven. by iFrame. }
        iModIntro. rewrite /is_pointer. wp_pures.
        wp_free; first by rewrite Hlen'.
        wp_pures.
        iApply ("IH" with "Hc †c S1 S2 AU").
      - (* A pointer: commit *)
        iDestruct "Hif" as "(>Hhdr & Hman)".
        iModIntro. iExists (Some ec.(e_blk)), 0, ec.(e_name), (S n), (node ec.(e_val) (length hist - 1)).
        iFrame "Hhdr Hman". iSplit.
        { iIntros "[Hhdr Hman]". iDestruct "Hlin" as "[Habort _]".
          iMod ("Habort" with "[Hba]") as "AU"; first (iExists γs; by iFrame).
          iMod ("Hcl" with "[-AU Hc †c S2 Hdst †dst]") as "_".
          { iExists k, hist, ec, cc. rewrite Heven. by iFrame. }
          by iFrame. }
        iIntros "(Hhdr & Hman & S1)". iDestruct "Hlin" as "[_ Hcommit]".
        iMod ("Hcommit" $! (Loc.blk_to_loc dst) with "[Hba]") as "HΦ"; first (iExists γs; by iFrame).
        iPoseProof (mono_nat_lb_own_get with "Hk") as "#Hlb".
        iPoseProof (mono_list_lb_own_get with "Hhist") as "#Hhist_lb".
        iPoseProof (mono_list_idx_own_get _ _ (wf_current _ _ _ _ _ Hwf) with "Hhist_lb") as "#Hidx".
        pose proof (wf_odd _ _ _ _ _ Hwf Heven) as Hk.
        pose proof (wf_ec_len _ _ _ _ _ Hwf) as Heclen.
        iMod ("Hcl" with "[-HΦ Hc †c S1 S2 Hdst †dst]") as "_".
        { iExists k, hist, ec, cc. rewrite Heven. by iFrame. }
        iModIntro. rewrite /is_pointer. wp_pures.
        wp_apply (wp_store_offset with "Hc") as "Hc"; first done.
        wp_pures.
        rewrite -/(Loc.loc_to_tagged_loc _).
        wp_apply (wp_copy_backup with "[$Hdst $S1]"); [done|done|].
        iIntros "[Hdst S1]". wp_pures.
        iModIntro. iApply "HΦ". iFrame "Hdst †dst".
        iSplit; first done.
        iExists c, h1, h2, d', _, _, st2. iFrame "∗ #". iSplit; first done.
        iSplit; first done.
        iRight. rewrite Heclen. iSplit; first done.
        iSplit; first (iPureIntro; lia).
        iSplit; first done.
        by replace (2 * (length hist - 1) - 1) with k by lia. }
    (* [hdr2]: the linearization point of the fast path *)
    wp_bind (! _)%E.
    iInv "Hinv" as (k2 hist2 ec2 c2) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf2)" "Hcl".
    rewrite -/(Loc.loc_to_tagged_loc _).
    destruct Hx1 as [(s & e & -> & ->)|(-> & p & ->)]; last first.
    { (* [hdr1] was a pointer *)
      destruct (Nat.even k2) eqn:Heven2;
        iDestruct "Hif" as "(>Hhdr & Hif)"; wp_load;
        (iMod ("Hcl" with "[-AU Hc †c S1 S2 Hdst †dst Hslow]") as "_";
         [iExists k2, hist2, ec2, c2; rewrite Heven2; by iFrame|]);
        iModIntro; rewrite /is_pointer; wp_pures;
        iApply ("Hslow" with "AU Hc †c S1 S2 Hdst †dst"). }
    destruct (decide (Nat.even k2 = true ∧ length hist2 - 1 = s)) as [[Heven2 <-]|Hno].
    - (* Fast path: the header did not change, so the cache held the current value *)
      rewrite Heven2. iDestruct "Hif" as "(>Hhdr & Hif)". wp_load.
      iDestruct "Hsnap" as "[Hlb Hidx]".
      iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He.
      rewrite (wf_current _ _ _ _ _ Hwf2) in He. injection He as ->.
      destruct (wf_even _ _ _ _ _ Hwf2 Heven2) as [Hk2 _].
      iAssert ⌜vs' = e.(e_val)⌝%I as %->.
      { iDestruct "Hgood" as "[Hlb'|%Hgood]".
        - iDestruct (mono_nat_auth_lb_own_valid with "Hk Hlb'") as %[_ ?]. lia.
        - iPureIntro. rewrite Hgood drop_0 take_ge //. rewrite (wf_ec_len _ _ _ _ _ Hwf2). lia. }
      iMod "AU" as (vs ver) "[(%γs' & %Henc & Hba) [_ Hcommit]]".
      apply (inj encode) in Henc as <-.
      iDestruct (ghost_var_agree with "Habs Hba") as %[= <- <-].
      iMod ("Hcommit" $! (Loc.blk_to_loc dst) with "[Hba]") as "HΦ"; first (iExists γs; by iFrame).
      iMod ("Hcl" with "[-HΦ Hc †c S1 S2 Hdst †dst]") as "_".
      { iExists k2, hist2, e, c2. rewrite Heven2. by iFrame. }
      iModIntro. rewrite /is_pointer. wp_pures.
      rewrite bool_decide_eq_true_2 //. wp_pures.
      wp_apply (wp_store_offset with "Hc") as "Hc"; first done.
      wp_pures. iModIntro. iApply "HΦ". iFrame "Hdst †dst".
      iSplit; first (iPureIntro; apply (wf_ec_len _ _ _ _ _ Hwf2)).
      iExists c, h1, h2, d', _, st1, st2. iFrame "∗ #". iSplit; first done.
      iSplit; first done. by iLeft.
    - (* The header changed: take the slow path *)
      destruct (Nat.even k2) eqn:Heven2;
        iDestruct "Hif" as "(>Hhdr & Hif)"; wp_load;
        (iMod ("Hcl" with "[-AU Hc †c S1 S2 Hdst †dst Hslow]") as "_";
         [iExists k2, hist2, ec2, c2; rewrite Heven2; by iFrame|]);
        iModIntro; rewrite /is_pointer; wp_pures.
      + rewrite bool_decide_eq_false_2; last (intros [= ?]; apply Hno; split; [done|lia]).
        wp_pures. iApply ("Hslow" with "AU Hc †c S1 S2 Hdst †dst").
      + iApply ("Hslow" with "AU Hc †c S1 S2 Hdst †dst").
  Qed.

  Lemma cached_me_sc_spec :
    big_atomic_llsc_sc_spec' cached_meN hazptrN (cached_me_sc hazptr) CachedME IsCachedME CachedMEThread.
  Proof using DISJN.
    iIntros (γ γd ba n ctx ver l_desired dq desired Hlen)
      "(%γs & %l & %d & -> & -> & %Hpos & #Hdomloc & #Hdom & #Hinv)
       (%c & %h1 & %h2 & %d' & %et & %st1 & %st2 & -> & Hc & †c & #Hdom' & S1 & S2 & #Hlink) Hdes".
    iIntros (Φ) "AU".
    iDestruct "Hlink" as (γs' e) "(%Henc & #Hidx & #Hcase)".
    apply (inj encode) in Henc as <-.
    iAssert (AU_sc (encode γs) ver desired
               (λ b, CachedMEThread γd #c (if b then None else Some (encode γs, ver)) ∗
                     l_desired ↦∗{dq} desired)%I Φ) with "[AU]" as "AU".
    { rewrite /AU_sc /=. iExact "AU". }
    wp_lam. wp_pures.
    wp_apply (wp_load_offset _ _ _ _ 2 with "Hc") as "Hc"; first done.
    wp_pures. wp_load. wp_pures.
    (* How to rebuild the thread-local state at the end *)
    iAssert (∀ st1' st2' (b : bool), c ↦∗ [ #h1; #h2; et ] -∗ hazptr.(Shield) γd h1 st1' -∗
               hazptr.(Shield) γd h2 st2' -∗ l_desired ↦∗{dq} desired -∗ ⌜b = false → st1' = st1⌝ -∗
               CachedMEThread γd #c (if b then None else Some (encode γs, ver)) ∗
               l_desired ↦∗{dq} desired)%I
      with "[†c]" as "HQ".
    { iIntros (st1' st2' b) "Hc S1 S2 Hdes %Hst1". iFrame "Hdes".
      iExists c, h1, h2, d', et, st1', st2'. iFrame "∗ #". iSplit; first done.
      destruct b; first done.
      rewrite Hst1 //. iExists γs, e. by iFrame "Hidx Hcase". }
    iDestruct "Hcase" as "[[-> #Hlb] | (-> & %Hver & -> & #Hlb)]".
    - (* [expected_tag] is the sequence number of [ver] *)
      rewrite /is_pointer. wp_pures.
      replace (Z.of_nat ver + 1)%Z with (Z.of_nat (S ver)) by lia.
      wp_apply (wp_backup_new with "Hdes") as (b) "(Hb & †b & Hdes)"; first done.
      wp_pures.
      wp_apply (wp_load_offset _ _ _ _ 1 with "Hc") as "Hc"; first done.
      wp_apply (hazptr.(shield_set_spec) (Some b) with "Hdom' S2") as "S2"; first solve_ndisj.
      wp_pures.
      (* [cur_tag := header] *)
      wp_bind (! _)%E.
      iInv "Hinv" as (k1 hist1 ec1 c1) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf1)" "Hcl".
      iDestruct (mono_nat_auth_lb_own_valid with "Hk Hlb") as %[_ Hk1].
      rewrite -/(Loc.loc_to_tagged_loc _).
      destruct (decide (Nat.even k1 = true ∧ length hist1 - 1 = ver)) as [[Heven1 Hv1]|Hno1].
      + (* The header is still [expected_tag] *)
        rewrite Heven1. iDestruct "Hif" as "(>Hhdr & Hif)". wp_load.
        iMod ("Hcl" with "[-AU HQ Hc S1 S2 Hdes Hb †b]") as "_".
        { iExists k1, hist1, ec1, c1. rewrite Heven1. by iFrame. }
        iModIntro. wp_pures.
        rewrite bool_decide_eq_true_2; last by rewrite Hv1. wp_pures.
        (* The first [cmp_xch] *)
        wp_bind (CmpXchg _ _ _).
        iInv "Hinv" as (k2 hist2 ec2 c2) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf2)" "Hcl".
        iDestruct (mono_nat_auth_lb_own_valid with "Hk Hlb") as %[_ Hk2].
        rewrite -/(Loc.loc_to_tagged_loc _).
        destruct (decide (Nat.even k2 = true ∧ length hist2 - 1 = ver)) as [[Heven2 Hv2]|Hno2].
        * (* Success: linearize *)
          rewrite Heven2. iDestruct "Hif" as "(>Hhdr & Hown & Hcc)".
          rewrite Hv2. wp_cmpxchg_suc.
          clear Hv1. subst ver.
          iMod (sc_commit_seq with "Hdom S2 Hb †b AU Habs Hhist Htoks Hk Hcache Hhdr Hcl")
            as (γ_new) "(%Hcclen & S2 & #Hidx_new & HΦ)"; [done..|].
          iModIntro. wp_pures.
          rewrite bool_decide_eq_true_2 //. wp_pures.
          wp_apply (wp_sc_stage3 with "Hinv Hdom Hidx_new [$Hown $Hcc $Hdes $Hc $S1 $S2]"); [done..|].
          iIntros (st1' st2') "(Hdes & Hc & S1 & S2)". wp_pures.
          iModIntro. iApply "HΦ". iApply ("HQ" $! _ _ true with "Hc S1 S2 Hdes"). done.
        * (* Failure: the version has changed *)
          iAssert (⌜length hist2 - 1 ≠ ver⌝)%I as %Hne2.
          { iPureIntro. eapply wf_ver_ne_seq; [done|lia|done]. }
          iMod (sc_commit_fail with "Habs AU") as "[Habs HΦ]"; first done.
          destruct (Nat.even k2) eqn:Heven2;
            iDestruct "Hif" as "(>Hhdr & Hif)";
            (wp_cmpxchg_fail; try (intros [= ?]; apply Hno2; split; [done|lia]));
            (iMod ("Hcl" with "[-HΦ HQ Hc S1 S2 Hdes Hb †b]") as "_";
             [iExists k2, hist2, ec2, c2; rewrite Heven2; by iFrame|]);
            iModIntro; wp_pures.
          -- rewrite bool_decide_eq_false_2; last (intros [= ?]; apply Hno2; split; [done|lia]).
             wp_pures. rewrite bool_decide_eq_false_2; last (intros [= ?]; apply Hno2; split; [done|lia]).
             wp_pures.
             wp_free; try (rewrite length_app /= Hlen; lia).
             iModIntro. iApply "HΦ". by iApply ("HQ" $! _ _ false with "Hc S1 S2 Hdes").
          -- wp_free; try (rewrite length_app /= Hlen; lia).
             iModIntro. iApply "HΦ". by iApply ("HQ" $! _ _ false with "Hc S1 S2 Hdes").
      + (* The header changed: the version has changed *)
        iAssert (⌜length hist1 - 1 ≠ ver⌝)%I as %Hne1.
        { iPureIntro. eapply wf_ver_ne_seq; [done|lia|done]. }
        iMod (sc_commit_fail with "Habs AU") as "[Habs HΦ]"; first done.
        destruct (Nat.even k1) eqn:Heven1;
          iDestruct "Hif" as "(>Hhdr & Hif)"; wp_load;
          (iMod ("Hcl" with "[-HΦ HQ Hc S1 S2 Hdes Hb †b]") as "_";
           [iExists k1, hist1, ec1, c1; rewrite Heven1; by iFrame|]);
          iModIntro; wp_pures.
        * rewrite bool_decide_eq_false_2; last (intros [= ?]; apply Hno1; split; [done|lia]).
          wp_pures. rewrite bool_decide_eq_false_2; last (intros [= ?]; apply Hno1; split; [done|lia]).
          wp_pures. rewrite bool_decide_eq_false_2; last (intros [= ?]; apply Hno1; split; [done|lia]).
          wp_pures.
          wp_free; try (rewrite length_app /= Hlen; lia).
          iModIntro. iApply "HΦ". by iApply ("HQ" $! _ _ false with "Hc S1 S2 Hdes").
        * wp_free; try (rewrite length_app /= Hlen; lia).
          iModIntro. iApply "HΦ". by iApply ("HQ" $! _ _ false with "Hc S1 S2 Hdes").
    - (* [expected_tag] is the protected backup [e] of [ver] *)
      iAssert (|={⊤}=> ⌜length e.(e_val) = n⌝)%I as ">%Helen".
      { iInv "Hinv" as (k0 hist0 ec0 c0) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf0)" "Hcl".
        iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He0.
        iMod ("Hcl" with "[-]") as "_"; first (iExists k0, hist0, ec0, c0; by iFrame).
        iPureIntro. exact (Forall_lookup_1 _ _ _ _ (wf_len _ _ _ _ _ Hwf0) He0). }
      rewrite Helen /is_pointer. wp_pures.
      rewrite -/(Loc.loc_to_tagged_loc _).
      wp_apply (wp_read_seqnum with "S1") as "S1"; first done.
      wp_pures.
      replace (Z.of_nat ver + 1)%Z with (Z.of_nat (S ver)) by lia.
      wp_apply (wp_backup_new with "Hdes") as (b) "(Hb & †b & Hdes)"; first done.
      wp_pures.
      wp_apply (wp_load_offset _ _ _ _ 1 with "Hc") as "Hc"; first done.
      wp_apply (hazptr.(shield_set_spec) (Some b) with "Hdom' S2") as "S2"; first solve_ndisj.
      wp_pures.
      (* [cur_tag := header] *)
      wp_bind (! _)%E.
      iInv "Hinv" as (k1 hist1 ec1 c1) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf1)" "Hcl".
      iDestruct (mono_nat_auth_lb_own_valid with "Hk Hlb") as %[_ Hk1].
      iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He1.
      rewrite -/(Loc.loc_to_tagged_loc _).
      destruct (decide (Nat.even k1 = true ∧ length hist1 - 1 = ver)) as [[Heven1 Hv1]|Hno1b].
      { (* The header is the sequence number of [ver] *)
        rewrite Heven1. iDestruct "Hif" as "(>Hhdr & Hif)". wp_load.
        iPoseProof (mono_nat_lb_own_get with "Hk") as "#Hlb1".
        iMod ("Hcl" with "[-AU HQ Hc S1 S2 Hdes Hb †b]") as "_".
        { iExists k1, hist1, ec1, c1. rewrite Heven1. by iFrame. }
        iModIntro. wp_pures.
        destruct (wf_even _ _ _ _ _ Hwf1 Heven1) as [Hk1' _].
        rewrite Hv1 bool_decide_eq_true_2 //. wp_pures.
        iApply (wp_sc_cas2 with "Hinv Hdom [] AU HQ Hc S1 S2 Hdes Hb †b"); [done|done|].
        by rewrite -Hv1 -Hk1'. }
      destruct (decide (Nat.even k1 = false ∧ ec1.(e_blk) = e.(e_blk))) as [[Heven1 Hb1]|Hno1a]; last first.
      { (* The header is neither: the version has changed *)
        iAssert (⌜length hist1 - 1 ≠ ver⌝)%I as %Hne1.
        { iPureIntro. eapply wf_ver_ne_ptr; [done|lia|done|done|done]. }
        iMod (sc_commit_fail with "Habs AU") as "[Habs HΦ]"; first done.
        destruct (Nat.even k1) eqn:Heven1;
          iDestruct "Hif" as "(>Hhdr & Hif)"; wp_load;
          (iMod ("Hcl" with "[-HΦ HQ Hc S1 S2 Hdes Hb †b]") as "_";
           [iExists k1, hist1, ec1, c1; rewrite Heven1; by iFrame|]);
          iModIntro; wp_pures.
        - rewrite bool_decide_eq_false_2; last (intros [= ?]; apply Hno1b; split; [done|lia]).
          wp_pures.
          wp_free; try (rewrite length_app /= Hlen; lia).
          iModIntro. iApply "HΦ". by iApply ("HQ" $! _ _ false with "Hc S1 S2 Hdes").
        - rewrite bool_decide_eq_false_2; last (intros [= Heq]; apply Hno1a; by split).
          wp_pures. rewrite bool_decide_eq_false_2; last (intros [= Heq]; apply Hno1a; by split).
          wp_pures.
          wp_free; try (rewrite length_app /= Hlen; lia).
          iModIntro. iApply "HΦ". by iApply ("HQ" $! _ _ false with "Hc S1 S2 Hdes"). }
      (* The header is still [expected_tag] *)
      rewrite Heven1. iDestruct "Hif" as "(>Hhdr & Hman)". wp_load.
      iMod ("Hcl" with "[-AU HQ Hc S1 S2 Hdes Hb †b]") as "_".
      { iExists k1, hist1, ec1, c1. rewrite Heven1. by iFrame. }
      iModIntro. rewrite Hb1. wp_pures.
      (* The first [cmp_xch] *)
      wp_bind (CmpXchg _ _ _).
      iInv "Hinv" as (k2 hist2 ec2 c2) "(>Habs & >Hhist & >Htoks & >Hk & >Hcache & Hif & >%Hwf2)" "Hcl".
      iDestruct (mono_nat_auth_lb_own_valid with "Hk Hlb") as %[_ Hk2].
      iDestruct (mono_list_auth_idx_lookup with "Hhist Hidx") as %He2.
      rewrite -/(Loc.loc_to_tagged_loc _).
      destruct (decide (Nat.even k2 = false ∧ ec2.(e_blk) = e.(e_blk))) as [[Heven2 Hb2]|Hno2a].
      + (* Success: linearize *)
        rewrite Heven2. iDestruct "Hif" as "(>Hhdr & Hman)". rewrite Hb2.
        wp_cmpxchg_suc.
        iDestruct (hazptr.(shield_managed_agree) with "S1 Hman") as %Hγ.
        pose proof (wf_current _ _ _ _ _ Hwf2) as Hcur2.
        assert (ver = length hist2 - 1) as Hv2.
        { eapply (NoDup_lookup (e_name <$> hist2)); [apply Hwf2| |].
          - by rewrite list_lookup_fmap He2.
          - by rewrite list_lookup_fmap Hcur2 /= Hγ. }
        rewrite Hv2 Hcur2 in He2. injection He2 as ->.
        iMod token_alloc as (γ_new) "Htok".
        iDestruct (tokens_fresh with "Htok Htoks") as %Hfresh.
        subst ver.
        iMod (sc_commit_success with "Hdom S2 Hb †b Habs Hhist AU")
          as "(Habs & Hhist & #Hidx_new & Hman' & S2 & HΦ)"; [done|by eapply wf_length_pos|done|].
        iMod (mono_nat_own_update (S (S k2)) with "Hk") as "[Hk _]"; first lia.
        iMod ("Hcl" with "[-HΦ HQ Hc S1 S2 Hdes Hman]") as "_".
        { iExists (S (S k2)), (hist2 ++ [Entry γ_new b desired]), (Entry γ_new b desired), c2.
          rewrite Nat.even_succ Nat.odd_succ Heven2 big_sepL_snoc /=. iFrame.
          iPureIntro. pose proof (wf_install _ _ _ _ _ (Entry γ_new b desired) Hwf2) as Hwf'.
          rewrite Heven2 in Hwf'. by apply Hwf'. }
        iModIntro. wp_pures.
        wp_apply (hazptr.(hazard_domain_retire_spec) with "Hdom Hman") as "_"; first solve_ndisj.
        wp_pures. iModIntro. iApply "HΦ". iApply ("HQ" $! _ _ true with "Hc S1 S2 Hdes"). done.
      + destruct (decide (Nat.even k2 = true ∧ length hist2 - 1 = ver)) as [[Heven2 Hv2]|Hno2b].
        * (* The backup was replaced by its sequence number: retry *)
          rewrite Heven2. iDestruct "Hif" as "(>Hhdr & Hif)".
          wp_cmpxchg_fail.
          iPoseProof (mono_nat_lb_own_get with "Hk") as "#Hlb2".
          destruct (wf_even _ _ _ _ _ Hwf2 Heven2) as [Hk2' _].
          iMod ("Hcl" with "[-AU HQ Hc S1 S2 Hdes Hb †b]") as "_".
          { iExists k2, hist2, ec2, c2. rewrite Heven2. by iFrame. }
          iModIntro. wp_pures.
          rewrite Hv2 bool_decide_eq_true_2 //. wp_pures.
          iApply (wp_sc_cas2 with "Hinv Hdom [] AU HQ Hc S1 S2 Hdes Hb †b"); [done|done|].
          by rewrite -Hv2 -Hk2'.
        * (* Failure: the version has changed *)
          iAssert (⌜length hist2 - 1 ≠ ver⌝)%I as %Hne2.
          { iPureIntro. eapply wf_ver_ne_ptr; [done|lia|done|done|done]. }
          iMod (sc_commit_fail with "Habs AU") as "[Habs HΦ]"; first done.
          destruct (Nat.even k2) eqn:Heven2;
            iDestruct "Hif" as "(>Hhdr & Hif)";
            (wp_cmpxchg_fail; try (intros [= Heq]; apply Hno2a; by split));
            (iMod ("Hcl" with "[-HΦ HQ Hc S1 S2 Hdes Hb †b]") as "_";
             [iExists k2, hist2, ec2, c2; rewrite Heven2; by iFrame|]);
            iModIntro; wp_pures.
          -- rewrite bool_decide_eq_false_2; last (intros [= ?]; apply Hno2b; split; [done|lia]).
             wp_pures.
             wp_free; try (rewrite length_app /= Hlen; lia).
             iModIntro. iApply "HΦ". by iApply ("HQ" $! _ _ false with "Hc S1 S2 Hdes").
          -- rewrite bool_decide_eq_false_2; last (intros [= Heq]; apply Hno2a; by split).
             wp_pures.
             wp_free; try (rewrite length_app /= Hlen; lia).
             iModIntro. iApply "HΦ". by iApply ("HQ" $! _ _ false with "Hc S1 S2 Hdes").
  Qed.

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
