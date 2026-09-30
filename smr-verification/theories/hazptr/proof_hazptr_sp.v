From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import invariants ghost_map.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr.algebra Require Import coPset.
From smr.base_logic.lib Require Import coP_ghost_map coP_cancellable_invariants.
From smr Require Import helpers smr_common.
From smr.hazptr Require Import spec_hazptr_sp code_hazptr_sp.
From iris.prelude Require Import options.

(* The lemmas of the section may use the bounds on [H] and [R]. *)
Local Set Default Proof Using "All".

(** * Proof of hazard pointers with bounded space

    Every registered block gets a fresh id [i] and its resource lives in a
    cancellable invariant. The permission to own it is split into shares: one
    per hazard slot [s] (the coPneset [{[slid s]}]) and the rest, [Mset], for
    the block's owner ([Managed], and then the retirer that holds it). The
    same shares split the block's entry in the map [ptrs] from blocks to ids.

    - The share of slot [s] is held by the invariant, by the shield of [s]
      while it is validated for [i], or by the retirer once it has seen that
      [s] does not protect [i]. Which one is recorded by the flag [tk(i, s)]
      ("taken by the retirer") and by the slot's ghost state [(v, o)], its
      protected pointer and the id it is validated for.
    - Validation needs [tk(i, s) = false], which the owner of the block knows,
      as it owns the flags. So once a block is retired nobody can validate it,
      and a retirer that reads a slot not protecting the block can take the
      slot's share for good.
    - When a retirer holds all the shares of a block, it cancels the
      invariant and frees the block.

    A retirer holds at most [R] blocks: when it holds [R] it takes a snapshot
    of the [H] slots and keeps only the blocks in it, which are distinct, so at
    most [H < R]. Its credits ([RetirerBody]) pay for the blocks it may still
    take. The domain's pool of [NP] retirers is in the invariant: a free
    retirer's body is there, and a thread that takes one takes its body. *)

Record ninfo := NInfo {
  ni_blk : blk;
  ni_size : nat;
  ni_cinv : gname;
  ni_data : gname;
}.

Record hp_names := HPNames {
  γinfo : gname;
  γptrs : gname;
  γtk : gname;
  γsst : gname;
}.

Global Instance hp_names_eq_dec : EqDecision hp_names.
Proof. solve_decision. Qed.

Global Instance hp_names_countable : Countable hp_names.
Proof.
  refine (inj_countable'
    (λ γs, (γs.(γinfo), γs.(γptrs), γs.(γtk), γs.(γsst)))
    (λ '(a, b, c, d), HPNames a b c d) _); by intros [].
Qed.

Class hazptr_spG Σ := HazptrSpG {
  #[local] hpsp_infoG :: ghost_mapG Σ positive ninfo;
  #[local] hpsp_ptrsG :: coP_ghost_mapG Σ blk positive;
  #[local] hpsp_cinvG :: coP_cinvG Σ;
  #[local] hpsp_tkG :: ghost_mapG Σ (positive * nat) bool;
  #[local] hpsp_sstG :: ghost_mapG Σ nat (option blk * option positive);
}.

Definition hazptr_spΣ : gFunctors := #[
  ghost_mapΣ positive ninfo;
  coP_ghost_mapΣ blk positive;
  coP_cinvΣ;
  ghost_mapΣ (positive * nat) bool;
  ghost_mapΣ nat (option blk * option positive)
].

Global Instance subG_hazptr_spΣ Σ : subG hazptr_spΣ Σ → hazptr_spG Σ.
Proof. solve_inG. Qed.

(** ** Slot ids and the shares of a block *)

Definition slid (s : nat) : positive := Pos.of_succ_nat s.

Definition slotset (H : nat) : gset positive := list_to_set (slid <$> seq 0 H).

(** The share of the block's owner. *)
Definition Mset (H : nat) : coPneset := coPneset_complement (slotset H).

Lemma slotset_S H : slotset (S H) = slotset H ∪ {[slid H]}.
Proof.
  rewrite /slotset seq_S fmap_app list_to_set_app_L /=. set_solver.
Qed.

Lemma slid_not_in_slotset H : slid H ∉ slotset H.
Proof.
  rewrite /slotset elem_of_list_to_set list_elem_of_fmap.
  intros (s & Heq & Hs%elem_of_seq). rewrite /slid in Heq. lia.
Qed.

Lemma Mset_S H : Mset H = Mset (S H) ∪ {[slid H]} ∧ Mset (S H) ## {[slid H]}.
Proof.
  split.
  - apply coPneset_eq. rewrite coPneset_union_eq /Mset /=.
    rewrite slotset_S gset_to_coPset_union.
    pose proof (slid_not_in_slotset H).
    apply set_eq=> x. rewrite elem_of_union !elem_of_difference elem_of_union.
    rewrite !elem_of_gset_to_coPset elem_of_singleton.
    destruct (decide (x = slid H)) as [->|]; set_solver.
  - apply coPneset_disj_iff. rewrite /Mset /=.
    rewrite slotset_S gset_to_coPset_union.
    apply disjoint_singleton_r. rewrite elem_of_difference elem_of_union !elem_of_gset_to_coPset.
    set_solver.
Qed.

Lemma Mset_0 : Mset 0 = ⊤.
Proof.
  apply coPneset_eq. rewrite /Mset /slotset /=. set_solver.
Qed.

Section shares.
  Context {PROP : bi}.

  (** The shares of all the slots and the owner's make the whole. *)
  Lemma shares_collect (Φ : coPneset → PROP) H :
    (∀ E1 E2, E1 ## E2 → Φ (E1 ∪ E2) ⊣⊢ Φ E1 ∗ Φ E2) →
    Φ (Mset H) ∗ ([∗ list] s ∈ seq 0 H, Φ {[slid s]}) ⊣⊢ Φ ⊤.
  Proof.
    intros HΦ. induction H as [|H IH].
    { by rewrite /= right_id Mset_0. }
    rewrite seq_S big_sepL_app /= right_id.
    destruct (Mset_S H) as [Heq Hdisj].
    rewrite -IH Heq HΦ //.
    iSplit; [iIntros "(A & B & C)"|iIntros "([A C] & B)"]; iFrame.
  Qed.
End shares.

Section hazptr_sp.
Context `{!heapGS_gen HasLc hsp Σ, !hazptr_spG Σ} (N : namespace).
Context (H R K NP : nat) (HR : H < R) (HH : 0 < H).
Notation iProp := (iProp Σ).
Implicit Types (γs : hp_names) (Rs : resource Σ).

Definition hpInvN := mgmtN N .@ "inv".
Definition resN (p : blk) (i : positive) := ptrN N p .@ i.

(** The resource of a block. *)
Definition res (Rs : resource Σ) (p : blk) (n : nat) (γ_p : gname) : iProp :=
  ∃ lv, ⌜length lv = n⌝ ∗ p ↦∗ lv ∗ Rs p lv γ_p.

(** A share [E] of block [p] with id [i], whose invariant is [γc]. *)
Definition shareE γs (γc : gname) (p : blk) (i : positive) (E : coPneset) : iProp :=
  coP_cinv_own γc E ∗ p ↪c[γs.(γptrs)]{E} i.

Lemma shareE_split γs γc p i E1 E2 :
  E1 ## E2 → shareE γs γc p i (E1 ∪ E2) ⊣⊢ shareE γs γc p i E1 ∗ shareE γs γc p i E2.
Proof.
  intros ?. rewrite /shareE coP_cinv_own_fractional // coP_ghost_map_elem_fractional //.
  iSplit; iIntros "[[$ $] [$ $]]".
Qed.

Lemma shareE_collect γs γc p i :
  shareE γs γc p i (Mset H) ∗ ([∗ list] s ∈ seq 0 H, shareE γs γc p i {[slid s]}) ⊣⊢
  shareE γs γc p i ⊤.
Proof. apply shares_collect. intros. by apply shareE_split. Qed.

(** ** The invariant *)

(** A slot is free and its ghost state is in the invariant, or it is taken
    by a shield and holds the pointer the shield protects. *)
Definition slot_inv γs (d : loc) (s : nat) (vo : option blk * option positive) : iProp :=
  ((d +ₗ s) ↦ #() ∗ ⌜vo = (None, None)⌝ ∗ s ↪[γs.(γsst)] vo) ∨
  (d +ₗ s) ↦ #(oblk_to_lit vo.1).

(** Whether slot [s] is validated for [i]. *)
Definition validated_for (sst : gmap nat (option blk * option positive)) (s : nat) (i : positive) : bool :=
  bool_decide (snd <$> sst !! s = Some (Some i)).

(** Where the share of slot [s] of block [i] is. *)
Definition node_inv γs (sst : gmap nat (option blk * option positive))
    (tkm : gmap (positive * nat) bool) (i : positive) (x : ninfo) : iProp :=
  [∗ list] s ∈ seq 0 H, ∃ b : bool, ⌜tkm !! (i, s) = Some b⌝ ∗
    if b then ⌜validated_for sst s i = false⌝
    else if validated_for sst s i then True
    else shareE γs x.(ni_cinv) x.(ni_blk) i {[slid s]}.

Definition sst_ok (info : gmap positive ninfo) (sst : gmap nat (option blk * option positive)) : Prop :=
  ∀ s v i, sst !! s = Some (v, Some i) → ∃ x, info !! i = Some x ∧ v = Some x.(ni_blk).

(** A retired block: a [Managed] whose flags record the slots it has seen
    not protecting it, with their shares. *)
Definition RetiredEntry γs (p : blk) (n : nat) : iProp :=
  ∃ i γc γ_p Rs,
    i ↪[γs.(γinfo)]□ NInfo p n γc γ_p ∗
    coP_cinv (resN p i) γc (res Rs p n γ_p) ∗
    shareE γs γc p i (Mset H) ∗
    ([∗ list] s ∈ seq 0 H, ∃ b : bool, (i, s) ↪[γs.(γtk)] b ∗
       if b then shareE γs γc p i {[slid s]} else True).

Fixpoint enc_entries (L : list (blk * nat)) : list val :=
  match L with
  | [] => []
  | (p, n) :: L => #(Loc.blk_to_loc p) :: #n :: enc_entries L
  end.

Definition retirer_cost : nat := (hp_retirer_size H R + R * K)%nat.

(** A retirer of domain [d]: its pending blocks, and the credits that the
    blocks it may still take would need. *)
Definition RetirerBody γs (d t : loc) : iProp :=
  ∃ (L : list (blk * nat)) (ents snap : list val) (bank : nat),
    (t +ₗ rtDomain) ↦ #d ∗ (t +ₗ rtCount) ↦ #(length L) ∗
    (t +ₗ rtEntries) ↦∗ ents ∗ (t +ₗ hp_snap_off R) ↦∗ snap ∗
    †t…(hp_retirer_size H R) ∗
    ⌜length L < R ∧ length ents = (2 * R)%nat ∧ length snap = H⌝ ∗
    ⌜take (2 * length L)%nat ents = enc_entries L⌝ ∗
    ⌜Forall (λ pn, pn.2 ≤ K) L⌝ ∗
    ♢ bank ∗ ⌜(bank + sum_list (snd <$> L) = R * K)%nat⌝ ∗
    ([∗ list] pn ∈ L, RetiredEntry γs pn.1 pn.2).

Definition HazardDomain γs (d : loc) : iProp :=
  ∃ (info : gmap positive ninfo) (ptrs : gmap blk positive)
    (tkm : gmap (positive * nat) bool) (sst : gmap nat (option blk * option positive)),
    ghost_map_auth γs.(γinfo) (DfracOwn 1) info ∗
    coP_ghost_map_auth γs.(γptrs) 1 ptrs ∗
    ghost_map_auth γs.(γtk) (DfracOwn 1) tkm ∗
    ghost_map_auth γs.(γsst) (DfracOwn 1) sst ∗
    ([∗ list] s ∈ seq 0 H, ∃ vo, ⌜sst !! s = Some vo⌝ ∗ slot_inv γs d s vo) ∗
    ⌜sst_ok info sst⌝ ∗
    ⌜∀ j s, is_Some (tkm !! (j, s)) → is_Some (info !! j)⌝ ∗
    ([∗ map] i ↦ x ∈ info, node_inv γs sst tkm i x) ∗
    ([∗ map] p ↦ i ∈ ptrs, ∃ x, ⌜info !! i = Some x ∧ x.(ni_blk) = p⌝ ∗ †p…x.(ni_size)) ∗
    (* The pool of retirers: a free retirer, or [NULL] if a thread holds it. *)
    ([∗ list] j ∈ seq 0 NP, ∃ v : val, (d +ₗ (H + j)%nat) ↦ v ∗
       (⌜v = #NULL⌝ ∨ ∃ t : loc, ⌜v = #t⌝ ∗ RetirerBody γs d t)).

(** ** Representation predicates *)

Definition IsHazardDomain (γd : gname) (d : loc) : iProp :=
  ∃ γs, ⌜γd = encode (γs, d)⌝ ∗ inv hpInvN (HazardDomain γs d).

Global Instance IsHazardDomain_Persistent γd d : Persistent (IsHazardDomain γd d).
Proof. apply _. Qed.

Definition Retirer (γd : gname) (t : loc) : iProp :=
  ∃ γs (d : loc), ⌜γd = encode (γs, d)⌝ ∗ inv hpInvN (HazardDomain γs d) ∗ RetirerBody γs d t.

Definition Managed (γd : gname) (p : blk) (γ_p : gname) (n : nat) Rs : iProp :=
  ∃ γs (d : loc) i γc, ⌜γd = encode (γs, d)⌝ ∗
    i ↪[γs.(γinfo)]□ NInfo p n γc γ_p ∗
    coP_cinv (resN p i) γc (res Rs p n γ_p) ∗
    shareE γs γc p i (Mset H) ∗
    ([∗ list] s ∈ seq 0 H, (i, s) ↪[γs.(γtk)] false).

Definition Shield (γd : gname) (sh : loc) (st : shield_state Σ) : iProp :=
  ∃ γs (d : loc) (idx : nat) vo, ⌜γd = encode (γs, d)⌝ ∗ ⌜sh = d +ₗ idx⌝ ∗ ⌜idx < H⌝ ∗
    inv hpInvN (HazardDomain γs d) ∗
    idx ↪[γs.(γsst)] vo ∗
    match st with
    | Deactivated => ⌜vo = (None, None)⌝
    | NotValidated p => ⌜vo = (Some p, None)⌝
    | Validated p γ_p Rs n => ∃ i γc, ⌜vo = (Some p, Some i)⌝ ∗
        i ↪[γs.(γinfo)]□ NInfo p n γc γ_p ∗
        coP_cinv (resN p i) γc (res Rs p n γ_p) ∗
        shareE γs γc p i {[slid idx]}
    end.

(** ** Helpers *)

(** The flags of a fresh block. *)
Definition tk0 (i : positive) : gmap (positive * nat) bool :=
  list_to_map ((λ s, ((i, s), false)) <$> seq 0 H).

Lemma lookup_tk0 i j s :
  tk0 i !! (j, s) = if bool_decide (j = i ∧ s < H) then Some false else None.
Proof.
  clear HR HH. rewrite /tk0. case_bool_decide as Hc.
  - destruct Hc as [-> Hs]. apply elem_of_list_to_map_1.
    + rewrite -list_fmap_compose. apply NoDup_fmap_2; last apply NoDup_seq.
      by intros ?? [=].
    + apply list_elem_of_fmap. exists s. split; first done. apply elem_of_seq. lia.
  - apply not_elem_of_list_to_map_1. rewrite -list_fmap_compose.
    intros (s' & [= -> ->] & ?%elem_of_seq)%list_elem_of_fmap. apply Hc. split; [done|lia].
Qed.

Lemma big_sepM_tk0 (Φ : positive * nat → bool → iProp) i :
  ([∗ map] k ↦ b ∈ tk0 i, Φ k b) ⊣⊢ [∗ list] s ∈ seq 0 H, Φ (i, s) false.
Proof.
  rewrite /tk0 big_sepM_list_to_map.
  - by rewrite big_sepL_fmap.
  - rewrite -list_fmap_compose. apply NoDup_fmap_2; last apply NoDup_seq.
    by intros ?? [=].
Qed.

Lemma big_sepL_replicate_seq {A} (Φ : nat → A → iProp) n x :
  ([∗ list] i ↦ v ∈ replicate n x, Φ i v) ⊣⊢ [∗ list] s ∈ seq 0 n, Φ s x.
Proof.
  clear HR HH. revert Φ. induction n as [|n IH]=> Φ; first done.
  rewrite replicate_S big_sepL_cons -cons_seq big_sepL_cons -fmap_S_seq big_sepL_fmap.
  f_equiv. apply (IH (λ i, Φ (S i))).
Qed.

(** The slots of a fresh domain. *)
Definition sst0 : gmap nat (option blk * option positive) := map_seq 0 (replicate H (None, None)).

Lemma lookup_sst0 s : s < H → sst0 !! s = Some (None, None).
Proof. clear HR HH. intros ?. rewrite /sst0 lookup_map_seq_0 lookup_replicate. by split. Qed.

Lemma sst0_ok : sst_ok ∅ sst0.
Proof.
  clear HR HH. intros s v i. rewrite /sst0 lookup_map_seq_0.
  by intros ([=] & _)%lookup_replicate.
Qed.

(** Updating one slot *)
Lemma slots_acc γs d (sst : gmap nat (option blk * option positive)) idx vo' :
  idx < H →
  ([∗ list] s ∈ seq 0 H, ∃ vo, ⌜sst !! s = Some vo⌝ ∗ slot_inv γs d s vo) -∗
  (∃ vo, ⌜sst !! idx = Some vo⌝ ∗ slot_inv γs d idx vo) ∗
  (slot_inv γs d idx vo' -∗
   [∗ list] s ∈ seq 0 H, ∃ vo, ⌜<[idx := vo']> sst !! s = Some vo⌝ ∗ slot_inv γs d s vo).
Proof.
  iIntros (Hidx) "Hslots".
  have Hl : seq 0 H !! idx = Some idx by rewrite lookup_seq_lt.
  iDestruct (big_sepL_lookup_acc_impl with "Hslots") as "[$ Hclose]"; first done.
  iIntros "Hslot". iApply ("Hclose" with "[] [Hslot]").
  - iIntros "!>" (k s Hks Hne) "(%vo & %Hvo & Hs)". iExists vo. iFrame. iPureIntro.
    apply lookup_seq in Hks as [-> _]. rewrite lookup_insert_ne //; lia.
  - iExists vo'. iFrame. by rewrite lookup_insert_eq.
Qed.

Lemma validated_for_insert (sst : gmap nat (option blk * option positive)) idx vo' s j :
  validated_for (<[idx := vo']> sst) s j =
  if decide (s = idx) then bool_decide (vo'.2 = Some j) else validated_for sst s j.
Proof.
  rewrite /validated_for. case_decide as Hs.
  - subst. rewrite lookup_insert_eq /=.
    apply bool_decide_ext. split; [by intros [=]|by intros ->].
  - rewrite lookup_insert_ne //.
Qed.

Lemma validated_for_lookup (sst : gmap nat (option blk * option positive)) s vo i :
  sst !! s = Some vo → validated_for sst s i = bool_decide (vo.2 = Some i).
Proof.
  intros Hs. rewrite /validated_for Hs /=.
  apply bool_decide_ext. split; [by intros [=]|by intros ->].
Qed.

(** Changing the protected pointer of a slot, but not its validation. *)
Lemma nodes_sst_same γs (info : gmap positive ninfo) (sst : gmap nat (option blk * option positive))
    (tkm : gmap (positive * nat) bool) idx vo vo' :
  sst !! idx = Some vo → vo.2 = vo'.2 →
  ([∗ map] i ↦ x ∈ info, node_inv γs sst tkm i x) ⊣⊢
  ([∗ map] i ↦ x ∈ info, node_inv γs (<[idx := vo']> sst) tkm i x).
Proof.
  intros Hvo Ho. apply big_sepM_proper=> i x _. rewrite /node_inv.
  apply big_sepL_proper=> k s _.
  have -> : validated_for (<[idx := vo']> sst) s i = validated_for sst s i.
  { rewrite validated_for_insert. case_decide; last done. subst.
    rewrite (validated_for_lookup _ _ _ _ Hvo) Ho. done. }
  done.
Qed.

(** A shield that stops protecting block [i] gives its share back. *)
Lemma nodes_unvalidate γs (info : gmap positive ninfo) (sst : gmap nat (option blk * option positive))
    (tkm : gmap (positive * nat) bool) idx v i x vo' :
  sst !! idx = Some (v, Some i) → info !! i = Some x → vo'.2 = None → idx < H →
  ([∗ map] j ↦ y ∈ info, node_inv γs sst tkm j y) -∗
  shareE γs x.(ni_cinv) x.(ni_blk) i {[slid idx]} -∗
  [∗ map] j ↦ y ∈ info, node_inv γs (<[idx := vo']> sst) tkm j y.
Proof.
  iIntros (Hvo Hx Ho' Hidx) "Hnodes Hsh".
  iDestruct (big_sepM_delete with "Hnodes") as "[Hi Hnodes]"; first done.
  iApply big_sepM_delete; first done. iSplitR "Hnodes".
  - rewrite /node_inv.
    have Hl : seq 0 H !! idx = Some idx by rewrite lookup_seq_lt.
    have Hval : validated_for sst idx i = true
      by rewrite (validated_for_lookup _ _ _ _ Hvo) bool_decide_true.
    iDestruct (big_sepL_lookup_acc_impl with "Hi") as "[(%b & %Hb & Hs) Hclose]"; first done.
    destruct b; first (rewrite Hval; by iDestruct "Hs" as %?).
    iApply ("Hclose" with "[] [Hsh]").
    + iIntros "!>" (k s Hks Hne) "(%b' & %Hb' & Hs)". iExists b'. iSplit; first done.
      apply lookup_seq in Hks as [-> _]. rewrite validated_for_insert decide_False //.
    + iExists false. iSplit; first done.
      rewrite validated_for_insert decide_True // Ho' bool_decide_false //.
  - iApply (big_sepM_mono with "Hnodes"). iIntros (j y Hjy) "Hj".
    apply lookup_delete_Some in Hjy as [Hji _].
    rewrite /node_inv. iApply (big_sepL_mono with "Hj"). iIntros (k s _) "Hs".
    rewrite validated_for_insert Ho'. case_decide; last done. subst.
    rewrite (validated_for_lookup _ _ _ _ Hvo) /= !bool_decide_false //; congruence.
Qed.

(** A shield validates block [i]: it takes the share of its slot. *)
Lemma nodes_validate γs (info : gmap positive ninfo) (sst : gmap nat (option blk * option positive))
    (tkm : gmap (positive * nat) bool) idx v i x :
  sst !! idx = Some (v, None) → info !! i = Some x → tkm !! (i, idx) = Some false → idx < H →
  ([∗ map] j ↦ y ∈ info, node_inv γs sst tkm j y) -∗
  shareE γs x.(ni_cinv) x.(ni_blk) i {[slid idx]} ∗
  [∗ map] j ↦ y ∈ info, node_inv γs (<[idx := (v, Some i)]> sst) tkm j y.
Proof.
  iIntros (Hvo Hx Htk Hidx) "Hnodes".
  iDestruct (big_sepM_delete with "Hnodes") as "[Hi Hnodes]"; first done.
  rewrite /node_inv.
  have Hl : seq 0 H !! idx = Some idx by rewrite lookup_seq_lt.
  iDestruct (big_sepL_lookup_acc_impl with "Hi") as "[(%b & %Hb & Hs) Hclose]"; first done.
  rewrite Htk in Hb. injection Hb as <-.
  rewrite (validated_for_lookup _ _ _ _ Hvo) bool_decide_false //.
  iFrame "Hs".
  iApply big_sepM_delete; first done. iSplitR "Hnodes".
  - iApply ("Hclose" with "[] []").
    + iIntros "!>" (k s Hks Hne) "(%b & %Hb & Hs)". iExists b. iSplit; first done.
      apply lookup_seq in Hks as [-> _]. rewrite validated_for_insert decide_False //.
    + iExists false. iSplit; first done. by rewrite validated_for_insert decide_True // bool_decide_true.
  - iApply (big_sepM_mono with "Hnodes"). iIntros (j y Hjy) "Hj".
    apply lookup_delete_Some in Hjy as [Hji _].
    iApply (big_sepL_mono with "Hj"). iIntros (k s _) "Hs".
    rewrite validated_for_insert. case_decide; last done. subst.
    rewrite (validated_for_lookup _ _ _ _ Hvo) /= !bool_decide_false //; congruence.
Qed.

(** A retirer takes the share of slot [s] of block [i], when [s] is not
    validated for [i]. *)
Lemma nodes_take γs (info : gmap positive ninfo) (sst : gmap nat (option blk * option positive))
    (tkm : gmap (positive * nat) bool) i x s :
  info !! i = Some x → tkm !! (i, s) = Some false → validated_for sst s i = false → s < H →
  ([∗ map] j ↦ y ∈ info, node_inv γs sst tkm j y) -∗
  shareE γs x.(ni_cinv) x.(ni_blk) i {[slid s]} ∗
  [∗ map] j ↦ y ∈ info, node_inv γs sst (<[(i, s) := true]> tkm) j y.
Proof.
  iIntros (Hx Htk Hval Hs) "Hnodes".
  iDestruct (big_sepM_delete with "Hnodes") as "[Hi Hnodes]"; first done.
  rewrite /node_inv.
  have Hl : seq 0 H !! s = Some s by rewrite lookup_seq_lt.
  iDestruct (big_sepL_lookup_acc_impl with "Hi") as "[(%b & %Hb & Hsh) Hclose]"; first done.
  rewrite Htk in Hb. injection Hb as <-. rewrite Hval. iFrame "Hsh".
  iApply big_sepM_delete; first done. iSplitR "Hnodes".
  - iApply ("Hclose" with "[] []").
    + iIntros "!>" (k s' Hks Hne) "(%b & %Hb & Hs)". iExists b. iFrame. iPureIntro.
      apply lookup_seq in Hks as [-> _]. rewrite lookup_insert_ne //. intros [= ?]. lia.
    + iExists true. by rewrite lookup_insert_eq.
  - iApply (big_sepM_mono with "Hnodes"). iIntros (j y Hjy) "Hj".
    apply lookup_delete_Some in Hjy as [Hji _].
    iApply (big_sepL_mono with "Hj"). iIntros (k s' _) "(%b & %Hb & Hs)".
    iExists b. iFrame. iPureIntro. rewrite lookup_insert_ne //; congruence.
Qed.

(** ** Specifications *)

(** A fresh retirer, but for its domain field. *)
Lemma retirer_alloc γs (d : loc) E Φ :
  ♢ retirer_cost -∗
  (∀ t : loc, (t +ₗ rtDomain) ↦ #0 -∗ ((t +ₗ rtDomain) ↦ #d -∗ RetirerBody γs d t) -∗ Φ #t) -∗
  WP AllocN #(hp_retirer_size H R) #0 @ E {{ Φ }}.
Proof.
  iIntros "Hc HΦ". rewrite /retirer_cost. iDestruct "Hc" as "[Hc Hbank]".
  wp_apply (wp_allocN_cred with "[Hc]") as (t) "[†t Ht]"; first (rewrite /hp_retirer_size; lia).
  { by rewrite Nat2Z.id. }
  rewrite Nat2Z.id.
  rewrite {2}/hp_retirer_size (replicate_add (2 + 2 * R) H) array_app.
  rewrite (replicate_add 2 (2 * R)) array_app.
  iDestruct "Ht" as "[[Hdc Hents] Hsnap]".
  iEval (rewrite length_replicate) in "Hents".
  iEval (rewrite length_app !length_replicate) in "Hsnap".
  change (replicate 2 #0) with [ #0; #0].
  rewrite array_cons array_singleton.
  iDestruct "Hdc" as "[Hd Hc]".
  iApply ("HΦ" with "[Hd]"); first by rewrite Loc.add_0.
  iIntros "Hd". iExists [], (replicate (2 * R) #0), (replicate H #0), (R * K)%nat.
  rewrite /hp_snap_off /= !length_replicate.
  iFrame "∗ #". iPureIntro. split_and!; try done; try lia.
Qed.

Lemma hp_pool_init_spec γs (d : loc) (i : nat) E :
  i ≤ NP →
  {{{ ([∗ list] j ∈ seq i (NP - i), (d +ₗ (H + j)%nat) ↦ #()) ∗ ♢ ((NP - i) * retirer_cost) }}}
    hp_pool_init H R NP #d #i @ E
  {{{ RET #(); [∗ list] j ∈ seq i (NP - i), ∃ t : loc, (d +ₗ (H + j)%nat) ↦ #t ∗ RetirerBody γs d t }}}.
Proof.
  iIntros (Hi Φ) "[Hcells Hc] HΦ".
  iLöb as "IH" forall (i Hi).
  wp_lam. wp_pures. destruct (decide (i = NP)) as [->|Hne].
  - rewrite (bool_decide_eq_true_2 (Z.of_nat NP = Z.of_nat NP)) //. wp_pures.
    iApply "HΦ". by rewrite Nat.sub_diag.
  - rewrite (bool_decide_eq_false_2 (Z.of_nat i = Z.of_nat NP)); last lia.
    rewrite (_ : (NP - i)%nat = S (NP - S i)); last lia.
    rewrite -cons_seq !big_sepL_cons.
    iDestruct "Hcells" as "[Hcell Hcells]".
    rewrite (_ : (S (NP - S i) * retirer_cost)%nat = (retirer_cost + (NP - S i) * retirer_cost)%nat);
      last lia.
    iDestruct "Hc" as "[Hc1 Hc]".
    wp_pures. wp_bind (AllocN _ _).
    iApply (retirer_alloc γs d with "Hc1"). iIntros (t) "Hd Hbody".
    wp_pures. wp_store. iDestruct ("Hbody" with "Hd") as "Hbody".
    wp_pures. rewrite -Nat2Z.inj_add. wp_store. wp_pures.
    replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
    iApply ("IH" with "[%] Hcells Hc"); first lia.
    iIntros "!> Hcells". iApply "HΦ".
    iSplitL "Hcell Hbody"; last iExact "Hcells".
    iExists t. iSplitL "Hcell"; [iExact "Hcell"|iExact "Hbody"].
Qed.

Lemma hazard_domain_new_spec :
  hazard_domain_new_sp_spec' N (hazard_domain_new_sp H R NP) (H + NP + NP * retirer_cost)%nat
    IsHazardDomain.
Proof.
  iIntros (E Φ) "[Hc Hcr] HΦ". iApply wp_fupd. wp_lam.
  wp_apply (wp_allocN_cred with "[Hc]") as (d) "[†d Hd]"; first lia.
  { by rewrite -?Nat2Z.inj_add Nat2Z.id. }
  rewrite -?Nat2Z.inj_add Nat2Z.id replicate_add array_app length_replicate.
  iDestruct "Hd" as "[Hd Hcells]".
  iAssert ([∗ list] j ∈ seq 0 (NP - 0), (Loc.blk_to_loc d +ₗ (H + j)%nat) ↦ #())%I
    with "[Hcells]" as "Hcells".
  { rewrite Nat.sub_0_r /array big_sepL_replicate_seq.
    iApply (big_sepL_mono with "Hcells"). iIntros (k j _) "Hj".
    by rewrite Loc.add_assoc Nat2Z.inj_add. }
  iMod (ghost_map_alloc (∅ : gmap positive ninfo)) as (γi) "[Hi _]".
  iMod (coP_ghost_map_alloc (∅ : gmap blk positive)) as (γp) "[Hp _]".
  iMod (ghost_map_alloc (∅ : gmap (positive * nat) bool)) as (γt) "[Ht _]".
  iMod (ghost_map_alloc sst0) as (γq) "[Hq Hqs]".
  set γs := HPNames γi γp γt γq.
  wp_pures.
  wp_apply (hp_pool_init_spec γs d 0 with "[$Hcells Hcr]") as "Hpool"; first lia.
  { by rewrite Nat.sub_0_r. }
  wp_pures.
  iMod (inv_alloc (hpInvN) _ (HazardDomain γs d) with "[-HΦ]") as "#Hinv".
  { iNext. iExists ∅, ∅, ∅, sst0. iFrame "Hi Hp Ht Hq".
    rewrite /sst0 big_sepM_map_seq big_sepL_replicate_seq.
    rewrite /array big_sepL_replicate_seq.
    iSplitL "Hd Hqs".
    { iCombine "Hd Hqs" as "H". rewrite -big_sepL_sep.
      iApply (big_sepL_mono with "H"). iIntros (k s Hks) "[Hd Hq]".
      apply list_elem_of_lookup_2, elem_of_seq in Hks.
      iExists (None, None). rewrite -/sst0 lookup_sst0; last lia.
      iSplit; first done. iLeft. by iFrame. }
    iSplit; first (iPureIntro; apply sst0_ok).
    iSplit; first (iPureIntro; intros ?? [? Hx]; by rewrite lookup_empty in Hx).
    rewrite !big_sepM_empty Nat.sub_0_r. iSplit; first done. iSplit; first done.
    iApply (big_sepL_mono with "Hpool"). iIntros (k j _) "(%t & Hj & Hb)".
    iExists #t. iFrame. iRight. iExists t. by iFrame. }
  iApply ("HΦ" $! (encode (γs, Loc.blk_to_loc d))). iModIntro. iExists γs. by iFrame "Hinv".
Qed.

Lemma hazard_domain_register : hazard_domain_register_sp' N IsHazardDomain Managed.
Proof.
  iIntros (Rs E p lv γ_p γd d HE) "#(%γs & -> & Hinv) (Hp & †p & HR)".
  iInv "Hinv" as (info ptrs tkm sst)
    "(>Hinfo & >Hptrs & >Htk & >Hsst & Hslots & >%Hok & >%Htkok & Hnodes & >Hfree & Hpool)" "Hcl".
  (* [p] is not registered: the invariant would hold its freeable permission. *)
  destruct (ptrs !! p) as [i0|] eqn:Hp0.
  { iDestruct (big_sepM_lookup with "Hfree") as (x) "(_ & †p')"; first done.
    iDestruct (heap_freeable_valid with "†p †p'") as %[]. }
  set i := fresh (dom info).
  have Hi : info !! i = None by apply not_elem_of_dom, is_fresh.
  iMod (coP_cinv_alloc _ (resN p i) (res Rs p (length lv) γ_p) with "[Hp HR]") as (γc) "[#Hci Hown]".
  { iNext. iExists lv. by iFrame. }
  iMod (ghost_map_insert_persist i (NInfo p (length lv) γc γ_p) with "Hinfo") as "[Hinfo #Hii]";
    first done.
  iMod (coP_ghost_map_insert p i with "Hptrs") as "[Hptrs Hpi]"; first done.
  have Hdisj : tk0 i ##ₘ tkm.
  { apply map_disjoint_spec. intros [j s] b1 b2. rewrite lookup_tk0.
    case_bool_decide as Hc; last done.
    destruct Hc as [-> _]. intros _ Hb2.
    destruct (Htkok i s) as [? Hx]; first by eexists. by rewrite Hi in Hx. }
  iMod (ghost_map_insert_big (tk0 i) with "Htk") as "[Htk Htks]"; first done.
  rewrite big_sepM_tk0.
  iAssert (shareE γs γc p i ⊤) with "[Hown Hpi]" as "Hsh"; first by iFrame.
  rewrite -shareE_collect. iDestruct "Hsh" as "[HM Hshs]".
  iMod ("Hcl" with "[-HM Htks]") as "_".
  { iNext.
    iExists (<[i := NInfo p (length lv) γc γ_p]> info), (<[p := i]> ptrs), (tk0 i ∪ tkm), sst.
    iFrame "Hinfo Hptrs Htk Hsst Hslots".
    iSplit.
    { iPureIntro. intros s v j Hs. destruct (Hok s v j Hs) as (x & Hx & ->).
      exists x. rewrite lookup_insert_ne //. intros ->. by rewrite Hi in Hx. }
    iSplit.
    { iPureIntro. intros j s [b Hb]. apply lookup_union_Some_raw in Hb as [Hb|[_ Hb]].
      - rewrite lookup_tk0 in Hb. case_bool_decide as Hc; last done.
        destruct Hc as [-> _]. rewrite lookup_insert_eq. by eexists.
      - destruct (Htkok j s) as [x Hx]; first by eexists.
        destruct (decide (j = i)) as [->|]; first by rewrite Hi in Hx.
        rewrite lookup_insert_ne //; by eexists. }
    iSplitR "Hfree †p Hpool".
    - rewrite big_sepM_insert //. iSplitL "Hshs".
      + rewrite /node_inv. iApply (big_sepL_mono with "Hshs"). iIntros (k s Hks) "Hs".
        apply list_elem_of_lookup_2, elem_of_seq in Hks.
        iExists false. iSplit.
        { iPureIntro. apply lookup_union_Some_l. rewrite lookup_tk0 bool_decide_true //. lia. }
        rewrite /validated_for bool_decide_false; first done.
        destruct (sst !! s) as [[v o]|] eqn:Hs; last done. simpl. intros [= ->].
        destruct (Hok _ _ _ Hs) as (x & Hx & _). by rewrite Hi in Hx.
      + iApply (big_sepM_mono with "Hnodes"). iIntros (j x Hjx) "Hn". rewrite /node_inv.
        iApply (big_sepL_mono with "Hn"). iIntros (k s _) "(%b & %Hb & Hs)".
        iExists b. iFrame. iPureIntro. apply lookup_union_Some_raw. right. split; last done.
        rewrite lookup_tk0 bool_decide_false //. intros [-> _]. by rewrite Hi in Hjx.
    - iSplitR "Hpool"; last iExact "Hpool".
      rewrite big_sepM_insert //. iSplitL "†p".
      { iExists (NInfo p (length lv) γc γ_p). iFrame. iPureIntro.
        split; [by rewrite lookup_insert_eq|done]. }
      iApply (big_sepM_mono with "Hfree"). iIntros (q j Hqj) "(%x & [%Hx %] & ?)".
      iExists x. iFrame. iPureIntro. split; last done.
      rewrite lookup_insert_ne //. intros ->. by rewrite Hi in Hx. }
  iModIntro. iExists γs, d, i, γc. by iFrame "Hii Hci HM Htks".
Qed.

(** The shield of slot [idx] changes its slot's pointer to [v'] and stops
    validating. *)
Lemma shield_write γs d idx vo v' (w : val) info tkm sst st (E' : coPset) Φ :
  idx < H →
  w = #(oblk_to_lit v') →
  ghost_map_auth γs.(γinfo) (DfracOwn 1) info -∗
  ghost_map_auth γs.(γsst) (DfracOwn 1) sst -∗
  idx ↪[γs.(γsst)] vo -∗
  ([∗ list] s ∈ seq 0 H, ∃ vo, ⌜sst !! s = Some vo⌝ ∗ slot_inv γs d s vo) -∗
  ⌜sst_ok info sst⌝ -∗
  ([∗ map] i ↦ x ∈ info, node_inv γs sst tkm i x) -∗
  match st with
  | Deactivated => ⌜vo = (None, None)⌝
  | NotValidated p => ⌜vo = (Some p, None)⌝
  | Validated p γ_p Rs n => ∃ i γc, ⌜vo = (Some p, Some i)⌝ ∗
      i ↪[γs.(γinfo)]□ NInfo p n γc γ_p ∗
      coP_cinv (resN p i) γc (res Rs p n γ_p) ∗
      shareE γs γc p i {[slid idx]}
  end -∗
  (ghost_map_auth γs.(γinfo) (DfracOwn 1) info -∗
    ghost_map_auth γs.(γsst) (DfracOwn 1) (<[idx := (v', None)]> sst) -∗
    idx ↪[γs.(γsst)] (v', None) -∗
    ([∗ list] s ∈ seq 0 H, ∃ vo, ⌜<[idx := (v', None)]> sst !! s = Some vo⌝ ∗ slot_inv γs d s vo) -∗
    ⌜sst_ok info (<[idx := (v', None)]> sst)⌝ -∗
    ([∗ map] i ↦ x ∈ info, node_inv γs (<[idx := (v', None)]> sst) tkm i x) ={E'}=∗
    Φ #()) -∗
  WP #(d +ₗ idx) <- w @ E' {{ Φ }}.
Proof.
  iIntros (Hidx ->) "Hinfo Hsst Hfrag Hslots %Hok Hnodes Hst HΦ".
  iDestruct (ghost_map_lookup with "Hsst Hfrag") as %Hvo.
  iDestruct (slots_acc γs d sst idx (v', None) with "Hslots") as "[(%vo0 & %Hvo0 & Hslot) Hslots]";
    first done.
  rewrite Hvo in Hvo0. injection Hvo0 as <-.
  iDestruct "Hslot" as "[(_ & _ & Hfrag') | Hw]".
  { by iDestruct (ghost_map_elem_valid_2 with "Hfrag Hfrag'") as %[? _]. }
  wp_store.
  iMod (ghost_map_update (v', None) with "Hsst Hfrag") as "[Hsst Hfrag]".
  iAssert (ghost_map_auth γs.(γinfo) (DfracOwn 1) info ∗
           [∗ map] j ↦ y ∈ info, node_inv γs (<[idx := (v', None)]> sst) tkm j y)%I
    with "[Hnodes Hst Hinfo]" as "[Hinfo Hnodes]".
  { destruct st as [|p0|p0 γ_p0 R0 n0]; simpl.
    - iDestruct "Hst" as %->. iFrame. by rewrite -(nodes_sst_same _ _ _ _ _ _ _ Hvo).
    - iDestruct "Hst" as %->. iFrame. by rewrite -(nodes_sst_same _ _ _ _ _ _ _ Hvo).
    - iDestruct "Hst" as (i γc) "(-> & #Hi & #Hci & Hsh)".
      iDestruct (ghost_map_lookup with "Hinfo Hi") as %Hx. iFrame "Hinfo".
      by iApply (nodes_unvalidate _ _ _ _ _ _ _ _ _ Hvo Hx with "Hnodes Hsh"). }
  iApply ("HΦ" with "Hinfo Hsst Hfrag [Hslots Hw] [] Hnodes").
  - iApply "Hslots". by iRight.
  - iPureIntro. intros s v i. rewrite lookup_insert_Some.
    intros [[<- [=]]|[_ Hs]]. by apply Hok in Hs.
Qed.

Lemma shield_set_spec : shield_set_sp_spec' N shield_set_sp IsHazardDomain Shield.
Proof.
  iIntros (p E γd d sh st HE) "_". iIntros (Φ) "!> Hsh HΦ".
  iDestruct "Hsh" as (γs d' idx vo) "(-> & -> & %Hidx & #Hinv & Hfrag & Hst)".
  wp_lam. wp_pures.
  iInv "Hinv" as (info ptrs tkm sst)
    "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok & >%Htkok & >Hnodes & >Hfree & Hpool)" "Hcl".
  iApply (shield_write _ _ _ _ p with "Hinfo Hsst Hfrag Hslots [//] Hnodes Hst"); [done|done|].
  iIntros "Hinfo Hsst Hfrag Hslots %Hok' Hnodes". iModIntro.
  iMod ("Hcl" with "[-HΦ Hfrag]") as "_".
  { iNext. iExists info, ptrs, tkm, _. by iFrame. }
  iModIntro. iApply "HΦ". iExists γs, d', idx, (p, None). iFrame "∗ #". iSplit; first done.
  iSplit; first done. iSplit; first done. by destruct p.
Qed.

Lemma shield_unset_spec : shield_unset_sp_spec' N shield_unset_sp IsHazardDomain Shield.
Proof.
  iIntros (E γd d sh st HE) "_". iIntros (Φ) "!> Hsh HΦ".
  iDestruct "Hsh" as (γs d' idx vo) "(-> & -> & %Hidx & #Hinv & Hfrag & Hst)".
  wp_lam. wp_pures.
  iInv "Hinv" as (info ptrs tkm sst)
    "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok & >%Htkok & >Hnodes & >Hfree & Hpool)" "Hcl".
  iApply (shield_write _ _ _ _ None with "Hinfo Hsst Hfrag Hslots [//] Hnodes Hst"); [done|done|].
  iIntros "Hinfo Hsst Hfrag Hslots %Hok' Hnodes". iModIntro.
  iMod ("Hcl" with "[-HΦ Hfrag]") as "_".
  { iNext. iExists info, ptrs, tkm, _. by iFrame. }
  iModIntro. iApply "HΦ". iExists γs, d', idx, (None, None). by iFrame "∗ #".
Qed.

Lemma shield_drop_spec : shield_drop_sp_spec' N shield_drop_sp IsHazardDomain Shield.
Proof.
  iIntros (E γd d sh st HE) "_". iIntros (Φ) "!> Hsh HΦ".
  iDestruct "Hsh" as (γs d' idx vo) "(-> & -> & %Hidx & #Hinv & Hfrag & Hst)".
  wp_lam. wp_pures.
  iInv "Hinv" as (info ptrs tkm sst)
    "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok & >%Htkok & >Hnodes & >Hfree & Hpool)" "Hcl".
  iDestruct (ghost_map_lookup with "Hsst Hfrag") as %Hvo.
  iDestruct (slots_acc γs d' sst idx (None, None) with "Hslots") as "[(%vo0 & %Hvo0 & Hslot) Hslots]";
    first done.
  rewrite Hvo in Hvo0. injection Hvo0 as <-.
  iDestruct "Hslot" as "[(_ & _ & Hfrag') | Hw]".
  { by iDestruct (ghost_map_elem_valid_2 with "Hfrag Hfrag'") as %[? _]. }
  wp_store.
  iMod (ghost_map_update (None, None) with "Hsst Hfrag") as "[Hsst Hfrag]".
  iAssert (ghost_map_auth γs.(γinfo) (DfracOwn 1) info ∗
           [∗ map] j ↦ y ∈ info, node_inv γs (<[idx := (None, None)]> sst) tkm j y)%I
    with "[Hnodes Hst Hinfo]" as "[Hinfo Hnodes]".
  { destruct st as [|p0|p0 γ_p0 R0 n0]; simpl.
    - iDestruct "Hst" as %->. iFrame. by rewrite -(nodes_sst_same _ _ _ _ _ _ _ Hvo).
    - iDestruct "Hst" as %->. iFrame. by rewrite -(nodes_sst_same _ _ _ _ _ _ _ Hvo).
    - iDestruct "Hst" as (i γc) "(-> & #Hi & #Hci & Hsh)".
      iDestruct (ghost_map_lookup with "Hinfo Hi") as %Hx. iFrame "Hinfo".
      by iApply (nodes_unvalidate _ _ _ _ _ _ _ _ _ Hvo Hx with "Hnodes Hsh"). }
  iMod ("Hcl" with "[-HΦ]") as "_".
  { iNext. iExists info, ptrs, tkm, _. iFrame. iSplitL.
    - iApply "Hslots". iLeft. by iFrame.
    - iPureIntro. split; last done. intros s v i. rewrite lookup_insert_Some.
      intros [[<- [=]]|[_ Hs]]. by apply Hok in Hs. }
  iModIntro. by iApply "HΦ".
Qed.

Lemma shield_new_spec : shield_new_sp_spec' N (shield_new_sp H) IsHazardDomain Shield.
Proof.
  iIntros (E γd d HE) "#(%γs & -> & #Hinv)". iIntros (Φ) "!> _ HΦ".
  wp_lam.
  iLöb as "IH" forall (Φ) "HΦ".
  iAssert (∀ Ψ (i : nat), ⌜i ≤ H⌝ -∗
    (∀ sh, Shield (encode (γs, d)) sh Deactivated -∗ Ψ #sh) -∗
    WP shield_new_loop_sp H #d #i @ E {{ Ψ }})%I as "Hloop".
  { iLöb as "IH'". iIntros (Ψ i Hi) "HΨ". wp_lam. wp_pures. case_bool_decide as Heq.
    - wp_pures. iApply ("IH'" $! Ψ 0 with "[%] HΨ"). lia.
    - assert (i < H) as Hlt by (assert (i ≠ H) by (intros ->; done); lia).
      wp_pures. wp_bind (CmpXchg _ _ _).
      iInv "Hinv" as (info ptrs tkm sst)
        "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok & >%Htkok & >Hnodes & >Hfree & Hpool)" "Hcl".
      iDestruct (big_sepL_lookup_acc with "Hslots") as "[(%vo & %Hvo & Hslot) Hslots]";
        first by apply lookup_seq_lt.
      iDestruct "Hslot" as "[(Hw & -> & Hfrag) | Hw]".
      + wp_cmpxchg_suc.
        iMod ("Hcl" with "[-HΨ Hfrag]") as "_".
        { iNext. iExists info, ptrs, tkm, _. iFrame. iSplit; last done.
          iApply "Hslots". iExists _. iSplit; first done. by iRight. }
        iModIntro. wp_pures. iApply "HΨ". iExists γs, d, i, (None, None). by iFrame "∗ #".
      + destruct (decide (#(oblk_to_lit vo.1) = #())) as [Heq'|Hne].
        { destruct vo as [[]?]; simpl in Heq'; done. }
        wp_cmpxchg_fail.
        iMod ("Hcl" with "[-HΨ]") as "_".
        { iNext. iExists info, ptrs, tkm, _. iFrame. iSplit; last done.
          iApply "Hslots". iExists _. iSplit; first done. by iRight. }
        iModIntro. wp_pures.
        replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
        iApply ("IH'" $! Ψ (S i) with "[%] HΨ"). lia. }
  iApply ("Hloop" $! Φ 0 with "[%] HΦ"). lia.
Qed.

Lemma shield_validate : shield_validate_sp' N IsHazardDomain Managed Shield.
Proof.
  iIntros (E γd d Rs p γ_p sh n HE) "#(%γs & -> & #Hinv) HM Hsh".
  iDestruct "HM" as (γs' d' i γc) "(%Henc & #Hi & #Hci & HMsh & Htks)".
  apply (inj encode) in Henc as [= <- <-].
  iDestruct "Hsh" as (γs'' d'' idx vo) "(%Henc' & -> & %Hidx & _ & Hfrag & ->)".
  apply (inj encode) in Henc' as [= <- <-].
  iInv "Hinv" as (info ptrs tkm sst)
    "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok & >%Htkok & >Hnodes & >Hfree & Hpool)" "Hcl".
  iDestruct (ghost_map_lookup with "Hsst Hfrag") as %Hvo.
  iDestruct (ghost_map_lookup with "Hinfo Hi") as %Hx.
  iDestruct (big_sepL_lookup_acc with "Htks") as "[Htk_idx Htks]"; first by apply lookup_seq_lt.
  iDestruct (ghost_map_lookup with "Htk Htk_idx") as %Htkv.
  iDestruct ("Htks" with "Htk_idx") as "Htks".
  iDestruct (nodes_validate _ _ _ _ idx (Some p) i _ Hvo Hx Htkv Hidx with "Hnodes") as "[Hsh Hnodes]".
  iDestruct (slots_acc γs d sst idx (Some p, Some i) with "Hslots") as "[(%vo0 & %Hvo0 & Hslot) Hslots]";
    first done.
  rewrite Hvo in Hvo0. injection Hvo0 as <-.
  iDestruct "Hslot" as "[(_ & _ & Hfrag') | Hw]".
  { by iDestruct (ghost_map_elem_valid_2 with "Hfrag Hfrag'") as %[? _]. }
  iMod (ghost_map_update (Some p, Some i) with "Hsst Hfrag") as "[Hsst Hfrag]".
  iMod ("Hcl" with "[-HMsh Htks Hfrag Hsh]") as "_".
  { iNext. iExists info, ptrs, tkm, _. iFrame. iSplitL.
    - iApply "Hslots". by iRight.
    - iPureIntro. split; last done. intros s v j. rewrite lookup_insert_Some.
      intros [[<- [= <- <-]]|[_ Hs]]; last by apply Hok in Hs.
      exists (NInfo p n γc γ_p). done. }
  iModIntro. iSplitL "HMsh Htks".
  - iExists γs, d, i, γc. by iFrame "∗ #".
  - iExists γs, d, idx, _. iFrame "∗ #". iPureIntro. done.
Qed.

Lemma tagged_blk_neq (p1 p2 : blk) (t1 t2 : nat) :
  (p1, t1) ≠ (p2, t2) →
  #(Some (Loc.blk_to_loc p1) &ₜ t1) ≠ #(Some (Loc.blk_to_loc p2) &ₜ t2).
Proof.
  intros Hne [= Hp Ht]. apply Hne. subst. f_equal. lia.
Qed.

Lemma shield_protect_tagged_spec :
  shield_protect_tagged_sp_spec' N shield_protect_tagged_sp IsHazardDomain Managed Shield.
Proof.
  intros E γd d sh st a dq HE.
  iIntros "#IHD Sh" (Φ) "AU".
  wp_lam. wp_pures.
  wp_bind (! _)%E. iMod "AU" as (p1 t1 γ n Rs) "[[a↦ M] [Abort _]]".
  wp_load. iMod ("Abort" with "[$a↦ $M]") as "AU". clear γ n Rs.
  iModIntro.
  iLöb as "IH" forall (p1 t1 st). wp_lam. wp_pures.
  change #(Some (Loc.blk_to_loc p1) &ₜ 0) with #(oblk_to_lit (Some p1)).
  wp_apply (shield_set_spec (Some p1) with "IHD Sh") as "Sh"; first done.
  wp_pures.
  wp_bind (! _)%E. iMod "AU" as (p2 t2 γ n Rs) "[[a↦ M] CloseAU]".
  wp_load.
  destruct (decide ((p1, t1) = (p2, t2))) as [Heq|NE].
  - injection Heq as <- <-.
    iMod (shield_validate with "IHD M Sh") as "[M Sh]"; first solve_ndisj.
    iDestruct "CloseAU" as "[_ Commit]".
    iMod ("Commit" with "[$a↦ $M $Sh]") as "HΦ".
    iModIntro. wp_pures. rewrite bool_decide_eq_true_2 //. wp_pures. iApply "HΦ".
  - iDestruct "CloseAU" as "[Abort _]".
    iMod ("Abort" with "[$a↦ $M]") as "AU".
    iModIntro. wp_pures. rewrite bool_decide_eq_false_2; last by apply tagged_blk_neq.
    wp_pures. iApply ("IH" with "Sh AU").
Qed.

Lemma shield_acc : shield_acc_sp' N Shield.
Proof.
  iIntros (E γd Rs sh p γ_p n HE) "Sh".
  iDestruct "Sh" as (γs d idx vo)
    "(%Henc & -> & %Hidx & #Hinv & Hfrag & (%i & %γc & -> & #Hi & #Hci & [Hown Hpe]))".
  iMod (coP_cinv_acc with "Hci Hown") as "(Hres & Hown & Hclose)"; first solve_ndisj.
  iDestruct "Hres" as (lv) "(>%Hlen & >Hp & HR)".
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iExists lv. iFrame "Hp HR". iSplit; first done.
  iSplitR "Hclose Hmask".
  { iExists γs, d, idx, _. iFrame "∗ #". iPureIntro. done. }
  iIntros (lv') "(%Hlen' & Hp & HR)". iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hp HR]") as "_"; last done.
  iNext. iExists lv'. iFrame. iPureIntro. lia.
Qed.

Lemma managed_acc : managed_acc_sp' N Managed.
Proof.
  iIntros (E γd Rs p γ_p n HE) "HM".
  iDestruct "HM" as (γs d i γc) "(%Henc & #Hi & #Hci & [Hown Hpe] & Htks)".
  iMod (coP_cinv_acc with "Hci Hown") as "(Hres & Hown & Hclose)"; first solve_ndisj.
  iDestruct "Hres" as (lv) "(>%Hlen & >Hp & HR)".
  iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
  iExists lv. iFrame "Hp HR". iSplit; first done.
  iSplitR "Hclose Hmask".
  { iExists γs, d, i, γc. by iFrame "∗ #". }
  iIntros (lv') "(%Hlen' & Hp & HR)". iMod "Hmask" as "_".
  iMod ("Hclose" with "[Hp HR]") as "_"; last done.
  iNext. iExists lv'. iFrame. iPureIntro. lia.
Qed.

Lemma coPneset_not_disj_self (E : coPneset) : ¬ E ## E.
Proof.
  rewrite coPneset_disj_iff. intros Hd. apply (coPneset_nonempty E). set_solver.
Qed.

Lemma managed_exclusive : managed_exclusive_sp' N Managed.
Proof.
  iIntros (γd p γ_p γ_p' n n' Rs Rs') "HM HM'".
  iDestruct "HM" as (γs d i γc) "(%Henc & _ & _ & [_ Hpe] & _)".
  iDestruct "HM'" as (γs' d' i' γc') "(%Henc' & _ & _ & [_ Hpe'] & _)".
  rewrite Henc in Henc'. apply (inj encode) in Henc' as [= <- <-].
  iDestruct (coP_ghost_map_elem_valid_2 with "Hpe Hpe'") as %[Hd _].
  by apply coPneset_not_disj_self in Hd.
Qed.

Lemma shield_managed_agree : shield_managed_agree_sp' N Managed Shield.
Proof.
  iIntros (γd sh p γ_p1 γ_p2 Rs1 Rs2 n1 n2) "Sh HM".
  iDestruct "Sh" as (γs d idx vo)
    "(%Henc & -> & %Hidx & #Hinv & Hfrag & (%i & %γc & -> & #Hi & #Hci & [Hown Hpe]))".
  iDestruct "HM" as (γs' d' i' γc') "(%Henc' & #Hi' & _ & [_ Hpe'] & _)".
  rewrite Henc in Henc'. apply (inj encode) in Henc' as [= <- <-].
  iDestruct (coP_ghost_map_elem_agree with "Hpe Hpe'") as %<-.
  iDestruct (ghost_map_elem_agree with "Hi Hi'") as %Heq.
  iPureIntro. by inversion Heq.
Qed.

(** ** Retirers *)

(** A retired block, with the slots [s] with [P s] known not to protect it:
    the retirer holds their shares. *)
Definition RetiredEntryC γs (p : blk) (n : nat) (P : nat → Prop) : iProp :=
  ∃ i γc γ_p Rs,
    i ↪[γs.(γinfo)]□ NInfo p n γc γ_p ∗
    coP_cinv (resN p i) γc (res Rs p n γ_p) ∗
    shareE γs γc p i (Mset H) ∗
    ([∗ list] s ∈ seq 0 H, ∃ b : bool, (i, s) ↪[γs.(γtk)] b ∗
       (if b then shareE γs γc p i {[slid s]} else True) ∗ ⌜P s → b = true⌝).

Lemma retired_entry_C γs p n :
  RetiredEntry γs p n ⊣⊢ RetiredEntryC γs p n (λ _, False%type).
Proof.
  rewrite /RetiredEntry /RetiredEntryC. iSplit.
  - iIntros "(%i & %γc & %γ_p & %Rs & Hi & Hci & HM & Hs)". iExists i, γc, γ_p, Rs. iFrame.
    iApply (big_sepL_mono with "Hs"). iIntros (k s _) "(%b & Hb & Hsh)".
    iExists b. iFrame. by iPureIntro.
  - iIntros "(%i & %γc & %γ_p & %Rs & Hi & Hci & HM & Hs)". iExists i, γc, γ_p, Rs. iFrame.
    iApply (big_sepL_mono with "Hs"). iIntros (k s _) "(%b & Hb & Hsh & _)".
    iExists b. iFrame.
Qed.

Lemma retired_entry_C_weaken γs p n (P Q : nat → Prop) :
  (∀ s, s < H → Q s → P s) →
  RetiredEntryC γs p n P -∗ RetiredEntryC γs p n Q.
Proof.
  iIntros (HPQ) "(%i & %γc & %γ_p & %Rs & Hi & Hci & HM & Hs)".
  iExists i, γc, γ_p, Rs. iFrame.
  iApply (big_sepL_impl with "Hs"). iIntros "!>" (k s Hks) "(%b & Hb & Hsh & %HP)".
  apply lookup_seq in Hks as [-> Hk].
  iExists b. iFrame. iPureIntro. intros HQ. apply HP, HPQ; [lia|done].
Qed.

(** Retired blocks are distinct. *)
Lemma retired_entries_NoDup γs (L : list (blk * nat)) (P : blk → nat → Prop) :
  ([∗ list] pn ∈ L, RetiredEntryC γs pn.1 pn.2 (P pn.1)) -∗ ⌜NoDup (fst <$> L)⌝.
Proof.
  iIntros "HL". iInduction L as [|[p n] L] "IH"; first (iPureIntro; constructor).
  iDestruct "HL" as "[(%i & %γc & %γ_p & %Rs & _ & _ & [_ Hpe] & _) HL]".
  iDestruct ("IH" with "HL") as %HND.
  iAssert ⌜p ∉ fst <$> L⌝%I as %Hnin.
  { iIntros ((pn & -> & Hin)%list_elem_of_fmap).
    iDestruct (big_sepL_elem_of with "HL") as "(%i' & %γc' & %γ_p' & %Rs' & _ & _ & [_ Hpe'] & _)";
      first done.
    iDestruct (coP_ghost_map_elem_valid_2 with "Hpe Hpe'") as %[Hd _].
    by apply coPneset_not_disj_self in Hd. }
  iPureIntro. simpl. by constructor.
Qed.

Lemma enc_entries_app L1 L2 : enc_entries (L1 ++ L2) = enc_entries L1 ++ enc_entries L2.
Proof. induction L1 as [|[??] L1 IH]; [done|]. by rewrite /= IH. Qed.

Lemma length_enc_entries L : length (enc_entries L) = (2 * length L)%nat.
Proof. induction L as [|[??] L IH]; [done|]. rewrite /= IH. lia. Qed.

Lemma sum_sizes_le (L : list (blk * nat)) :
  Forall (λ pn, pn.2 ≤ K) L → (sum_list (snd <$> L) ≤ length L * K)%nat.
Proof.
  clear HR HH. induction 1 as [|[p n] L ? _ IH]; cbn in *; lia.
Qed.

Lemma sum_sizes_cons (p : blk) (n : nat) (L : list (blk * nat)) :
  sum_list (snd <$> ((p, n) :: L)) = (n + sum_list (snd <$> L))%nat.
Proof. done. Qed.

Lemma sum_sizes_nil : sum_list (snd <$> ([] : list (blk * nat))) = 0%nat.
Proof. done. Qed.

Lemma enc_entries_lookup (L : list (blk * nat)) (m : nat) (p : blk) (n : nat) :
  L !! m = Some (p, n) →
  enc_entries L !! (2 * m)%nat = Some #(Loc.blk_to_loc p) ∧
  enc_entries L !! (2 * m + 1)%nat = Some #n.
Proof.
  clear HR HH. revert m. induction L as [|[p' n'] L IH]=> m Hm; first done.
  destruct m as [|m]; simpl in *.
  - by injection Hm as -> ->.
  - replace (m + S (m + 0))%nat with (S (2 * m))%nat by lia. simpl.
    replace (2 * m + 1)%nat with (S (2 * m)) in IH by lia.
    by apply IH.
Qed.


Lemma NULL_ne_loc (t : loc) : #t ≠ #NULL.
Proof. by intros [=]. Qed.

Lemma hazard_retirer_new_spec :
  hazard_retirer_new_spec' N (hazard_retirer_new_sp H NP) IsHazardDomain Retirer.
Proof.
  iIntros (E γd d HE) "#(%γs & -> & #Hinv)". iIntros (Φ) "!> _ HΦ".
  wp_lam.
  iAssert (∀ (i : nat), ⌜i ≤ NP⌝ -∗ WP hazard_retirer_new_loop H NP #d #i @ E {{ Φ }})%I
    with "[HΦ]" as "Hloop"; last (iApply ("Hloop" $! 0); iPureIntro; lia).
  iLöb as "IH". iIntros (i Hi). wp_lam. wp_pures.
  destruct (decide (i = NP)) as [->|Hne].
  { rewrite (bool_decide_eq_true_2 (Z.of_nat NP = Z.of_nat NP)) //. wp_pures.
    iSpecialize ("IH" with "HΦ"). iApply ("IH" $! 0 with "[%]"). lia. }
  rewrite (bool_decide_eq_false_2 (Z.of_nat i = Z.of_nat NP)); last lia.
  have Hl : seq 0 NP !! i = Some i by rewrite lookup_seq_lt; last lia.
  wp_pures. rewrite -Nat2Z.inj_add.
  (* read the cell *)
  wp_bind (! _)%E.
  iInv "Hinv" as (info ptrs tkm sst)
    "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok & >%Htkok & >Hnodes & >Hfree & Hpool)" "Hcl".
  iDestruct (big_sepL_lookup_acc with "Hpool") as "[(%v & >Hv & Hcase) Hpool]"; first done.
  wp_load.
  iMod ("Hcl" with "[-HΦ]") as "_".
  { iNext. iExists info, ptrs, tkm, sst. iFrame. iSplit; first done. iSplit; first done. iApply "Hpool". iExists v. iFrame. }
  iModIntro. wp_pures.
  destruct (decide (v = #NULL)) as [->|Hvne].
  { rewrite (bool_decide_eq_true_2 (#NULL = #NULL)) //. wp_pures.
    replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
    iSpecialize ("IH" with "HΦ"). iApply ("IH" $! (S i) with "[%]"). lia. }
  rewrite (bool_decide_eq_false_2 (v = #NULL)) //. wp_pures. rewrite -Nat2Z.inj_add.
  wp_bind (CmpXchg _ _ _).
  iInv "Hinv" as (info' ptrs' tkm' sst')
    "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok' & >%Htkok' & >Hnodes & >Hfree & Hpool)" "Hcl".
  iDestruct (big_sepL_lookup_acc with "Hpool") as "[(%v' & >Hv & Hcase) Hpool]"; first done.
  destruct (decide (v' = v)) as [->|Hne'].
  - iDestruct "Hcase" as "[>%Heq|(%t & >-> & Hbody)]"; first done.
    wp_cmpxchg_suc.
    iMod ("Hcl" with "[-HΦ Hbody]") as "_".
    { iNext. iExists info', ptrs', tkm', sst'. iFrame. iSplit; first done. iSplit; first done. iApply "Hpool". iExists #NULL. iFrame.
      by iLeft. }
    iModIntro. wp_pures. iApply "HΦ". iModIntro. iExists γs, d.
    iSplit; first done. iSplit; first done. iExact "Hbody".
  - iAssert (▷ (⌜val_is_unboxed v'⌝ ∗
                (⌜v' = #NULL⌝ ∨ ∃ t : loc, ⌜v' = #t⌝ ∗ RetirerBody γs d t)))%I
      with "[Hcase]" as "[>%Hub Hcase]".
    { iNext. iDestruct "Hcase" as "[->|(%t & -> & Hb)]".
      - iSplit; [done|by iLeft].
      - iSplit; first done. iRight. iExists t. iSplit; first done. iExact "Hb". }
    wp_cmpxchg_fail.
    iMod ("Hcl" with "[-HΦ]") as "_".
    { iNext. iExists info', ptrs', tkm', sst'. iFrame. iSplit; first done. iSplit; first done. iApply "Hpool". iExists v'. iFrame. }
    iModIntro. wp_pures.
    replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
    iSpecialize ("IH" with "HΦ"). iApply ("IH" $! (S i) with "[%]"). lia.
Qed.

Lemma hazard_retirer_release_spec :
  hazard_retirer_release_spec' N (hazard_retirer_release_sp H NP) Retirer.
Proof.
  iIntros (E γd t HE Φ) "(%γs & %d & -> & #Hinv & Hbody) HΦ".
  wp_lam.
  iAssert (∃ v, (t +ₗ rtDomain) ↦ v ∗ ⌜v = #d⌝ ∗ ((t +ₗ rtDomain) ↦ v -∗ RetirerBody γs d t))%I
    with "[Hbody]" as (v) "(Hd & -> & Hbody)".
  { iDestruct "Hbody" as (L ents snap bank) "(Hd & Hrest)". iExists _. iFrame "Hd".
    iSplit; first done. iIntros "Hd". iExists L, ents, snap, bank. iFrame. }
  wp_load.
  iDestruct ("Hbody" with "Hd") as "Hbody".
  wp_pures.
  iAssert (∀ (i : nat), ⌜i ≤ NP⌝ -∗ RetirerBody γs d t -∗
    WP hazard_retirer_release_loop H NP #d #t #i @ E {{ Φ }})%I
    with "[HΦ]" as "Hloop"; last (iApply ("Hloop" $! 0 with "[%] Hbody"); lia).
  iLöb as "IH". iIntros (i Hi) "Hbody". wp_lam. wp_pures.
  destruct (decide (i = NP)) as [->|Hne].
  { rewrite (bool_decide_eq_true_2 (Z.of_nat NP = Z.of_nat NP)) //. wp_pures.
    iSpecialize ("IH" with "HΦ"). iApply ("IH" $! 0 with "[%] Hbody"). lia. }
  rewrite (bool_decide_eq_false_2 (Z.of_nat i = Z.of_nat NP)); last lia.
  have Hl : seq 0 NP !! i = Some i by rewrite lookup_seq_lt; last lia.
  wp_pures. rewrite -Nat2Z.inj_add.
  wp_bind (CmpXchg _ _ _).
  iInv "Hinv" as (info ptrs tkm sst)
    "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok & >%Htkok & >Hnodes & >Hfree & Hpool)" "Hcl".
  iDestruct (big_sepL_lookup_acc with "Hpool") as "[(%v & >Hv & Hcase) Hpool]"; first done.
  destruct (decide (v = #NULL)) as [->|Hne'].
  - wp_cmpxchg_suc.
    iMod ("Hcl" with "[-HΦ]") as "_".
    { iNext. iExists info, ptrs, tkm, sst. iFrame. iSplit; first done. iSplit; first done. iApply "Hpool". iExists #t.
      iSplitL "Hv"; first iExact "Hv". iRight. iExists t. iSplit; first done. iExact "Hbody". }
    iModIntro. wp_pures. by iApply "HΦ".
  - wp_cmpxchg_fail.
    iMod ("Hcl" with "[-HΦ Hbody]") as "_".
    { iNext. iExists info, ptrs, tkm, sst. iFrame. iSplit; first done. iSplit; first done. iApply "Hpool". iExists v. iFrame. }
    iModIntro. wp_pures.
    replace (Z.of_nat i + 1)%Z with (Z.of_nat (S i)) by lia.
    iSpecialize ("IH" with "HΦ"). iApply ("IH" $! (S i) with "[%] Hbody"). lia.
Qed.

Lemma hp_snap_contains_spec (t : loc) snap (p : blk) (s : nat) E :
  s ≤ H → length snap = H →
  {{{ (t +ₗ hp_snap_off R) ↦∗ snap }}}
    hp_snap_contains H R #t #p #s @ E
  {{{ RET #(bool_decide (#(Loc.blk_to_loc p) ∈ drop s snap)); (t +ₗ hp_snap_off R) ↦∗ snap }}}.
Proof.
  iIntros (Hs Hlen Φ) "Hsnap HΦ".
  iLöb as "IH" forall (s Hs Φ).
  wp_lam. wp_pures. destruct (decide (s = H)) as [->|Hne].
  - rewrite (bool_decide_eq_true_2 (Z.of_nat H = Z.of_nat H)) //.
    wp_pures. rewrite drop_ge; last lia.
    rewrite bool_decide_false; last by intros ?%elem_of_nil. by iApply "HΦ".
  - rewrite (bool_decide_eq_false_2 (Z.of_nat s = Z.of_nat H)); last lia.
    assert (s < H) as Hlt by lia.
    destruct (lookup_lt_is_Some_2 snap s) as [w Hw]; first lia.
    wp_pures. rewrite -Loc.add_assoc.
    wp_apply (wp_load_offset with "Hsnap") as "Hsnap"; first done.
    wp_pures. rewrite (drop_S _ _ _ Hw).
    destruct (decide (w = #(Loc.blk_to_loc p))) as [->|Hweq].
    + rewrite (bool_decide_eq_true_2 (#(Loc.blk_to_loc p) = #(Loc.blk_to_loc p))) //.
      wp_pures.
      have -> : bool_decide (#(Loc.blk_to_loc p) ∈ #(Loc.blk_to_loc p) :: drop (S s) snap) = true.
      { apply bool_decide_true. by left. }
      by iApply "HΦ".
    + rewrite (bool_decide_eq_false_2 (w = #(Loc.blk_to_loc p))) //.
      wp_pures. replace (Z.of_nat s + 1)%Z with (Z.of_nat (S s)) by lia.
      iApply ("IH" with "[%] Hsnap"); first lia.
      iIntros "!> Hsnap".
      rewrite (bool_decide_ext (#(Loc.blk_to_loc p) ∈ w :: drop (S s) snap)
                               (#(Loc.blk_to_loc p) ∈ drop (S s) snap)); first by iApply "HΦ".
      rewrite elem_of_cons. naive_solver.
Qed.

(** The shares that a read of slot [s] gives to a retirer: those of the blocks
    that the slot does not hold. *)
Lemma entries_take γs (info : gmap positive ninfo) (sst : gmap nat (option blk * option positive))
    (tkm : gmap (positive * nat) bool) (L : list (blk * nat)) (P : blk → nat → Prop) s (w : val) :
  s < H → sst_ok info sst →
  (∀ vo, sst !! s = Some vo → (w = #() ∧ vo = (None, None)) ∨ w = #(oblk_to_lit vo.1)) →
  ghost_map_auth γs.(γtk) (DfracOwn 1) tkm -∗
  ghost_map_auth γs.(γinfo) (DfracOwn 1) info -∗
  ([∗ map] i ↦ x ∈ info, node_inv γs sst tkm i x) -∗
  ([∗ list] pn ∈ L, RetiredEntryC γs pn.1 pn.2 (P pn.1)) ==∗
  ∃ tkm', ghost_map_auth γs.(γtk) (DfracOwn 1) tkm' ∗
    ghost_map_auth γs.(γinfo) (DfracOwn 1) info ∗
    ([∗ map] i ↦ x ∈ info, node_inv γs sst tkm' i x) ∗
    ⌜∀ j s', is_Some (tkm' !! (j, s')) ↔ is_Some (tkm !! (j, s'))⌝ ∗
    [∗ list] pn ∈ L, RetiredEntryC γs pn.1 pn.2
      (λ s', P pn.1 s' ∨ (s' = s ∧ w ≠ #(Loc.blk_to_loc pn.1)))%type.
Proof.
  iIntros (Hs Hok Hw) "Htk Hinfo Hnodes HL".
  iInduction L as [|[p n] L] "IH" forall (tkm).
  { iModIntro. iExists tkm. by iFrame. }
  iDestruct "HL" as "[(%i & %γc & %γ_p & %Rs & #Hi & #Hci & HM & Hss) HL]".
  iDestruct (ghost_map_lookup with "Hinfo Hi") as %Hx.
  have Hl : seq 0 H !! s = Some s by rewrite lookup_seq_lt.
  iDestruct (big_sepL_lookup_acc_impl with "Hss") as "[(%b & Hb & Hsh & %HP) Hclose]"; first done.
  iDestruct (ghost_map_lookup with "Htk Hb") as %Hb.
  iAssert (|==> ∃ tkm1 (b' : bool), ghost_map_auth γs.(γtk) (DfracOwn 1) tkm1 ∗
      ([∗ map] i ↦ x ∈ info, node_inv γs sst tkm1 i x) ∗
      ⌜∀ j s', is_Some (tkm1 !! (j, s')) ↔ is_Some (tkm !! (j, s'))⌝ ∗
      (i, s) ↪[γs.(γtk)] b' ∗ (if b' then shareE γs γc p i {[slid s]} else True) ∗
      ⌜P p s ∨ (s = s ∧ w ≠ #(Loc.blk_to_loc p)) → b' = true⌝)%I
    with "[Htk Hnodes Hb Hsh]" as ">(%tkm1 & %b' & Htk & Hnodes & %Htk1 & Hb & Hsh & %HP')".
  { destruct (decide (b = false ∧ w ≠ #(Loc.blk_to_loc p))) as [[-> Hne]|Hno].
    - have Hval : validated_for sst s i = false.
      { rewrite /validated_for bool_decide_false //.
        destruct (sst !! s) as [[v o]|] eqn:Hvo; last done. simpl. intros [= ->].
        destruct (Hok _ _ _ Hvo) as (x & Hx' & ->). rewrite Hx in Hx'. injection Hx' as <-.
        destruct (Hw _ eq_refl) as [[_ Hvo']|Hw']; first done.
        apply Hne. by rewrite Hw'. }
      iDestruct (nodes_take _ _ _ _ i _ s Hx Hb Hval Hs with "Hnodes") as "[Hsh' Hnodes]".
      iMod (ghost_map_update true with "Htk Hb") as "[Htk Hb]".
      iModIntro. iExists _, true. iFrame. iSplit; last done.
      iPureIntro. intros j s'. rewrite lookup_insert_is_Some'. naive_solver.
    - iModIntro. iExists tkm, b. iFrame. iPureIntro. split; first done.
      intros [HPs|[_ Hne]]; first by apply HP.
      destruct b; first done. exfalso. by apply Hno. }
  iMod ("IH" with "Htk Hinfo Hnodes HL") as (tkm') "(Htk & Hinfo & Hnodes & %Htk' & HL)".
  iModIntro. iExists tkm'. iFrame "Htk Hinfo Hnodes HL".
  iSplit.
  { iPureIntro. intros j s'. rewrite Htk'. apply Htk1. }
  iExists i, γc, γ_p, Rs. iFrame "Hi Hci HM".
  iApply ("Hclose" with "[] [Hb Hsh]").
  - iIntros "!>" (k s' Hks Hne) "(%b1 & Hb1 & Hsh1 & %HP1)". iExists b1. iFrame. iPureIntro.
    apply lookup_seq in Hks as [-> _].
    intros [HPs|[Heq _]]; first by apply HP1. simpl in Heq. lia.
  - iExists b'. iFrame. done.
Qed.

Lemma hp_snapshot_loop_spec γs (d t : loc) (L : list (blk * nat)) snap (s : nat) E :
  ↑(mgmtN N) ⊆ E → s ≤ H → length snap = H →
  {{{ inv hpInvN (HazardDomain γs d) ∗ (t +ₗ hp_snap_off R) ↦∗ snap ∗
      [∗ list] pn ∈ L, RetiredEntryC γs pn.1 pn.2
        (λ s', s' < s ∧ snap !! s' ≠ Some #(Loc.blk_to_loc pn.1))%type }}}
    hp_snapshot_loop H R #t #d #s @ E
  {{{ snap', RET #(); (t +ₗ hp_snap_off R) ↦∗ snap' ∗ ⌜length snap' = H⌝ ∗
      [∗ list] pn ∈ L, RetiredEntryC γs pn.1 pn.2
        (λ s', s' < H ∧ snap' !! s' ≠ Some #(Loc.blk_to_loc pn.1))%type }}}.
Proof.
  iIntros (HE Hs Hlen Φ) "(#Hinv & Hsnap & HL) HΦ".
  iLöb as "IH" forall (s snap Hs Hlen).
  wp_lam. wp_pures. destruct (decide (s = H)) as [->|Hne].
  - rewrite (bool_decide_eq_true_2 (Z.of_nat H = Z.of_nat H)) //.
    wp_pures. iApply ("HΦ" $! snap). iFrame "Hsnap HL". done.
  - rewrite (bool_decide_eq_false_2 (Z.of_nat s = Z.of_nat H)); last lia.
    assert (s < H) as Hlt by lia.
    wp_pures. wp_bind (! _)%E.
    iInv "Hinv" as (info ptrs tkm sst)
      "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok & >%Htkok & >Hnodes & >Hfree & Hpool)" "Hcl".
    iDestruct (big_sepL_lookup_acc with "Hslots") as "[(%vo & %Hvo & Hslot) Hslots]";
      first by apply lookup_seq_lt.
    iAssert (∃ w, (d +ₗ s) ↦ w ∗ ⌜(w = #() ∧ vo = (None, None)) ∨ w = #(oblk_to_lit vo.1)⌝ ∗
               ((d +ₗ s) ↦ w -∗ slot_inv γs d s vo))%I
      with "[Hslot]" as (w) "(Hw & %Hwvo & Hslot)".
    { iDestruct "Hslot" as "[(Hw & -> & Hfrag) | Hw]"; iExists _; iFrame "Hw".
      - iSplit; first by iLeft. iIntros "Hw". iLeft. by iFrame.
      - iSplit; first by iRight. iIntros "Hw". by iRight. }
    wp_load.
    iMod (entries_take _ _ _ _ L (λ q s', s' < s ∧ snap !! s' ≠ Some #(Loc.blk_to_loc q))%type s w
      with "Htk Hinfo Hnodes HL")
      as (tkm') "(Htk & Hinfo & Hnodes & %Htk' & HL)"; [done|done| |].
    { intros vo' Hvo'. rewrite Hvo in Hvo'. by injection Hvo' as <-. }
    iMod ("Hcl" with "[-Hsnap HL HΦ]") as "_".
    { iNext. iExists info, ptrs, tkm', sst. iFrame. iSplitL.
      - iApply "Hslots". iExists vo. iSplit; first done. by iApply "Hslot".
      - iPureIntro. split; first done. intros j s' Hj. apply (Htkok j s'). by apply Htk'. }
    iModIntro. wp_pures. rewrite -Loc.add_assoc.
    wp_apply (wp_store_offset with "Hsnap") as "Hsnap"; first by apply lookup_lt_is_Some_2; lia.
    wp_pures. replace (Z.of_nat s + 1)%Z with (Z.of_nat (S s)) by lia.
    iApply ("IH" $! (S s) (<[s := w]> snap) with "[%] [%] Hsnap [HL] HΦ"); [lia|by rewrite length_insert|].
    iApply (big_sepL_mono with "HL"). iIntros (k [p n] _) "HE".
    iApply (retired_entry_C_weaken with "HE"). simpl.
    intros s' _ [Hs' Hne'].
    destruct (decide (s' = s)) as [->|Hs's].
    + right. split; first done. intros ->. apply Hne'. by rewrite list_lookup_insert_eq; last lia.
    + left. split; first lia. by rewrite list_lookup_insert_ne in Hne'.
Qed.

(** A retirer that holds all the shares of a block frees it. *)
Lemma reclaim_entry γs (d : loc) (p : blk) n E :
  ↑N ⊆ E →
  inv hpInvN (HazardDomain γs d) -∗
  RetiredEntryC γs p n (λ s', s' < H)%type ={E}=∗
  ∃ lv, p ↦∗ lv ∗ †p…n ∗ ⌜length lv = n⌝.
Proof.
  iIntros (HE) "#Hinv (%i & %γc & %γ_p & %Rs & #Hi & #Hci & HM & Hss)".
  iAssert ([∗ list] s ∈ seq 0 H, shareE γs γc p i {[slid s]})%I with "[Hss]" as "Hss".
  { iApply (big_sepL_impl with "Hss"). iIntros "!>" (k s Hks) "(%b & _ & Hsh & %HP)".
    apply lookup_seq in Hks as [-> Hk]. rewrite HP //. }
  iCombine "HM Hss" as "Hsh". rewrite shareE_collect. iDestruct "Hsh" as "[Hown Hpe]".
  iMod (coP_cinv_cancel with "Hci Hown") as "Hres"; first solve_ndisj.
  iDestruct "Hres" as (lv) "(>%Hlen & >Hp & _)".
  iInv "Hinv" as (info ptrs tkm sst)
    "(>Hinfo & >Hptrs & >Htk & >Hsst & >Hslots & >%Hok & >%Htkok & >Hnodes & >Hfree & Hpool)" "Hcl".
  iDestruct (coP_ghost_map_lookup with "Hptrs Hpe") as %Hpi.
  iDestruct (ghost_map_lookup with "Hinfo Hi") as %Hx.
  iDestruct (big_sepM_delete with "Hfree") as "[(%x & [%Hx' _] & †p) Hfree]"; first done.
  rewrite Hx in Hx'. injection Hx' as <-.
  iMod (coP_ghost_map_delete with "Hptrs Hpe") as "Hptrs".
  iMod ("Hcl" with "[-Hp †p]") as "_".
  { iNext. iExists info, (delete p ptrs), tkm, sst. by iFrame. }
  iModIntro. iExists lv. by iFrame.
Qed.

Lemma take_enc_insert (ents : list val) (kept : list (blk * nat)) (p : blk) (n : nat) :
  take (2 * length kept) ents = enc_entries kept →
  (2 * length kept + 1 < length ents)%nat →
  take (2 * length (kept ++ [(p, n)]))
    (<[(2 * length kept + 1)%nat := #n]> (<[(2 * length kept)%nat := #(Loc.blk_to_loc p)]> ents)) =
  enc_entries (kept ++ [(p, n)]).
Proof.
  intros Htake Hlen.
  rewrite enc_entries_app -Htake length_app. change (length [(p, n)]) with 1%nat.
  change (enc_entries [(p, n)]) with [ #(Loc.blk_to_loc p); #n].
  apply list_eq=> m. rewrite lookup_take.
  have Htl : length (take (2 * length kept) ents) = (2 * length kept)%nat
    by rewrite length_take; lia.
  destruct (decide (m < 2 * length kept)%nat) as [Hlt|Hge].
  - rewrite decide_True; last lia. rewrite !list_lookup_insert_ne; [|lia|lia].
    rewrite lookup_app_l; last lia. rewrite lookup_take decide_True //.
  - rewrite lookup_app_r; last lia. rewrite Htl.
    destruct (decide (m = 2 * length kept)%nat) as [->|Hm1].
    + rewrite decide_True; last lia. rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_insert_eq; last lia. by rewrite Nat.sub_diag.
    + destruct (decide (m = 2 * length kept + 1)%nat) as [->|Hm2].
      * rewrite decide_True; last lia.
        rewrite list_lookup_insert_eq; last (rewrite length_insert; lia).
        by replace (2 * length kept + 1 - 2 * length kept)%nat with 1%nat by lia.
      * rewrite decide_False; last lia. symmetry. apply lookup_ge_None_2. simpl. lia.
Qed.

Lemma hp_compact_loop_spec γs (d t : loc) (L : list (blk * nat)) snap ents
    (kept : list (blk * nat)) (j : nat) bank E :
  ↑N ⊆ E → length kept ≤ j → j ≤ length L → length L ≤ R →
  length ents = (2 * R)%nat → length snap = H →
  take (2 * length kept) ents = enc_entries kept →
  (∀ m (pn : blk * nat), L !! m = Some pn → j ≤ m →
     ents !! (2 * m)%nat = Some #(Loc.blk_to_loc pn.1) ∧ ents !! (2 * m + 1)%nat = Some #pn.2) →
  Forall (λ pn, pn.2 ≤ K) L → Forall (λ pn, pn.2 ≤ K) kept →
  Forall (λ pn : blk * nat, #(Loc.blk_to_loc pn.1) ∈ snap) kept →
  (bank + sum_list (snd <$> kept) + sum_list (snd <$> drop j L) = R * K)%nat →
  {{{ inv hpInvN (HazardDomain γs d) ∗ (t +ₗ rtEntries) ↦∗ ents ∗
      (t +ₗ hp_snap_off R) ↦∗ snap ∗ ♢ bank ∗
      ([∗ list] pn ∈ kept, RetiredEntry γs pn.1 pn.2) ∗
      ([∗ list] pn ∈ drop j L, RetiredEntryC γs pn.1 pn.2
         (λ s', s' < H ∧ snap !! s' ≠ Some #(Loc.blk_to_loc pn.1))%type) }}}
    hp_compact_loop H R #t #(length L) #j #(length kept) @ E
  {{{ kept' ents' bank', RET #(length kept');
      (t +ₗ rtEntries) ↦∗ ents' ∗ (t +ₗ hp_snap_off R) ↦∗ snap ∗ ♢ bank' ∗
      ⌜length ents' = (2 * R)%nat⌝ ∗ ⌜take (2 * length kept') ents' = enc_entries kept'⌝ ∗
      ⌜Forall (λ pn, pn.2 ≤ K) kept'⌝ ∗ ⌜Forall (λ pn : blk * nat, #(Loc.blk_to_loc pn.1) ∈ snap) kept'⌝ ∗
      ⌜(bank' + sum_list (snd <$> kept') = R * K)%nat⌝ ∗
      [∗ list] pn ∈ kept', RetiredEntry γs pn.1 pn.2 }}}.
Proof.
  iIntros (HE Hkj HjL HLR Hents Hsnap Htake Hrest HFL HFk HFs Hbank Φ)
    "(#Hinv & Hents & Hsnap & Hbank & Hkept & Hrest) HΦ".
  iLöb as "IH" forall (ents kept j bank Hkj HjL Hents Htake Hrest HFk HFs Hbank).
  wp_lam. wp_pures.
  destruct (decide (j = length L)) as [->|Hne].
  - rewrite (bool_decide_eq_true_2 (Z.of_nat (length L) = Z.of_nat (length L))) //. wp_pures.
    rewrite drop_ge in Hbank; last done. simpl in Hbank.
    iApply ("HΦ" $! kept ents bank). iFrame. iPureIntro. split_and!; try done. lia.
  - rewrite (bool_decide_eq_false_2 (Z.of_nat j = Z.of_nat (length L))); last lia.
    destruct (lookup_lt_is_Some_2 L j) as [[p n] Hpn]; first lia.
    destruct (Hrest j (p, n) Hpn) as [Hep Hen]; first lia. cbn [fst snd] in Hep, Hen.
    rewrite (drop_S _ _ _ Hpn) in Hbank |- *.
    iDestruct "Hrest" as "[He Hrest]".
    wp_pures.
    replace (Z.of_nat 2 + 2 * Z.of_nat j)%Z with (Z.of_nat 2 + Z.of_nat (2 * j))%Z by lia.
    rewrite -Loc.add_assoc.
    wp_apply (wp_load_offset with "Hents") as "Hents"; first done.
    wp_pures.
    replace (Z.of_nat 2 + 2 * Z.of_nat j + 1)%Z with (Z.of_nat 2 + Z.of_nat (2 * j + 1))%Z by lia.
    rewrite -Loc.add_assoc.
    wp_apply (wp_load_offset with "Hents") as "Hents"; first done.
    wp_pures.
    wp_apply (hp_snap_contains_spec _ _ _ 0 with "Hsnap") as "Hsnap"; [lia|done|].
    rewrite drop_0.
    have Hn : n ≤ K by (rewrite Forall_lookup in HFL; by apply (HFL j (p, n))).
    destruct (decide (#(Loc.blk_to_loc p) ∈ snap)) as [Hin|Hnin].
    + rewrite bool_decide_true //. wp_pures.
      replace (Z.of_nat 2 + 2 * Z.of_nat (length kept))%Z
        with (Z.of_nat 2 + Z.of_nat (2 * length kept))%Z by lia.
      rewrite -Loc.add_assoc.
      wp_apply (wp_store_offset with "Hents") as "Hents"; first (apply lookup_lt_is_Some_2; lia).
      wp_pures.
      replace (Z.of_nat 2 + 2 * Z.of_nat (length kept) + 1)%Z
        with (Z.of_nat 2 + Z.of_nat (2 * length kept + 1))%Z by lia.
      rewrite -Loc.add_assoc.
      wp_apply (wp_store_offset with "Hents") as "Hents";
        first (apply lookup_lt_is_Some_2; rewrite length_insert; lia).
      wp_pures.
      replace (Z.of_nat j + 1)%Z with (Z.of_nat (S j)) by lia.
      replace (Z.of_nat (length kept) + 1)%Z with (Z.of_nat (length (kept ++ [(p, n)])))
        by (rewrite length_app /=; lia).
      iApply ("IH" with "[%] [%] [%] [%] [%] [%] [%] [%] Hents Hsnap Hbank [Hkept He] Hrest HΦ").
      * rewrite length_app /=. lia.
      * lia.
      * by rewrite !length_insert.
      * apply take_enc_insert; [done|lia].
      * intros m pn Hm Hjm. destruct (Hrest m pn Hm) as [H1 H2]; first lia.
        rewrite !list_lookup_insert_ne; [|lia|lia|lia|lia]. done.
      * apply Forall_app. split; first done. by apply Forall_singleton.
      * apply Forall_app. split; first done. by apply Forall_singleton.
      * rewrite fmap_app sum_list_with_app sum_sizes_cons sum_sizes_nil.
        rewrite sum_sizes_cons in Hbank. lia.
      * rewrite big_sepL_app /=. iFrame "Hkept". iSplitL; last done.
        rewrite retired_entry_C. iApply (retired_entry_C_weaken with "He"). naive_solver.
    + rewrite bool_decide_false //. wp_pures.
      iMod (reclaim_entry with "Hinv [He]") as (lv) "(Hp & †p & %Hlv)"; first done.
      { iApply (retired_entry_C_weaken with "He"). simpl. intros s' Hs' _. split; first done.
        intros Hsome. apply Hnin. by eapply list_elem_of_lookup_2. }
      wp_apply (wp_free_cred with "[$Hp †p]") as "Hc"; first by rewrite Hlv.
      { by rewrite Hlv. }
      iCombine "Hbank Hc" as "Hbank".
      wp_pures. replace (Z.of_nat j + 1)%Z with (Z.of_nat (S j)) by lia.
      iApply ("IH" with "[%] [%] [%] [%] [%] [%] [%] [%] Hents Hsnap Hbank Hkept Hrest HΦ");
        try done; try lia.
      * intros m pn Hm Hjm. apply Hrest; [done|lia].
      * rewrite sum_sizes_cons in Hbank. rewrite Hlv. cbn [snd] in *. lia.
Qed.

(** The survivors of a scan are distinct pointers of the snapshot, so there
    are at most [H] of them. *)
Lemma survivors_bound γs (kept : list (blk * nat)) (snap : list val) :
  Forall (λ pn : blk * nat, #(Loc.blk_to_loc pn.1) ∈ snap) kept →
  ([∗ list] pn ∈ kept, RetiredEntry γs pn.1 pn.2) -∗ ⌜length kept ≤ length snap⌝.
Proof.
  iIntros (Hin) "Hkept".
  iAssert ([∗ list] pn ∈ kept,
             RetiredEntryC γs pn.1 pn.2 ((λ (_ : blk) (_ : nat), False%type) pn.1))%I
    with "[Hkept]" as "Hkept".
  { iApply (big_sepL_mono with "Hkept"). iIntros (k pn _) "HE". by rewrite retired_entry_C. }
  iDestruct (retired_entries_NoDup _ kept (λ (_ : blk) (_ : nat), False%type) with "Hkept") as %HND.
  iPureIntro.
  rewrite -(length_fmap (λ pn : blk * nat, #(Loc.blk_to_loc pn.1)) kept).
  apply submseteq_length, NoDup_submseteq.
  - rewrite (list_fmap_compose fst (λ p : blk, #(Loc.blk_to_loc p))).
    apply NoDup_fmap_2; last done.
    intros p1 p2 [= Hp]. done.
  - intros v (pn & -> & Hpn)%list_elem_of_fmap. rewrite Forall_forall in Hin. by apply Hin.
Qed.

Lemma hp_reclaim_spec γs (d t : loc) (L : list (blk * nat)) snap ents bank (c0 : Z) E :
  ↑N ⊆ E → length L ≤ R → length ents = (2 * R)%nat → length snap = H →
  take (2 * length L) ents = enc_entries L →
  Forall (λ pn, pn.2 ≤ K) L →
  (bank + sum_list (snd <$> L) = R * K)%nat →
  {{{ inv hpInvN (HazardDomain γs d) ∗ (t +ₗ rtDomain) ↦ #d ∗ (t +ₗ rtCount) ↦ #c0 ∗
      (t +ₗ rtEntries) ↦∗ ents ∗ (t +ₗ hp_snap_off R) ↦∗ snap ∗ ♢ bank ∗
      [∗ list] pn ∈ L, RetiredEntry γs pn.1 pn.2 }}}
    hp_reclaim H R #t #(length L) @ E
  {{{ L' ents' snap' bank', RET #();
      (t +ₗ rtDomain) ↦ #d ∗ (t +ₗ rtCount) ↦ #(length L') ∗
      (t +ₗ rtEntries) ↦∗ ents' ∗ (t +ₗ hp_snap_off R) ↦∗ snap' ∗ ♢ bank' ∗
      ⌜length L' ≤ H ∧ length ents' = (2 * R)%nat ∧ length snap' = H⌝ ∗
      ⌜take (2 * length L') ents' = enc_entries L'⌝ ∗ ⌜Forall (λ pn, pn.2 ≤ K) L'⌝ ∗
      ⌜(bank' + sum_list (snd <$> L') = R * K)%nat⌝ ∗
      [∗ list] pn ∈ L', RetiredEntry γs pn.1 pn.2 }}}.
Proof.
  iIntros (HE HLR Hents Hsnap Htake HF Hbank Φ) "(#Hinv & Hd & Hc & Hents & Hsnap & Hbank & HL) HΦ".
  wp_lam. wp_pures. rewrite Loc.add_0. wp_load.
  wp_apply (hp_snapshot_loop_spec _ _ _ L _ 0 with "[$Hinv $Hsnap HL]") as (snap') "(Hsnap & %Hsnap' & HL)";
    [solve_ndisj|lia|done| |].
  { iApply (big_sepL_mono with "HL"). iIntros (k pn _) "HE".
    rewrite retired_entry_C. iApply (retired_entry_C_weaken with "HE"). intros ?? [? _]. lia. }
  wp_pures.
  wp_apply (hp_compact_loop_spec _ _ _ L snap' ents [] 0 bank with "[$Hinv $Hents $Hsnap $Hbank HL]")
    as (kept' ents' bank') "(Hents & Hsnap & Hbank & %Hents' & %Htake' & %HFk & %HFs & %Hbank' & Hkept)";
    try done; try lia.
  { intros m [p n] Hm _. have Hlt := lookup_lt_Some _ _ _ Hm.
    destruct (enc_entries_lookup L m p n Hm) as [H1 H2].
    rewrite -Htake in H1 H2. rewrite lookup_take decide_True in H1; last lia.
    rewrite lookup_take decide_True in H2; last lia. done. }
  { rewrite drop_0 sum_sizes_nil. lia. }
  { rewrite drop_0. by iFrame. }
  iDestruct (survivors_bound with "Hkept") as %Hkept; first done.
  wp_pures. wp_store.
  iApply ("HΦ" $! kept' ents' snap' bank'). iFrame. iPureIntro. split_and!; try done; lia.
Qed.

Lemma hazard_retire_spec : hazard_retire_spec' N (hazard_retire_sp H R) K Managed Retirer.
Proof.
  iIntros (E γd t Rs p γ_p n HE Hn Φ) "[Hret HM] HΦ".
  iDestruct "Hret" as (γs d) "(-> & #Hinv & %L & %ents & %snap & %bank &
      Hd & Hc & Hents & Hsnap & †t & (%HLR & %Hents & %Hsnap) & %Htake & %HF &
      Hbank & %Hbank & HL)".
  iDestruct "HM" as (γs' d' i γc) "(%Henc & #Hi & #Hci & HMsh & Htks)".
  apply (inj encode) in Henc as [= <- <-].
  iAssert (RetiredEntry γs p n) with "[HMsh Htks]" as "HE".
  { iExists i, γc, γ_p, Rs. iFrame "∗ #". iApply (big_sepL_mono with "Htks").
    iIntros (k s _) "Hb". iExists false. by iFrame. }
  have Hsum := sum_sizes_le L HF.
  have HRK : ((length L + 1) * K ≤ R * K)%nat by apply Nat.mul_le_mono_r; lia.
  rewrite (_ : bank = (n + (bank - n))%nat); last lia.
  iDestruct "Hbank" as "[Hn Hbank]".
  wp_lam. wp_pures. wp_load. wp_pures.
  replace (Z.of_nat 2 + 2 * Z.of_nat (length L))%Z
    with (Z.of_nat 2 + Z.of_nat (2 * length L))%Z by lia.
  rewrite -Loc.add_assoc.
  wp_apply (wp_store_offset with "Hents") as "Hents"; first (apply lookup_lt_is_Some_2; lia).
  wp_pures.
  replace (Z.of_nat 2 + 2 * Z.of_nat (length L) + 1)%Z
    with (Z.of_nat 2 + Z.of_nat (2 * length L + 1))%Z by lia.
  rewrite -Loc.add_assoc.
  wp_apply (wp_store_offset with "Hents") as "Hents";
    first (apply lookup_lt_is_Some_2; rewrite length_insert; lia).
  wp_pures.
  have Htake' := take_enc_insert ents L p n Htake ltac:(lia).
  have HF' : Forall (λ pn, pn.2 ≤ K) (L ++ [(p, n)]).
  { apply Forall_app. split; first done. by apply Forall_singleton. }
  have Hbank' : ((bank - n) + sum_list (snd <$> (L ++ [(p, n)])) = R * K)%nat.
  { rewrite fmap_app sum_list_with_app sum_sizes_cons sum_sizes_nil. lia. }
  destruct (decide (length L + 1 = R)%nat) as [Hfull|Hnfull].
  - rewrite (bool_decide_eq_true_2 (Z.of_nat (length L) + 1 = Z.of_nat R)%Z); last lia.
    wp_pures.
    replace (Z.of_nat (length L) + 1)%Z with (Z.of_nat (length (L ++ [(p, n)])))
      by (rewrite length_app /=; lia).
    wp_apply (hp_reclaim_spec _ _ _ (L ++ [(p, n)]) with "[$Hinv $Hd $Hc $Hents $Hsnap $Hbank HL HE]")
      as (L' ents' snap' bank') "(Hd & Hc & Hents & Hsnap & Hbank & (%HL' & %Hents' & %Hsnap') &
        %Htake'' & %HF'' & %Hbank'' & HL')";
      try done.
    { rewrite length_app /=. lia. }
    { by rewrite !length_insert. }
    { rewrite big_sepL_app /=. by iFrame. }
    iApply "HΦ". iSplitR "Hn"; last done. iExists γs, d. iFrame "Hinv".
    iSplit; first done. iExists L', ents', snap', bank'. iFrame "∗ #".
    iPureIntro. split_and!; try done; lia.
  - rewrite (bool_decide_eq_false_2 (Z.of_nat (length L) + 1 = Z.of_nat R)%Z); last lia.
    wp_pures.
    replace (Z.of_nat (length L) + 1)%Z with (Z.of_nat (length (L ++ [(p, n)])))
      by (rewrite length_app /=; lia).
    wp_store.
    iApply "HΦ". iSplitR "Hn"; last done.
    iExists γs, d. iFrame "Hinv". iModIntro. iSplit; first done.
    iExists (L ++ [(p, n)]), _, snap, (bank - n)%nat.
    iFrame "Hd Hc Hents Hsnap †t Hbank".
    iSplit.
    { iPureIntro. rewrite length_app !length_insert. change (length [(p, n)]) with 1%nat.
      split_and!; lia. }
    iSplit; first done. iSplit; first done. iSplit; first done.
    rewrite big_sepL_app /=. iFrame.
Qed.

Definition hazptr_sp_impl : hazard_pointer_sp_spec Σ N := {|
  hazard_pointer_sp_spec_code := hazptr_sp_code H R NP;

  hp_kmax := K;
  hp_domain_cost := (H + NP + NP * retirer_cost)%nat;

  IsHazardDomainSp := IsHazardDomain;
  ManagedSp := Managed;
  ShieldSp := Shield;
  spec_hazptr_sp.Retirer := Retirer;

  IsHazardDomainSp_Persistent := IsHazardDomain_Persistent;

  hazard_domain_new_sp_spec := hazard_domain_new_spec;
  hazard_domain_register_sp := hazard_domain_register;
  shield_new_sp_spec := shield_new_spec;
  shield_set_sp_spec := shield_set_spec;
  shield_validate_sp := shield_validate;
  shield_protect_tagged_sp_spec := shield_protect_tagged_spec;
  shield_unset_sp_spec := shield_unset_spec;
  shield_drop_sp_spec := shield_drop_spec;
  shield_acc_sp := shield_acc;
  managed_acc_sp := managed_acc;
  managed_exclusive_sp := managed_exclusive;
  shield_managed_agree_sp := shield_managed_agree;
  spec_hazptr_sp.hazard_retirer_new_spec := hazard_retirer_new_spec;
  spec_hazptr_sp.hazard_retirer_release_spec := hazard_retirer_release_spec;
  spec_hazptr_sp.hazard_retire_spec := hazard_retire_spec;
|}.

End hazptr_sp.












