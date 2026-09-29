From iris.base_logic.lib Require Import invariants ghost_var token.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation lib.array.
From smr.base_logic Require Import lib.mono_list.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr hazptr.spec_big_atomic hazptr.spec_writable_big_atomic.
From smr Require Import hazptr.code_cached_wf hazptr.code_writable_big_atomic.

(** * Proof of the wait-free Load/Store/CAS big atomic

    The central big atomic [Z] holds a [Value]: the value, a sequence number and
    a mark. Every change of [Z] increments its sequence number, so the history
    [zs] of [Z] is indexed by sequence numbers. The write buffer [W] points to
    the last node of the list [ns] of installed nodes; node [0] is the initial
    one. A node is done once its value has been transferred to [Z]; the entry of
    [zs] for sequence number [s] records the number [z_done] of done nodes, which
    is either the index [j] of the current node (it is pending) or [j + 1]. The
    marks of [Z] and [W] differ iff the current node is pending.

    Changes of [Z] are either transfers of the pending node, or successful CASes
    that change the value. A store installs a node only when the current node is
    done, so at most one node is installed per sequence number ([z_node] is the
    current node at the start of a sequence number).

    Linearization with helping:
    - A store registers its atomic update with a deadline [δ]: it linearizes
      (silently, just before the transfer) when node [δ] is transferred. A store
      that installs a node linearizes when that node is transferred, after the
      silent ones.
    - A CAS whose prophecy says it will fail (its CAS on [Z] will not succeed)
      registers its atomic update with the expected value: it linearizes at the
      first change of the value. *)

Record zrec := ZRec {
  z_val : list val;
  z_mark : nat;
  z_done : nat;
  z_node : nat;
}.

Global Instance zrec_inhabited : Inhabited zrec.
Proof. constructor. exact (ZRec [] 0 0 0). Qed.

Record nrec := NRec {
  n_blk : blk;
  n_name : gname;
  n_val : list val;
  n_mark : nat;
  n_seq : nat;
  n_inst : nat;
}.

Global Instance nrec_inhabited : Inhabited nrec.
Proof. constructor. exact (NRec inhabitant inhabitant [] 0 0 0). Qed.

(** The deadline of a registered store: silent until node [δ] is done, or the
    installer of node [j]. *)
Inductive sstate := SPend (δ : nat) | SInst (j : nat).

Global Instance sstate_eq_dec : EqDecision sstate.
Proof. solve_decision. Qed.

Definition sbound (st : sstate) : nat :=
  match st with SPend δ => δ | SInst j => j end.

Class writableG Σ := WritableG {
  #[local] writable_absG :: ghost_varG Σ (list val);
  #[local] writable_boolG :: ghost_varG Σ bool;
  #[local] writable_sstateG :: ghost_varG Σ sstate;
  #[local] writable_zsG :: mono_listG zrec Σ;
  #[local] writable_nsG :: mono_listG nrec Σ;
  #[local] writable_sregG :: mono_listG (gname * gname) Σ;
  #[local] writable_cregG :: mono_listG (gname * list val * nat) Σ;
  #[local] writable_tokenG :: tokenG Σ;
}.

Definition writableΣ : gFunctors := #[
  ghost_varΣ (list val);
  ghost_varΣ bool;
  ghost_varΣ sstate;
  mono_listΣ zrec;
  mono_listΣ nrec;
  mono_listΣ (gname * gname);
  mono_listΣ (gname * list val * nat);
  tokenΣ
].

Global Instance subG_writableΣ {Σ} :
  subG writableΣ Σ → writableG Σ.
Proof. solve_inG. Qed.

(** [lia] after dropping the hypotheses it cannot use: Iris proof contexts carry
    many, and [lia] is slow to preprocess them. *)
Ltac slia :=
  repeat match goal with
  | H : ?P |- _ =>
      lazymatch type of P with
      | Prop =>
          lazymatch P with
          | @eq nat _ _ => fail | @eq Z _ _ => fail | le _ _ => fail | lt _ _ => fail
          | (_ ∨ _) => fail | not _ => fail | (_ ∧ _) => fail
          | _ => clear H
          end
      end
  end; lia.

(** ** Prophecies of a CAS *)

(** A CAS prophesies whether one of its CASes on [Z] succeeds: that is the
    first resolution which is not a failed compare-exchange. *)
Fixpoint proph_succ (pvs : list (val * val)) : bool :=
  match pvs with
  | (PairV _ (LitV (LitBool b)), _) :: pvs' => if b then true else proph_succ pvs'
  | _ => false
  end.

Lemma proph_succ_failed rs pvs :
  Forall cas_failed_res rs → proph_succ (rs ++ pvs) = proph_succ pvs.
Proof. induction 1 as [|r rs (w & v & ->) _ IH]; done. Qed.

Lemma cas_succ_res_proph pvs : cas_succ_res pvs → proph_succ pvs = true.
Proof. intros (rs & w & v & pvs' & Hrs & ->). by rewrite proph_succ_failed. Qed.

(** ** Pure facts of the invariant *)

(** [zc] and [nc] are the current entries of [zs] and [ns]. *)
Record wwf (n : nat) (zs : list zrec) (ns : list nrec) (zc : zrec) (nc : nrec) : Prop := {
  wf_zlast : last zs = Some zc;
  wf_nlast : last ns = Some nc;
  wf_zs : Forall (λ zr, length zr.(z_val) = n ∧ zr.(z_mark) ≤ 1 ∧ 1 ≤ zr.(z_done) ∧ Forall val_is_unboxed zr.(z_val)) zs;
  wf_ns : Forall (λ nr, length nr.(n_val) = n ∧ nr.(n_mark) ≤ 1 ∧ nr.(n_seq) < length zs ∧ Forall val_is_unboxed nr.(n_val)) ns;
  wf_nodup : NoDup (n_name <$> ns);
  wf_marks : ∀ j a b, ns !! j = Some a → ns !! S j = Some b → b.(n_mark) = 1 - a.(n_mark);
  wf_done : zc.(z_done) = length ns - 1 ∨ zc.(z_done) = length ns;
  wf_mark : zc.(z_mark) = nc.(n_mark) ↔ zc.(z_done) = length ns;
  wf_node : length ns - 1 = zc.(z_node) ∨ length ns - 1 = S zc.(z_node);
  wf_inst : length ns - 1 = S zc.(z_node) →
    nc.(n_seq) = length zs - 1 ∧
    ∃ nr, ns !! zc.(z_node) = Some nr ∧ zc.(z_mark) = nr.(n_mark);
  wf_pend : zc.(z_done) = length ns - 1 → length zs - 1 ≤ S nc.(n_seq);
  wf_steps : ∀ s a b, zs !! s = Some a → zs !! S s = Some b →
    a.(z_done) ≤ b.(z_done) ∧ (b.(z_done) = a.(z_done) → b.(z_val) ≠ a.(z_val));
  wf_wit : ∀ j nr, ns !! S j = Some nr →
    ∃ sz zr, sz ≤ nr.(n_seq) ∧ zs !! sz = Some zr ∧ zr.(z_done) = S j ∧ zr.(z_val) ≠ nr.(n_val);
}.

Section wf.
  Implicit Types (zs : list zrec) (ns : list nrec) (zc zr : zrec) (nc nr : nrec).

  Lemma last_lookup_pred {A} (l : list A) x :
    last l = Some x → l !! (length l - 1) = Some x.
  Proof.
    rewrite last_lookup. intros H. by replace (length l - 1) with (pred (length l)) by lia.
  Qed.

  Lemma last_length_pos {A} (l : list A) x : last l = Some x → 0 < length l.
  Proof. destruct l; [done|simpl; lia]. Qed.

  Lemma wf_zcur n zs ns zc nc : wwf n zs ns zc nc → zs !! (length zs - 1) = Some zc.
  Proof. intros Hwf. apply last_lookup_pred, Hwf. Qed.

  Lemma wf_ncur n zs ns zc nc : wwf n zs ns zc nc → ns !! (length ns - 1) = Some nc.
  Proof. intros Hwf. apply last_lookup_pred, Hwf. Qed.

  (** [z_done] is monotone along the history. *)
  Lemma wf_done_mono n zs ns zc nc s s' a b :
    wwf n zs ns zc nc → s ≤ s' → zs !! s = Some a → zs !! s' = Some b →
    a.(z_done) ≤ b.(z_done).
  Proof.
    intros Hwf Hle. revert b. induction Hle as [|s' Hle IH]; intros b Ha Hb.
    { by simplify_eq. }
    destruct (zs !! s') as [c|] eqn:Hc; last first.
    { apply lookup_lt_Some in Hb. apply lookup_ge_None in Hc. lia. }
    etrans; first by apply IH.
    by eapply (wf_steps _ _ _ _ _ Hwf).
  Qed.

  Lemma wf_done_cur n zs ns zc nc s zr :
    wwf n zs ns zc nc → zs !! s = Some zr → zr.(z_done) ≤ zc.(z_done).
  Proof.
    intros Hwf Hs. eapply wf_done_mono; [done| |done|by eapply wf_zcur].
    apply lookup_lt_Some in Hs. lia.
  Qed.

  Lemma wf_nval_len n zs ns zc nc j nr :
    wwf n zs ns zc nc → ns !! j = Some nr → length nr.(n_val) = n.
  Proof. intros Hwf Hj. by destruct (Forall_lookup_1 _ _ _ _ (wf_ns _ _ _ _ _ Hwf) Hj). Qed.

  Lemma wf_zval_len n zs ns zc nc s zr :
    wwf n zs ns zc nc → zs !! s = Some zr → length zr.(z_val) = n.
  Proof. intros Hwf Hs. by destruct (Forall_lookup_1 _ _ _ _ (wf_zs _ _ _ _ _ Hwf) Hs). Qed.

  Lemma wf_nmark n zs ns zc nc j nr :
    wwf n zs ns zc nc → ns !! j = Some nr → nr.(n_mark) ≤ 1.
  Proof. intros Hwf Hj. by destruct (Forall_lookup_1 _ _ _ _ (wf_ns _ _ _ _ _ Hwf) Hj) as (?&?&?&?). Qed.

  Lemma wf_zmark n zs ns zc nc : wwf n zs ns zc nc → zc.(z_mark) ≤ 1.
  Proof.
    intros Hwf. by destruct (Forall_lookup_1 _ _ _ _ (wf_zs _ _ _ _ _ Hwf) (wf_zcur _ _ _ _ _ Hwf)) as (?&?&?&?).
  Qed.

  Lemma wf_nseq n zs ns zc nc j nr :
    wwf n zs ns zc nc → ns !! j = Some nr → nr.(n_seq) < length zs.
  Proof. intros Hwf Hj. by destruct (Forall_lookup_1 _ _ _ _ (wf_ns _ _ _ _ _ Hwf) Hj) as (?&?&?&?). Qed.

  Lemma wf_nval_unboxed n zs ns zc nc j nr :
    wwf n zs ns zc nc → ns !! j = Some nr → Forall val_is_unboxed nr.(n_val).
  Proof. intros Hwf Hj. by destruct (Forall_lookup_1 _ _ _ _ (wf_ns _ _ _ _ _ Hwf) Hj) as (?&?&?&?). Qed.

  Lemma wf_zval_unboxed n zs ns zc nc s zr :
    wwf n zs ns zc nc → zs !! s = Some zr → Forall val_is_unboxed zr.(z_val).
  Proof. intros Hwf Hs. by destruct (Forall_lookup_1 _ _ _ _ (wf_zs _ _ _ _ _ Hwf) Hs) as (?&?&?&?). Qed.

  Lemma wf_done_pos n zs ns zc nc : wwf n zs ns zc nc → 1 ≤ zc.(z_done).
  Proof.
    intros Hwf. by destruct (Forall_lookup_1 _ _ _ _ (wf_zs _ _ _ _ _ Hwf) (wf_zcur _ _ _ _ _ Hwf)) as (?&?&?&?).
  Qed.

  (** A transfer of the pending node [nc]. *)
  Lemma wf_transfer n zs ns zc nc :
    wwf n zs ns zc nc → zc.(z_done) = length ns - 1 →
    wwf n (zs ++ [ZRec nc.(n_val) nc.(n_mark) (length ns) (length ns - 1)]) ns
      (ZRec nc.(n_val) nc.(n_mark) (length ns) (length ns - 1)) nc.
  Proof.
    intros Hwf Hpend.
    pose proof (wf_zcur _ _ _ _ _ Hwf) as Hzc. pose proof (wf_ncur _ _ _ _ _ Hwf) as Hnc.
    pose proof (last_length_pos _ _ (wf_nlast _ _ _ _ _ Hwf)).
    pose proof (wf_done_pos _ _ _ _ _ Hwf).
    split; simpl.
    - by rewrite last_snoc.
    - apply Hwf.
    - apply Forall_app. split; first apply Hwf. apply Forall_singleton. simpl.
      split_and!; [by eapply wf_nval_len|by eapply wf_nmark|lia|by eapply wf_nval_unboxed].
    - eapply Forall_impl; first apply Hwf. simpl. intros nr (?&?&?&?).
      rewrite length_app /=. split_and!; [done|done|lia|done].
    - apply Hwf.
    - apply Hwf.
    - by right.
    - split; [done|done].
    - by left.
    - lia.
    - lia.
    - intros s a b Ha Hb.
      destruct (decide (S s < length zs)) as [Hlt|Hge].
      + rewrite lookup_app_l in Ha; last lia. rewrite lookup_app_l in Hb; last done.
        by eapply (wf_steps _ _ _ _ _ Hwf).
      + rewrite lookup_app_r in Hb; last lia.
        apply list_lookup_singleton_Some in Hb as [Hs <-].
        rewrite lookup_app_l in Ha; last lia.
        replace s with (length zs - 1) in Ha by lia. rewrite Hzc in Ha. simplify_eq/=.
        split; first lia. lia.
    - intros j nr Hj. destruct (wf_wit _ _ _ _ _ Hwf j nr Hj) as (sz & zr & ? & ? & ? & ?).
      exists sz, zr. split_and!; try done. rewrite lookup_app_l //. by eapply lookup_lt_Some.
  Qed.

  (** A successful CAS that changes the value to [d]. It can only happen if the
      current node was done at the start of the current sequence number. *)
  Lemma wf_cas n zs ns zc nc d :
    wwf n zs ns zc nc → length d = n → Forall val_is_unboxed d → d ≠ zc.(z_val) →
    zc.(z_done) = S zc.(z_node) →
    wwf n (zs ++ [ZRec d zc.(z_mark) zc.(z_done) (length ns - 1)]) ns
      (ZRec d zc.(z_mark) zc.(z_done) (length ns - 1)) nc.
  Proof.
    intros Hwf Hlen Hunboxed Hne Hnopend.
    pose proof (wf_zcur _ _ _ _ _ Hwf) as Hzc.
    pose proof (wf_done_pos _ _ _ _ _ Hwf). pose proof (wf_zmark _ _ _ _ _ Hwf).
    split; simpl.
    - by rewrite last_snoc.
    - apply Hwf.
    - apply Forall_app. split; first apply Hwf. apply Forall_singleton. simpl. split_and!; [lia..|done].
    - eapply Forall_impl; first apply Hwf. simpl. intros nr (?&?&?&?).
      rewrite length_app /=. split_and!; [done|done|lia|done].
    - apply Hwf.
    - apply Hwf.
    - apply Hwf.
    - apply Hwf.
    - by left.
    - lia.
    - intros Hpend. rewrite length_app /=.
      destruct (wf_node _ _ _ _ _ Hwf) as [Hj|Hj]; first lia.
      destruct (wf_inst _ _ _ _ _ Hwf Hj) as [-> _]. lia.
    - intros s a b Ha Hb.
      destruct (decide (S s < length zs)) as [Hlt|Hge].
      + rewrite lookup_app_l in Ha; last lia. rewrite lookup_app_l in Hb; last done.
        by eapply (wf_steps _ _ _ _ _ Hwf).
      + rewrite lookup_app_r in Hb; last lia.
        apply list_lookup_singleton_Some in Hb as [Hs <-].
        rewrite lookup_app_l in Ha; last lia.
        replace s with (length zs - 1) in Ha by lia. rewrite Hzc in Ha. simplify_eq/=.
        split; first lia. done.
    - intros j nr Hj. destruct (wf_wit _ _ _ _ _ Hwf j nr Hj) as (sz & zr & ? & ? & ? & ?).
      exists sz, zr. split_and!; try done. rewrite lookup_app_l //. by eapply lookup_lt_Some.
  Qed.

  (** A store installs a node while the current node is done. The installer saw
      the value [zr.(z_val)] at sequence number [sz], while the current node was
      done. *)
  Lemma wf_install n zs ns zc nc b γ vs i sz zr :
    wwf n zs ns zc nc → zc.(z_done) = length ns →
    γ ∉ n_name <$> ns → length vs = n → Forall val_is_unboxed vs →
    zs !! sz = Some zr → zr.(z_done) = length ns → zr.(z_val) ≠ vs →
    wwf n zs (ns ++ [NRec b γ vs (1 - zc.(z_mark)) (length zs - 1) i]) zc
      (NRec b γ vs (1 - zc.(z_mark)) (length zs - 1) i).
  Proof.
    intros Hwf Hdone Hfresh Hlen Hunboxed Hsz Hzrd Hzrv.
    pose proof (wf_zcur _ _ _ _ _ Hwf) as Hzc. pose proof (wf_ncur _ _ _ _ _ Hwf) as Hnc.
    pose proof (last_length_pos _ _ (wf_nlast _ _ _ _ _ Hwf)).
    pose proof (last_length_pos _ _ (wf_zlast _ _ _ _ _ Hwf)).
    pose proof (wf_zmark _ _ _ _ _ Hwf).
    assert (zc.(z_mark) = nc.(n_mark)) as Hmark by by apply (wf_mark _ _ _ _ _ Hwf).
    (* The current node was not installed in the current sequence number. *)
    assert (length ns - 1 = zc.(z_node)) as Hnode.
    { destruct (wf_node _ _ _ _ _ Hwf) as [|Hj]; first done.
      destruct (wf_inst _ _ _ _ _ Hwf Hj) as [_ (nr & Hnr & Hm)].
      assert (ns !! S zc.(z_node) = Some nc) as Hnc' by by rewrite -Hj.
      pose proof (wf_marks _ _ _ _ _ Hwf _ _ _ Hnr Hnc'). lia. }
    split; simpl.
    - apply Hwf.
    - by rewrite last_snoc.
    - apply Hwf.
    - apply Forall_app. split; first apply Hwf. apply Forall_singleton. simpl. split_and!; [lia..|done].
    - rewrite fmap_app. apply NoDup_app. split_and!; [apply Hwf| |apply NoDup_singleton].
      intros x Hx ->%list_elem_of_singleton. done.
    - intros j a c Ha Hc.
      destruct (decide (S j < length ns)) as [Hlt|Hge].
      + rewrite lookup_app_l in Ha; last lia. rewrite lookup_app_l in Hc; last done.
        by eapply (wf_marks _ _ _ _ _ Hwf).
      + rewrite lookup_app_r in Hc; last lia.
        apply list_lookup_singleton_Some in Hc as [Hj <-].
        rewrite lookup_app_l in Ha; last lia.
        replace j with (length ns - 1) in Ha by lia. rewrite Hnc in Ha. simplify_eq/=. lia.
    - rewrite length_app /=. left. lia.
    - rewrite length_app /=. lia.
    - rewrite length_app /=. right. lia.
    - rewrite length_app /=. intros _. split; first done.
      exists nc. rewrite lookup_app_l; last lia. by rewrite -Hnode.
    - rewrite length_app /=. intros _. lia.
    - apply Hwf.
    - intros j nr Hj.
      destruct (decide (S j < length ns)) as [Hlt|Hge].
      + rewrite lookup_app_l in Hj; last done. by eapply (wf_wit _ _ _ _ _ Hwf).
      + rewrite lookup_app_r in Hj; last lia.
        apply list_lookup_singleton_Some in Hj as [Hj <-]. simpl.
        exists sz, zr. split_and!; [|done|lia|done].
        apply lookup_lt_Some in Hsz. lia.
  Qed.

  (** A transfer that does not change the value of [Z] happens at most one
      sequence number after a sequence number with the same value: two
      consecutive such transfers would need a store that installs a node with
      the value it saw. *)
  Lemma wf_transfer_same n zs ns zc nc sr zr :
    wwf n zs ns zc nc → zc.(z_done) = length ns - 1 →
    nc.(n_val) = zc.(z_val) →
    zs !! sr = Some zr → zr.(z_val) = zc.(z_val) →
    length zs ≤ sr + 2 → length zs = sr + 1.
  Proof.
    intros Hwf Hpend Hsame Hsr Hsrv Hle.
    pose proof (wf_zcur _ _ _ _ _ Hwf) as Hzc. pose proof (wf_ncur _ _ _ _ _ Hwf) as Hnc.
    pose proof (wf_done_pos _ _ _ _ _ Hwf).
    pose proof (lookup_lt_Some _ _ _ Hsr).
    destruct (decide (length zs = sr + 1)) as [|Hne]; first done. exfalso.
    assert (length zs - 1 = S sr) as Hs by lia.
    rewrite Hs in Hzc.
    (* The change from [sr] to [sr + 1] kept the value, so it was a transfer. *)
    destruct (wf_steps _ _ _ _ _ Hwf _ _ _ Hsr Hzc) as [Hmono Hchg].
    assert (zr.(z_done) < zc.(z_done)) as Hlt.
    { destruct (decide (zc.(z_done) = zr.(z_done))) as [Heq|]; last lia.
      by destruct (Hchg Heq). }
    (* The installer of the current node saw a different value, while all nodes
       before it were done. *)
    destruct (length ns - 1) as [|j] eqn:Hj; first lia.
    rewrite -Hj in Hnc. replace (length ns - 1) with (S j) in Hnc by lia.
    destruct (wf_wit _ _ _ _ _ Hwf j nc Hnc) as (sz & zr' & Hsz & Hzr' & Hdone' & Hval').
    pose proof (wf_nseq _ _ _ _ _ _ _ Hwf Hnc).
    destruct (decide (sz ≤ sr)).
    - pose proof (wf_done_mono _ _ _ _ _ _ _ _ _ Hwf ltac:(done) Hzr' Hsr). lia.
    - assert (sz = S sr) as -> by lia. rewrite Hzc in Hzr'. simplify_eq; congruence.
  Qed.
  Lemma wf_init n vs b γ :
    length vs = n → Forall val_is_unboxed vs →
    wwf n [ZRec vs 0 1 0] [NRec b γ vs 0 0 0] (ZRec vs 0 1 0) (NRec b γ vs 0 0 0).
  Proof.
    intros Hlen Hub.
    split; simpl.
    - done.
    - done.
    - apply Forall_singleton; simpl. split_and!; [done|lia|lia|done].
    - apply Forall_singleton; simpl. split_and!; [done|lia|lia|done].
    - apply NoDup_singleton.
    - intros j a b' _ Hb'%lookup_lt_Some. simpl in Hb'. lia.
    - by right.
    - done.
    - by left.
    - lia.
    - lia.
    - intros s a b' _ Hb'%lookup_lt_Some. simpl in Hb'. lia.
    - intros j nr Hj%lookup_lt_Some. simpl in Hj. lia.
  Qed.
End wf.

Section writable.
  Context `{!heapGS Σ, !writableG Σ}.
  Context (writableN hazptrN : namespace) (DISJN : writableN ## hazptrN).

  Definition zN := writableN .@ "z".
  Definition invN := writableN .@ "inv".
  Definition storeN := writableN .@ "store".
  Definition casN := writableN .@ "cas".
  Definition Eo : coPset := ⊤ ∖ (↑writableN ∪ ↑ptrsN hazptrN).

  (** Namespace side conditions: [solve_ndisj] does not see through these
      definitions, and is slow on unions and in large contexts. *)
  Ltac wdisj :=
    repeat (first [apply disjoint_union_r | apply disjoint_union_l]; split); solve_ndisj.
  Ltac wndisj :=
    clear - DISJN;
    unfold Eo, zN, invN, storeN, casN, spec_big_atomic.mainN, spec_big_atomic.readN, spec_big_atomic.casN;
    repeat (apply subseteq_difference_r; [wdisj|]); set_solver.

  Local Notation zmainN := (spec_big_atomic.mainN zN).
  Local Notation zreadN := (spec_big_atomic.readN zN).
  Local Notation zcasN := (spec_big_atomic.casN zN).

  (** [Eo] is below the masks where the construction opens its invariants. *)
  Ltac wEo :=
    clear - DISJN;
    assert (↑zN ⊆ (↑writableN : coPset)) by (unfold zN; solve_ndisj);
    assert (↑invN ⊆ (↑writableN : coPset)) by (unfold invN; solve_ndisj);
    assert (↑storeN ⊆ (↑writableN : coPset)) by (unfold storeN; solve_ndisj);
    assert (↑casN ⊆ (↑writableN : coPset)) by (unfold casN; solve_ndisj);
    assert (↑zmainN ⊆ (↑zN : coPset)) by (unfold spec_big_atomic.mainN; solve_ndisj);
    assert (↑zreadN ⊆ (↑zN : coPset)) by (unfold spec_big_atomic.readN; solve_ndisj);
    assert (↑zcasN ⊆ (↑zN : coPset)) by (unfold spec_big_atomic.casN; solve_ndisj);
    unfold Eo; set_solver.

  Lemma zDISJ : zN ## hazptrN.
  Proof using DISJN. solve_ndisj. Qed.

  Variable (hazptr : hazard_pointer_spec Σ hazptrN).
  Variable (ba : big_atomic_spec Σ zN hazptrN zDISJ hazptr).

  Implicit Types (zs : list zrec) (ns : list nrec) (zc zr : zrec) (nc nr : nrec).

  Definition WBA (γ : gname) (vs : list val) : iProp Σ := ghost_var γ (DfracOwn (1/2)) vs.

  (** The contents of [Z] at sequence number [s]. *)
  Definition zcont (s : nat) zr : list val := zr.(z_val) ++ [ #s; #zr.(z_mark) ].

  Lemma Z_of_nat_add1 (n : nat) : (Z.of_nat n + 1)%Z = Z.of_nat (n + 1).
  Proof. lia. Qed.
  Lemma Z_of_nat_succ (n : nat) : (Z.of_nat n + 1)%Z = Z.of_nat (S n).
  Proof. lia. Qed.
  Lemma Z_to_nat_add2 (n : nat) : Z.to_nat (Z.of_nat n + 2) = n + 2.
  Proof. lia. Qed.

  Lemma zcont_length s zr : length (zcont s zr) = length zr.(z_val) + 2.
  Proof. rewrite /zcont length_app /=. lia. Qed.

  Lemma zcont_unboxed s zr : Forall val_is_unboxed zr.(z_val) → Forall val_is_unboxed (zcont s zr).
  Proof. intros H. apply Forall_app. split; first done. repeat constructor. Qed.

  Lemma zcont_inj s s' zr zr' :
    length zr.(z_val) = length zr'.(z_val) → zcont s zr = zcont s' zr' →
    s = s' ∧ zr.(z_val) = zr'.(z_val) ∧ zr.(z_mark) = zr'.(z_mark).
  Proof.
    rewrite /zcont. intros Hlen Heq. apply app_inj_1 in Heq as [Hv Heq]; last done.
    simplify_eq. split_and!; [lia|done|lia].
  Qed.

  Lemma zcont_lookup_seq s zr : zcont s zr !! length zr.(z_val) = Some #s.
  Proof. rewrite /zcont lookup_app_r // Nat.sub_diag //. Qed.

  Lemma zcont_lookup_mark s zr : zcont s zr !! (length zr.(z_val) + 1) = Some #zr.(z_mark).
  Proof. rewrite /zcont lookup_app_r; last lia. by replace (length zr.(z_val) + 1 - length zr.(z_val)) with 1 by lia. Qed.

  (** A node holds its value forever. *)
  Definition node_res (vs : list val) : resource Σ := λ _ lv _, ⌜lv = vs⌝%I.

  Definition wptr nr : val := #(Some (Loc.blk_to_loc nr.(n_blk)) &ₜ nr.(n_mark)).

  Definition AU_store (γ : gname) (Φ : val → iProp Σ) (des : list val) (ldes : loc) (dq : dfrac) : iProp Σ :=
    AU <{ ∃∃ vs, WBA γ vs }>
         @ ⊤ ∖ (↑writableN ∪ ↑ptrsN hazptrN), ↑mgmtN hazptrN
       <{ WBA γ des, COMM ldes ↦∗{dq} des -∗ Φ #() }>.

  Definition AU_cas (γ : gname) (Φ : val → iProp Σ) (e d : list val) (le ld : loc) (dq dq' : dfrac) : iProp Σ :=
    AU <{ ∃∃ actual, WBA γ actual }>
         @ ⊤ ∖ (↑writableN ∪ ↑ptrsN hazptrN), ↑mgmtN hazptrN
       <{ if bool_decide (actual = e) then WBA γ d else WBA γ actual,
          COMM le ↦∗{dq} e ∗ ld ↦∗{dq'} d -∗ Φ #(bool_decide (actual = e)) }>.

  (** A registered store: its atomic update, until it has been linearized; then
      its receipt, until its thread takes it (with the token [γt]). *)
  Definition store_inv γ (Φ : val → iProp Σ) (γl γt : gname) (ldes : loc) dq des : iProp Σ :=
    (£ 2 ∗ AU_store γ Φ des ldes dq ∗ ghost_var γl (DfracOwn (1/2)) false)
    ∨ (£ 1 ∗ (ldes ↦∗{dq} des -∗ Φ #()) ∗ ghost_var γl (DfracOwn (1/2)) true)
    ∨ (token γt ∗ ghost_var γl (DfracOwn (1/2)) true).

  (** A registered CAS that will fail. *)
  Definition cas_inv γ (Φ : val → iProp Σ) (γl γt : gname) (le ld : loc) dq dq' e d : iProp Σ :=
    (£ 2 ∗ AU_cas γ Φ e d le ld dq dq' ∗ ghost_var γl (DfracOwn (1/2)) false)
    ∨ (£ 1 ∗ (le ↦∗{dq} e ∗ ld ↦∗{dq'} d -∗ Φ #false) ∗ ghost_var γl (DfracOwn (1/2)) true)
    ∨ (token γt ∗ ghost_var γl (DfracOwn (1/2)) true).

  (** The store registered at index [i], with the linearization flag [γl] and
      deadline [γδ]. It is linearized once node [sbound st] is done, and not
      before ([store_ok]). It is the installer of a node iff that node says so. *)
  Definition store_ok (D : nat) (b : bool) (st : sstate) : Prop :=
    (b = false → D ≤ sbound st) ∧ (b = true → sbound st < D).

  Definition store_entry_gen γ (ok : bool → sstate → Prop) ns (i : nat) (e : gname * gname) : iProp Σ :=
    ∃ (b : bool) (st : sstate),
      ghost_var e.1 (DfracOwn (1/2)) b ∗ ghost_var e.2 (DfracOwn (1/2)) st ∗ ⌜ok b st⌝ ∗
      ⌜∀ j, st = SInst j ↔ ∃ nr, ns !! j = Some nr ∧ 1 ≤ j ∧ nr.(n_inst) = i⌝ ∗
      ∃ Φ γt ldes dq des,
        ⌜∀ j nr, st = SInst j → ns !! j = Some nr → des = nr.(n_val)⌝ ∗
        inv storeN (store_inv γ Φ e.1 γt ldes dq des).

  Definition store_entry γ (D : nat) ns (i : nat) (e : gname * gname) : iProp Σ :=
    store_entry_gen γ (store_ok D) ns i e.

  (** The CAS registered with expected value [ev] at sequence number [sr]: until
      it is linearized, the value is still [ev], and has changed at most once. *)
  Definition cas_entry γ zs (e : gname * list val * nat) : iProp Σ :=
    let '(γl, ev, sr) := e in
    ∃ (b : bool),
      ghost_var γl (DfracOwn (1/2)) b ∗
      ⌜b = false → (∃ zc, last zs = Some zc ∧ zc.(z_val) = ev) ∧
                   (∃ zr, zs !! sr = Some zr ∧ zr.(z_val) = ev) ∧ length zs ≤ sr + 2⌝ ∗
      ∃ Φ γt le ld dq dq' d, inv casN (cas_inv γ Φ γl γt le ld dq dq' ev d).

  Definition winv (γ γz γzs γns γsr γcr γd : gname) (l : loc) (n : nat) : iProp Σ :=
    ∃ zs ns zc nc (sreg : list (gname * gname)) (creg : list (gname * list val * nat)),
      mono_list_auth_own γzs 1 zs ∗ mono_list_auth_own γns 1 ns ∗
      ba.(BigAtomic) γz (zcont (length zs - 1) zc) ∗
      ghost_var γ (DfracOwn (1/2)) zc.(z_val) ∗
      (l +ₗ w_off) ↦ wptr nc ∗
      hazptr.(Managed) γd nc.(n_blk) nc.(n_name) n (node_res nc.(n_val)) ∗
      ([∗ list] nr ∈ ns, token nr.(n_name)) ∗
      mono_list_auth_own γsr 1 sreg ∗ ([∗ list] i ↦ e ∈ sreg, store_entry γ zc.(z_done) ns i e) ∗
      mono_list_auth_own γcr 1 creg ∗ ([∗ list] e ∈ creg, cas_entry γ zs e) ∗
      ⌜wwf n zs ns zc nc⌝ ∗
      ⌜∀ j nr, ns !! S j = Some nr → nr.(n_inst) < length sreg⌝.

  Definition IsWBA_at γ γz γzs γns γsr γcr γd (l d : loc) (Zv : val) (n : nat) : iProp Σ :=
    ⌜0 < n⌝ ∗
    (l +ₗ z_off) ↦□ Zv ∗ (l +ₗ domain_off) ↦□ #d ∗
    hazptr.(IsHazardDomain) γd d ∗ ba.(IsBigAtomic) γz Zv (n + 2) ∗
    inv invN (winv γ γz γzs γns γsr γcr γd l n).

  Definition IsWBA (γ : gname) (v : val) (n : nat) : iProp Σ :=
    ∃ (l d : loc) (Zv : val) (γz γzs γns γsr γcr γd : gname),
      ⌜v = #l⌝ ∗ IsWBA_at γ γz γzs γns γsr γcr γd l d Zv n.

  Global Instance WBA_Timeless γ vs : Timeless (WBA γ vs).
  Proof. apply _. Qed.

  Global Instance IsWBA_Persistent γ v n : Persistent (IsWBA γ v n).
  Proof. apply _. Qed.

  (** Persistent observations *)
  Definition zs_idx γzs (s : nat) zr : iProp Σ := mono_list_idx_own γzs s zr.
  Definition ns_idx γns (j : nat) nr : iProp Σ := mono_list_idx_own γns j nr.

  (** All nodes before [k] are done. *)
  Definition done_lb γzs (k : nat) : iProp Σ := ∃ s zr, zs_idx γzs s zr ∗ ⌜k ≤ zr.(z_done)⌝.

  (** The current node was done at the start of sequence number [s]. *)
  Definition nopend γzs (s : nat) : iProp Σ := ∃ zr, zs_idx γzs s zr ∗ ⌜zr.(z_done) = S zr.(z_node)⌝.

  Definition seq_lb γzs (s : nat) : iProp Σ := ∃ zr, zs_idx γzs s zr.

  (** ** Physical helpers *)

  Lemma wp_array_equal (l l' : loc) (dq dq' : dfrac) (vs vs' : list val) n :
    length vs = n → length vs' = n → Forall2 vals_compare_safe vs vs' →
    {{{ l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}
      array_equal #l #l' #n
    {{{ RET #(bool_decide (vs = vs')); l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}.
  Proof.
    iIntros (Hlen Hlen' Hsafe Φ) "[Hl Hl'] HΦ".
    iInduction vs as [|v vs] "IH" forall (n l l' vs' Hsafe Hlen Hlen') "HΦ".
    - wp_rec. wp_pures. simplify_list_eq.
      apply length_zero_iff_nil in Hlen' as ->.
      wp_pures. rewrite bool_decide_eq_true_2 //. iApply ("HΦ" with "[$]").
    - wp_rec. wp_pures. simplify_list_eq.
      destruct vs' as [| v' vs']; first discriminate.
      inv Hlen'. inv Hsafe.
      repeat rewrite array_cons.
      iDestruct "Hl" as "[Hl Hlrest]". iDestruct "Hl'" as "[Hl' Hlrest']".
      do 2 wp_load. wp_pures.
      destruct (decide (v = v')) as [-> | Hne].
      + rewrite (bool_decide_eq_true_2 (v' = v')); last done.
        wp_pures. rewrite Z.sub_1_r -Nat2Z.inj_pred /=; last lia.
        iApply ("IH" $! (length vs') _ _ vs' with "[//] [//] [//] [$] [$]").
        iIntros "!> [Hlrest Hlrest']".
        iSpecialize ("HΦ" with "[$]").
        destruct (decide (vs = vs')) as [-> | Hne].
        * rewrite bool_decide_eq_true_2; last done. by rewrite bool_decide_eq_true_2.
        * rewrite bool_decide_eq_false_2.
          -- by rewrite bool_decide_eq_false_2.
          -- by intros [=].
      + rewrite (bool_decide_eq_false_2 (v = v')); last done.
        iSpecialize ("HΦ" with "[$]"). wp_pures.
        destruct (decide (vs = vs')) as [-> | Hne'];
        rewrite bool_decide_eq_false_2; auto; by intros [=].
  Qed.

  Lemma wp_array_copy_to_protected_off (dst : loc) (src : blk) vdst vsrc γd s γ_src (i : nat) :
    i + length vdst = length vsrc →
      {{{ dst ↦∗ vdst ∗ hazptr.(Shield) γd s (Validated src γ_src (node_res vsrc) (length vsrc)) }}}
        array_copy_to #dst #(src +ₗ i) #(length vdst)
      {{{ RET #(); dst ↦∗ drop i vsrc ∗ hazptr.(Shield) γd s (Validated src γ_src (node_res vsrc) (length vsrc)) }}}.
  Proof.
    iIntros (Hlen Φ) "[Hdst S] HΦ".
    iLöb as "IH" forall (dst vdst i Hlen).
    wp_rec. wp_pures. destruct vdst as [|v vdst].
    { simplify_list_eq. wp_pures. iApply "HΦ".
      iModIntro. replace i with (length vsrc) in * by lia.
      rewrite drop_all. iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv Hvdst]".
    simplify_list_eq. wp_pures.
    wp_bind (! _)%E.
    wp_apply (shield_read with "S") as (? v') "(S & -> & %EQ)"; [solve_ndisj|lia|].
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
    { apply list_eq. intros [|j].
      { rewrite /= -EQ lookup_drop Nat.add_0_r //. }
      do 2 rewrite /= lookup_drop.
      f_equal. lia. }
    iFrame.
  Qed.

  Lemma wp_array_copy_to_protected (dst : loc) (src : blk) vdst vsrc γd s γ_src n :
    length vdst = n → length vsrc = n →
      {{{ dst ↦∗ vdst ∗ hazptr.(Shield) γd s (Validated src γ_src (node_res vsrc) n) }}}
        array_copy_to #dst #src #n
      {{{ RET #(); dst ↦∗ vsrc ∗ hazptr.(Shield) γd s (Validated src γ_src (node_res vsrc) n) }}}.
  Proof.
    iIntros (Hlen_dst Hlen_src Φ) "[Hdst S] HΦ".
    rewrite -(Loc.add_0 src). change 0%Z with (Z.of_nat O). simplify_eq.
    wp_apply (wp_array_copy_to_protected_off with "[Hdst S]").
    { simpl. symmetry. eassumption. }
    { rewrite Hlen_src. iFrame. }
    iIntros "[Hdst S]".
    rewrite drop_0 Hlen_src.
    iApply ("HΦ" with "[$]").
  Qed.

  (** ** Helping *)


  (** Linearize a registered store, silently or as an installer, if it is
      selected by [sel]. *)
  Lemma store_entry_step γ ns i e (ok1 ok2 : bool → sstate → Prop) (sel : sstate → Prop)
      `{∀ st, Decision (sel st)} (v : list val) (vfin : list val) E :
    ↑storeN ⊆ E → Eo ⊆ E ∖ ↑storeN →
    (∀ b st, ok1 b st → ¬ (b = false ∧ sel st) → ok2 b st) →
    (∀ st, ok1 false st → sel st → ok2 true st) →
    (∀ st j nr, sel st → st = SInst j → ns !! j = Some nr → nr.(n_val) = vfin) →
    ghost_var γ (DfracOwn (1/2)) v -∗ store_entry_gen γ ok1 ns i e ={E}=∗
    ∃ v', ghost_var γ (DfracOwn (1/2)) v' ∗ store_entry_gen γ ok2 ns i e ∗
      ⌜v' = v ∨ ∃ st, sel st ∧ (∀ j, st = SInst j → v' = vfin)⌝.
  Proof.
    iIntros (HE HEo Hkeep Hdone Hfin) "Hγ (%b & %st & Hl & Hδ & %Hok & %Hinst & %Φ & %γt & %ldes & %dq & %des & %Hdes & #Hsinv)".
    destruct (decide (b = false ∧ sel st)) as [[-> Hsel] | Hno]; last first.
    { iModIntro. iExists v. iFrame "Hγ". iSplitL; last by iLeft.
      iExists b, st. iFrame "∗ #". iPureIntro. split_and!; eauto. }
    iInv "Hsinv" as "[(>[Hc Hc'] & AU & >Hl') | [(_ & _ & >Hl') | (_ & >Hl')]]" "Hclose"; first last.
    { by iCombine "Hl Hl'" gives %[_ ?]. }
    { by iCombine "Hl Hl'" gives %[_ ?]. }
    iMod (ghost_var_update_halves true with "Hl Hl'") as "[Hl Hl']".
    iMod (lc_fupd_elim_later with "Hc AU") as "AU". rewrite /AU_store.
    iMod "AU" as (vs) "[Hγ' [_ Hcommit]]".
    iCombine "Hγ Hγ'" gives %[_ <-].
    iMod (ghost_var_update_halves des with "Hγ Hγ'") as "[Hγ Hγ']".
    iMod ("Hcommit" with "Hγ'") as "HΦ".
    iMod ("Hclose" with "[Hc' HΦ Hl']") as "_".
    { iRight. iLeft. iFrame. }
    iModIntro. iExists des. iFrame "Hγ". iSplitL.
    { iExists true, st. iFrame "∗ #". iPureIntro. split_and!; eauto. }
    iPureIntro. right. exists st. split; first done.
    intros j ->. destruct (proj1 (Hinst j) eq_refl) as (nr & Hnr & _).
    rewrite (Hdes j nr eq_refl Hnr). by eapply Hfin.
  Qed.

  (** The same for a list of registered stores. *)
  Lemma store_entries_step γ ns (f : nat → nat) (l : list (gname * gname)) (ok1 ok2 : bool → sstate → Prop)
      (sel : sstate → Prop) `{∀ st, Decision (sel st)} (v : list val) (vfin : list val) E :
    ↑storeN ⊆ E → Eo ⊆ E ∖ ↑storeN →
    (∀ b st, ok1 b st → ¬ (b = false ∧ sel st) → ok2 b st) →
    (∀ st, ok1 false st → sel st → ok2 true st) →
    (∀ st j nr, sel st → st = SInst j → ns !! j = Some nr → nr.(n_val) = vfin) →
    ghost_var γ (DfracOwn (1/2)) v -∗ ([∗ list] k ↦ e ∈ l, store_entry_gen γ ok1 ns (f k) e) ={E}=∗
    ∃ v', ghost_var γ (DfracOwn (1/2)) v' ∗ ([∗ list] k ↦ e ∈ l, store_entry_gen γ ok2 ns (f k) e) ∗
      ⌜v' = v ∨ ∃ st, sel st ∧ (∀ j, st = SInst j → v' = vfin)⌝.
  Proof.
    iIntros (HE HEo Hkeep Hdone Hfin) "Hγ Hl".
    iInduction l as [|e l] "IH" forall (f v).
    { iModIntro. iExists v. iFrame. by iLeft. }
    rewrite !big_sepL_cons.
    iDestruct "Hl" as "[He Hl]".
    iMod (store_entry_step with "Hγ He") as (v1) "(Hγ & He & %Hv1)"; [done..|].
    iMod ("IH" $! (λ k, f (S k)) v1 with "Hγ Hl") as (v2) "(Hγ & Hl & %Hv2)".
    iModIntro. iExists v2. iFrame. iPureIntro.
    destruct Hv2 as [->|]; last by right. done.
  Qed.

  (** Linearize a registered failing CAS: the value [v] is not its expected
      value. *)
  Lemma cas_entry_commit γ zs zs' e v E :
    ↑casN ⊆ E → Eo ⊆ E ∖ ↑casN →
    (∃ zc, last zs = Some zc ∧ zc.(z_val) ≠ v) →
    ghost_var γ (DfracOwn (1/2)) v -∗ cas_entry γ zs e ={E}=∗
    ghost_var γ (DfracOwn (1/2)) v ∗ cas_entry γ zs' e.
  Proof.
    iIntros (HE HEo [zc [Hlast Hne]]) "Hγ".
    destruct e as [[γl ev] sr].
    iIntros "(%b & Hl & %Hb & %Φ & %γt & %le & %ld & %dq & %dq' & %d & #Hcinv)".
    destruct b; first by iFrame "∗ #".
    destruct (Hb eq_refl) as [(zc' & Hlast' & Hev) _].
    rewrite Hlast in Hlast'. simplify_eq.
    iInv "Hcinv" as "[(>[Hc Hc'] & AU & >Hl') | [(_ & _ & >Hl') | (_ & >Hl')]]" "Hclose"; first last.
    { by iCombine "Hl Hl'" gives %[_ ?]. }
    { by iCombine "Hl Hl'" gives %[_ ?]. }
    iMod (ghost_var_update_halves true with "Hl Hl'") as "[Hl Hl']".
    iMod (lc_fupd_elim_later with "Hc AU") as "AU". rewrite /AU_cas.
    iMod "AU" as (vs) "[Hγ' [_ Hcommit]]".
    iCombine "Hγ Hγ'" gives %[_ <-].
    rewrite bool_decide_eq_false_2; last done.
    iMod ("Hcommit" with "Hγ'") as "HΦ".
    iMod ("Hclose" with "[Hc' HΦ Hl']") as "_".
    { iRight. iLeft. iFrame. }
    iModIntro. iFrame "Hγ". iExists true. iFrame "∗ #". by iPureIntro.
  Qed.

  Lemma cas_entries_commit γ zs zs' creg v E :
    ↑casN ⊆ E → Eo ⊆ E ∖ ↑casN →
    (∃ zc, last zs = Some zc ∧ zc.(z_val) ≠ v) →
    ghost_var γ (DfracOwn (1/2)) v -∗ ([∗ list] e ∈ creg, cas_entry γ zs e) ={E}=∗
    ghost_var γ (DfracOwn (1/2)) v ∗ ([∗ list] e ∈ creg, cas_entry γ zs' e).
  Proof.
    iIntros (HE HEo Hne) "Hγ Hl".
    iInduction creg as [|e creg] "IH"; first by iFrame.
    rewrite !big_sepL_cons. iDestruct "Hl" as "[He Hl]".
    iMod (cas_entry_commit _ _ zs' with "Hγ He") as "[Hγ He]"; [done..|].
    iMod ("IH" with "Hγ Hl") as "[Hγ Hl]". by iFrame.
  Qed.

  (** A registered CAS stays pending when the value does not change. *)
  Lemma cas_entries_keep γ zs zs' creg :
    (∀ ev sr, (∃ zc, last zs = Some zc ∧ zc.(z_val) = ev) →
              (∃ zr, zs !! sr = Some zr ∧ zr.(z_val) = ev) → length zs ≤ sr + 2 →
              (∃ zc, last zs' = Some zc ∧ zc.(z_val) = ev) ∧
              (∃ zr, zs' !! sr = Some zr ∧ zr.(z_val) = ev) ∧ length zs' ≤ sr + 2) →
    ([∗ list] e ∈ creg, cas_entry γ zs e) -∗ ([∗ list] e ∈ creg, cas_entry γ zs' e).
  Proof.
    iIntros (Hkeep) "Hl". iApply (big_sepL_mono with "Hl").
    iIntros (k [[γl ev] sr] _) "(%b & Hl & %Hb & H)". iExists b. iFrame. iPureIntro.
    intros Hb'. destruct (Hb Hb') as (?&?&?). by apply Hkeep.
  Qed.

  (** A transfer of node [j] linearizes the stores whose deadline is [j]: the
      silent ones first ... *)
  Definition mid_ok (j : nat) (b : bool) (st : sstate) : Prop :=
    (st = SInst j ∧ b = false) ∨ (st ≠ SInst j ∧ store_ok (S j) b st).

  Lemma stores_transfer_silent γ ns j sreg (v : list val) E :
    ↑storeN ⊆ E → Eo ⊆ E ∖ ↑storeN →
    ghost_var γ (DfracOwn (1/2)) v -∗ ([∗ list] i ↦ e ∈ sreg, store_entry γ j ns i e) ={E}=∗
    ∃ v' : list val, ghost_var γ (DfracOwn (1/2)) v' ∗ ([∗ list] i ↦ e ∈ sreg, store_entry_gen γ (mid_ok j) ns i e).
  Proof.
    iIntros (HE HEo) "Hγ Hl".
    iMod (store_entries_step γ ns (λ k, k) sreg (store_ok j) (mid_ok j) (λ st, st = SPend j) v []
      with "Hγ Hl") as (v') "(Hγ & Hl & _)"; [done|done| | |by intros ??? -> ?|by iFrame].
    - intros b st [Hf Ht] Hno. destruct (decide (st = SInst j)) as [->|Hne].
      + left. split; first done. destruct b; last done. specialize (Ht eq_refl). simpl in Ht. lia.
      + right. split; first done. split.
        * intros ->. specialize (Hf eq_refl).
          assert (sbound st ≠ j); last lia.
          destruct st; simpl in *; [|congruence]. intros ->. by apply Hno.
        * intros ->. specialize (Ht eq_refl). lia.
    - intros st Hok ->. right. split; first done. split; [done|simpl; lia].
  Qed.

  (** ... and then the installer of node [j]. *)
  Lemma stores_transfer_inst γ ns j nc sreg γl γδ (v : list val) E :
    ↑storeN ⊆ E → Eo ⊆ E ∖ ↑storeN →
    ns !! j = Some nc → 1 ≤ j → sreg !! nc.(n_inst) = Some (γl, γδ) →
    ghost_var γ (DfracOwn (1/2)) v -∗ ([∗ list] i ↦ e ∈ sreg, store_entry_gen γ (mid_ok j) ns i e) ={E}=∗
    ghost_var γ (DfracOwn (1/2)) nc.(n_val) ∗ ([∗ list] i ↦ e ∈ sreg, store_entry γ (S j) ns i e).
  Proof.
    iIntros (HE HEo Hj Hj1 Hi) "Hγ Hl".
    iDestruct (big_sepL_lookup_acc_impl with "Hl") as "[He Hl]"; first done.
    iDestruct "He" as (b st) "(Hl1 & Hδ & %Hok & %Hinst & %Φ & %γt & %ldes & %dq & %des & %Hdes & #Hsinv)".
    assert (st = SInst j) as ->.
    { apply Hinst. by exists nc. }
    destruct Hok as [[_ ->]|[? _]]; last done.
    simpl.
    iInv "Hsinv" as "[(>[Hc Hc'] & AU & >Hl') | [(_ & _ & >Hl') | (_ & >Hl')]]" "Hclose"; first last.
    { by iCombine "Hl1 Hl'" gives %[_ ?]. }
    { by iCombine "Hl1 Hl'" gives %[_ ?]. }
    iMod (ghost_var_update_halves true with "Hl1 Hl'") as "[Hl1 Hl']".
    iMod (lc_fupd_elim_later with "Hc AU") as "AU". rewrite /AU_store.
    iMod "AU" as (vs) "[Hγ' [_ Hcommit]]".
    iCombine "Hγ Hγ'" gives %[_ <-].
    rewrite (Hdes j nc eq_refl Hj).
    iMod (ghost_var_update_halves nc.(n_val) with "Hγ Hγ'") as "[Hγ Hγ']".
    iMod ("Hcommit" with "Hγ'") as "HΦ".
    iMod ("Hclose" with "[Hc' HΦ Hl']") as "_".
    { iRight. iLeft. rewrite -(Hdes j nc eq_refl Hj). iFrame. }
    iModIntro. iFrame "Hγ".
    iApply ("Hl" with "[] [Hl1 Hδ]").
    - iIntros "!>" (k e' Hk Hne) "(%b' & %st' & Hl1 & Hδ & %Hok' & %Hinst' & H)".
      iExists b', st'. iFrame. iPureIntro. split; last done.
      destruct Hok' as [[-> ->]|[_ ?]]; last done.
      exfalso. destruct (proj1 (Hinst' j) eq_refl) as (nr & Hnr & _ & Hk').
      rewrite Hj in Hnr. by simplify_eq.
    - iExists true, (SInst j). iFrame "∗ #". iPureIntro. split_and!.
      + by split; [|simpl; lia].
      + done.
      + intros j0 nr [= <-] Hnr. rewrite Hj in Hnr. by simplify_eq.
  Qed.

  (** ** Help-write *)

  Lemma help_write_spec γ γz γzs γns γsr γcr γd (l d : loc) Zv n (j : nat) nr s0 :
    nr.(n_seq) ≤ s0 →
    IsWBA_at γ γz γzs γns γsr γcr γd l d Zv n -∗ ns_idx γns j nr -∗ seq_lb γzs s0 -∗
    {{{ True }}}
      help_write hazptr ba n #l
    {{{ (r : bool), RET #r; ∃ sa, ⌜s0 ≤ sa⌝ ∗
        if r then done_lb γzs (S j) ∗ (nopend γzs sa ∨ seq_lb γzs (S sa))
        else seq_lb γzs (S sa) ∗ (if decide (nr.(n_seq) < sa) then done_lb γzs (S j) else True) }}}.
  Proof.
    iIntros (Hs0) "#(%Hn & HZv & Hd & Hdom & HZ & Hinv) #Hnr #Hseq0 !>". iIntros (Φ) "_ HΦ".
    wp_rec. wp_pures. wp_load.
    (* Read [Z] (point [a]) *)
    awp_apply (ba.(big_atomic_read_spec) with "HZ"). rewrite /atomic_acc /=.
    iInv "Hinv" as (zs ns zc nc sreg creg) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr & Hsreg & >Hcr & Hcreg & >%Hwf & >%Hinsts)" "Hcl".
    iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first wndisj.
    iModIntro. iExists _. iFrame "HZa". iSplit.
    { iIntros "HZa". iMod "Hclose" as "_".
      iMod ("Hcl" with "[-HΦ]") as "_"; last done.
      iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
    iIntros (lz) "HZa". iMod "Hclose" as "_".
    iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_a".
    iDestruct (mono_list_lb_own_get with "Hns") as "#Hns_a".
    iDestruct (mono_list_auth_idx_lookup with "Hns Hnr") as %Hj.
    iDestruct "Hseq0" as (zr0) "Hzr0".
    iDestruct (mono_list_auth_idx_lookup with "Hzs Hzr0") as %Hzr0.
    pose proof (wf_zcur _ _ _ _ _ Hwf) as Hza.
    pose proof (wf_ncur _ _ _ _ _ Hwf) as Hna.
    pose proof (wf_done _ _ _ _ _ Hwf) as Hdone_a.
    pose proof (wf_mark _ _ _ _ _ Hwf) as Hmark_a.
    iMod ("Hcl" with "[-HΦ]") as "_".
    { iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
    iModIntro. iIntros "Hlz".
    assert (s0 ≤ length zs - 1) as Hsa by (apply lookup_lt_Some in Hzr0; slia).
    assert (j ≤ length ns - 1) as Hja by (apply lookup_lt_Some in Hj; slia).
    pose proof (wf_zval_len _ _ _ _ _ _ _ Hwf Hza) as Hzalen.
    pose proof (wf_zval_unboxed _ _ _ _ _ _ _ Hwf Hza) as Hzaub.
    pose proof (last_length_pos _ _ (wf_zlast _ _ _ _ _ Hwf)) as Hzs_pos.
    pose proof (last_length_pos _ _ (wf_nlast _ _ _ _ _ Hwf)) as Hns_pos.
    (* Protect [W] (point [b]) *)
    wp_pures. wp_load.
    wp_apply (hazptr.(shield_new_spec) with "Hdom [//]") as (sh) "S"; first solve_ndisj.
    wp_pures.
    awp_apply (hazptr.(shield_protect_tagged_spec) with "Hdom S"); first solve_ndisj.
    rewrite /atomic_acc /=.
    iInv "Hinv" as (zs1 ns1 zc1 nc1 sreg1 creg1) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr & Hsreg & >Hcr & Hcreg & >%Hwf1 & >%Hinsts1)" "Hcl".
    iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first wndisj.
    iModIntro. iExists nc1.(n_blk), nc1.(n_mark), nc1.(n_name), n, (node_res nc1.(n_val)).
    rewrite /wptr. iFrame "Hw HM". iSplit.
    { iIntros "[Hw HM]". iMod "Hclose" as "_".
      iMod ("Hcl" with "[-HΦ Hlz]") as "_"; last by iFrame.
      iExists zs1, ns1, zc1, nc1, sreg1, creg1. by iFrame. }
    iIntros "(Hw & HM & S)". iMod "Hclose" as "_".
    iDestruct (mono_list_auth_lb_valid with "Hzs Hzs_a") as %[_ Hzs_pre].
    iDestruct (mono_list_auth_lb_valid with "Hns Hns_a") as %[_ Hns_pre].
    iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_b".
    iDestruct (mono_list_lb_own_get with "Hns") as "#Hns_b".
    pose proof (wf_zcur _ _ _ _ _ Hwf1) as Hzb.
    pose proof (wf_ncur _ _ _ _ _ Hwf1) as Hnb.
    pose proof (wf_done _ _ _ _ _ Hwf1) as Hdone_b.
    pose proof (wf_mark _ _ _ _ _ Hwf1) as Hmark_b.
    pose proof (wf_node _ _ _ _ _ Hwf1) as Hnode_b.
    pose proof (wf_inst _ _ _ _ _ Hwf1) as Hinst_b.
    pose proof (wf_marks _ _ _ _ _ Hwf1) as Hmarks_b.
    pose proof (wf_zmark _ _ _ _ _ Hwf1) as Hzm_b.
    iMod ("Hcl" with "[-HΦ Hlz S]") as "_".
    { iExists zs1, ns1, zc1, nc1, sreg1, creg1. rewrite /wptr. by iFrame. }
    iModIntro.
    (* The observations at [b]: [Z] is at least at [a], and [W] is [nc1]. *)
    assert (zs1 !! (length zs - 1) = Some zc) as Hza1 by by eapply prefix_lookup_Some.
    assert (ns1 !! j = Some nr) as Hj1 by by eapply prefix_lookup_Some.
    assert (length zs ≤ length zs1) as Hlen_zs1 by by apply prefix_length.
    assert (length ns ≤ length ns1) as Hlen_ns1 by by apply prefix_length.
    pose proof (wf_nval_len _ _ _ _ _ _ _ Hwf1 Hnb) as Hnblen.
    pose proof (wf_nval_unboxed _ _ _ _ _ _ _ Hwf1 Hnb) as Hnbub.
    pose proof (wf_nmark _ _ _ _ _ _ _ Hwf1 Hnb) as Hnbm.
    wp_pures.
    rewrite Z_of_nat_add1.
    wp_apply (wp_load_offset with "Hlz") as "Hlz".
    { rewrite -Hzalen. apply zcont_lookup_mark. }
    wp_pures.
    destruct (decide (zc.(z_mark) = nc1.(n_mark))) as [Hmatch|Hmismatch].
    { (* The marks match: nothing to transfer *)
      rewrite bool_decide_eq_true_2; last by rewrite Hmatch.
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "Hdom S") as "_"; first solve_ndisj.
      wp_pures. iApply "HΦ". iModIntro. iExists (length zs - 1). iSplit; first done.
      destruct (decide (length zs1 = length zs)) as [Heq|Hne].
      - (* [Z] did not change: the current node was done at the start *)
        assert (zc1 = zc) as ->.
        { rewrite Heq in Hzb. rewrite Hzb in Hza1. by simplify_eq. }
        assert (z_done zc = length ns1) as Hd1 by by apply Hmark_b.
        assert (length ns1 - 1 = z_node zc) as Hnd.
        { destruct Hnode_b as [|Hj']; first done.
          destruct (Hinst_b Hj') as [_ (nr' & Hnr' & Hm')].
          assert (ns1 !! S (z_node zc) = Some nc1) as Hnc1 by by rewrite -Hj'.
          pose proof (Hmarks_b _ _ _ Hnr' Hnc1). slia. }
        iSplit.
        + iExists (length zs - 1), zc. iSplit; first by iApply (mono_list_idx_own_get with "Hzs_a").
          iPureIntro. apply lookup_lt_Some in Hj1. slia.
        + iLeft. iExists zc. iSplit; first by iApply (mono_list_idx_own_get with "Hzs_a").
          iPureIntro. pose proof (last_length_pos _ _ (wf_nlast _ _ _ _ _ Hwf1)). slia.
      - iSplit; last first.
        { iRight. destruct (lookup_lt_is_Some_2 zs1 (S (length zs - 1))) as [zr' Hzr']; first slia.
          iExists zr'. by iApply (mono_list_idx_own_get with "Hzs_b"). }
        (* All nodes up to [j] were done at [a] or at [b]. *)
        destruct (decide (S j ≤ z_done zc)) as [Hle|Hlt].
        { iExists (length zs - 1), zc. iSplit; last done. by iApply (mono_list_idx_own_get with "Hzs_a"). }
        assert (j = length ns - 1) as ->.
        { destruct Hdone_a; slia. }
        rewrite Hj in Hna. injection Hna as <-.
        assert (z_mark zc ≠ n_mark nr) as Hm.
        { intros ?%Hmark_a. slia. }
        assert (length ns1 - 1 ≠ length ns - 1) as Hjb.
        { intros Heq'. rewrite Heq' Hj1 in Hnb. simplify_eq; congruence. }
        iExists (length zs1 - 1), zc1. iSplit; first by iApply (mono_list_idx_own_get with "Hzs_b").
        iPureIntro. clear - Hdone_b Hlen_ns1 Hjb Hns_pos. destruct Hdone_b; lia. }
    rewrite bool_decide_eq_false_2; last by intros [= ?%(inj Z.of_nat)].
    wp_pures.
    (* Build the new value of [Z] *)
    wp_alloc lz' as "Hlz'" "†Hlz'"; first slia.
    wp_pures.
    rewrite Z_to_nat_add2.
    rewrite replicate_add.
    iDestruct (array_app with "Hlz'") as "[Hlz' Hlz'r]".
    rewrite length_replicate.
    iDestruct (array_cons with "Hlz'r") as "[Hseq' Hmark']".
    rewrite array_singleton Loc.add_assoc.
    rewrite Z_of_nat_add1.
    wp_apply (wp_array_copy_to_protected _ _ _ _ _ _ _ n with "[$Hlz' $S]") as "[Hlz' S]".
    { by rewrite length_replicate. }
    { done. }
    wp_pures.
    wp_apply (wp_load_offset with "Hlz") as "Hlz".
    { rewrite -Hzalen. apply zcont_lookup_seq. }
    wp_pures. wp_store. wp_pures. wp_store.
    iAssert (lz' ↦∗ (n_val nc1 ++ [ #(S (length zs - 1)); #(n_mark nc1) ]))%I with "[Hlz' Hseq' Hmark']" as "Hlz'".
    { rewrite array_app array_cons array_singleton Hnblen Loc.add_assoc.
      rewrite Z_of_nat_succ.
      rewrite Z_of_nat_add1. iFrame. }
    wp_apply wp_new_proph as (pvs p) "Hp"; first done.
    wp_pure credit:"Hc". wp_pures. wp_load.
    set (des := n_val nc1 ++ [ #(S (length zs - 1)); #(n_mark nc1) ]).
    assert (length (zcont (length zs - 1) zc) = n + 2) as Hlen_e by rewrite zcont_length Hzalen //.
    assert (length des = n + 2) as Hlen_d by rewrite /des length_app Hnblen //.
    assert (Forall val_is_unboxed (zcont (length zs - 1) zc)) as Hub_e by by apply zcont_unboxed.
    assert (Forall val_is_unboxed des) as Hub_d.
    { apply Forall_app. split; first done. repeat constructor. }
    awp_apply (ba.(big_atomic_cas_spec) _ _ _ _ _ _ _ _ _ _ _ Hlen_e Hlen_d Hub_e Hub_d with "HZ Hlz Hlz' Hp").
    rewrite /atomic_acc /=.
    iInv "Hinv" as (zs2 ns2 zc2 nc2 sreg2 creg2) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr & Hsreg & >Hcr & Hcreg & >%Hwf2 & >%Hinsts2)" "Hcl".
    { wndisj. }
    iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first wndisj.
    iModIntro. iExists _. iFrame "HZa". iSplit.
    { iIntros "HZa". iMod "Hclose" as "_".
      iMod ("Hcl" with "[-HΦ S †Hlz' Hc]") as "_"; last by iFrame.
      iExists zs2, ns2, zc2, nc2, sreg2, creg2. by iFrame. }
    iIntros "HZa". iMod "Hclose" as "_".
    iDestruct (mono_list_auth_lb_valid with "Hzs Hzs_b") as %[_ Hzs_pre2].
    iDestruct (mono_list_auth_lb_valid with "Hns Hns_b") as %[_ Hns_pre2].
    pose proof (wf_zcur _ _ _ _ _ Hwf2) as Hzc2.
    pose proof (wf_ncur _ _ _ _ _ Hwf2) as Hnc2.
    pose proof (wf_done _ _ _ _ _ Hwf2) as Hdone_c.
    pose proof (wf_mark _ _ _ _ _ Hwf2) as Hmark_c.
    pose proof (wf_node _ _ _ _ _ Hwf2) as Hnode_c.
    pose proof (wf_inst _ _ _ _ _ Hwf2) as Hinst_c.
    pose proof (wf_zval_len _ _ _ _ _ _ _ Hwf2 Hzc2) as Hzc2len.
    assert (zs2 !! (length zs - 1) = Some zc) as Hza2 by by eapply prefix_lookup_Some.
    assert (ns2 !! j = Some nr) as Hj2 by by eapply prefix_lookup_Some.
    assert (ns2 !! (length ns1 - 1) = Some nc1) as Hnb2 by by eapply prefix_lookup_Some.
    assert (length zs1 ≤ length zs2) as Hlen_zs2 by by apply prefix_length.
    assert (length ns1 ≤ length ns2) as Hlen_ns2 by by apply prefix_length.
    destruct (decide (zcont (length zs2 - 1) zc2 = zcont (length zs - 1) zc)) as [Heq|Hne].
    - (* Success: transfer the pending node [nc1] *)
      rewrite bool_decide_eq_true_2 //. iDestruct "HZa" as "[HZa _]".
      apply zcont_inj in Heq as (Hs2 & _ & _); last by rewrite Hzc2len Hzalen.
      assert (length zs2 = length zs) as Hzs2eq by slia.
      assert (zc2 = zc) as ->.
      { rewrite Hs2 in Hzc2. rewrite Hzc2 in Hza2. by simplify_eq. }
      assert (length zs1 = length zs) as Hzs1eq by slia.
      assert (zc1 = zc) as ->.
      { rewrite Hzs1eq in Hzb. rewrite Hzb in Hza1. by simplify_eq. }
      assert (length ns2 - 1 = length ns1 - 1) as Hns2eq.
      { destruct (decide (length ns2 - 1 = length ns1 - 1)) as [|Hne2]; first done. exfalso.
        assert (length ns1 - 1 = z_node zc ∧ length ns2 - 1 = S (z_node zc)) as [Hb Hc].
        { clear - Hnode_b Hnode_c Hne2 Hlen_ns2. destruct Hnode_b, Hnode_c; lia. }
        destruct (Hinst_c Hc) as [_ (nr' & Hnr' & Hm')].
        rewrite -Hb Hnb2 in Hnr'. by simplify_eq. }
      assert (nc2 = nc1) as ->.
      { rewrite Hns2eq Hnb2 in Hnc2. by simplify_eq. }
      assert (z_done zc = length ns2 - 1) as Hpend.
      { destruct Hdone_c as [|Hd']; first done. by destruct Hmismatch; apply Hmark_c. }
      pose proof (wf_done_pos _ _ _ _ _ Hwf2) as Hdpos.
      assert (ns2 !! z_done zc = Some nc1) as Hncd by rewrite Hpend Hns2eq //.
      destruct (lookup_lt_is_Some_2 sreg2 (n_inst nc1)) as [[γl γδ] Hi].
      { apply (Hinsts2 (z_done zc - 1)). by replace (S (z_done zc - 1)) with (z_done zc) by slia. }
      iCombine "Hsreg Hcreg" as "Hregs".
      iMod (lc_fupd_elim_later with "Hc Hregs") as "[Hsreg Hcreg]".
      iMod (stores_transfer_silent with "Hγ Hsreg") as (v1) "[Hγ Hsreg]"; [wndisj|wndisj|].
      iMod (stores_transfer_inst with "Hγ Hsreg") as "[Hγ Hsreg]"; [wndisj|wndisj|done|slia|done|].
      set (zn := ZRec nc1.(n_val) nc1.(n_mark) (length ns2) (length ns2 - 1)).
      iAssert (|={⊤ ∖ (↑zmainN ∪ ↑zreadN ∪ ↑zcasN ∪ ↑ptrsN hazptrN) ∖ ↑invN}=>
        ghost_var γ (DfracOwn (1/2)) nc1.(n_val) ∗ [∗ list] e ∈ creg2, cas_entry γ (zs2 ++ [zn]) e)%I
        with "[Hγ Hcreg]" as ">[Hγ Hcreg]".
      { destruct (decide (n_val nc1 = z_val zc)) as [Hsame|Hdiff].
        - iFrame. iApply (cas_entries_keep with "Hcreg").
          intros ev sr (zc' & Hlast & Hev) (zr & Hsr & Hzr) Hle.
          rewrite (wf_zlast _ _ _ _ _ Hwf2) in Hlast. simplify_eq.
          pose proof (wf_transfer_same _ _ _ _ _ _ _ Hwf2 Hpend Hsame Hsr Hzr Hle) as Hsr1.
          split_and!.
          + exists zn. by rewrite last_snoc.
          + exists zr. split; last done. rewrite lookup_app_l //. by eapply lookup_lt_Some.
          + rewrite length_app /=. slia.
        - iApply (cas_entries_commit with "Hγ Hcreg"); [wndisj|wndisj|].
          exists zc. split; [apply Hwf2|done]. }
      iMod (mono_list_auth_own_update_app [zn] with "Hzs") as "[Hzs #Hzs_c]".
      iMod ("Hcl" with "[-HΦ S †Hlz']") as "_".
      { assert (S (length zs - 1) = length zs2) as Hsz by slia.
        rewrite /des Hsz.
        iExists (zs2 ++ [zn]), ns2, zn, nc1, sreg2, creg2. iFrame.
        rewrite length_app /= Nat.add_sub /zcont /=. iFrame.
        rewrite /zn /=. replace (S (z_done zc)) with (length ns2) by slia. iFrame.
        iPureIntro. split; last done. by apply (wf_transfer _ _ _ zc). }
      iModIntro. iIntros "(Hlz & Hlz' & Hp)".
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "Hdom S") as "_"; first solve_ndisj.
      wp_pures. iApply "HΦ". iModIntro. iExists (length zs - 1). iSplit; first done.
      assert ((zs2 ++ [zn]) !! S (length zs - 1) = Some zn) as Hzn.
      { rewrite lookup_app_r; last slia. by replace (S (length zs - 1) - length zs2) with 0 by slia. }
      iSplit.
      + iExists (S (length zs - 1)), zn. iSplit; first by iApply (mono_list_idx_own_get with "Hzs_c").
        iPureIntro. simpl. apply lookup_lt_Some in Hj2. slia.
      + iRight. iExists zn. by iApply (mono_list_idx_own_get with "Hzs_c").
    - (* Failure: [Z] changed since [a] *)
      rewrite bool_decide_eq_false_2 //.
      assert (length zs < length zs2) as Hlt2.
      { destruct (decide (length zs2 = length zs)) as [Heq|]; last slia. exfalso. apply Hne.
        rewrite Heq in Hzc2. rewrite Hzc2 in Hza2. simplify_eq. by rewrite Heq. }
      iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_c".
      iAssert (if decide (n_seq nr < length zs - 1) then done_lb γzs (S j) else True)%I as "#Hdone".
      { destruct (decide (n_seq nr < length zs - 1)) as [Hlt|]; last done.
        iExists (length zs2 - 1), zc2. iSplit; first by iApply (mono_list_idx_own_get with "Hzs_c").
        iPureIntro. destruct (decide (S j ≤ z_done zc2)) as [|Hgt]; first done. exfalso.
        assert (j ≤ length ns2 - 1) by (apply lookup_lt_Some in Hj2; slia).
        assert (length ns2 - 1 = j ∧ z_done zc2 = j) as [Hjc Hdc].
        { clear - Hdone_c Hgt H. destruct Hdone_c; lia. }
        rewrite Hjc Hj2 in Hnc2. simplify_eq.
        pose proof (wf_pend _ _ _ _ _ Hwf2 ltac:(slia)). slia. }
      iMod ("Hcl" with "[-HΦ S †Hlz']") as "_".
      { iExists zs2, ns2, zc2, nc2, sreg2, creg2. by iFrame. }
      iModIntro. iIntros "(Hlz & Hlz' & Hp)".
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "Hdom S") as "_"; first solve_ndisj.
      wp_pures. iApply "HΦ". iModIntro. iExists (length zs - 1). iSplit; first done.
      iFrame "Hdone".
      destruct (lookup_lt_is_Some_2 zs2 (S (length zs - 1))) as [zr' Hzr']; first slia.
      iExists zr'. by iApply (mono_list_idx_own_get with "Hzs_c").
  Qed.

  (** ** New and load *)

  Lemma writable_new_spec : writable_new_spec' writableN hazptrN (writable_new ba) hazptr WBA IsWBA.
  Proof using DISJN.
    iIntros (γd d n l dq vs Hn Hlen Hub Φ) "[#Hdom Hl] HΦ".
    wp_rec. wp_pures.
    wp_alloc lw as "Hlw" "†Hlw".
    wp_pures.
    wp_alloc lz as "Hlz" "†Hlz"; first lia.
    wp_pures.
    rewrite Z_to_nat_add2 replicate_add.
    iDestruct (array_app with "Hlz") as "[Hlz Hlzr]".
    wp_apply (wp_array_copy_to with "[$Hlz $Hl]") as "[Hlz Hl]"; [by rewrite length_replicate|done|].
    wp_pures.
    iAssert (lz ↦∗ zcont 0 (ZRec vs 0 1 0))%I with "[Hlz Hlzr]" as "Hlz".
    { rewrite /zcont array_app length_replicate -Hlen /=. iFrame. }
    wp_apply (ba.(big_atomic_new_spec) with "[$Hdom $Hlz]") as (γz Zv) "(#HZ & HZa & Hlz)".
    { lia. }
    { rewrite zcont_length /=. lia. }
    { by apply zcont_unboxed. }
    wp_pures.
    wp_apply (wp_store_offset _ _ lw 0 with "Hlw") as "Hlw"; first done.
    wp_pures.
    wp_apply (wp_array_clone with "Hl") as (b0) "(Hl & Hb0 & †Hb0)"; [done|lia|].
    wp_pures.
    wp_apply (wp_store_offset _ _ lw 1 with "Hlw") as "Hlw"; first done.
    wp_pures.
    wp_apply (wp_store_offset _ _ lw 2 with "Hlw") as "Hlw"; first done.
    wp_pures.
    iMod token_alloc as (γ0) "Htok0".
    iMod (hazptr.(hazard_domain_register) (node_res vs) ⊤ b0 vs γ0 with "Hdom [$Hb0 †Hb0]") as "HM"; first solve_ndisj.
    { rewrite Hlen. by iFrame. }
    rewrite Hlen.
    iMod (ghost_var_alloc vs) as (γ) "[Hγ Hγ']".
    iMod (mono_list_own_alloc [ZRec vs 0 1 0]) as (γzs) "[Hzs _]".
    iMod (mono_list_own_alloc [NRec b0 γ0 vs 0 0 0]) as (γns) "[Hns _]".
    iMod (mono_list_own_alloc ([] : list (gname * gname))) as (γsr) "[Hsr _]".
    iMod (mono_list_own_alloc ([] : list (gname * list val * nat))) as (γcr) "[Hcr _]".
    simpl.
    iDestruct (array_cons with "Hlw") as "[Hz Hlw]".
    iDestruct (array_cons with "Hlw") as "[Hw Hlw]".
    iDestruct (array_singleton with "Hlw") as "Hd".
    rewrite Loc.add_assoc /=.
    iMod (pointsto_persist with "Hz") as "#Hz".
    iMod (pointsto_persist with "Hd") as "#Hd".
    iMod (inv_alloc invN _ (winv γ γz γzs γns γsr γcr γd lw n) with "[-HΦ Hl Hγ']") as "#Hinv".
    { iNext. iExists [ZRec vs 0 1 0], [NRec b0 γ0 vs 0 0 0], (ZRec vs 0 1 0), (NRec b0 γ0 vs 0 0 0), [], [].
      rewrite /wptr /=. iFrame. iSplit; first done. iPureIntro. split.
      - by apply wf_init.
      - intros j nr Hj. apply lookup_lt_Some in Hj. simpl in Hj. lia. }
    iModIntro. iApply "HΦ". iFrame "Hl Hγ'".
    iExists lw, d, Zv, γz, γzs, γns, γsr, γcr, γd. iSplit; first done.
    rewrite /IsWBA_at !Loc.add_0. iFrame "#". by iPureIntro.
  Qed.

  Lemma writable_load_spec : writable_load_spec' writableN hazptrN (writable_load ba) WBA IsWBA.
  Proof using DISJN.
    iIntros (γ v n) "(%l & %d & %Zv & %γz & %γzs & %γns & %γsr & %γcr & %γd & -> & #(%Hn & HZv & Hd & Hdom & HZ & Hinv))".
    iIntros (Φ) "AU".
    wp_rec. wp_pures. wp_load.
    awp_apply (ba.(big_atomic_read_spec) with "HZ"). rewrite /atomic_acc /=.
    iInv "Hinv" as (zs ns zc nc sreg creg) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr & Hsreg & >Hcr & Hcreg & >%Hwf & >%Hinsts)" "Hcl".
    iMod "AU" as (vs) "[Hγ' Hlin]".
    iCombine "Hγ Hγ'" gives %[_ <-].
    iModIntro. iExists _. iFrame "HZa". iSplit.
    { iIntros "HZa". iDestruct "Hlin" as "[Habort _]".
      iMod ("Habort" with "Hγ'") as "AU".
      iMod ("Hcl" with "[-AU]") as "_"; last done.
      iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
    iIntros (lz) "HZa". iDestruct "Hlin" as "[_ Hcommit]".
    iMod ("Hcommit" $! lz with "Hγ'") as "HΦ".
    iMod ("Hcl" with "[-HΦ]") as "_".
    { iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
    iModIntro. iIntros "Hlz".
    rewrite /zcont. iDestruct (array_app with "Hlz") as "[Hlz _]".
    by iApply "HΦ".
  Qed.

  (** ** Store *)

  Lemma all_vals_compare_safe vs vs' :
    Forall val_is_unboxed vs → length vs = length vs' → Forall2 vals_compare_safe vs vs'.
  Proof.
    revert vs'. induction vs as [|v vs IH]; intros [|v' vs'] Hub Hlen; try done.
    inv Hub. constructor; [by left|]. apply IH; [done|by inv Hlen].
  Qed.

  (** Installing a node does not change the other registered stores. *)
  Lemma store_entry_extend γ D ns nr' k e :
    nr'.(n_inst) ≠ k →
    store_entry γ D ns k e -∗ store_entry γ D (ns ++ [nr']) k e.
  Proof.
    iIntros (Hk) "(%b & %st & Hl & Hδ & %Hok & %Hinst & %Φ & %γt & %ldes & %dq & %des & %Hdes & Hsinv)".
    iExists b, st. iFrame. iSplit; first done. iSplit.
    - iPureIntro. intros j. rewrite Hinst. split.
      + intros (nr & Hnr & ? & ?). exists nr. split_and!; [|done|done].
        rewrite lookup_app_l //. by eapply lookup_lt_Some.
      + intros (nr & Hnr & ? & ?). exists nr. split_and!; [|done|done].
        apply lookup_app_Some in Hnr as [?|[? Hnr']]; first done.
        apply list_lookup_singleton_Some in Hnr' as [_ <-]. congruence.
    - iPureIntro. intros j nr Hst Hnr.
      apply lookup_app_Some in Hnr as [?|[Hge Hnr']]; first by eapply Hdes.
      exfalso. destruct (proj1 (Hinst j) Hst) as (nr0 & Hnr0 & _).
      apply lookup_lt_Some in Hnr0. lia.
  Qed.

  (** The receipt of a registered store, once it has been linearized. *)
  Lemma store_take_receipt γ Φ γl γt ldes dq des E :
    ↑storeN ⊆ E →
    inv storeN (store_inv γ Φ γl γt ldes dq des) -∗ token γt -∗ ghost_var γl (DfracOwn (1/2)) true ={E}=∗
    ghost_var γl (DfracOwn (1/2)) true ∗ (ldes ↦∗{dq} des -∗ Φ #()).
  Proof.
    iIntros (?) "#Hsinv Ht Hl".
    iInv "Hsinv" as "[(_ & _ & >Hl') | [(>Hc & HΦ & >Hl') | (>Ht' & _)]]" "Hclose".
    - by iCombine "Hl Hl'" gives %[_ ?].
    - iMod (lc_fupd_elim_later with "Hc HΦ") as "HΦ".
      iMod ("Hclose" with "[Ht Hl']") as "_"; first by iRight; iRight; iFrame.
      by iFrame.
    - by iCombine "Ht Ht'" gives %[].
  Qed.

  (** The end of a store: help the pending write (the target node [j]) until it
      is done, and take the receipt. *)
  Lemma store_tail_spec γ γz γzs γns γsr γcr γd (l d : loc) Zv n (sh : loc) s_st γl γδ γt i Φ' ldes dq des j nr s0 :
    n_seq nr ≤ s0 →
    IsWBA_at γ γz γzs γns γsr γcr γd l d Zv n -∗ ns_idx γns j nr -∗ seq_lb γzs s0 -∗
    inv storeN (store_inv γ Φ' γl γt ldes dq des) -∗ mono_list_idx_own γsr i (γl, γδ) -∗
    {{{ hazptr.(Shield) γd sh s_st ∗ £ 1 ∗
        ((ldes ↦∗{dq} des -∗ Φ' #()) ∨
         (∃ st, ghost_var γδ (DfracOwn (1/2)) st ∗ ⌜sbound st ≤ j⌝ ∗ token γt)) }}}
      (if: ~ help_write hazptr ba n #l then help_write hazptr ba n #l;; #() else #());; hazptr.(shield_drop) #sh
    {{{ RET #(); ldes ↦∗{dq} des -∗ Φ' #() }}}.
  Proof using DISJN.
    iIntros (Hs0) "#HI #Hnr #Hs0 #Hsinv #Hidx !>". iIntros (Ψ) "(S & Hc & Hst) HΨ".
    iPoseProof "HI" as "(%Hn & HZv & Hd & Hdom & HZ & Hinv)".
    (* Help twice: afterwards, node [j] is done *)
    wp_apply (help_write_spec with "HI Hnr Hs0 [//]") as (r1) "(%sa1 & %Hsa1 & H1)"; first done.
    wp_pures. wp_bind (if: _ then _ else _)%E.
    iApply (wp_wand _ _ _ (λ _, done_lb γzs (S j))%I with "[H1]").
    { destruct r1; wp_pures.
      - iDestruct "H1" as "[$ _]". done.
      - iDestruct "H1" as "[Hs1 _]".
        wp_apply (help_write_spec _ _ _ _ _ _ _ _ _ _ _ _ _ (S sa1) with "HI Hnr Hs1 [//]") as (r2) "(%sa2 & %Hsa2 & H2)"; first slia.
        wp_pures. destruct r2.
        + by iDestruct "H2" as "[$ _]".
        + iDestruct "H2" as "[_ H2]". rewrite decide_True //; slia. }
    iIntros (?) "#Hdone". wp_pures.
    (* Take the receipt *)
    iAssert (|={⊤}=> ldes ↦∗{dq} des -∗ Φ' #())%I with "[Hst Hc]" as ">HR".
    { iDestruct "Hst" as "[$ | (%st & Hδ' & %Hst & Ht)]"; first done.
      iInv "Hinv" as (zs ns zc nc sreg creg) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr & Hsreg & >Hcr & Hcreg & >%Hwf & >%Hinsts)" "Hcl".
      iMod (lc_fupd_elim_later with "Hc Hsreg") as "Hsreg".
      iDestruct (mono_list_auth_idx_lookup with "Hsr Hidx") as %Hi.
      iDestruct "Hdone" as (sd zd) "[Hzd %Hzd]".
      iDestruct (mono_list_auth_idx_lookup with "Hzs Hzd") as %Hzd'.
      pose proof (wf_done_cur _ _ _ _ _ _ _ Hwf Hzd').
      iDestruct (big_sepL_lookup_acc with "Hsreg") as "[He Hsreg]"; first done.
      iDestruct "He" as (b st') "(Hl & Hδ & %Hok & Hrest)". simpl.
      iCombine "Hδ Hδ'" gives %[_ <-].
      destruct b; last first.
      { exfalso. destruct Hok as [Hok _]. specialize (Hok eq_refl). slia. }
      iMod (store_take_receipt with "Hsinv Ht Hl") as "[Hl HR]"; first wndisj.
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr Hsreg Hcr Hcreg Hl Hδ Hrest]") as "_".
      { iExists zs, ns, zc, nc, sreg, creg. iFrame. iSplitL; last done.
        iApply "Hsreg". iExists true, st'. by iFrame. }
      done. }
    wp_apply (hazptr.(shield_drop_spec) with "Hdom S") as "_"; first solve_ndisj.
    by iApply "HΨ".
  Qed.

  Lemma writable_store_spec : writable_store_spec' writableN hazptrN (writable_store hazptr ba) WBA IsWBA.
  Proof using DISJN.
    iIntros (γ v n ldes dq des Hlen Hub) "(%l & %d & %Zv & %γz & %γzs & %γns & %γsr & %γcr & %γd & -> & #HI) Hldes %Φ AU".
    iPoseProof "HI" as "(%Hn & HZv & Hd & Hdom & HZ & Hinv)".
    wp_rec. wp_pure credit:"Hc1". wp_pure credit:"Hc2". wp_load.
    wp_apply (hazptr.(shield_new_spec) with "Hdom [//]") as (sh) "S"; first solve_ndisj.
    wp_pure credit:"Hc3". wp_pures.
    (* Protect [W] and register the store (point [t_w]) *)
    awp_apply (hazptr.(shield_protect_tagged_spec) with "Hdom S"); first solve_ndisj.
    rewrite /atomic_acc /=.
    iInv "Hinv" as (zs ns zc nc sreg creg) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr & Hsreg & >Hcr & Hcreg & >%Hwf & >%Hinsts)" "Hcl".
    iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first wndisj.
    iModIntro. iExists nc.(n_blk), nc.(n_mark), nc.(n_name), n, (node_res nc.(n_val)).
    rewrite /wptr. iFrame "Hw HM". iSplit.
    { iIntros "[Hw HM]". iMod "Hclose" as "_".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr Hsreg Hcr Hcreg]") as "_".
      { iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
      by iFrame. }
    iIntros "(Hw & HM & S)". iMod "Hclose" as "_".
    pose proof (wf_ncur _ _ _ _ _ Hwf) as Hnw.
    pose proof (wf_done _ _ _ _ _ Hwf) as Hdone_w.
    pose proof (last_length_pos _ _ (wf_nlast _ _ _ _ _ Hwf)) as Hns_pos.
    pose proof (last_length_pos _ _ (wf_zlast _ _ _ _ _ Hwf)) as Hzs_pos.
    iMod (ghost_var_alloc false) as (γl) "[Hl Hl']".
    iMod (ghost_var_alloc (SPend (length ns))) as (γδ) "[Hδ Hδ']".
    iMod token_alloc as (γt) "Ht".
    iMod (inv_alloc storeN _ (store_inv γ Φ γl γt ldes dq des) with "[AU Hc1 Hc2 Hl']") as "#Hsinv".
    { iNext. iLeft. iFrame. iCombine "Hc1 Hc2" as "$". }
    iMod (mono_list_auth_own_update_app [(γl, γδ)] with "Hsr") as "[Hsr #Hsr_lb]".
    iAssert (mono_list_idx_own γsr (length sreg) (γl, γδ)) as "#Hidx".
    { iApply (mono_list_idx_own_get with "Hsr_lb"). by rewrite lookup_app_r // Nat.sub_diag. }
    iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_w".
    iDestruct (mono_list_lb_own_get with "Hns") as "#Hns_w".
    iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr Hsreg Hcr Hcreg Hl Hδ]") as "_".
    { iExists zs, ns, zc, nc, (sreg ++ [(γl, γδ)]), creg. iFrame. iNext.
      iSplitL; [iSplit; [|done]|].
      - iSplit; first (iPureIntro; split; [simpl; slia|done]).
        iSplit.
        + iPureIntro. intros j. split; first done.
          intros (nr & Hnr & Hj1 & Hi). destruct j as [|j]; first slia.
          specialize (Hinsts j nr Hnr). slia.
        + iExists Φ, γt, ldes, dq, des. by iFrame "Hsinv".
      - iPureIntro. split; first done. intros j nr Hnr. rewrite length_app /=.
        specialize (Hinsts j nr Hnr). slia. }
    iModIntro.
    clear Hinsts.
    set (jw := length ns - 1). set (nw := nc).
    (* Read [Z] (point [t_z]) *)
    wp_pure credit:"Hc4". wp_pure credit:"Hc5". wp_load.
    awp_apply (ba.(big_atomic_read_spec) with "HZ"). rewrite /atomic_acc /=.
    iInv "Hinv" as (zs1 ns1 zc1 nc1 sreg1 creg1) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr & Hsreg & >Hcr & Hcreg & >%Hwf1 & >%Hinsts1)" "Hcl".
    iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first wndisj.
    iModIntro. iExists _. iFrame "HZa". iSplit.
    { iIntros "HZa". iMod "Hclose" as "_".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr Hsreg Hcr Hcreg]") as "_".
      { iExists zs1, ns1, zc1, nc1, sreg1, creg1. by iFrame. }
      by iFrame. }
    iIntros (lz) "HZa". iMod "Hclose" as "_".
    iDestruct (mono_list_auth_lb_valid with "Hzs Hzs_w") as %[_ Hzs_pre].
    iDestruct (mono_list_auth_lb_valid with "Hns Hns_w") as %[_ Hns_pre].
    iDestruct (mono_list_auth_idx_lookup with "Hsr Hidx") as %Hi1.
    iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_z".
    iDestruct (mono_list_lb_own_get with "Hns") as "#Hns_z".
    pose proof (wf_zcur _ _ _ _ _ Hwf1) as Hzc1.
    pose proof (wf_ncur _ _ _ _ _ Hwf1) as Hnc1.
    pose proof (wf_done _ _ _ _ _ Hwf1) as Hdone1.
    pose proof (wf_mark _ _ _ _ _ Hwf1) as Hmark1.
    pose proof (wf_nseq _ _ _ _ _ _ _ Hwf1 Hnc1) as Hnseq1.
    pose proof (wf_zval_len _ _ _ _ _ _ _ Hwf1 Hzc1) as Hzc1len.
    pose proof (wf_zval_unboxed _ _ _ _ _ _ _ Hwf1 Hzc1) as Hzc1ub.
    pose proof (wf_done_pos _ _ _ _ _ Hwf1) as Hdpos1.
    assert (ns1 !! jw = Some nw) as Hnw1 by by eapply prefix_lookup_Some.
    assert (length ns ≤ length ns1) as Hlen_ns1 by by apply prefix_length.
    iMod (lc_fupd_elim_later with "Hc4 Hsreg") as "Hsreg".
    iDestruct (big_sepL_lookup_acc with "Hsreg") as "[He Hsreg]"; first done.
    iDestruct "He" as (b st) "(Hl & Hδ & %Hok & %Hinst & Hes)". simpl.
    iCombine "Hδ Hδ'" gives %[_ ->].
    iAssert (ns_idx γns (length ns1 - 1) nc1) as "#Hnc1".
    { by iApply (mono_list_idx_own_get with "Hns_z"). }
    iAssert (seq_lb γzs (length zs1 - 1)) as "#Hsz".
    { iExists zc1. by iApply (mono_list_idx_own_get with "Hzs_z"). }
    destruct (decide (z_val zc1 = des)) as [Hsame|Hdiff].
    { (* The value is already [des]: linearize here *)
      subst des.
      iAssert (|={⊤ ∖ (↑zreadN ∪ ↑ptrsN hazptrN) ∖ ↑invN}=>
        (ldes ↦∗{dq} z_val zc1 -∗ Φ #()) ∗ store_entry γ (z_done zc1) ns1 (length sreg) (γl, γδ) ∗
        ghost_var γ (DfracOwn (1/2)) (z_val zc1))%I
        with "[Hl Hδ Hδ' Hes Ht Hγ]" as ">(HR & He & Hγ)".
      { destruct b.
        - iMod (store_take_receipt with "Hsinv Ht Hl") as "[Hl HR]"; first wndisj.
          iModIntro. iFrame "HR Hγ". iExists true, (SPend (length ns)). iFrame "Hl Hδ Hes".
          iSplit; by iPureIntro.
        - iInv "Hsinv" as "[(>[Hc Hc'] & AU & >Hl') | [(_ & _ & >Hl') | (>Ht' & _)]]" "Hcls"; first last.
          { by iCombine "Ht Ht'" gives %[]. }
          { by iCombine "Hl Hl'" gives %[_ ?]. }
          iMod (lc_fupd_elim_later with "Hc AU") as "AU". rewrite /AU_store.
          iMod "AU" as (vs) "[Hγ' [_ Hcommit]]"; first wEo.
          iCombine "Hγ Hγ'" gives %[_ <-].
          iMod ("Hcommit" with "Hγ'") as "HR".
          iMod (ghost_var_update_halves true with "Hl Hl'") as "[Hl Hl']".
          iMod (ghost_var_update_halves (SPend 0) with "Hδ Hδ'") as "[Hδ Hδ']".
          iMod ("Hcls" with "[Ht Hl']") as "_".
          { iRight. iRight. iFrame. }
          iModIntro. iFrame "HR Hγ". iExists true, (SPend 0). iFrame. iSplit.
          { iPureIntro. split; [done|simpl; slia]. }
          iSplit.
          { iPureIntro. intros j. split; first done. intros Hr. by apply Hinst in Hr. }
          iExists Φ, γt, ldes, dq, (z_val zc1). by iFrame "Hsinv". }
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr Hsreg Hcr Hcreg He]") as "_".
      { iExists zs1, ns1, zc1, nc1, sreg1, creg1. iFrame. iSplitL; last done. by iApply "Hsreg". }
      iModIntro. iIntros "Hlz". wp_pures.
      rewrite /zcont. iDestruct (array_app with "Hlz") as "[Hlz _]".
      wp_apply (wp_array_equal with "[$Hlz $Hldes]") as "[_ Hldes]"; [done|done|by apply all_vals_compare_safe|].
      rewrite bool_decide_eq_true_2 //. wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "Hdom S") as "_"; first solve_ndisj.
      by iApply "HR". }
    destruct (decide (z_mark zc1 = n_mark nw)) as [Hmatch|Hmismatch]; last first.
    { (* The marks differ: a write is pending, which will linearize the store *)
      iAssert (|={⊤ ∖ (↑zreadN ∪ ↑ptrsN hazptrN) ∖ ↑invN}=>
        store_entry γ (z_done zc1) ns1 (length sreg) (γl, γδ) ∗
        ((ldes ↦∗{dq} des -∗ Φ #()) ∨
         (∃ st, ghost_var γδ (DfracOwn (1/2)) st ∗ ⌜sbound st ≤ length ns1 - 1⌝ ∗ token γt)))%I
        with "[Hl Hδ Hδ' Hes Ht]" as ">[He Hst]".
      { destruct b.
        - iMod (store_take_receipt with "Hsinv Ht Hl") as "[Hl HR]"; first wndisj.
          iModIntro. iSplitR "HR"; last by iLeft.
          iExists true, (SPend (length ns)). iFrame "Hl Hδ Hes". iSplit; by iPureIntro.
        - assert (z_done zc1 = length ns1 - 1) as Hpend.
          { destruct Hok as [Hok _]. specialize (Hok eq_refl). simpl in Hok.
            destruct (decide (length ns1 = length ns)) as [Heq|Hne].
            - unfold jw in Hnw1. rewrite -Heq Hnc1 in Hnw1. injection Hnw1 as ->.
              destruct Hdone1 as [|Hd]; first done. by destruct Hmismatch; apply Hmark1.
            - clear - Hok Hdone1 Hne Hlen_ns1. destruct Hdone1; lia. }
          iMod (ghost_var_update_halves (SPend (length ns1 - 1)) with "Hδ Hδ'") as "[Hδ Hδ']".
          iModIntro. iSplitR "Hδ' Ht"; last (iRight; iFrame; iPureIntro; simpl; lia).
          iExists false, (SPend (length ns1 - 1)). iFrame "Hl Hδ". iSplit.
          { iPureIntro. split; [simpl; slia|done]. }
          iSplit.
          { iPureIntro. intros j. split; first done. intros Hr. by apply Hinst in Hr. }
          iExists Φ, γt, ldes, dq, des. by iFrame "Hsinv". }
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr Hsreg Hcr Hcreg He]") as "_".
      { iExists zs1, ns1, zc1, nc1, sreg1, creg1. iFrame. iSplitL; last done. by iApply "Hsreg". }
      iModIntro. iIntros "Hlz". wp_pures.
      rewrite /zcont. iDestruct (array_app with "Hlz") as "[Hlz Hlzr]".
      wp_apply (wp_array_equal with "[$Hlz $Hldes]") as "[Hlz Hldes]";
        [done|done|apply all_vals_compare_safe; [done|by rewrite Hzc1len Hlen]|].
      rewrite bool_decide_eq_false_2 //. wp_pures.
      iCombine "Hlz Hlzr" as "Hlz". rewrite -array_app.
      rewrite Z_of_nat_add1.
      wp_apply (wp_load_offset with "Hlz") as "Hlz".
      { rewrite -Hzc1len. apply zcont_lookup_mark. }
      wp_pures. rewrite bool_decide_eq_false_2; last by intros [= ?%(inj Z.of_nat)].
      wp_pures.
      wp_apply (store_tail_spec with "HI Hnc1 Hsz Hsinv Hidx [$S $Hc3 $Hst]") as "HR"; first slia.
      by iApply "HR". }
    (* The marks match: try to install a node *)
    assert (length ns1 = length ns → z_done zc1 = length ns) as Hsame1.
    { intros Heq. unfold jw in Hnw1. rewrite -Heq Hnc1 in Hnw1. injection Hnw1 as ->.
      rewrite -Heq. by apply Hmark1. }
    iAssert (|={⊤ ∖ (↑zreadN ∪ ↑ptrsN hazptrN) ∖ ↑invN}=>
      store_entry γ (z_done zc1) ns1 (length sreg) (γl, γδ) ∗
      (((ldes ↦∗{dq} des -∗ Φ #()) ∗ ⌜length ns < z_done zc1⌝) ∨
       (ghost_var γδ (DfracOwn (1/2)) (SPend (length ns)) ∗ token γt)))%I
      with "[Hl Hδ Hδ' Hes Ht]" as ">[He Hst]".
    { destruct b.
      - iMod (store_take_receipt with "Hsinv Ht Hl") as "[Hl HR]"; first wndisj.
        iModIntro. iSplitR "HR".
        + iExists true, (SPend (length ns)). iFrame "Hl Hδ Hes". iSplit; by iPureIntro.
        + iLeft. iFrame. iPureIntro. destruct Hok as [_ Hok]. by apply Hok.
      - iModIntro. iSplitR "Hδ' Ht"; last (iRight; iFrame).
        iExists false, (SPend (length ns)). iFrame "Hl Hδ Hes". iSplit; by iPureIntro. }
    iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr Hsreg Hcr Hcreg He]") as "_".
    { iExists zs1, ns1, zc1, nc1, sreg1, creg1. iFrame. iSplitL; last done. by iApply "Hsreg". }
    iModIntro. iIntros "Hlz". wp_pures.
    rewrite /zcont. iDestruct (array_app with "Hlz") as "[Hlz Hlzr]".
    wp_apply (wp_array_equal with "[$Hlz $Hldes]") as "[Hlz Hldes]";
      [done|done|apply all_vals_compare_safe; [done|by rewrite Hzc1len Hlen]|].
    rewrite bool_decide_eq_false_2 //. wp_pures.
    iCombine "Hlz Hlzr" as "Hlz". rewrite -array_app.
    rewrite Z_of_nat_add1.
    wp_apply (wp_load_offset with "Hlz") as "Hlz".
    { rewrite -Hzc1len. apply zcont_lookup_mark. }
    wp_pures. rewrite bool_decide_eq_true_2; last by rewrite Hmatch.
    wp_pures.
    wp_apply (wp_load_offset with "Hlz") as "Hlz".
    { rewrite -Hzc1len. apply zcont_lookup_mark. }
    wp_pures.
    wp_apply (wp_array_clone with "Hldes") as (nb) "(Hldes & Hnb & †Hnb)"; [done|slia|].
    wp_pures.
    (* The CAS on [W] *)
    wp_bind (CmpXchg _ _ _)%E.
    iInv "Hinv" as (zs2 ns2 zc2 nc2 sreg2 creg2) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr & Hsreg & >Hcr & Hcreg & >%Hwf2 & >%Hinsts2)" "Hcl".
    iDestruct (mono_list_auth_lb_valid with "Hzs Hzs_z") as %[_ Hzs_pre2].
    iDestruct (mono_list_auth_lb_valid with "Hns Hns_z") as %[_ Hns_pre2].
    iDestruct (mono_list_auth_idx_lookup with "Hsr Hidx") as %Hi2.
    pose proof (wf_zcur _ _ _ _ _ Hwf2) as Hzc2.
    pose proof (wf_ncur _ _ _ _ _ Hwf2) as Hnc2.
    pose proof (wf_done _ _ _ _ _ Hwf2) as Hdone2.
    pose proof (wf_mark _ _ _ _ _ Hwf2) as Hmark2.
    pose proof (wf_nodup _ _ _ _ _ Hwf2) as Hnodup2.
    pose proof (wf_zmark _ _ _ _ _ Hwf2) as Hzm2.
    assert (ns2 !! jw = Some nw) as Hnw2 by by eapply prefix_lookup_Some.
    assert (zs2 !! (length zs1 - 1) = Some zc1) as Hzc12 by by eapply prefix_lookup_Some.
    pose proof (wf_done_cur _ _ _ _ _ _ _ Hwf2 Hzc12) as Hdmono.
    assert (length ns1 ≤ length ns2) as Hlen_ns2 by by apply prefix_length.
    iCombine "HM Hsreg" as "HMs".
    iMod (lc_fupd_elim_later with "Hc5 HMs") as "[HM Hsreg]".
    iDestruct (big_sepL_lookup_acc_impl with "Hsreg") as "[He Hsreg]"; first done.
    iDestruct "He" as (b2 st2) "(Hl & Hδ & %Hok2 & %Hinst2 & Hes)". simpl.
    rewrite /wptr.
    destruct (decide (nc2.(n_blk) = nw.(n_blk) ∧ nc2.(n_mark) = nw.(n_mark))) as [[Hb Hm]|Hne].
    - (* Success: [W] still points to [nw], which is done *)
      rewrite Hb Hm.
      wp_cmpxchg_suc.
      iDestruct (hazptr.(shield_managed_agree) with "S HM") as %Hname.
      assert (length ns2 - 1 = jw) as Hjc.
      { eapply NoDup_lookup; [done| |].
        - by rewrite list_lookup_fmap Hnc2.
        - by rewrite list_lookup_fmap Hnw2 /= Hname. }
      assert (nc2 = nw) as ->.
      { rewrite Hjc Hnw2 in Hnc2. by injection Hnc2. }
      assert (length ns1 = length ns ∧ length ns2 = length ns) as [Hl1 Hl2].
      { unfold jw in Hjc. clear - Hjc Hlen_ns1 Hlen_ns2 Hns_pos. lia. }
      pose proof (Hsame1 Hl1) as Hd1.
      assert (z_done zc2 = length ns2) as Hd2.
      { clear - Hd1 Hdmono Hdone2 Hl2. destruct Hdone2; lia. }
      iDestruct "Hst" as "[[_ %Hlt] | [Hδ' Ht]]"; first (exfalso; clear - Hlt Hd1; lia).
      iCombine "Hδ Hδ'" gives %[_ ->].
      destruct b2; first (exfalso; destruct Hok2 as [_ Hok2]; specialize (Hok2 eq_refl); simpl in Hok2; clear - Hok2 Hd2 Hl2; lia).
      (* Install the new node *)
      iMod token_alloc as (γn) "Htn".
      iAssert ⌜γn ∉ n_name <$> ns2⌝%I as %Hfresh.
      { iIntros (Hin). apply list_elem_of_fmap in Hin as (nr0 & -> & Hnr0).
        iDestruct (big_sepL_elem_of with "Htoks") as "Ht'"; first done.
        by iCombine "Htn Ht'" gives %[]. }
      iMod (hazptr.(hazard_domain_register) (node_res des) (⊤ ∖ ↑invN) nb des γn with "Hdom [$Hnb †Hnb]") as "HMn"; first wndisj.
      { rewrite Hlen. by iFrame. }
      rewrite Hlen.
      set (nr' := NRec nb γn des (1 - z_mark zc2) (length zs2 - 1) (length sreg)).
      assert (wwf n zs2 (ns2 ++ [nr']) zc2 nr') as Hwf2'.
      { apply (wf_install n zs2 ns2 zc2 nw nb γn des (length sreg) (length zs1 - 1) zc1); try done.
        all: by rewrite ?Hd1 ?Hl2. }
      iMod (mono_list_auth_own_update_app [nr'] with "Hns") as "[Hns #Hns_c]".
      iMod (ghost_var_update_halves (SInst (length ns2)) with "Hδ Hδ'") as "[Hδ Hδ']".
      iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_c".
      assert (z_mark zc2 = z_mark zc1) as Hzm.
      { rewrite Hmatch. by apply Hmark2. }
      assert (length sreg < length sreg2) as Hlt_sreg by by eapply lookup_lt_Some.
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HMn Htoks Htn Hsr Hsreg Hcr Hcreg Hl Hδ]") as "_".
      { iExists zs2, (ns2 ++ [nr']), zc2, nr', sreg2, creg2. iFrame. iNext.
        iSplitL "Hw".
        { rewrite /wptr /nr' /=. replace (1 - Z.of_nat (z_mark zc1))%Z with (Z.of_nat (1 - z_mark zc2)); first done.
          rewrite Hzm. pose proof (wf_zmark _ _ _ _ _ Hwf1). clear - H. lia. }
        iSplitR; first done.
        iSplitL.
        - iApply ("Hsreg" with "[] [Hl Hδ]").
          + iIntros "!>" (k e' Hk Hne') "He". iApply (store_entry_extend with "He"). done.
          + iExists false, (SInst (length ns2)). iFrame. iSplit.
            { iPureIntro. split; [simpl; slia|done]. }
            iSplit.
            { iPureIntro. intros j. split.
              - intros [= <-]. exists nr'. split_and!; [|slia|done].
                rewrite lookup_app_r // Nat.sub_diag //.
              - intros (nr0 & Hnr0 & Hj1 & Hi0).
                apply lookup_app_Some in Hnr0 as [Hnr0|[Hge Hnr0]].
                + exfalso. pose proof (proj2 (Hinst2 j) (ex_intro _ nr0 (conj Hnr0 (conj Hj1 Hi0)))). congruence.
                + apply list_lookup_singleton_Some in Hnr0 as [? _]. f_equal. slia. }
            iExists Φ, γt, ldes, dq, des. iFrame "Hsinv". iPureIntro.
            intros j nr0 [= <-] Hnr0. rewrite lookup_app_r // Nat.sub_diag in Hnr0. by injection Hnr0 as <-.
        - iPureIntro. split; first done. intros j nr0 Hnr0.
          apply lookup_app_Some in Hnr0 as [Hnr0|[Hge Hnr0]]; first by eapply Hinsts2.
          apply list_lookup_singleton_Some in Hnr0 as [_ <-]. done. }
      iModIntro. wp_pures. wp_load.
      wp_apply (hazptr.(hazard_domain_retire_spec) with "Hdom HM") as "_"; first solve_ndisj.
      wp_pures.
      iAssert (ns_idx γns (length ns2) nr') as "#Hnr'".
      { iApply (mono_list_idx_own_get with "Hns_c"). by rewrite lookup_app_r // Nat.sub_diag. }
      iAssert (seq_lb γzs (length zs2 - 1)) as "#Hsz2".
      { iExists zc2. by iApply (mono_list_idx_own_get with "Hzs_c"). }
      wp_apply (store_tail_spec with "HI Hnr' Hsz2 Hsinv Hidx [$S $Hc3 Hδ' Ht]") as "HR"; first done.
      { iRight. iExists (SInst (length ns2)). by iFrame. }
      by iApply "HR".
    - (* Failure: another node was installed *)
      wp_cmpxchg_fail.
      { intros [=]. apply Hne. split; [done|lia]. }
      assert (length ns ≤ length ns2 - 1) as Hjc.
      { destruct (decide (length ns2 - 1 = jw)) as [Heq|]; last (unfold jw in *; slia).
        exfalso. rewrite Heq Hnw2 in Hnc2. injection Hnc2 as ->. by apply Hne. }
      pose proof (wf_nseq _ _ _ _ _ _ _ Hwf2 Hnc2) as Hnseq2.
      iAssert (|={⊤ ∖ ↑invN}=>
        store_entry γ (z_done zc2) ns2 (length sreg) (γl, γδ) ∗
        ((ldes ↦∗{dq} des -∗ Φ #()) ∨
         (∃ st, ghost_var γδ (DfracOwn (1/2)) st ∗ ⌜sbound st ≤ length ns2 - 1⌝ ∗ token γt)))%I
        with "[Hl Hδ Hes Hst]" as ">[He Hst]".
      { iDestruct "Hst" as "[[HR _] | [Hδ' Ht]]".
        - iModIntro. iSplitR "HR"; last by iLeft.
          iExists b2, st2. iFrame. iSplit; by iPureIntro.
        - iCombine "Hδ Hδ'" gives %[_ ->].
          destruct b2.
          + iMod (store_take_receipt with "Hsinv Ht Hl") as "[Hl HR]"; first wndisj.
            iModIntro. iSplitR "HR"; last by iLeft.
            iExists true, (SPend (length ns)). iFrame. iSplit; by iPureIntro.
          + iModIntro. iSplitR "Hδ' Ht".
            * iExists false, (SPend (length ns)). iFrame. iSplit; by iPureIntro.
            * iRight. iExists (SPend (length ns)). iFrame. iPureIntro. simpl. slia. }
      iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_c".
      iDestruct (mono_list_lb_own_get with "Hns") as "#Hns_c".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr Hsreg Hcr Hcreg He]") as "_".
      { iExists zs2, ns2, zc2, nc2, sreg2, creg2. iFrame. iSplitL; last done.
        iApply ("Hsreg" with "[] He"). iIntros "!>" (k e' _ _) "$". }
      iModIntro. wp_pures.
      wp_apply (wp_free _ _ n with "[$Hnb †Hnb]") as "_"; [by rewrite Hlen|by rewrite Hlen|].
      wp_pures.
      iAssert (ns_idx γns (length ns2 - 1) nc2) as "#Hnc2".
      { by iApply (mono_list_idx_own_get with "Hns_c"). }
      iAssert (seq_lb γzs (length zs2 - 1)) as "#Hsz2".
      { iExists zc2. by iApply (mono_list_idx_own_get with "Hzs_c"). }
      wp_apply (store_tail_spec with "HI Hnc2 Hsz2 Hsinv Hidx [$S $Hc3 $Hst]") as "HR"; first slia.
      by iApply "HR".
  Qed.

  (** ** CAS *)

  Lemma cas_take_receipt γ Φ γl γt le ld dq dq' ev dv E :
    ↑casN ⊆ E →
    inv casN (cas_inv γ Φ γl γt le ld dq dq' ev dv) -∗ token γt -∗ ghost_var γl (DfracOwn (1/2)) true ={E}=∗
    ghost_var γl (DfracOwn (1/2)) true ∗ (le ↦∗{dq} ev ∗ ld ↦∗{dq'} dv -∗ Φ #false).
  Proof.
    iIntros (?) "#Hcinv Ht Hl".
    iInv "Hcinv" as "[(_ & _ & >Hl') | [(>Hc & HΦ & >Hl') | (>Ht' & _)]]" "Hclose".
    - by iCombine "Hl Hl'" gives %[_ ?].
    - iMod (lc_fupd_elim_later with "Hc HΦ") as "HΦ".
      iMod ("Hclose" with "[Ht Hl']") as "_"; first by iRight; iRight; iFrame.
      by iFrame.
    - by iCombine "Ht Ht'" gives %[].
  Qed.

  (** The last iteration: the prophecy says that no CAS succeeded, so the CAS
      has been linearized. *)
  Lemma cas_loop_2 γ Φ (l : loc) n ev dv (le ld : loc) dq dq' (p : proph_id) pvs :
    proph p pvs -∗ le ↦∗{dq} ev -∗ ld ↦∗{dq'} dv -∗
    ((AU_cas γ Φ ev dv le ld dq dq' ∗ ⌜proph_succ pvs = true⌝) ∨ (le ↦∗{dq} ev ∗ ld ↦∗{dq'} dv -∗ Φ #false)) -∗
    WP writable_cas_loop hazptr ba n #l #le #ld #p #2 {{ Φ }}.
  Proof.
    iIntros "Hp Hle Hld Hmode".
    wp_rec. wp_pures.
    wp_apply (wp_resolve_proph with "Hp") as (pvs') "[-> _]".
    wp_pures.
    iDestruct "Hmode" as "[[_ %Hm] | HR]"; first done.
    iApply ("HR" with "[$]").
  Qed.

  (** The second iteration of a CAS that is registered as failing. *)
  Lemma cas_loop_D γ γz γzs γns γsr γcr γd (l dm : loc) Zv n Φ ev dv (le ld : loc) dq dq' (p : proph_id) pvs k γl γt sr :
    length ev = n → length dv = n → Forall val_is_unboxed ev → Forall val_is_unboxed dv →
    proph_succ pvs = false → ev ≠ dv →
    IsWBA_at γ γz γzs γns γsr γcr γd l dm Zv n -∗
    mono_list_idx_own γcr k (γl, ev, sr) -∗ inv casN (cas_inv γ Φ γl γt le ld dq dq' ev dv) -∗ seq_lb γzs (S sr) -∗
    proph p pvs -∗ le ↦∗{dq} ev -∗ ld ↦∗{dq'} dv -∗ token γt -∗
    WP writable_cas_loop hazptr ba n #l #le #ld #p #1 {{ Φ }}.
  Proof using DISJN.
    iIntros (Hlen Hldv Hue Hud Hpred Hed) "#HI #Hk #Hcinv #Hsr Hp Hle Hld Ht".
    iPoseProof "HI" as "(%Hn & HZv & Hd & Hdom & HZ & Hinv)".
    wp_rec. wp_pure credit:"Hc1". wp_pure credit:"Hc2". wp_pures. wp_load.
    (* Read [Z] *)
    awp_apply (ba.(big_atomic_read_spec) with "HZ"). rewrite /atomic_acc /=.
    iInv "Hinv" as (zs ns zc nc sreg creg) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr' & Hsreg & >Hcr & Hcreg & >%Hwf & >%Hinsts)" "Hcl".
    iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first wndisj.
    iModIntro. iExists _. iFrame "HZa". iSplit.
    { iIntros "HZa". iMod "Hclose" as "_".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
      { iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
      by iFrame. }
    iIntros (lz) "HZa". iMod "Hclose" as "_".
    pose proof (wf_zcur _ _ _ _ _ Hwf) as Hzc.
    pose proof (wf_zval_len _ _ _ _ _ _ _ Hwf Hzc) as Hzclen.
    pose proof (wf_zval_unboxed _ _ _ _ _ _ _ Hwf Hzc) as Hzcub.
    pose proof (last_length_pos _ _ (wf_zlast _ _ _ _ _ Hwf)) as Hzs_pos.
    pose proof (last_length_pos _ _ (wf_nlast _ _ _ _ _ Hwf)) as Hns_pos.
    destruct (lookup_lt_is_Some_2 ns 0) as [nr0 Hnr0]; first done.
    pose proof (wf_nseq _ _ _ _ _ _ _ Hwf Hnr0) as Hnseq0.
    iDestruct "Hsr" as (zsr) "Hzsr".
    iDestruct (mono_list_auth_idx_lookup with "Hzs Hzsr") as %Hzsr.
    iDestruct (mono_list_auth_idx_lookup with "Hcr Hk") as %Hk.
    iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_a".
    iDestruct (mono_list_lb_own_get with "Hns") as "#Hns_a".
    destruct (decide (z_val zc = ev)) as [Heq|Hne]; last first.
    { (* The value changed: the CAS has been linearized *)
      iMod (lc_fupd_elim_later with "Hc1 Hcreg") as "Hcreg".
      iDestruct (big_sepL_lookup_acc with "Hcreg") as "[He Hcreg]"; first done.
      iDestruct "He" as (b) "(Hl & %Hb & Hes)".
      destruct b; last first.
      { exfalso. destruct (Hb eq_refl) as [(zc' & Hlast & Hev) _].
        rewrite (wf_zlast _ _ _ _ _ Hwf) in Hlast. injection Hlast as <-. done. }
      iMod (cas_take_receipt with "Hcinv Ht Hl") as "[Hl HR]"; first wndisj.
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg Hl Hes]") as "_".
      { iExists zs, ns, zc, nc, sreg, creg. iFrame. iSplitL; last done.
        iApply "Hcreg". iExists true. by iFrame. }
      iModIntro. iIntros "Hlz". wp_pures.
      rewrite /zcont. iDestruct (array_app with "Hlz") as "[Hlz _]".
      wp_apply (wp_array_equal with "[$Hlz $Hle]") as "[_ Hle]";
        [done|done|apply all_vals_compare_safe; [done|by rewrite Hzclen Hlen]|].
      rewrite bool_decide_eq_false_2 //. wp_pures.
      iApply ("HR" with "[$]"). }
    iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
    { iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
    iModIntro. iIntros "Hlz". wp_pures.
    rewrite /zcont. iDestruct (array_app with "Hlz") as "[Hlz Hlzr]".
    wp_apply (wp_array_equal with "[$Hlz $Hle]") as "[Hlz Hle]";
      [done|done|apply all_vals_compare_safe; [done|by rewrite Hzclen Hlen]|].
    rewrite bool_decide_eq_true_2 //. wp_pures.
    wp_apply (wp_array_equal with "[$Hle $Hld]") as "[Hle Hld]";
      [done|done|apply all_vals_compare_safe; [done|by rewrite Hlen Hldv]|].
    rewrite bool_decide_eq_false_2 //. wp_pures.
    iCombine "Hlz Hlzr" as "Hlz". rewrite -array_app -/(zcont (length zs - 1) zc).
    (* Help *)
    iAssert (ns_idx γns 0 nr0) as "#Hnr0". { by iApply (mono_list_idx_own_get with "Hns_a"). }
    iAssert (seq_lb γzs (length zs - 1)) as "#Hs". { iExists zc. by iApply (mono_list_idx_own_get with "Hzs_a"). }
    wp_apply (help_write_spec with "HI Hnr0 Hs [//]") as (r) "_"; first slia.
    wp_pures.
    (* Build the new value of [Z] *)
    wp_alloc lz' as "Hlz'" "†Hlz'"; first slia.
    wp_pures.
    rewrite Z_to_nat_add2 replicate_add.
    iDestruct (array_app with "Hlz'") as "[Hlz' Hlz'r]".
    rewrite length_replicate.
    iDestruct (array_cons with "Hlz'r") as "[Hseq' Hmark']".
    rewrite array_singleton Loc.add_assoc Z_of_nat_add1.
    wp_apply (wp_array_copy_to with "[$Hlz' $Hld]") as "[Hlz' Hld]"; [by rewrite length_replicate|done|].
    wp_pures.
    wp_apply (wp_load_offset with "Hlz") as "Hlz".
    { rewrite -Hzclen. apply zcont_lookup_seq. }
    wp_pures. wp_store. wp_pures.
    wp_apply (wp_load_offset with "Hlz") as "Hlz".
    { rewrite -Hzclen. apply zcont_lookup_mark. }
    wp_pures. wp_store.
    iAssert (lz' ↦∗ zcont (S (length zs - 1)) (ZRec dv zc.(z_mark) 0 0))%I with "[Hlz' Hseq' Hmark']" as "Hlz'".
    { rewrite /zcont array_app array_cons array_singleton Hldv Loc.add_assoc Z_of_nat_succ Z_of_nat_add1 /=.
      iFrame. }
    wp_pures. wp_load.
    assert (length (zcont (length zs - 1) zc) = n + 2) as Hlen_e by rewrite zcont_length Hzclen //.
    assert (length (zcont (S (length zs - 1)) (ZRec dv zc.(z_mark) 0 0)) = n + 2) as Hlen_d by rewrite zcont_length /= Hldv //.
    assert (Forall val_is_unboxed (zcont (length zs - 1) zc)) as Hub_e by by apply zcont_unboxed.
    assert (Forall val_is_unboxed (zcont (S (length zs - 1)) (ZRec dv zc.(z_mark) 0 0))) as Hub_d by by apply zcont_unboxed.
    awp_apply (ba.(big_atomic_cas_spec) _ _ _ _ _ _ _ _ _ _ _ Hlen_e Hlen_d Hub_e Hub_d with "HZ Hlz Hlz' Hp").
    rewrite /atomic_acc /=.
    iInv "Hinv" as (zs2 ns2 zc2 nc2 sreg2 creg2) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr' & Hsreg & >Hcr & Hcreg & >%Hwf2 & >%Hinsts2)" "Hcl".
    { wndisj. }
    iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first wndisj.
    iModIntro. iExists _. iFrame "HZa". iSplit.
    { iIntros "HZa". iMod "Hclose" as "_".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
      { iExists zs2, ns2, zc2, nc2, sreg2, creg2. by iFrame. }
      by iFrame. }
    iIntros "HZa". iMod "Hclose" as "_".
    destruct (decide (zcont (length zs2 - 1) zc2 = zcont (length zs - 1) zc)) as [Hsame|Hdiff].
    { (* The CAS cannot succeed: the prophecy says so *)
      rewrite bool_decide_eq_true_2 //. iDestruct "HZa" as "[_ %Hsucc]".
      exfalso. destruct Hsucc as [Hsucc|Hsucc%cas_succ_res_proph]; last congruence.
      apply zcont_inj in Hsucc as [? _]; [slia|by rewrite Hzclen].  }
    rewrite bool_decide_eq_false_2 //.
    (* [Z] changed twice since the registration: the CAS has been linearized *)
    iDestruct (mono_list_auth_lb_valid with "Hzs Hzs_a") as %[_ Hzs_pre].
    pose proof (wf_zcur _ _ _ _ _ Hwf2) as Hzc2.
    assert (zs2 !! (length zs - 1) = Some zc) as Hza2 by by eapply prefix_lookup_Some.
    assert (length zs < length zs2) as Hlt2.
    { pose proof (prefix_length _ _ Hzs_pre).
      destruct (decide (length zs2 = length zs)) as [Heq2|]; last slia. exfalso. apply Hdiff.
      rewrite Heq2 in Hzc2. rewrite Hzc2 in Hza2. injection Hza2 as ->. by rewrite Heq2. }
    iMod (lc_fupd_elim_later with "Hc2 Hcreg") as "Hcreg".
    iDestruct (mono_list_auth_idx_lookup with "Hcr Hk") as %Hk2.
    iDestruct (big_sepL_lookup_acc with "Hcreg") as "[He Hcreg]"; first done.
    iDestruct "He" as (b) "(Hl & %Hb & Hes)".
    destruct b; last first.
    { exfalso. destruct (Hb eq_refl) as (_ & _ & Hle2).
      apply lookup_lt_Some in Hzsr. slia. }
    iMod (cas_take_receipt with "Hcinv Ht Hl") as "[Hl HR]"; first wndisj.
    iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg Hl Hes]") as "_".
    { iExists zs2, ns2, zc2, nc2, sreg2, creg2. iFrame. iSplitL; last done.
      iApply "Hcreg". iExists true. by iFrame. }
    iModIntro. iIntros "(Hlz & Hlz' & %pvs' & Hp & _)".
    wp_pures.
    iApply (cas_loop_2 γ with "Hp Hle Hld [HR]"). by iRight.
  Qed.

  (** An iteration of a CAS that holds its atomic update. *)
  Lemma cas_loop_A γ γz γzs γns γsr γcr γd (l dm : loc) Zv n Φ ev dv (le ld : loc) dq dq' (p : proph_id) :
    length ev = n → length dv = n → Forall val_is_unboxed ev → Forall val_is_unboxed dv →
    IsWBA_at γ γz γzs γns γsr γcr γd l dm Zv n -∗
    ∀ (i : nat) pvs, ⌜i ≤ 1⌝ -∗ ⌜i = 0 ∨ proph_succ pvs = true⌝ -∗
      proph p pvs -∗ le ↦∗{dq} ev -∗ ld ↦∗{dq'} dv -∗ AU_cas γ Φ ev dv le ld dq dq' -∗
      WP writable_cas_loop hazptr ba n #l #le #ld #p #i {{ Φ }}.
  Proof using DISJN.
    iIntros (Hlen Hldv Hue Hud) "#HI".
    iPoseProof "HI" as "(%Hn & HZv & Hd & Hdom & HZ & Hinv)".
    iLöb as "IH". iIntros (i pvs Hi Hpi) "Hp Hle Hld AU".
    wp_rec. wp_pure credit:"Hc1". wp_pure credit:"Hc2". wp_pure credit:"Hc3". wp_pure credit:"Hc4".
    wp_pures. rewrite bool_decide_eq_false_2; last (intros [= ?]; slia).
    wp_pures. wp_load.
    (* Read [Z] *)
    awp_apply (ba.(big_atomic_read_spec) with "HZ"). rewrite /atomic_acc /=.
    iInv "Hinv" as (zs ns zc nc sreg creg) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr' & Hsreg & >Hcr & Hcreg & >%Hwf & >%Hinsts)" "Hcl".
    rewrite /AU_cas. iMod "AU" as (vs) "[Hγ' Hlin]".
    iCombine "Hγ Hγ'" gives %[_ <-].
    iModIntro. iExists _. iFrame "HZa". iSplit.
    { iIntros "HZa". iDestruct "Hlin" as "[Habort _]".
      iMod ("Habort" with "Hγ'") as "AU".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
      { iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
      by iFrame. }
    iIntros (lz) "HZa".
    pose proof (wf_zcur _ _ _ _ _ Hwf) as Hzc.
    pose proof (wf_zval_len _ _ _ _ _ _ _ Hwf Hzc) as Hzclen.
    pose proof (wf_zval_unboxed _ _ _ _ _ _ _ Hwf Hzc) as Hzcub.
    pose proof (last_length_pos _ _ (wf_zlast _ _ _ _ _ Hwf)) as Hzs_pos.
    pose proof (last_length_pos _ _ (wf_nlast _ _ _ _ _ Hwf)) as Hns_pos.
    destruct (lookup_lt_is_Some_2 ns 0) as [nr0 Hnr0]; first done.
    pose proof (wf_nseq _ _ _ _ _ _ _ Hwf Hnr0) as Hnseq0.
    iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_a".
    iDestruct (mono_list_lb_own_get with "Hns") as "#Hns_a".
    destruct (decide (z_val zc = ev)) as [Heq|Hne]; last first.
    { (* The value is not [ev]: fail here *)
      iDestruct "Hlin" as "[_ Hcommit]". rewrite bool_decide_eq_false_2 //.
      iMod ("Hcommit" with "Hγ'") as "HR".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
      { iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
      iModIntro. iIntros "Hlz". wp_pures.
      rewrite /zcont. iDestruct (array_app with "Hlz") as "[Hlz _]".
      wp_apply (wp_array_equal with "[$Hlz $Hle]") as "[_ Hle]";
        [done|done|apply all_vals_compare_safe; [done|by rewrite Hzclen Hlen]|].
      rewrite bool_decide_eq_false_2 //. wp_pures.
      iApply ("HR" with "[$]"). }
    destruct (decide (ev = dv)) as [<-|Hed].
    { (* [ev = dv]: succeed here without a change *)
      iDestruct "Hlin" as "[_ Hcommit]". rewrite bool_decide_eq_true_2 //.
      iMod ("Hcommit" with "[Hγ']") as "HR"; first by rewrite /WBA Heq.
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
      { iExists zs, ns, zc, nc, sreg, creg. by iFrame. }
      iModIntro. iIntros "Hlz". wp_pures.
      rewrite /zcont. iDestruct (array_app with "Hlz") as "[Hlz _]".
      wp_apply (wp_array_equal with "[$Hlz $Hle]") as "[_ Hle]";
        [done|done|apply all_vals_compare_safe; [done|by rewrite Hzclen Hlen]|].
      rewrite bool_decide_eq_true_2 //. wp_pures.
      wp_apply (wp_array_equal with "[$Hle $Hld]") as "[Hle Hld]";
        [done|done|apply all_vals_compare_safe; [done|done]|].
      rewrite bool_decide_eq_true_2 //. wp_pures.
      iApply ("HR" with "[$]"). }
    iDestruct "Hlin" as "[Habort _]".
    iMod ("Habort" with "Hγ'") as "AU".
    (* Register the CAS if it will fail *)
    iAssert (|={⊤ ∖ (↑zreadN ∪ ↑ptrsN hazptrN) ∖ ↑invN}=> ∃ creg',
        mono_list_auth_own γcr 1 creg' ∗ ▷ ([∗ list] e ∈ creg', cas_entry γ zs e) ∗
        ((AU_cas γ Φ ev dv le ld dq dq' ∗ ⌜proph_succ pvs = true⌝) ∨
         (⌜i = 0 ∧ proph_succ pvs = false⌝ ∗ ∃ k γl γt,
            mono_list_idx_own γcr k (γl, ev, length zs - 1) ∗ token γt ∗
            inv casN (cas_inv γ Φ γl γt le ld dq dq' ev dv))))%I
      with "[AU Hc1 Hc2 Hcr Hcreg]" as ">(%creg' & Hcr & Hcreg & Hmode)".
    { destruct (decide (i = 0 ∧ proph_succ pvs = false)) as [[-> Hpf]|Hnreg]; last first.
      { iModIntro. iExists creg. iFrame. iLeft. iFrame. iPureIntro.
        destruct Hpi as [->|?]; last done. destruct (proph_succ pvs); naive_solver. }
      iMod (ghost_var_alloc false) as (γl) "[Hl Hl']".
      iMod token_alloc as (γt) "Ht".
      iMod (inv_alloc casN _ (cas_inv γ Φ γl γt le ld dq dq' ev dv) with "[AU Hc1 Hc2 Hl']") as "#Hcinv".
      { iNext. iLeft. iFrame. iCombine "Hc1 Hc2" as "$". }
      iMod (mono_list_auth_own_update_app [(γl, ev, length zs - 1)] with "Hcr") as "[Hcr #Hcr_lb]".
      iModIntro. iExists (creg ++ [(γl, ev, length zs - 1)]). iFrame "Hcr".
      iSplitL "Hcreg Hl".
      - rewrite big_sepL_snoc. iNext. iFrame "Hcreg".
        iExists false. iFrame "Hl". iSplit.
        + iPureIntro. intros _. split_and!.
          * exists zc. split; [apply Hwf|done].
          * by exists zc.
          * slia.
        + iExists Φ, γt, le, ld, dq, dq', dv. by iFrame "Hcinv".
      - iRight. iSplit; first done. iExists (length creg), γl, γt. iFrame "Ht Hcinv".
        iApply (mono_list_idx_own_get with "Hcr_lb"). by rewrite lookup_app_r // Nat.sub_diag. }
    iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
    { iExists zs, ns, zc, nc, sreg, creg'. by iFrame. }
    iModIntro. iIntros "Hlz". wp_pures.
    rewrite /zcont. iDestruct (array_app with "Hlz") as "[Hlz Hlzr]".
    wp_apply (wp_array_equal with "[$Hlz $Hle]") as "[Hlz Hle]";
      [done|done|apply all_vals_compare_safe; [done|by rewrite Hzclen Hlen]|].
    rewrite bool_decide_eq_true_2 //. wp_pures.
    wp_apply (wp_array_equal with "[$Hle $Hld]") as "[Hle Hld]";
      [done|done|apply all_vals_compare_safe; [done|by rewrite Hlen Hldv]|].
    rewrite bool_decide_eq_false_2 //. wp_pures.
    iCombine "Hlz Hlzr" as "Hlz". rewrite -array_app -/(zcont (length zs - 1) zc).
    (* Help *)
    iAssert (ns_idx γns 0 nr0) as "#Hnr0". { by iApply (mono_list_idx_own_get with "Hns_a"). }
    iAssert (seq_lb γzs (length zs - 1)) as "#Hs". { iExists zc. by iApply (mono_list_idx_own_get with "Hzs_a"). }
    wp_apply (help_write_spec with "HI Hnr0 Hs [//]") as (r) "(%sa & %Hsa & Hr)"; first slia.
    wp_pures.
    (* Build the new value of [Z] *)
    wp_alloc lz' as "Hlz'" "†Hlz'"; first slia.
    wp_pures.
    rewrite Z_to_nat_add2 replicate_add.
    iDestruct (array_app with "Hlz'") as "[Hlz' Hlz'r]".
    rewrite length_replicate.
    iDestruct (array_cons with "Hlz'r") as "[Hseq' Hmark']".
    rewrite array_singleton Loc.add_assoc Z_of_nat_add1.
    wp_apply (wp_array_copy_to with "[$Hlz' $Hld]") as "[Hlz' Hld]"; [by rewrite length_replicate|done|].
    wp_pures.
    wp_apply (wp_load_offset with "Hlz") as "Hlz".
    { rewrite -Hzclen. apply zcont_lookup_seq. }
    wp_pures. wp_store. wp_pures.
    wp_apply (wp_load_offset with "Hlz") as "Hlz".
    { rewrite -Hzclen. apply zcont_lookup_mark. }
    wp_pures. wp_store.
    set (zd := ZRec dv zc.(z_mark) 0 0).
    iAssert (lz' ↦∗ zcont (S (length zs - 1)) zd)%I with "[Hlz' Hseq' Hmark']" as "Hlz'".
    { rewrite /zcont array_app array_cons array_singleton Hldv Loc.add_assoc Z_of_nat_succ Z_of_nat_add1 /=.
      iFrame. }
    wp_pures. wp_load.
    assert (length (zcont (length zs - 1) zc) = n + 2) as Hlen_e by rewrite zcont_length Hzclen //.
    assert (length (zcont (S (length zs - 1)) zd) = n + 2) as Hlen_d by rewrite zcont_length /= Hldv //.
    assert (Forall val_is_unboxed (zcont (length zs - 1) zc)) as Hub_e by by apply zcont_unboxed.
    assert (Forall val_is_unboxed (zcont (S (length zs - 1)) zd)) as Hub_d by by apply zcont_unboxed.
    awp_apply (ba.(big_atomic_cas_spec) _ _ _ _ _ _ _ _ _ _ _ Hlen_e Hlen_d Hub_e Hub_d with "HZ Hlz Hlz' Hp").
    rewrite /atomic_acc /=.
    iInv "Hinv" as (zs2 ns2 zc2 nc2 sreg2 creg2) "(>Hzs & >Hns & >HZa & >Hγ & >Hw & HM & >Htoks & >Hsr' & Hsreg & >Hcr & Hcreg & >%Hwf2 & >%Hinsts2)" "Hcl".
    { wndisj. }
    iDestruct (mono_list_auth_lb_valid with "Hzs Hzs_a") as %[_ Hzs_pre].
    pose proof (wf_zcur _ _ _ _ _ Hwf2) as Hzc2.
    pose proof (wf_zval_len _ _ _ _ _ _ _ Hwf2 Hzc2) as Hzc2len.
    assert (zs2 !! (length zs - 1) = Some zc) as Hza2 by by eapply prefix_lookup_Some.
    assert (length zs ≤ length zs2) as Hlen_zs2 by by apply prefix_length.
    (* The CAS on [Z] succeeds iff [Z] did not change *)
    assert (zcont (length zs2 - 1) zc2 = zcont (length zs - 1) zc ↔ length zs2 = length zs) as Hchg.
    { split.
      - intros Hs%zcont_inj; last by rewrite Hzc2len Hzclen. slia.
      - intros Heq2. rewrite Heq2 in Hzc2. rewrite Hzc2 in Hza2. injection Hza2 as ->. by rewrite Heq2. }
    iDestruct "Hmode" as "[[AU %Hps] | [[-> %Hpf] (%k & %γl & %γt & #Hk & Ht & #Hcinv)]]"; last first.
    { (* Registered: the CAS on [Z] cannot succeed *)
      iMod (fupd_mask_subseteq (↑mgmtN hazptrN)) as "Hclose"; first wndisj.
      iModIntro. iExists _. iFrame "HZa". iSplit.
      { iIntros "HZa". iMod "Hclose" as "_".
        iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
        { iExists zs2, ns2, zc2, nc2, sreg2, creg2. by iFrame. }
        iModIntro. iFrame "Hc3 Hc4 Hle Hr †Hlz' Hld". iRight. iSplit; first done.
        iExists k, γl, γt. by iFrame "Hk Ht Hcinv". }
      iIntros "HZa". iMod "Hclose" as "_".
      destruct (decide (zcont (length zs2 - 1) zc2 = zcont (length zs - 1) zc)) as [Hsame|Hdiff].
      { rewrite bool_decide_eq_true_2 //. iDestruct "HZa" as "[_ %Hsucc]".
        exfalso. destruct Hsucc as [Hsucc|Hsucc%cas_succ_res_proph]; last congruence.
        apply zcont_inj in Hsucc as [? _]; [slia|by rewrite Hzclen]. }
      rewrite bool_decide_eq_false_2 //.
      assert (length zs < length zs2) as Hlt2.
      { destruct (decide (length zs2 = length zs)) as [Heq2|]; [by apply Hchg in Heq2|slia]. }
      iDestruct (mono_list_lb_own_get with "Hzs") as "#Hzs_c".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
      { iExists zs2, ns2, zc2, nc2, sreg2, creg2. by iFrame. }
      iModIntro. iIntros "(Hlz & Hlz' & %pvs' & Hp & %Hpvs')".
      wp_pures.
      destruct Hpvs' as [?|(rs & Hrs & ->)]; first done.
      destruct (lookup_lt_is_Some_2 zs2 (S (length zs - 1))) as [zr' Hzr']; first slia.
      iApply (cas_loop_D with "HI Hk Hcinv [] Hp Hle Hld Ht"); try done.
      - by rewrite proph_succ_failed in Hpf.
      - iExists zr'. by iApply (mono_list_idx_own_get with "Hzs_c"). }
    (* Holding the atomic update *)
    rewrite /AU_cas. iMod "AU" as (vs) "[Hγ' Hlin]"; first wEo.
    iCombine "Hγ Hγ'" gives %[_ <-].
    iModIntro. iExists _. iFrame "HZa". iSplit.
    { iIntros "HZa". iDestruct "Hlin" as "[Habort _]".
      iMod ("Habort" with "Hγ'") as "AU".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
      { iExists zs2, ns2, zc2, nc2, sreg2, creg2. by iFrame. }
      iModIntro. iFrame "Hc3 Hc4 Hle Hr †Hlz' Hld". iLeft. by iFrame. }
    iIntros "HZa".
    destruct (decide (zcont (length zs2 - 1) zc2 = zcont (length zs - 1) zc)) as [Hsame|Hdiff].
    - (* Success: linearize the CAS, and the registered CASes of [ev] *)
      rewrite (bool_decide_eq_true_2 (zcont (length zs2 - 1) zc2 = zcont (length zs - 1) zc)) //.
      iDestruct "HZa" as "[HZa _]".
      apply Hchg in Hsame as Heq2.
      assert (zc2 = zc) as ->.
      { rewrite Heq2 in Hzc2. rewrite Hzc2 in Hza2. by injection Hza2. }
      iAssert ⌜z_done zc = S (z_node zc)⌝%I as %Hnopend.
      { destruct r.
        - iDestruct "Hr" as "[_ [(%zr & Hzr & %Hzr) | (%zr & Hzr)]]".
          + iDestruct (mono_list_auth_idx_lookup with "Hzs Hzr") as %Hzr'.
            assert (sa = length zs - 1) as ->.
            { apply lookup_lt_Some in Hzr'. slia. }
            rewrite Hza2 in Hzr'. by injection Hzr' as ->.
          + iDestruct (mono_list_auth_idx_lookup with "Hzs Hzr") as %Hzr'.
            apply lookup_lt_Some in Hzr'. exfalso. slia.
        - iDestruct "Hr" as "[(%zr & Hzr) _]".
          iDestruct (mono_list_auth_idx_lookup with "Hzs Hzr") as %Hzr'.
          apply lookup_lt_Some in Hzr'. exfalso. slia. }
      set (zn := ZRec dv (z_mark zc) (z_done zc) (length ns2 - 1)).
      assert (wwf n (zs2 ++ [zn]) ns2 zn nc2) as Hwf2'.
      { apply wf_cas; try done. by rewrite Heq. }
      iDestruct "Hlin" as "[_ Hcommit]". rewrite (bool_decide_eq_true_2 (z_val zc = ev)) //.
      iMod (ghost_var_update_halves dv with "Hγ Hγ'") as "[Hγ Hγ']".
      iMod ("Hcommit" with "Hγ'") as "HR".
      iMod (lc_fupd_elim_later with "Hc3 Hcreg") as "Hcreg".
      iMod (cas_entries_commit _ zs2 (zs2 ++ [zn]) with "Hγ Hcreg") as "[Hγ Hcreg]"; [wndisj|wEo| |].
      { exists zc. split; [apply Hwf2|by rewrite Heq]. }
      iMod (mono_list_auth_own_update_app [zn] with "Hzs") as "[Hzs _]".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
      { iExists (zs2 ++ [zn]), ns2, zn, nc2, sreg2, creg2. iFrame.
        rewrite length_app /= Nat.add_sub.
        replace (length zs2) with (S (length zs - 1)) by slia.
        rewrite /zcont /=. iFrame. iPureIntro. by split. }
      iModIntro. iIntros "_". wp_pures.
      iApply ("HR" with "[$]").
    - (* Failure: try again *)
      rewrite (bool_decide_eq_false_2 (zcont (length zs2 - 1) zc2 = zcont (length zs - 1) zc)) //.
      iDestruct "Hlin" as "[Habort _]".
      iMod ("Habort" with "Hγ'") as "AU".
      iMod ("Hcl" with "[Hzs Hns HZa Hγ Hw HM Htoks Hsr' Hsreg Hcr Hcreg]") as "_".
      { iExists zs2, ns2, zc2, nc2, sreg2, creg2. by iFrame. }
      iModIntro. iIntros "(Hlz & Hlz' & %pvs' & Hp & %Hpvs')".
      destruct Hpvs' as [?|(rs & Hrs & ->)]; first done.
      rewrite proph_succ_failed // in Hps.
      destruct (decide (i = 0)) as [->|Hi1].
      + wp_pures. iApply ("IH" $! 1 with "[] [] Hp Hle Hld AU"); [done|by iRight].
      + assert (i = 1) as -> by slia. wp_pures.
        iApply (cas_loop_2 with "Hp Hle Hld [AU]"). iLeft. by iFrame.
  Qed.

  Lemma writable_cas_spec : writable_cas_spec' writableN hazptrN (writable_cas hazptr ba) WBA IsWBA.
  Proof using DISJN.
    iIntros (γ v n le ld dq dq' ev dv Hlen Hldv Hue Hud) "(%l & %dm & %Zv & %γz & %γzs & %γns & %γsr & %γcr & %γd & -> & #HI) Hle Hld %Φ AU".
    wp_rec. wp_pures.
    wp_apply wp_new_proph as (pvs p) "Hp"; first done.
    wp_pures.
    iPoseProof (cas_loop_A γ γz γzs γns γsr γcr γd l dm Zv n Φ ev dv le ld dq dq' p Hlen Hldv Hue Hud with "HI") as "Hloop".
    iApply ("Hloop" $! 0 pvs with "[] [] Hp Hle Hld [AU]"); [iPureIntro; lia|iPureIntro; by left|].
    rewrite /AU_cas. iExact "AU".
  Qed.

  Definition writable_big_atomic_code_impl : writable_big_atomic_code := {|
    writable_big_atomic_new := writable_new ba;
    writable_big_atomic_load := writable_load ba;
    writable_big_atomic_store := writable_store hazptr ba;
    writable_big_atomic_cas := writable_cas hazptr ba;
  |}.

  Definition writable_big_atomic_impl : writable_big_atomic_spec Σ writableN hazptrN DISJN hazptr := {|
    writable_big_atomic_spec_code := writable_big_atomic_code_impl;
    WritableBigAtomic := WBA;
    IsWritableBigAtomic := IsWBA;
    WritableBigAtomic_Timeless := WBA_Timeless;
    IsWritableBigAtomic_Persistent := IsWBA_Persistent;
    writable_big_atomic_new_spec := writable_new_spec;
    writable_big_atomic_load_spec := writable_load_spec;
    writable_big_atomic_store_spec := writable_store_spec;
    writable_big_atomic_cas_spec := writable_cas_spec;
  |}.

End writable.
