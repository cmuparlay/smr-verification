Require Import iris.program_logic.atomic.

From iris.program_logic Require Import atomic.
From iris.algebra Require Import auth gmap gset list lib.mono_nat.
From smr.lang Require Import lang proofmode notation lib.array.
From iris.base_logic.lib Require Import token ghost_var mono_nat invariants.
From smr.program_logic Require Import atomic.

Import derived_laws.bi.
From Stdlib Require Import ZArith.Zquot.
Require Import iris.bi.interface.

Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(* Begin hooks to make `lia` work witrefines_right_CG_dequeueh Nat.modulo and Nat.div *)
From Stdlib Require Import Arith ZArith ZifyClasses ZifyInst Lia.

Global Program Instance Op_Nat_mod : BinOp Nat.modulo :=
  {| TBOp := Z.modulo ; TBOpInj := Nat2Z.inj_mod |}.
Add Zify BinOp Op_Nat_mod.

Global Program Instance Op_Nat_div : BinOp Nat.div :=
  {| TBOp := Z.div ; TBOpInj := Nat2Z.inj_div |}.
Add Zify BinOp Op_Nat_div.

From stdpp Require Import base tactics option list gmap sorting.

From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr hazptr.spec_big_atomic hazptr.code_cached_wf.

Notation version_off := 0 (only parsing).
Notation backup_off := 1 (only parsing).
Notation domain_off := 2 (only parsing).
Notation cache_off := 3 (only parsing).

Definition log := gmap nat $ agree $ (loc * list val)%type.

Definition index := gmap nat $ agree nat.

Definition indexUR := authUR $ gmapUR nat (agreeR gnameO).

Definition logUR := authUR $ gmapUR gname $ agreeR $ listO valO.

Definition requestReg := gmap nat $ agree (gname * gname * loc).
Definition requestRegUR := authUR $ gmapUR nat $ agreeR $ prodO (prodO gnameO gnameO) gname.

Definition validatedUR := authUR $ gsetUR $ gnameO.
Definition invalidUR := authUR $ gmapUR gnameO $ agreeR natO.
Definition orderUR := authUR $ gmapUR gnameO $ agreeR natO.

Definition abstractionUR := authUR $ gmapUR gnameO $ agreeR blkO.

Class cached_wfG (Σ : gFunctors) := {
  (* #[local] cached_wf_heapGS :: heapGS Σ; *)
  #[local] cached_wf_logUR :: inG Σ logUR;
  #[local] cached_wf_indexUR :: inG Σ indexUR;
  #[local] cached_wf_requestRegUR :: inG Σ requestRegUR;
  #[local] cached_wf_mono_natG :: mono_natG Σ;
  #[local] cached_wf_ghost_varG_bool :: ghost_varG Σ bool;
  #[local] cached_wf_ghost_varG_loc_val :: ghost_varG Σ (gname * list val);
  #[local] cached_wf_tokenG :: tokenG Σ;
  #[local] cached_wf_invalidUR :: inG Σ invalidUR;
  #[local] cached_wf_orderUR :: inG Σ orderUR;
  #[local] cached_wf_validatedUR :: inG Σ validatedUR;
  #[local] cached_wf_abstractonUR :: inG Σ abstractionUR;
}.

Definition cached_wfΣ : gFunctors := #[
  ghost_varΣ bool;
  ghost_varΣ (gname * list val);
  GFunctor logUR;
  GFunctor indexUR;
  GFunctor requestRegUR;
  mono_natΣ;
  tokenΣ;
  GFunctor invalidUR;
  GFunctor orderUR;
  GFunctor validatedUR;
  GFunctor abstractionUR
].

Global Instance subG_cached_wfΣ {Σ} :
  subG cached_wfΣ Σ → cached_wfG Σ.
Proof. solve_inG. Qed.

(** [iFrame "∗ # %"] is extremely slow on the large invariants of this file
    (up to a minute or two per call): framing with ["%"] tries every pure
    hypothesis in the (large) Coq context against every conjunct of the goal,
    and each failing attempt is expensive. Framing the hypotheses that actually
    match is cheap, so [iFrame_fast] goes the other way around: for each pure
    conjunct [⌜ψ⌝] of the goal, it looks for [ψ] (or the fields of the record
    [ψ]) in the context using [assumption], and frames it. *)
Ltac iFrame_pure_goals :=
  repeat match goal with
  | |- environments.envs_entails _ ?G =>
      (* Existentials are handled by [iFrame_pure_exists]. *)
      lazymatch G with
      | bi_exist _ => fail | bi_later (bi_exist _) => fail | _ => idtac
      end;
      match G with
      | context [bi_pure ?ψ] =>
          (* Do not commit to instantiations of evars. *)
          tryif has_evar ψ then fail else idtac;
          let H := fresh "Hpure" in
          (* [ψ] is either in the context, or a record of pure facts whose
             fields are in the context. *)
          assert ψ as H by (assumption || (constructor; assumption));
          iFrame (H); clear H
      end
  end.
(** Instantiate evars in pure conjuncts [⌜ψ⌝] of the goal by unifying them with
    pure hypotheses, trying hypotheses in context order (like [iFrame "%"]). *)
Ltac iFrame_pure_hyps_evars :=
  repeat match reverse goal with
  | H : ?φ |- environments.envs_entails _ ?G =>
      lazymatch type of φ with Prop => idtac end;
      match G with
      | context [bi_pure ?ψ] => has_evar ψ; unify φ ψ
      end;
      iFrame (H)
  end.
(** For a goal [(▷) ∃ x.., P], pick the witnesses by framing pure hypotheses.
    Fails (without committing) if some witness is not determined this way. *)
Ltac iFrame_pure_exists :=
  lazymatch goal with
  | |- environments.envs_entails _ (bi_exist _) => idtac
  | |- environments.envs_entails _ (bi_later (bi_exist _)) => idtac
  end;
  repeat iExists _;
  iFrame_pure_hyps_evars;
  lazymatch goal with
  | |- environments.envs_entails _ ?G => tryif has_evar G then fail else idtac
  end;
  iFrame_pure_goals.
(** As a last resort, fall back to [iFrame "%"] (on a by now smaller goal). *)
Ltac iFrame_pure_finish :=
  first [iEmpIntro | iFrame_pure_exists; try iEmpIntro | iFrame "%"].
Tactic Notation "iFrame_fast" constr(sel) :=
  iFrame sel; iFrame_pure_goals; iFrame_pure_finish.
Tactic Notation "iFrame_fast" := iFrame_fast "∗ #".
(** Split a goal consisting of (records of) pure facts into the individual
    facts, discharging those that are in the context. *)
Ltac iSplit_facts :=
  repeat iSplit;
  try (try iNext; iPureIntro; split_and?; try constructor);
  try done.
(** Replacement for [iFrame "%"]. *)
Tactic Notation "iFrame_fast_pure" := iFrame_pure_goals; iFrame_pure_finish.

Section cached_wf.
  Context (cached_wfN hazptrN : namespace) (DISJN : cached_wfN ## hazptrN).
  Context `{!cached_wfG Σ, !heapGS Σ}.

  Definition casN := casN cached_wfN.

  Definition readN := readN cached_wfN.

  Definition mainN := mainN cached_wfN.

  Variable (hazptr : hazard_pointer_spec Σ hazptrN).

  Variable (hazptr_code : hazard_pointer_code).

  Definition CachedWF γ (vs : list val) : iProp Σ := ∃ (backup : gname), ghost_var_frac γ (1/2) (backup, vs).

  Global Instance CachedWF_Timeless γ vs : Timeless (CachedWF γ vs).
  Proof. apply _. Qed.

  Lemma wp_array_equal (l l' : loc) (dq dq' : dfrac) (vs vs' : list val) n :
    length vs = n → length vs' = n → Forall2 vals_compare_safe vs vs' →
    {{{ l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}
      array_equal #l #l' #n
    {{{ RET #(bool_decide (vs = vs')); l ↦∗{dq} vs ∗ l' ↦∗{dq'} vs' }}}.
    iIntros (Hlen Hlen' Hsafe Φ) "[Hl Hl'] HΦ".
    Proof.
    iInduction vs as [|v vs] "IH" forall (n l l' vs' Hsafe Hlen Hlen') "HΦ".
    - wp_rec. wp_pures. simplify_list_eq.
      apply length_zero_iff_nil in Hlen' as ->.
      wp_pures.
      rewrite bool_decide_eq_true_2 //.
      iApply ("HΦ" with "[$]").
    - wp_rec. wp_pures. simplify_list_eq.
      destruct vs' as [| v' vs']; first discriminate.
      inv Hlen'. inv Hsafe.
      repeat rewrite array_cons.
      iDestruct "Hl" as "[Hl Hlrest]".
      iDestruct "Hl'" as "[Hl' Hlrest']".
      do 2 wp_load.
      wp_pures.
      destruct (decide (v = v')) as [-> | Hne].
      + rewrite (bool_decide_eq_true_2 (v' = v')); last done.
        wp_pures.
        rewrite Z.sub_1_r.
        rewrite -Nat2Z.inj_pred /=; last lia.
        iApply ("IH" $! (length vs') _ _ vs' with "[//] [//] [//] [$] [$]").
        iIntros "!> [Hlrest Hlrest']".
        iSpecialize ("HΦ" with "[$]").
        destruct (decide (vs = vs')) as [-> | Hne].
        * rewrite bool_decide_eq_true_2; last done.
          by rewrite bool_decide_eq_true_2.
        * rewrite bool_decide_eq_false_2.
          -- by rewrite bool_decide_eq_false_2.
          -- by intros [=].
      + rewrite (bool_decide_eq_false_2 (v = v')); last done.
        iSpecialize ("HΦ" with "[$]").
        wp_pures.
        destruct (decide (vs = vs')) as [-> | Hne'];
        rewrite bool_decide_eq_false_2; auto; by intros [=].
  Qed.

  (* Definition gmap_auth_own `{Countable K} {V} (γ : gname) (q : Qp) (m : gmap K V) := own (A:=gmapUR K (agreeR V)) γ (●{#q} (fmap (M:=gmap K) to_agree m)). *)

  Definition index_auth_own γᵢ (q : Qp) (index : list gname) := own γᵢ (●{#q} map_seq 0 (to_agree <$> index)).

  Definition index_frag_own' γ (index : list gname) := own γ (◯ map_seq 0 (to_agree <$> index)).

  Definition log_auth_own (γᵥ : gname) (q : Qp) (log : gmap gname (list val)) := own γᵥ (●{#q} fmap (M:=gmap gname) to_agree log).

  Definition vers_auth_own (γᵥ : gname) (q : Qp) (log : gmap gname nat) := own γᵥ (●{#q} fmap (M:=gmap gname) to_agree log).

  Definition log_frag_own γₕ l (value : list val) := own γₕ (◯ {[l := to_agree value ]}).

  Definition vers_frag_own γ (l : gname) (ver : nat) := own γ (◯ {[l := to_agree ver]}).

  Definition index_frag_own γᵢ (i : nat) (l : gname) := own γᵢ (◯ {[i := to_agree l]}).

  Definition validated_auth_own (γ : gname) (q : Qp) (validated : gset gname) := own γ (●{#q} validated).

  Definition validated_frag_own (γ : gname) (l : gname) := own γ (◯ {[ l ]}).

  Definition abstraction_auth_own (γᵥ : gname) (q : Qp) (log : gmap gname blk) := own γᵥ (●{#q} fmap (M:=gmap gname) to_agree log).

  Definition abstraction_frag_own γ (γ_l : gname) (l : blk) := own γ (◯ {[γ_l := to_agree l]}).

  (** The history of backups: the log of their values, and the abstraction mapping
      logical backups to physical ones. It is shared (half/half) between the read
      invariant and the main invariant. *)
  Definition history (γₕ γ_abs : gname) (q : Qp) (log : gmap gname (list val)) (abstraction : gmap gname blk) : iProp Σ :=
    log_auth_own γₕ q log ∗ abstraction_auth_own γ_abs q abstraction.

  (* Maximum value over a map *)
  Definition map_max `{Countable K} (m : gmap K nat) : nat :=
    map_fold (λ _ ver acc, max ver acc) 0 m.

  Lemma le_max_iff_nat (x y z : nat) :
    x ≤ Nat.max y z ↔ x ≤ y ∨ x ≤ z.
  Proof.
    split.
    - intros H.
      destruct (le_ge_dec y z) as [Hyz|Hzy].
      + rewrite (Nat.max_r y z) // in H. auto.
      + rewrite (Nat.max_l y z) in H; auto with lia.
    - intros [Hy|Hz].
      + eapply Nat.le_trans; first done. apply Nat.le_max_l.
      + eapply Nat.le_trans; first done. apply Nat.le_max_r.
  Qed.

  Lemma map_max_spec {K} `{Countable K} (m : gmap K nat) k v :
    m !! k = Some v → v ≤ map_max m.
  Proof.
    unfold map_max.
    intros Hlookup.
    induction m using map_first_key_ind.
    - done.
    - rewrite map_fold_insert_first_key //.
      destruct (decide (i = k)) as [<- | Hne].
      + rewrite lookup_insert_eq in Hlookup.
        simplify_eq. rewrite le_max_iff_nat. auto.
      + rewrite lookup_insert_ne // in Hlookup.
        rewrite le_max_iff_nat. auto.
  Qed.

  Lemma index_auth_update (l : gname) γ (index : list gname) :
    index_auth_own γ 1 index ==∗
      index_auth_own γ 1 (index ++ [l]) ∗ index_frag_own γ (length index) l.
  Proof.
    iIntros "H●".
    rewrite /index_auth_own /index_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length index)
          (x := to_agree l).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
      replace (length index) with (O + length (to_agree <$> index)) at 1 
          by (now rewrite length_fmap).
      rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  Lemma index_frag_alloc i l γ index q :
    index !! i = Some l →
      index_auth_own γ q index ==∗
        index_auth_own γ q index ∗ index_frag_own γ i l.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree l]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree l). split; last done.
      rewrite lookup_map_seq_0 list_lookup_fmap Hlookup //. }
    by iFrame.
  Qed.

  Lemma index_frag_alloc' i l γ index q :
    index !! i = Some l →
      index_auth_own γ q index ==∗ index_frag_own γ i l.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree l]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree l). split; last done.
      rewrite lookup_map_seq_0 list_lookup_fmap Hlookup //. }
    by iFrame.
  Qed.

  Lemma validated_auth_update (l : gname) (γ : gname) (validated : gset gname) :
    validated_auth_own γ 1 validated ==∗
      validated_auth_own γ 1 ({[ l ]} ∪ validated) ∗ validated_frag_own γ l.
  Proof using DISJN.
    iIntros "H●".
    (* rewrite /validated_auth_own /log_frag_own. *)
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply (gset_local_update _ _ ({[ l ]} ∪ validated)). set_solver. }
    iFrame. iModIntro.
    rewrite /validated_frag_own.
    iPoseProof (own_mono with "H◯") as "H"; last done.
    apply auth_frag_mono. set_solver.
  Qed.

  Lemma validated_auth_frag_alloc (l : gname) (γ : gname) (q : Qp) (validated : gset gname) :
    l ∈ validated →
      validated_auth_own γ q validated ==∗ validated_auth_own γ q validated ∗ validated_frag_own γ l.
  Proof using DISJN.
    iIntros (Hfresh) "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply (auth_update_dfrac_alloc _ _ {[ l ]}). set_solver. }
    by iFrame.
  Qed.

  Lemma validated_auth_frag_alloc' (l : gname) (γ : gname) (q : Qp) (validated : gset gname) :
      validated_auth_own γ q validated ==∗ validated_auth_own γ q validated ∗ if bool_decide (l ∈ validated) then validated_frag_own γ l else True.
  Proof using DISJN.
    iIntros "H●".
    destruct (decide (l ∈ validated)).
    - iMod (own_update with "H●") as "[H● H◯]".
      { apply (auth_update_dfrac_alloc _ _ {[ l ]}). set_solver. }
      rewrite bool_decide_eq_true_2 //.
      by iFrame.
    - rewrite bool_decide_eq_false_2 //.
      by iFrame.
  Qed.

  Lemma validated_auth_frag_dup (γ : gname) (q : Qp) (validated : gset gname) :
    validated_auth_own γ q validated ==∗ validated_auth_own γ q validated ∗ own γ (◯ validated).
  Proof using DISJN.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := validated).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma validated_auth_frag_agree γ dq l validated :
    validated_auth_own γ dq validated -∗
      validated_frag_own γ l -∗
        ⌜l ∈ validated⌝.
  Proof using DISJN.
    iIntros "●H ◯H".
    iCombine "●H ◯H" gives %(_ & H & _)%auth_both_dfrac_valid_discrete.
    set_solver.
  Qed.

  (* Lemma validated_auth_alloc_empty : |==> ∃ γ, validated_auth_own γ 1 ∅)%I. *)

  Lemma log_auth_update (l : gname) (value : list val) (γₕ : gname) (log : gmap gname (list val)) :
    log !! l = None →
      log_auth_own γₕ 1 log ==∗
        log_auth_own γₕ 1 (<[l := value]>log) ∗ log_frag_own γₕ l value.
  Proof.
    iIntros (Hfresh) "H●".
    rewrite /log_auth_own /log_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := l)
          (x := to_agree value).
      { by rewrite lookup_fmap fmap_None. }
      constructor. }
    rewrite fmap_insert.
    by iFrame.
  Qed.

  Lemma abstraction_auth_update (γ_l : gname) (l : blk) (γₕ : gname) (abstraction : gmap gname blk) :
    abstraction !! γ_l = None →
      abstraction_auth_own γₕ 1 abstraction ==∗
        abstraction_auth_own γₕ 1 (<[γ_l := l]>abstraction) ∗ abstraction_frag_own γₕ γ_l l.
  Proof.
    iIntros (Hfresh) "H●".
    rewrite /log_auth_own /log_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := γ_l)
          (x := to_agree l).
      { by rewrite lookup_fmap fmap_None. }
      constructor. }
    rewrite -fmap_insert.
    by iFrame.
  Qed.

  Lemma vers_auth_update (l : gname) (ver : nat) (γ : gname) (log : gmap gname nat) :
    log !! l = None →
      vers_auth_own γ 1 log ==∗
        vers_auth_own γ 1 (<[l := ver]>log) ∗ vers_frag_own γ l ver.
  Proof.
    iIntros (Hfresh) "H●".
    rewrite /log_auth_own /log_frag_own.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := l)
          (x := to_agree ver).
      { by rewrite lookup_fmap fmap_None. }
      constructor. }
    rewrite -fmap_insert.
    by iFrame.
  Qed.

  Lemma vers_frag_alloc_singleton vers l i γ q :
    vers !! l = Some i →
      vers_auth_own γ q vers ==∗
        vers_auth_own γ q vers ∗ vers_frag_own γ l i.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[ l := to_agree i ]}).
      { apply _. }
      apply singleton_included_l with (i := l).
      exists (to_agree i). split; last done.
      rewrite lookup_fmap Hlookup //.
    }
    by iFrame.
  Qed.

  Lemma log_frag_alloc i value γₕ log q :
    log !! i = Some value →
      log_auth_own γₕ q log ==∗
        log_auth_own γₕ q log ∗ log_frag_own γₕ i value.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[i := to_agree value]}).
      { apply _. }
      apply singleton_included_l with (i := i).
      exists (to_agree value). split; last done.
      rewrite lookup_fmap Hlookup //.
    }
    by iFrame.
  Qed.

  Lemma abstraction_frag_alloc γ_l l γ q abstraction :
    abstraction !! γ_l = Some l →
      abstraction_auth_own γ q abstraction ==∗
        abstraction_auth_own γ q abstraction ∗ abstraction_frag_own γ γ_l l.
  Proof.
    iIntros (Hlookup) "Hauth".
    iMod (own_update with "Hauth") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := {[γ_l := to_agree l]}).
      { apply _. }
      apply singleton_included_l.
      exists (to_agree l). split; last done.
      rewrite lookup_fmap Hlookup //.
    }
    by iFrame.
  Qed.

  Lemma log_auth_frag_agree γₕ q log i value : 
    log_auth_own γₕ q log -∗
      log_frag_own γₕ i value -∗
        ⌜log !! i = Some value⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -lookup_fmap /= Hvs'' //.
  Qed.

  Lemma abstraction_auth_frag_agree γ q abs γ_backup backup : 
    abstraction_auth_own γ q abs -∗
      abstraction_frag_own γ γ_backup backup -∗
        ⌜abs !! γ_backup = Some backup⌝.
  Proof using DISJN.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -lookup_fmap /= Hvs'' //.
  Qed.

  Lemma history_log_frag_agree γₕ γ_abs q log abs γ_l value :
    history γₕ γ_abs q log abs -∗ log_frag_own γₕ γ_l value -∗ ⌜log !! γ_l = Some value⌝.
  Proof. iIntros "[Hl _] Hf". iApply (log_auth_frag_agree with "Hl Hf"). Qed.

  Lemma history_abs_frag_agree γₕ γ_abs q log abs γ_l l :
    history γₕ γ_abs q log abs -∗ abstraction_frag_own γ_abs γ_l l -∗ ⌜abs !! γ_l = Some l⌝.
  Proof using DISJN. iIntros "[_ Ha] Hf". iApply (abstraction_auth_frag_agree with "Ha Hf"). Qed.

  Lemma history_log_frag_alloc γ_l value γₕ γ_abs q log abs :
    log !! γ_l = Some value →
    history γₕ γ_abs q log abs ==∗ history γₕ γ_abs q log abs ∗ log_frag_own γₕ γ_l value.
  Proof. iIntros (?) "[Hl $]". by iApply log_frag_alloc. Qed.

  Lemma history_abs_frag_alloc γ_l l γₕ γ_abs q log abs :
    abs !! γ_l = Some l →
    history γₕ γ_abs q log abs ==∗ history γₕ γ_abs q log abs ∗ abstraction_frag_own γ_abs γ_l l.
  Proof. iIntros (?) "[$ Ha]". by iApply abstraction_frag_alloc. Qed.

  Lemma history_halves γₕ γ_abs log abs :
    history γₕ γ_abs (1/2) log abs -∗ history γₕ γ_abs (1/2) log abs -∗ history γₕ γ_abs 1 log abs.
  Proof.
    rewrite /history. iIntros "[Hl Ha] [Hl' Ha']".
    iSplitL "Hl Hl'"; [iCombine "Hl Hl'" as "$" | iCombine "Ha Ha'" as "$"].
  Qed.

  (** Record a new backup [γ_l] (with value [value] and physical block [l]). *)
  Lemma history_insert γ_l value l γₕ γ_abs log abs :
    log !! γ_l = None → abs !! γ_l = None →
    history γₕ γ_abs 1 log abs ==∗
      history γₕ γ_abs (1/2) (<[γ_l:=value]> log) (<[γ_l:=l]> abs) ∗
      history γₕ γ_abs (1/2) (<[γ_l:=value]> log) (<[γ_l:=l]> abs) ∗
      log_frag_own γₕ γ_l value ∗ abstraction_frag_own γ_abs γ_l l.
  Proof.
    rewrite /history. iIntros (Hlog Habs) "[Hl Ha]".
    iMod (log_auth_update with "Hl") as "[[$ $] $]"; first done.
    by iMod (abstraction_auth_update with "Ha") as "[[$ $] $]".
  Qed.

  Lemma index_auth_frag_agree (γ : gname) (i : nat) (l : gname) (index : list gname) (q : Qp) : 
    index_auth_own γ q index -∗
      index_frag_own γ i l -∗
        ⌜index !! i = Some l⌝.
  Proof using DISJN.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -list_lookup_fmap /= -lookup_map_seq_0 Hvs'' //.
  Qed.

  Lemma prefix_lookup {A} (xs ys : list A) :
    (∀ i x, xs !! i = Some x → ys !! i = Some x) → xs `prefix_of` ys.
  Proof.
    rewrite /prefix. generalize dependent ys.
    induction xs as [| x xs IH].
    - eauto.
    - intros ys Hpoint. simpl.
      destruct ys as [| y ys].
      { specialize (Hpoint 0 x). intuition. discriminate. }
      epose proof (IH ys _) as [ys' ->]. Unshelve.
      + specialize (Hpoint 0 x). simpl in *.
        intuition. simplify_eq. eauto.
      + intros i x' Hlookup.
        specialize (Hpoint (S i) x').
        auto.
  Qed.

  Lemma map_seq_0_included {A} (l l' : list A) :
    map_seq (M := gmap nat A) O l ⊆ map_seq O l' →
      l `prefix_of` l'.
  Proof.
    intros Hincl.
    rewrite map_subseteq_spec in Hincl.
    apply prefix_lookup.
    intros i x.
    do 2 rewrite -lookup_map_seq_0.
    apply Hincl.
  Qed.

  Lemma fmap_to_agree_included_subseteq (m m' : gmap gname (gname * list val)) :
          (to_agree <$> m) ≼ (to_agree <$> m') → m ⊆ m'.
  Proof.
    intros Hincl. apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_included in Hincl.
    specialize (Hincl i).
    do 2 rewrite lookup_fmap in Hincl.
    rewrite Hix /= in Hincl.
    apply Some_included_is_Some in Hincl as H.
    destruct H as [y Hsome].
    rewrite Hsome Some_included_total in Hincl.
    rewrite -lookup_fmap lookup_fmap_Some in Hsome.
    destruct Hsome as (x' & <- & Hix').
    by apply to_agree_included, leibniz_equiv in Hincl as <-.
  Qed.

  Lemma fmap_to_agree_included_subseteq' (m m' : gmap gname nat) :
          (to_agree <$> m) ≼ (to_agree <$> m') → m ⊆ m'.
  Proof.
    intros Hincl. apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_included in Hincl.
    specialize (Hincl i).
    do 2 rewrite lookup_fmap in Hincl.
    rewrite Hix /= in Hincl.
    apply Some_included_is_Some in Hincl as H.
    destruct H as [y Hsome].
    rewrite Hsome Some_included_total in Hincl.
    rewrite -lookup_fmap lookup_fmap_Some in Hsome.
    destruct Hsome as (x' & <- & Hix').
    by apply to_agree_included, leibniz_equiv in Hincl as <-.
  Qed.

  Lemma fmap_to_agree_included_subseteq'' (m m' : gmap nat gname) :
          (to_agree <$> m) ≼ (to_agree <$> m') → m ⊆ m'.
  Proof.
    intros Hincl. apply map_subseteq_spec.
    intros i x Hix.
    rewrite lookup_included in Hincl.
    specialize (Hincl i).
    do 2 rewrite lookup_fmap in Hincl.
    rewrite Hix /= in Hincl.
    apply Some_included_is_Some in Hincl as H.
    destruct H as [y Hsome].
    rewrite Hsome Some_included_total in Hincl.
    rewrite -lookup_fmap lookup_fmap_Some in Hsome.
    destruct Hsome as (x' & <- & Hix').
    by apply to_agree_included, leibniz_equiv in Hincl as <-.
  Qed.

  Lemma index_auth_frag_agree' (γ : gname) (q : Qp) (index index' : list gname) : 
    index_auth_own γ q index -∗
      index_frag_own' γ index' -∗
        ⌜index' `prefix_of` index⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & Hvalid & _)%auth_both_dfrac_valid_discrete.
    iPureIntro.
    apply map_seq_0_included, fmap_to_agree_included_subseteq''.
    by repeat rewrite fmap_map_seq.
  Qed.

  Definition registry γᵣ (requests : list (gname * gname * gname)) :=
    own γᵣ (● map_seq O (to_agree <$> requests)).

  (* Fragmental ownership over a single request *)
  Definition registered γᵣ i (γₗ γₑ l : gname) :=
   own γᵣ (◯ ({[i := to_agree (γₗ, γₑ, l)]})).

  Lemma registry_update γₗ γₑ l γ requests : 
    registry γ requests ==∗ 
      registry γ (requests ++ [(γₗ, γₑ, l)]) ∗ registered γ (length requests) γₗ γₑ l.
  Proof.
    iIntros "H●".
    rewrite /registry /registered.
    iMod (own_update with "H●") as "[H● H◯]".
    { eapply auth_update_alloc.
      apply alloc_singleton_local_update 
        with 
          (i := length requests)
          (x := to_agree (γₗ, γₑ, l)).
      { rewrite lookup_map_seq_None length_fmap. by right. }
      constructor. }
    replace (length requests) with (O + length (to_agree <$> requests)) at 1 
          by (now rewrite length_fmap).
    rewrite -map_seq_snoc fmap_snoc. by iFrame.
  Qed.

  (* The authoritative view of the request registry must agree with its fragment *)
  Lemma registry_agree γᵣ (requests : list (gname * gname * gname)) (i : nat) γₗ γₑ ver :
    registry γᵣ requests -∗
      registered γᵣ i γₗ γₑ ver -∗
        ⌜requests !! i = Some (γₗ, γₑ, ver)⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -list_lookup_fmap /= -lookup_map_seq_0 Hvs'' //.
  Qed.

  Definition log_tokens (γs : gset gname) : iProp Σ :=
    [∗ set] γ ∈ γs, token γ.

  Definition node actual (_ : blk) (lv : list val) (_ : gname) : iProp Σ := ⌜lv = actual⌝.

  (** Pure facts of the read invariant, grouped by what they are about. *)

  (** Every value has the right size and is unboxed. *)
  Record read_sizes (len : nat) (actual cache : list val) (log : gmap gname (list val)) : Prop := {
    (* Every value of CachedWF is unboxed *)
    read_sizes_unboxed : Forall val_is_unboxed actual;
    (* Big atomic is of fixed size *)
    read_sizes_actual : length actual = len;
    read_sizes_cache : length cache = len;
    (* Every logged value is of correct length *)
    read_sizes_log : map_Forall (λ _ value, length value = len) log;
  }.

  (** The index maps every version to a logged backup. *)
  Record read_index_wf (ver : nat) (index : list gname) (log : gmap gname (list val)) (γ_backup' : gname) : Prop := {
    (* The most recent version is associated with some other backup pointer *)
    read_index_last : last index = Some γ_backup';
    (* The is a mapping in the index for every version *)
    read_index_length : length index = S (Nat.div2 (S ver));
    (* Because the mapping from versions to log entries is injective, the index should not contain duplicates *)
    read_index_nodup : NoDup index;
    (* Moreover, every index should be less than the length of the log (to ensure every version
       corresponds to a valid entry) *)
    read_index_logged : Forall (.∈ dom log) index;
  }.

  (** The installed backup (and the backup of the latest version) are logged and
      abstracted consistently. *)
  Record read_backup_wf (log : gmap gname (list val)) (abstraction : gmap gname blk) (actual : list val)
      (γ_backup γ_backup' : gname) (backup backup' : blk) : Prop := {
    (* The last item in the log corresponds to the currently installed backup pointer *)
    read_backup_logged : log !! γ_backup = Some actual;
    read_backup_abs : abstraction !! γ_backup = Some backup;
    read_backup_abs' : abstraction !! γ_backup' = Some backup';
    read_backup_dom : dom log = dom abstraction;
  }.

  (** The tag bit, the cache, and the set of validated backups agree. *)
  Record read_valid_wf (t ver : nat) (actual cache : list val) (γ_backup γ_backup' : gname)
      (log : gmap gname (list val)) (validated : gset gname) : Prop := {
    (* If the backup is validated, then the cache is unlocked, the logical state is equal to the cache,
       and the backup pointer corresponding to the most recent version is up to date *)
    read_valid_tag : if bool_decide (t = 0) then Nat.Even ver ∧ actual = cache ∧ γ_backup = γ_backup' else t = 1;
    (* If the version is even, the the value of the backup corresponding to the
       stores the cache. Otherwise it must not be valid *)
    read_valid_cache : if Nat.even ver then log !! γ_backup' = Some cache else t = 1;
    (* The backup pointer is in the set of validated pointer iff it has actually been validated *)
    read_valid_iff : γ_backup ∈ validated ↔ t = 0;
    (* All pointers validated have also been logged *)
    read_valid_logged : validated ⊆ dom log;
  }.

  Definition read_inv (γ γᵥ γₕ γᵢ γ_val γz γ_abs : gname) (l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (log : gmap gname (list val)) (abstraction : gmap gname blk) (actual cache : list val) (γ_backup γ_backup' : gname) (backup backup' : blk) (index : list gname) (validated : gset gname) (t : nat),
      (* Physical state of version *)
      (l +ₗ version_off) ↦ #ver ∗
      (* backup, consisting of boolean to indicate whether cache is valid, and the backup pointer itself *)
      (l +ₗ backup_off) ↦{# 1/2} #(Some (Loc.blk_to_loc backup) &ₜ t) ∗
      (* Half ownership of logical state *)
      ghost_var_frac γ (1/4) (γ_backup, actual) ∗
      (* Shared read ownership of backup using node predicate *)
      hazptr.(Managed) γz backup γ_backup len (node actual) ∗
      (* For every pair of (backup', cache') in the log, we have ownership of the corresponding points-to *)
      log_tokens (dom log) ∗
      (* Half of the history (log and abstraction), the other half is in the main invariant *)
      history γₕ γ_abs (1/2) log abstraction ∗
      (* Ownership of at least half of the index *)
      index_auth_own γᵢ (1/4) index ∗
      (* Ownership of at least half of the counter *)
      mono_nat_auth_own_frac γᵥ (1/4) ver ∗
      (* Ownership of at least half of the physical state of the cache *)
      (l +ₗ cache_off) ↦∗{# 1/2} cache ∗
      (* If the version is even, we have full ownership of index and logical state of version *)
      (if Nat.even ver then index_auth_own γᵢ (1/4) index ∗ mono_nat_auth_own_frac γᵥ (1/4) ver ∗(l +ₗ cache_off) ↦∗{# 1/2} cache else True) ∗
      (* Auth ownership of all pointers that have been validated *)
      validated_auth_own γ_val 1 validated ∗
      ⌜read_sizes len actual cache log⌝ ∗
      ⌜read_index_wf ver index log γ_backup'⌝ ∗
      ⌜read_backup_wf log abstraction actual γ_backup γ_backup' backup backup'⌝ ∗
      ⌜read_valid_wf t ver actual cache γ_backup γ_backup' log validated⌝.

  Definition AU_cas (Φ : val → iProp Σ) γ (expected desired : list val) (lexp ldes : loc) dq dq' pvs : iProp Σ :=
       AU <{ ∃∃ actual, CachedWF γ actual }>
            @ ⊤ ∖ (↑mainN ∪ ↑readN ∪ ↑casN ∪ ↑ptrsN hazptrN), ↑mgmtN hazptrN
          <{ if bool_decide (actual = expected) then CachedWF γ desired ∗ ⌜expected = desired ∨ cas_succ_res pvs⌝ else CachedWF γ actual,
             COMM lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired -∗ Φ #(bool_decide (actual = expected)) }>.

  (** The private postcondition of CAS, with the prophecy it was given. *)
  Definition cas_post (Φ : val → iProp Σ) (p : proph_id) (pvs : list (val * val)) : val → iProp Σ :=
    λ v, ((∃ pvs', proph p pvs' ∗ ⌜v = #true ∨ ∃ rs, Forall cas_failed_res rs ∧ pvs = rs ++ pvs'⌝) -∗ Φ v)%I.

  Lemma AU_cas_intro Φ γ expected desired lexp ldes dq dq' p pvs :
    AU <{ ∃∃ actual, CachedWF γ actual }>
         @ ⊤ ∖ (↑mainN ∪ ↑readN ∪ ↑casN ∪ ↑ptrsN hazptrN), ↑mgmtN hazptrN
       <{ if bool_decide (actual = expected) then CachedWF γ desired ∗ ⌜expected = desired ∨ cas_succ_res pvs⌝ else CachedWF γ actual,
          COMM lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired ∗
            (∃ pvs', proph p pvs' ∗ ⌜actual = expected ∨ ∃ rs, Forall cas_failed_res rs ∧ pvs = rs ++ pvs'⌝) -∗
            Φ #(bool_decide (actual = expected)) }> -∗
    AU_cas (cas_post Φ p pvs) γ expected desired lexp ldes dq dq' pvs.
  Proof.
    iIntros "AU". rewrite /AU_cas. iAuIntro.
    iApply (aacc_aupd with "AU"); first done.
    iIntros (actual) "Hγ". iAaccIntro with "Hγ".
    { iIntros "Hγ !>". iFrame. by iIntros "$ !>". }
    iIntros "Hβ !>". iRight. iFrame "Hβ". rewrite /cas_post.
    iIntros "HΦ !> [Hlexp Hldes] (%pvs' & Hp & %Hpvs)". iApply ("HΦ" with "[$Hlexp $Hldes $Hp]").
    iPureIntro. destruct Hpvs as [Heq | ?]; last by right.
    left. case_bool_decide; simplify_eq; done.
  Qed.

  Lemma cas_post_true Φ p pvs pvs' : proph p pvs' -∗ cas_post Φ p pvs #true -∗ Φ #true.
  Proof. iIntros "Hp HΦ". iApply "HΦ". iFrame. by iLeft. Qed.

  Lemma cas_post_false Φ p pvs pvs' rs :
    pvs = rs ++ pvs' → Forall cas_failed_res rs →
    proph p pvs' -∗ cas_post Φ p pvs #false -∗ Φ #false.
  Proof. iIntros (??) "Hp HΦ". iApply "HΦ". iFrame. iPureIntro. right. eauto. Qed.

  Ltac solve_failed_res := repeat (constructor; first by eexists _, _); constructor.

  Definition cas_inv (Φ : val → iProp Σ) (γ γₑ γₗ γₜ γ_exp γd : gname) (lexp : blk) (lexp_src ldes : loc) (dq dq' : dfrac) (expected desired : list val) s (pvs : list (val * val)) : iProp Σ :=
    (hazptr.(Shield) γd s (Validated lexp γ_exp (node expected) (length expected)) ∗
      ((£ 1 ∗ (lexp_src ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired -∗ Φ #false) ∗ (∃ b : bool, ghost_var_frac γₑ (1/2) b) ∗ ghost_var_frac γₗ (1/2) false) (* The failing write has already been linearized and its atomic update has been consumed *)
    ∨ (£ 2 ∗ AU_cas Φ γ expected desired lexp_src ldes dq dq' pvs ∗ ghost_var_frac γₑ (1/2) true ∗ ghost_var_frac γₗ (1/2) true)))
    ∨ (token γₜ ∗ (∃ b : bool, ghost_var_frac γₑ (1/2) b) ∗ ∃ b : bool, ghost_var_frac γₗ (1/2) b).  (* The failing write has linearized and returned *)

  Lemma log_tokens_impl log l :
    l ∈ log → log_tokens log -∗ token l.
  Proof.
    iIntros (Hbound) "Hlog".
    iPoseProof (big_sepS_elem_of with "Hlog") as "H /=".
    { done. }
    done. 
  Qed.

  Lemma log_tokens_singleton l :
    log_tokens {[ l ]} ⊣⊢ token l.
  Proof.
    rewrite /log_tokens big_sepS_singleton //.
  Qed.

  Definition request_inv (γ γₗ γₑ γ_exp γd : gname) (lactual : blk) (actual : list val) (abstraction : gmap gname blk) : iProp Σ :=
    ∃ lexp, ⌜abstraction !! γ_exp = Some lexp⌝ ∗
      ghost_var_frac γₗ (1/2) (bool_decide (lactual = lexp)) ∗
      (* Note that the [lexp] bound here points to a copy of the expected value *)
      ∃ (Φ : val → iProp Σ) (γₜ : gname) (lexp_src ldes : loc) (dq dq' : dfrac) (expected desired : list val) s pvs,
        ghost_var_frac γₑ (1/2) (bool_decide (actual = expected)) ∗
        inv casN (cas_inv Φ γ γₑ γₗ γₜ γ_exp γd lexp lexp_src ldes dq dq' expected desired s pvs).

  Definition registry_inv γ γd lactual actual (requests : list (gname * gname * gname)) (abstraction : gmap gname blk) : iProp Σ :=
    [∗ list] '(γₗ, γₑ, γ_exp) ∈ requests,
      request_inv γ γₗ γₑ γ_exp γd lactual actual abstraction.

  Lemma registry_inv_mono γ γd lactual actual requests (abstraction abstraction' : gmap gname blk) : 
    abstraction ⊆ abstraction' →
      registry_inv γ γd lactual actual requests abstraction -∗
        registry_inv γ γd lactual actual requests abstraction'.
  Proof.
    iIntros (Hsub) "Hreginv".
    iInduction requests as [|[[γₗ γₑ] lexp] requests] "IH".
    - done.
    - rewrite /registry_inv /=.
      iDestruct "Hreginv" as "[Hreqinv Hreginv]".
      iPoseProof ("IH" with "Hreginv") as "$".
      rewrite /request_inv.
      iDestruct "Hreqinv" as "(%lexp' & %Hγ_exp & Hlin & $)".
      iFrame. iPureIntro.
      by eapply map_subseteq_spec.
  Qed.

  Lemma array_frac_add l dq dq' vs vs' : length vs = length vs' → l ↦∗{dq} vs -∗ l ↦∗{dq'} vs' -∗ l ↦∗{dq ⋅ dq'} vs ∗ ⌜vs = vs'⌝.
  Proof.
    iIntros (Hlen) "Hl Hl'".
    iInduction vs as [|v vs] "IH" forall (l vs' Hlen).
    - symmetry in Hlen. rewrite length_zero_iff_nil in Hlen. simplify_list_eq. by iSplit.
    - destruct vs' as [|v' vs']; simplify_list_eq.
      repeat rewrite array_cons.
      iDestruct "Hl" as "[Hl Hls]".
      iDestruct "Hl'" as "[Hl' Hls']".
      iPoseProof (pointsto_combine with "Hl Hl'") as "[Hl ->]".
      iFrame.
      iPoseProof ("IH" with "[//] [$] [$]") as "[Hl <-]".
      by iFrame.
  Qed.

  Lemma array_pointsto_valid l dq vs : length vs > 0 → l ↦∗{dq} vs -∗ ⌜✓ dq⌝.
  Proof.
    iIntros (Hpos) "Hl".
    destruct vs as [|v vs].
    { inv Hpos. }
    rewrite array_cons.
    iDestruct "Hl" as "[Hl _]".
    iApply (pointsto_valid with "Hl").
  Qed.

  Lemma array_pointsto_pointsto_persist l vs vs' :
    length vs = length vs' → length vs > 0 → 
      l ↦∗ vs -∗ l ↦∗□ vs' -∗ False.
  Proof.
    iIntros (Hlensame Hlenpos) "Hl Hl'".
    iPoseProof (array_frac_add with "Hl Hl'") as "[Hl %HJ]".
    { done. }
    by iDestruct (array_pointsto_valid with "Hl") as %Hvalid.
  Qed.

  Definition gmap_injective {K A} `{Countable K} (m : gmap K A) :=
    ∀ i j v, m !! i = Some v → m !! j = Some v → i = j.

  Definition gmap_mono `{Countable K} (order : gmap K nat) (k k' : K) :=
    ∀ i j, 
      order !! k = Some i → 
        order !! k' = Some j →
          i < j.

  Lemma gmap_mono_alloc `{Countable K} (l : K) (i : nat) (order : gmap K nat) (index : list K) :
    l ∉ index →
      StronglySorted (gmap_mono order) index →
        StronglySorted (gmap_mono (<[l := i]>order)) index.
  Proof.
    induction index as [|loc' index IH].
    - intros. constructor.
    - intros [Hne Hnmem]%not_elem_of_cons Hsorted.
      inv Hsorted.
      constructor.
      + auto.
      + clear IH.
        induction index as [| loc'' index IH'].
        * constructor.
        * inv H2. inv H3. rewrite not_elem_of_cons in Hnmem.
          destruct Hnmem as [Hne' Hnmem].
          constructor.
          { rewrite /gmap_mono.
            intros j k.
            do 2 rewrite lookup_insert_ne //. auto. }
          { auto. }
  Qed.

  Lemma StronglySorted_subseteq `{Countable K} (order order' : gmap K nat) (index : list K) :
    order ⊆ order' →
      Forall (.∈ dom order) index →
        StronglySorted (gmap_mono order) index →
          StronglySorted (gmap_mono order') index.
  Proof.
    intros Hsub Hdom Hssorted.
    induction index as [| l index IH].
    - constructor.
    - inv Hdom. inv Hssorted. constructor.
      + auto.
      + clear IH.
        induction index as [| l' index IH].
        * constructor.
        * inv H4. inv H3. inv H5.
          constructor.
          { intros i j Hi Hj.
            apply elem_of_dom in H2 as [i' Hi'].
            apply elem_of_dom in H4 as [j' Hj'].
            rewrite map_subseteq_spec in Hsub.
            apply Hsub in Hi' as Hi''.
            apply Hsub in Hj' as Hj''.
            simplify_eq. auto. }
          { auto. }
  Qed.

  Lemma StronglySorted_impl {A} (Q R : A → A → Prop) (l : list A) :
    (∀ x y, Q x y → R x y) →
      StronglySorted Q l →
        StronglySorted R l.
  Proof.
    intros Hweak Hsorted.
    induction Hsorted.
    - constructor.
    - constructor.
      + done.
      + eapply Forall_impl; eauto.
  Qed. 

  Lemma StronglySorted_snoc {A} (R : A → A → Prop) (xs : list A) (y : A) :
    StronglySorted R xs →
      Forall (λ x, R x y) xs →
        StronglySorted R (xs ++ [y]).
  Proof.
    induction xs as [|x xs IH]; intros Hssorted Hord.
    - repeat constructor.
    - inv Hssorted. inv Hord. simpl. constructor.
      + by apply IH.
      + rewrite Forall_app; auto.
  Qed.

  (** Pure facts of the main invariant, grouped by what they are about. *)

  (** The installed backup is logged and abstracted. *)
  Record main_backup_wf (log : gmap gname (list val)) (abstraction : gmap gname blk)
      (actual : list val) (γ_backup : gname) (backup : blk) : Prop := {
    main_backup_logged : log !! γ_backup = Some actual;
    main_backup_abs : abstraction !! γ_backup = Some backup;
  }.

  (** The history map tracks which versions have been published. *)
  Record main_vers_wf (log : gmap gname (list val)) (vers : gmap gname nat)
      (γ_backup : gname) (ver t : nat) : Prop := {
    main_vers_dom : dom vers ⊂ dom log;
    main_vers_latest :
      if bool_decide (1 < size log) then
        (∃ ver',
          vers !! γ_backup = Some ver' ∧
          ver' ≤ ver ∧
          map_Forall (λ _ ver'', ver'' ≤ ver') vers ∧
          if bool_decide (ver = ver') then t ≠ 0 else True)
      else vers = ∅;
  }.

  (** The logical ordering of backups. *)
  Record main_order_wf (log : gmap gname (list val)) (order : gmap gname nat)
      (index : list gname) (γ_backup : gname) (idx : nat) : Prop := {
    main_order_dom : dom order = dom log;
    main_order_inj : gmap_injective order;
    main_order_backup : order !! γ_backup = Some idx;
    main_order_index : StronglySorted (gmap_mono order) index;
    main_order_max : map_Forall (λ _ idx', idx' ≤ idx) order;
  }.

  Definition cached_wf_inv (γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ γ_abs γd : gname) (l : loc) (len : nat) : iProp Σ :=
    ∃ (ver : nat) (log : gmap gname (list val)) (abstraction : gmap gname blk)
      (actual : list val) (γ_backup : gname)
      (backup : blk) (requests : list (gname * gname * gname))
      (vers : gmap gname nat) (index : list gname) (order : gmap gname nat) (idx : nat) (t : nat),
      (* Ownership of remaining quarter of logical counter *)
      mono_nat_auth_own_frac γᵥ (1/2) ver ∗
      (* Ownership of the backup location (stored with a tag bit) *)
      (l +ₗ backup_off) ↦{# 1/2} #(Some (Loc.blk_to_loc backup) &ₜ t) ∗
      (* Ownership of the logical state (remaining quarter) *)
      ghost_var_frac γ (1/4) (γ_backup, actual) ∗
      (* Other half of the history, shared with the read invariant *)
      history γₕ γ_abs (1/2) log abstraction ∗
      (* Ownership of request registry *)
      registry γᵣ requests ∗
      (* State of request registry against the current abstraction *)
      registry_inv γ γd backup actual requests abstraction ∗
      (* Authoritative ownership of version mapping *)
      vers_auth_own γ_vers 1 vers ∗
      (* Own other half of index *)
      index_auth_own γᵢ (1/2) index ∗
      (* Authoritative ownership of the logical ordering *)
      vers_auth_own γₒ 1 order ∗
      ⌜main_backup_wf log abstraction actual γ_backup backup⌝ ∗
      ⌜main_vers_wf log vers γ_backup ver t⌝ ∗
      ⌜main_order_wf log order index γ_backup idx⌝.

  Global Instance pointsto_array_persistent l vs : Persistent (l ↦∗□ vs).
  Proof.
    rewrite /Persistent.
    iIntros "P".
    iInduction vs as [|v vs] "IH" forall (l).
    - rewrite array_nil. by iModIntro.
    - rewrite array_cons.
      iDestruct "P" as "[#Hl Hrest]".
      iPoseProof ("IH" with "Hrest") as "Hvs".
      by iFrame "#".
  Qed.

  Lemma backup_logged `{Countable K} {V} (log : gmap K V) (index : list K) (backup' : K) : Forall (.∈ dom log) index → last index = Some backup' → is_Some (log !! backup').
  Proof.
    rewrite Forall_lookup last_lookup.
    intros Hrange Hindex.
    by eapply elem_of_dom, Hrange.
  Qed.

  Lemma wp_array_copy_to' γ γᵥ γₕ γᵢ γ_val γz γ_abs (dst src : loc) (n i : nat) vdst ver :
    (* Length of destination matches that of source (CachedWF) *)
    i ≤ n → length vdst = n - i →
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ (dst +ₗ i) ↦∗ vdst }}}
            array_copy_to #(dst +ₗ i) #(src +ₗ cache_off +ₗ i) #(n - i)
          {{{ vers vdst', RET #(); 
              (* the destination array contains some values [vdst'] *)
              (dst +ₗ i) ↦∗ vdst' ∗
              ⌜length vdst' = n - i⌝ ∗
              (* Vers is a monotonically increasing list of versions *)
              ⌜StronglySorted Nat.le vers⌝ ∗
              (* Ever version in the list is at least the lower bound *)
              ⌜Forall (Nat.le ver) vers⌝ ∗
              (* For version version [ver'] and value [v] at index [j] *)
              ([∗ list] j ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γᵥ ver' ∗ 
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  (⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ γ_l vs,
                      (* Version [i] is associated with backup [l] *)
                      index_frag_own γᵢ (Nat.div2 ver') γ_l ∗
                      (* Location [l] is associated with value [vs] *)
                      log_frag_own γₕ γ_l vs ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! (i + j)%nat = Some v⌝)) }}}.
  Proof.
    iIntros "%Hle %Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
    iLöb as "IH" forall (i vdst ver Hle Hvdst) "Hlb".
    wp_rec.
    wp_pures.
    case_bool_decide as Hdone.
    - wp_pures.
      assert (i = n)%Z as -> by lia. clear Hdone. simplify_eq/=.
      rewrite Nat.sub_diag length_zero_iff_nil in Hvdst.
      clear Hle. subst.
      iApply ("HΦ" $! [] []). iFrame.
      iModIntro.
      iSplit; first rewrite Nat.sub_diag //.
      by repeat (iSplit; first by iPureIntro; constructor).
    - wp_pures.
      destruct vdst as [| v vdst].
      { simplify_list_eq. lia. }
      clear Hdone. simpl in *. rewrite array_cons.
      iDestruct "Hdst" as "[Hhd Htl]".
      wp_bind (! _)%E. 
      iInv readN as "(%ver' & %log & %abstraction & %actual & %cache & %γ_backup & %γ_backup' & %backup & %backup' & %index & %validated & %t & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes & >%Hidx_wf & >%Hbackup_wf & >%Hvalid_wf)" "Hcl".
      pose proof Hsizes as [Hunboxed Hlenactual Hlencache Hloglen].
      pose proof Hidx_wf as [Hindex Hlenᵢ Hnodup Hrange].
      pose proof Hbackup_wf as [Hlogged Habs_backup Habs_backup' Hdom_eq].
      pose proof Hvalid_wf as [Htag Hcons Hvalidated_iff Hvalidated_sub].
      wp_apply (wp_load_offset with "Hcache").
      { apply list_lookup_lookup_total_lt. lia. }
      iMod (index_frag_alloc with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ]".
      { by rewrite last_lookup Hlenᵢ in Hindex. }
      iIntros "Hsrc".
      iPoseProof (mono_nat_auth_lb_own_valid with "●Hγᵥ Hlb") as "[%Ha %Hord]".
      iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb'".
      eapply backup_logged in Hrange as Hbackup_logged; last done.
      destruct Hbackup_logged as [backup'vs Hbackup'vs].
      iMod (history_log_frag_alloc γ_backup' with "●Hhist") as "[●Hhist #◯Hlog]".
      { done. }
      iMod ("Hcl" with "[-Hhd Htl HΦ]") as "_".
      { iExists ver', log, abstraction, actual, cache, γ_backup, γ_backup', backup, backup', index, validated, t. iFrame_fast. }
      iModIntro.
      wp_store.
      wp_pures.
      rewrite -Z.sub_add_distr.
      do 2 rewrite Loc.add_assoc.
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_add Nat.add_1_r.
      wp_apply ("IH" $! _ vdst ver' with "[] [] [$] [-] [//]").
      { iPureIntro. lia. }
      { iPureIntro. lia. }
      iIntros (vers vdst') "!> (Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
      iApply "HΦ".
      replace (S i) with (i + 1) by lia.
      rewrite Nat2Z.inj_add -Loc.add_assoc.
      iCombine "Hhd Hdst" as "Hdst".
      rewrite -array_cons.
      iFrame. repeat iSplit.
      { iIntros "!% /=". lia. }
      { iPureIntro. by eapply SSorted_cons. }
      { iPureIntro. constructor; first done.
        eapply Forall_impl; eauto. lia. }
      { iSplitR "Hcons".
        - iSplitR; first done.
          iIntros "%Heven'".
          rewrite Nat.Odd_div2; first last.
          { rewrite Nat.Odd_succ //. }
          rewrite -Nat.even_spec in Heven'.
          rewrite Heven' in Hcons.
          iExists γ_backup', _.
          iFrame_fast.
          rewrite Nat.add_0_r.
          rewrite list_lookup_lookup_total_lt //.
          * iPureIntro. do 2 f_equal.
            simpl in *. congruence.
          * rewrite /map_Forall in Hloglen.
            apply Hloglen in Hbackup'vs as ->. lia.
        - rewrite big_sepL2_mono; first done.
          iIntros (k ver''' v') "_ _ H".
          rewrite -Nat.add_1_r -Nat.add_assoc Nat.add_1_r //.  }
  Qed.

  Lemma abstraction_auth_auth_agree γ p q (abs abs' : gmap gname blk) :
    abstraction_auth_own γ p abs -∗
      abstraction_auth_own γ q abs' -∗
        ⌜abs = abs'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply map_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    repeat rewrite -lookup_fmap //.
  Qed.

  Lemma log_auth_auth_agree γₕ p q (log log' : gmap gname (list val)) :
    log_auth_own γₕ p log -∗
      log_auth_own γₕ q log'  -∗
        ⌜log = log'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply map_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    repeat rewrite -lookup_fmap //.
  Qed.

  Lemma history_auth_agree γₕ γ_abs p q log log' abs abs' :
    history γₕ γ_abs p log abs -∗ history γₕ γ_abs q log' abs' -∗ ⌜log = log' ∧ abs = abs'⌝.
  Proof.
    iIntros "[Hl Ha] [Hl' Ha']".
    iDestruct (log_auth_auth_agree with "Hl Hl'") as %->.
    by iDestruct (abstraction_auth_auth_agree with "Ha Ha'") as %->.
  Qed.


  Lemma index_auth_auth_agree γₕ p q (index index' : list gname) :
    index_auth_own γₕ p index -∗
      index_auth_own γₕ q index'  -∗
        ⌜index = index'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply list_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    do 2 rewrite -lookup_map_seq_0 -lookup_fmap fmap_map_seq //.
  Qed.

  Lemma vers_auth_auth_agree γₕ p q (log log' : gmap gname nat) :
    vers_auth_own γₕ p log -∗
      vers_auth_own γₕ q log'  -∗
        ⌜log = log'⌝.
  Proof.
    iIntros "H H'".
    iCombine "H H'" gives %Hagree%auth_auth_dfrac_op_inv.
    iPureIntro.
    apply map_eq.
    intros i.
    apply leibniz_equiv, (inj (fmap to_agree)).
    repeat rewrite -lookup_fmap //.
  Qed.

  Lemma vers_auth_frag_agree γₕ q log i value : 
    vers_auth_own γₕ q log -∗
      vers_frag_own γₕ i value -∗
        ⌜log !! i = Some value⌝.
  Proof.
    iIntros "H● H◯".
    iCombine "H● H◯" gives %(_ & (y & Hlookup & [[=] | (a & b & [=<-] & [=<-] & H)]%option_included_total)%singleton_included_l & Hvalid)%auth_both_dfrac_valid_discrete.
    assert (✓ y) as Hy.
    { by eapply lookup_valid_Some; eauto. }
    pose proof (to_agree_uninj y Hy) as [vs'' Hvs''].
    rewrite -Hvs'' to_agree_included in H. simplify_eq.
    iPureIntro. apply leibniz_equiv, (inj (fmap to_agree)).
    rewrite -lookup_fmap /= Hvs'' //.
  Qed.


  Lemma wp_array_copy_to_wk γ γᵥ γₕ γᵢ γ_val γz γ_abs (dst src : loc) (n : nat) vdst ver :
    (* Length of destination matches that of source (CachedWF) *)
    length vdst = n →
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ dst ↦∗ vdst }}}
            array_copy_to #dst #(src +ₗ cache_off) #n
          {{{ vers vdst', RET #(); 
              (* the destination array contains some values [vdst'] *)
              dst ↦∗ vdst' ∗
              ⌜length vdst' = n⌝ ∗
              (* Vers is a monotonically increasing list of versions *)
              ⌜StronglySorted Nat.le vers⌝ ∗
              (* Ever version in the list is at least the lower bound *)
              ⌜Forall (Nat.le ver) vers⌝ ∗
              (* For version version [ver'] and value [v] at index [j] *)
              ([∗ list] i ↦ ver' ; v ∈ vers ; vdst',
                  mono_nat_lb_own γᵥ ver' ∗ 
                  (* If the version is even, then the value read then was valid, as the lock was unlocked *)
                  (⌜Nat.Even ver'⌝ →
                  (* Then there exists some list of values associated with that version *)
                    ∃ γ_l vs,
                      (* Version [i] is associated with backup [l] *)
                      index_frag_own γᵢ (Nat.div2 ver') γ_l ∗
                      (* Location [l] is associated with value [vs] *)
                      log_frag_own γₕ γ_l vs ∗
                      (* Where the value stored at index [i + j] is exactly [v] *)
                      ⌜vs !! i = Some v⌝ ))}}}.
  Proof.
     iIntros "%Hvdst #Hinv #Hlb !> %Φ Hdst HΦ".
     rewrite -(Loc.add_0 (src +ₗ cache_off)).
     rewrite -(Loc.add_0 dst).
     replace (Z.of_nat n) with (n - 0)%Z by lia.
     change 0%Z with (Z.of_nat O).
     wp_smart_apply (wp_array_copy_to' _ _ _ _ _ _ _ _ _ _ _ vdst _ with "[//] [//] [$] [-]"); try lia.
     iIntros "!> %vers %vdst' /=".
     rewrite Nat.sub_0_r //.
  Qed.


Definition vers_cons γᵥ γₕ γᵢ vers vdst : iProp Σ := 
  [∗ list] i ↦ ver' ; v ∈ vers ; vdst, 
    mono_nat_lb_own γᵥ ver' ∗
    (* If the version is even, then the value read then was valid, as the lock was unlocked *)
    (⌜Nat.Even ver'⌝ →
      (* Then there exists some list of values associated with that version *)
      ∃ γ_l vs,
        (* Version [i] is associated with backup [l] *)
        index_frag_own γᵢ (Nat.div2 ver') γ_l ∗
        (* Location [l] is associated with value [vs] *)
        log_frag_own γₕ γ_l vs ∗
        (* Where the value stored at index [i + j] is exactly [v] *)
        ⌜vs !! i = Some v⌝).

  Lemma wp_array_clone_wk γ γᵥ γₕ γᵢ γ_val γz γ_abs (src : loc) (n : nat) ver :
    n > 0 →
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs src n) -∗
        (* The current version is at least [ver] *)
        mono_nat_lb_own γᵥ ver -∗
          {{{ True }}}
            array_clone #(src +ₗ cache_off) #n
          {{{ vers vdst (dst : blk), RET #dst; 
              (* the destination array contains some values [vdst'] *)
              dst ↦∗ vdst ∗
              ⌜length vdst = n⌝ ∗
              (* Vers is a monotonically increasing list of versions *)
              ⌜StronglySorted Nat.le vers⌝ ∗
              (* Ever version in the list is at least the lower bound *)
              ⌜Forall (Nat.le ver) vers⌝ ∗
              vers_cons γᵥ γₕ γᵢ vers vdst }}}.
  Proof.
    iIntros "%Hpos #Hinv #Hlb %Φ !# _ HΦ".
    rewrite /array_clone.
    wp_pures.
    wp_alloc dst as "Hdst" "†Hdst".
    { lia. }
    wp_pures.
    wp_apply (wp_array_copy_to_wk with "[//] [//] [$Hdst]").
    { rewrite length_replicate. lia. }
    iIntros (vers vdst') "(Hdst & %Hlen & %Hsorted & %Hbound & Hcons)".
    wp_pures.
    iModIntro.
    iApply ("HΦ" with "[$Hdst $Hcons]").
    by iPureIntro.
  Qed.

  Lemma Even_inj n : Z.Even (Z.of_nat n) ↔ Nat.Even n.
  Proof.
    split.
    - intros [k H]. exists (Z.to_nat k). lia.
    - intros [k H]. exists k. lia.
  Qed.

  Lemma Odd_inj n : Nat.Odd n ↔ Z.Odd (Z.of_nat n).
  Proof.
    split.
    - intros [k H]. exists k. lia.
    - intros [k H]. exists (Z.to_nat k). lia.
  Qed.

  Lemma wp_array_copy_to_half' γ γᵥ γₕ γᵢ γ_val γz γ_abs dst src (vs vs' : list val) i n dq :
    i ≤ n → length vs = n - i → length vs = length vs' →
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs dst n) -∗
        {{{ (dst +ₗ cache_off +ₗ i) ↦∗{#1 / 2} vs ∗ (src +ₗ i) ↦∗{dq} vs' }}}
          array_copy_to #(dst +ₗ cache_off +ₗ i) #(src +ₗ i) #(n - i)%nat
        {{{ RET #(); (dst +ₗ cache_off +ₗ i) ↦∗{#1 / 2} vs' ∗ (src +ₗ i) ↦∗{dq} vs' }}}.
  Proof.
    iIntros (Hle Hlen Hmatch) "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    iLöb as "IH" forall (i vs vs' Hlen Hle Hmatch).
    wp_rec.
    wp_pures.
    case_bool_decide.
    - wp_pures.
      simpl in *.
      assert (i = n) as -> by lia.
      rewrite Nat.sub_diag in Hlen.
      rewrite Hlen in Hmatch.
      symmetry in Hmatch.
      rewrite length_zero_iff_nil in Hlen.
      rewrite length_zero_iff_nil in Hmatch.
      subst.
      repeat rewrite array_nil.
      by iApply "HΦ".
    - wp_pures.
      assert (length vs > 0) by lia.
      destruct vs as [| v vs].
      { simplify_list_eq. lia. }
      destruct vs' as [| v' vs']; first simplify_list_eq.
      do 2 rewrite array_cons.
      iDestruct "Hdst" as "[Hdst Hdst']".
      iDestruct "Hsrc" as "[Hsrc Hsrc']".
      wp_load.
      wp_bind (_ <- _)%E.
      iInv readN as "(%ver & %log & %abstraction & %actual & %cache & %γ_backup & %γ_backup' & %backup & %backup' & %index & %validated & %t & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes & >%Hidx_wf & >%Hbackup_wf & >%Hvalid_wf)" "Hcl".
      pose proof Hsizes as [Hunboxed Hlenactual Hlencache Hloglen].
      pose proof Hidx_wf as [Hindex Hlenᵢ Hnodup Hrange].
      pose proof Hbackup_wf as [Hlogged Habs_backup Habs_backup' Hdom_eq].
      pose proof Hvalid_wf as [Htag Hcons Hvalidated_iff Hvalidated_sub].
      assert (i < length cache) as [v'' Hv'']%lookup_lt_is_Some by lia.
      destruct (Nat.even ver) eqn:Heven.
      { iMod "Hlock" as "(Hγᵢ' & Hγᵥ' & Hcache') /=".
        iCombine "Hcache Hcache'" as "Hcache".
        iPoseProof (update_array _ _ _ i v'' with "Hcache") as "[Hcache _]".
        { done. }
        iDestruct (pointsto_combine with "Hdst Hcache") as "[Hdst ->]".
        iDestruct (pointsto_valid with "Hdst") as %[=]%dfrac_valid_own_r. }
      simplify_eq.
      iPoseProof (update_array _ _ _ i v'' with "Hcache") as "[Hcache Hacc]".
      { done. }
      iDestruct (pointsto_combine with "Hdst Hcache") as "[Hcache ->]".
      rewrite dfrac_op_own Qp.half_half.
      wp_store.
      iDestruct "Hcache" as "[Hcache Hcache']".
      iPoseProof ("Hacc" with "Hcache") as "Hcache".
      (* $Hregistry $Hreginv $Hver Hγᵢ Hγᵥ Hcache *)
      simplify_eq.
      iMod ("Hcl" with "[-Hcache' Hdst' Hsrc Hsrc' HΦ]") as "_".
      { iExists ver, log, abstraction, actual, (<[i:=v']>cache), γ_backup, γ_backup', backup, backup', index, validated, 1.
        iFrame_fast.
        rewrite Heven. iFrame.
        iSplit_facts; rewrite ?Heven ?length_insert //. }
      iModIntro.
      wp_pures.
      rewrite -> Nat2Z.inj_sub by done.
      rewrite -Z.sub_add_distr.
      rewrite (Loc.add_assoc (dst +ₗ cache_off)) /=.
      rewrite (Loc.add_assoc src) /=.
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_add Nat.add_comm /=.
      rewrite <- Nat2Z.inj_sub by lia.
      simplify_list_eq.
      wp_apply ("IH" $! (S i) vs vs' with "[] [] [//] [$] [$]").
      * iPureIntro. lia.
      * iPureIntro. lia.
      * iIntros "[Hdst' Hsrc']".
        iApply "HΦ". iFrame.
        rewrite (Loc.add_assoc (dst +ₗ cache_off)) /=.
        change 1%Z with (Z.of_nat 1).
        rewrite -Nat2Z.inj_add Nat.add_comm //=.
  Qed.

  Lemma wp_array_copy_to_half γ γᵥ γₕ γᵢ γ_val γz γ_abs dst src (vs vs' : list val) n dq :
    length vs = n → length vs = length vs' →
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs dst n) -∗
        {{{ (dst +ₗ cache_off) ↦∗{#1 / 2} vs ∗ src ↦∗{dq} vs' }}}
          array_copy_to #(dst +ₗ cache_off) #src #n
        {{{ RET #(); (dst +ₗ cache_off) ↦∗{#1 / 2} vs' ∗ src↦∗ {dq} vs' }}}.
  Proof.
    iIntros (Hlen Hlen') "#Hinv %Φ !> [Hdst Hsrc] HΦ".
    rewrite -(Loc.add_0 (dst +ₗ cache_off)).
    rewrite -(Loc.add_0 src).
    change 0%Z with (Z.of_nat 0).
    rewrite -{2}(Nat.sub_0_r n).
    wp_apply (wp_array_copy_to_half' _ _ _ _ _ _ _ _ _ vs vs' with "[$] [$] [$]").
    - lia.
    - lia.
    - done.
  Qed.

  Lemma even_iff_not_odd n : Nat.Even n ↔ ¬ (Nat.Odd n).
  Proof.
    split.
    - rewrite /not. apply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma odd_iff_not_even n : Nat.Odd n ↔ ¬ (Nat.Even n).
  Proof.
    split.
    - rewrite /not. intros. by eapply Nat.Even_Odd_False.
    - intros Hnotodd. by pose proof Nat.Even_or_Odd n as [Heven | Hodd].
  Qed.

  Lemma div2_def n : Nat.div2 (S (S n)) = S (Nat.div2 n).
  Proof. done. Qed.

  Definition IsCachedWF (γ : gname) (v : val) (n : nat) : iProp Σ :=
    ∃ (dst d : loc) (γₕ γᵥ γᵣ γᵢ γₒ γ_vers γ_val γ_abs γd : gname),
      ⌜n > 0⌝ ∗
      ⌜v = #dst⌝ ∗
      (dst +ₗ domain_off) ↦□ #d ∗ 
      hazptr.(IsHazardDomain) γd d ∗
      inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γd γ_abs dst n) ∗
      inv mainN (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ γ_abs γd dst n).

  Global Instance IsCachedWF_Persistent γ v n : Persistent (IsCachedWF γ v n).
  Proof. apply _. Qed.

  Lemma array_persist l vs : l ↦∗ vs ==∗ l ↦∗□ vs.
  Proof.
    iInduction vs as [| v vs] "IH" forall (l).
    - by iIntros.
    - do 2 rewrite array_cons. iIntros "[Hl Hrest]".
      iSplitL "Hl".
      + iApply (pointsto_persist with "Hl").
      + iApply ("IH" with "Hrest").
  Qed.

  Lemma gmap_injective_singleton `{Countable K} {V} (k : K) (v : V) :
    gmap_injective {[k := v]}.
  Proof.
    rewrite /gmap_injective.
    intros i j v'. do 2 rewrite lookup_singleton_Some.
    by intros [<- <-] [<- _].
  Qed.

Lemma gmap_injective_insert `{Countable K, Countable V} (k : K) (v : V) (m : gmap K V) :
  v ∉ map_img (SA:=gset V) m →
    gmap_injective m →
      gmap_injective (<[k := v]>m).
  Proof.
    rewrite /gmap_injective. intros Hfresh Hinj.
    intros i j v'.
    destruct (decide (i = k)) as [-> | Hne]; destruct (decide (j = k)) as [-> | Hne'].
    - rewrite lookup_insert_eq //.
    - rewrite lookup_insert_eq lookup_insert_ne //.
      intros [=<-] Hmj. by apply not_elem_of_map_img_1 with (i := j) in Hfresh.
    - rewrite lookup_insert_eq lookup_insert_ne //.
      intros Hsome [=<-]. by apply not_elem_of_map_img_1 with (i := i) in Hfresh.
    - do 2 rewrite lookup_insert_ne //. apply Hinj.
  Qed.    

  Lemma cached_wf_new_spec :
      big_atomic_new_spec' cached_wfN hazptrN cached_wf_new hazptr CachedWF IsCachedWF.
  Proof using DISJN.
    iIntros (γd d n src dq vs Hpos Hlen Hunboxed Φ) "[#Hdom Hsrc] HΦ".
    wp_rec.
    wp_pures.
    wp_alloc l as "Hl" "†Hl".
    wp_pures.
    rewrite Nat2Z.id /= array_cons array_cons array_cons.
    iDestruct "Hl" as "(Hversion & Hvalidated & Hdomain & Hcache)".
    rewrite Loc.add_assoc Loc.add_assoc /=.
    change 1%Z with (Z.of_nat 1).
    do 2 rewrite -Nat2Z.inj_add /=.
    change (1 + 1)%Z with 2%Z.
    wp_apply (wp_array_clone with "Hsrc").
    { auto. }
    { lia. }
    iIntros (backup) "(Hsrc & Hbackup & †Hbackup)".
    wp_store. wp_store.
    (* rewrite -{5}(length_replicate (length vs) #0). *)
    wp_smart_apply (wp_array_copy_to with "[$Hcache $Hsrc]").
    { rewrite length_replicate //. }
    { done. }
    iIntros "[[Hcache Hcache'] Hsrc]".
    iMod token_alloc as "[%γ_backup Hγ_backup]".
    iMod (ghost_var_alloc (γ_backup, vs)) as "(%γ & Hγ & Hγ' & Hγ'')".
    iMod (mono_nat_own_alloc 0) as "(%γᵥ & (Hγᵥ & Hγᵥ' & Hγᵥ'') & _)".
    iMod (own_alloc (● map_seq O (to_agree <$> [γ_backup]))) as "(%γᵢ & Hγᵢ & Hγᵢ' & Hγᵢ'')".
    { by apply auth_auth_valid, singleton_valid. }
    replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
    (* iMod token_alloc as "[%γₜ Hγₜ]". *)
    iMod (own_alloc (● fmap (M := gmap gname) to_agree ({[ γ_backup := backup ]}))) as "(%γ_abs & Hγ_abs & Hγ_abs')".
    { rewrite map_fmap_singleton. by apply auth_auth_valid, singleton_valid. }
    iMod (own_alloc (● fmap (M := gmap gname) to_agree {[ γ_backup := vs ]})) as "(%γₕ & Hγₕ & Hγₕ')".
    { rewrite map_fmap_singleton. by apply auth_auth_valid, singleton_valid. }
    iMod (own_alloc (● map_seq O (to_agree <$> []))) as "[%γᵣ Hγᵣ]".
    { by apply auth_auth_valid. }
    iDestruct "Hvalidated" as "[Hvalidated Hvalidated']".
    replace (1 / 2 / 2)%Qp with (1/4)%Qp by compute_done.
    iMod (own_alloc (● {[ γ_backup ]})) as "[%γ_val Hγ_val]".
    { by apply auth_auth_valid. }
    change #backup with #(Some (Loc.blk_to_loc backup) &ₜ O).
    change (Z.of_nat 1) with 1%Z.
    simplify_eq.
    iMod (hazptr.(hazard_domain_register) (node vs) with "Hdom [$Hbackup $†Hbackup //]") as "Hmanaged".
    { solve_ndisj. }
    iMod (inv_alloc readN _ (read_inv γ γᵥ γₕ γᵢ γ_val γd γ_abs l (length vs)) with "[$Hmanaged Hvalidated $Hγ' $Hγᵥ' Hγᵥ'' Hγ_val Hγₕ Hγᵢ' Hγᵢ'' Hcache Hcache' Hversion Hγ_backup Hγ_abs]") as "#Hreadinv".
    { iExists {[ γ_backup := vs ]}, {[ γ_backup := backup ]}, vs. iFrame_fast.
      iExists γ_backup, backup.
      iNext. iSplitL.
      { by rewrite dom_singleton_L log_tokens_singleton. }
      iPureIntro. split_and!; constructor;
        solve
          [ done
          | by rewrite map_Forall_singleton
          | by rewrite lookup_singleton_eq
          | by rewrite !dom_singleton_L
          | apply NoDup_singleton
          | rewrite Forall_singleton; set_solver
          | rewrite bool_decide_eq_true_2 //; split; [by rewrite -Nat.even_spec | done]
          | simpl; by rewrite lookup_singleton_eq
          | set_solver ]. }
    iMod (own_alloc (● (fmap (M := gmap gname) to_agree (∅ : gmap gname nat)))) as "[%γ_vers Hγ_vers]".
    { rewrite fmap_empty. by apply auth_auth_valid. }
    iMod (own_alloc (● (fmap (M := gmap gname) to_agree {[ γ_backup := O ]}))) as "[%γₒ Hγₒ]".
    { rewrite map_fmap_singleton. by apply auth_auth_valid, singleton_valid. }
    iMod (inv_alloc mainN _ (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ γ_abs γd l (length vs)) with "[$Hγ'' $Hγₕ' $Hγᵣ $Hvalidated' $Hγᵥ Hγ_vers Hγₒ $Hγᵢ $Hγ_abs']") as "#Hinv".
    { iExists ∅, {[ γ_backup := O ]}, O. 
      rewrite /registry_inv /vers_auth_own map_fmap_singleton /=. iFrame.
      iPureIntro. split_and!; constructor;
        solve
          [ done
          | by rewrite lookup_singleton_eq
          | rewrite bool_decide_eq_false_2; [done | rewrite map_size_singleton; lia]
          | set_solver
          | apply gmap_injective_singleton
          | repeat constructor
          | by rewrite map_Forall_singleton ]. }
    wp_pures.
    iMod (pointsto_persist with "Hdomain") as "#Hdomain".
    iModIntro.
    by iApply ("HΦ" with "[$Hsrc $Hinv $Hreadinv $Hdomain $Hdom $Hγ]").
  Qed.

  Lemma div2_mono x y : x ≤ y → Nat.div2 x ≤ Nat.div2 y.
  Proof.
    intros Hle. induction Hle as [| y Hle IH].
    - done.
    - destruct (Nat.Even_Odd_dec y).
      + by rewrite -Nat.Even_div2.
      + rewrite <- Nat.Odd_div2 by done. by constructor.
  Qed.

  Lemma even_odd_negb n b : Nat.even n = b ↔ Nat.odd n = negb b.
  Proof.
    split; destruct b; simpl.
    - intros Heven%Nat.even_spec.
      apply dec_stable.
      rewrite not_false_iff_true.
      intros Hodd%Nat.odd_spec.
      by eapply Nat.Even_Odd_False.
    - rewrite -not_true_iff_false Nat.even_spec Nat.odd_spec. 
      intros Hnoteven.
      destruct (Nat.Even_Odd_dec n).
      + contradiction.
      + done.
    - rewrite -not_true_iff_false Nat.even_spec Nat.odd_spec. 
      intros Hnoteven.
      destruct (Nat.Even_Odd_dec n).
      + done.
      + contradiction.
    - intros Hodd%Nat.odd_spec.
      apply dec_stable.
      rewrite not_false_iff_true.
      intros Heven%Nat.even_spec.
      by eapply Nat.Even_Odd_False.
  Qed.

  Lemma odd_even_negb n b : Nat.odd n = b ↔ Nat.even n = negb b.
  Proof.
    rewrite even_odd_negb negb_involutive //.
  Qed.

  Lemma even_inj n : Z.even (Z.of_nat n) = Nat.even n.
  Proof.
    destruct (Z.even n) eqn:H, (Nat.even n) eqn:H'; auto.
    - rewrite Z.even_spec Even_inj in H.
      by rewrite -not_true_iff_false Nat.even_spec in H'.
    - rewrite Nat.even_spec in H'.
      by rewrite -not_true_iff_false Z.even_spec Even_inj in H.
  Qed.

  Lemma odd_inj n : Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    destruct (Z.odd n) eqn:H, (Nat.odd n) eqn:H'; auto.
    - rewrite Z.odd_spec -Odd_inj in H.
      by rewrite -not_true_iff_false Nat.odd_spec in H'.
    - rewrite Nat.odd_spec in H'.
      by rewrite -not_true_iff_false Z.odd_spec -Odd_inj in H.
  Qed.

  Lemma wp_array_copy_to_protected_off_inv (dst : loc) (src : blk) (vdst expected desired : list val) (i : nat) ψ γ γₑ γₗ γₜ γ_src γz lexp_src ldes dq dq' s pvs :
    i + length vdst = length expected →
    inv casN (cas_inv ψ γ γₑ γₗ γₜ γ_src γz src lexp_src ldes dq dq' expected desired s pvs) -∗
      {{{ token γₜ ∗ dst ↦∗ vdst }}}
        array_copy_to #dst #(src +ₗ i) #(length vdst)
      {{{ RET #(); token γₜ ∗ dst ↦∗ drop i expected }}}.
  Proof using DISJN.
    iIntros (Hlen) "#Hcasinv %Φ !# [Hγₜ Hdst] HΦ". 
    iLöb as "IH" forall (dst vdst i Hlen).
    wp_rec. wp_pures. destruct vdst as [|v vdst].
    { simplify_list_eq. wp_pures. iApply "HΦ".
      iModIntro. replace i with (length expected) in * by lia.
      rewrite drop_all. iFrame. }
    iDestruct (array_cons with "Hdst") as "[Hv Hvdst]".
    simplify_list_eq. wp_pure credit:"Hcredit'".
    wp_bind (! _)%E.
    (* iInv casN as "[[S [(>Hcredit & Hψ & [%b >Hγₑ'] & >Hlin) | (>Hcredit & AU & >Hγₑ' & >Hlin)]] | (>Hlintok & [%b >Hγₑ'] & [%b' >Hlin])]" "Hclose". *)
    iInv casN as "[[S H] | [>Hlintok _]]" "Hclose".
    { iMod (lc_fupd_elim_later with "Hcredit' S") as "S".
      wp_apply (shield_read with "S") as (? v') "(S & -> & %EQ)".
      { solve_ndisj. }
      { lia. }
      iMod ("Hclose" with "[S H]").
      { iLeft. iFrame. }
      iModIntro.
      wp_store. wp_pures.
      rewrite Loc.add_assoc.
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_sub /=; last lia.
      rewrite Nat.sub_0_r -Nat2Z.inj_add Nat.add_1_r.
      wp_apply ("IH" with "[] [$Hγₜ] [$Hvdst]").
      { iPureIntro. lia. }
      iIntros "[Hγₜ Hvdst]".
      iApply "HΦ". 
      iPoseProof (array_cons with "[$Hv $Hvdst]") as "Hvdst".
      assert (v' :: drop (S i) expected = drop i expected) as ->.
      { apply list_eq. intros [|j].
        { rewrite /= -EQ lookup_drop Nat.add_0_r //. }
        do 2 rewrite /= lookup_drop.
        f_equal. lia. }
      iFrame. }
    { iCombine "Hγₜ Hlintok" gives %[]. }
  Qed.

  Lemma wp_array_copy_to_protected_inv (dst : loc) (src : blk) (vdst expected desired : list val) (n : nat) ψ γ γₑ γₗ γₜ γ_src γz lexp_src ldes dq dq' s pvs :
    length vdst = n → length expected = n →
    inv casN (cas_inv ψ γ γₑ γₗ γₜ γ_src γz src lexp_src ldes dq dq' expected desired s pvs) -∗
      {{{ token γₜ ∗ dst ↦∗ vdst }}}
        array_copy_to #dst #src #n
      {{{ RET #(); token γₜ ∗ dst ↦∗ expected }}}.
  Proof using DISJN.
    iIntros (Hlen_dst Hlen_src) "#Hcasinv !# %Φ [Hγₜ Hdst] HΦ".
    rewrite -(Loc.add_0 src). change 0%Z with (Z.of_nat O). simplify_eq.
    wp_apply (wp_array_copy_to_protected_off_inv with "[//] [Hγₜ Hdst]").
    { simpl. symmetry. eassumption. }
    { iFrame. }
    iIntros "[Hγₜ Hdst]".
    rewrite drop_0.
    iApply ("HΦ" with "[$]").
  Qed.

 Lemma wp_array_copy_to_protected_off (dst : loc) (src : blk) vdst vsrc γz s γ_src (i : nat) :
    i + length vdst = length vsrc →
      {{{ dst ↦∗ vdst ∗ hazptr.(Shield) γz s (Validated src γ_src (node vsrc) (length vsrc)) }}}
        array_copy_to #dst #(src +ₗ i) #(length vdst)
      {{{ RET #(); dst ↦∗ drop i vsrc ∗ hazptr.(Shield) γz s (Validated src γ_src (node vsrc) (length vsrc)) }}}.
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

  Lemma wp_array_copy_to_protected (dst : loc) (src : blk) vdst vsrc γz s γ_src n :
    length vdst = n → length vsrc = n →
      {{{ dst ↦∗ vdst ∗ hazptr.(Shield) γz s (Validated src γ_src (node vsrc) n) }}}
        array_copy_to #dst #src #n
      {{{ RET #(); dst ↦∗ vsrc ∗ hazptr.(Shield) γz s (Validated src γ_src (node vsrc) n) }}}.
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

  Definition extract_bool (vs : list (val * val)) : option bool :=
    match vs with
    | (LitV (LitBool b), _) :: _ => Some b
    | _ => None
    end.

  Definition extract_tloc (vs : list (val * val)) : option Loc.tagged_loc :=
    match vs with
    | (LitV (LitLoc l), _) :: _ => Some l
    | _ => None
    end.

  Definition extract_int (vs : list (val * val)) : option Z :=
    match vs with
    | (LitV (LitInt (FinInt i)), _) :: _ => Some i
    | _ => None
    end.


  Lemma cached_wf_read_spec :
    big_atomic_read_spec' cached_wfN hazptrN (cached_wf_read hazptr) CachedWF IsCachedWF.
  Proof using DISJN.
    iIntros (γ v n) "(%l & %d & %γₕ & %γᵥ & %γᵣ & %γᵢ & %γₒ & %γ_vers & %γ_val & %γ_abs & %γd & %Hpos & -> & #Hd & #Hd_domain & #Hreadinv & #Hinv) %Φ AU".
    wp_rec. wp_pures. rewrite Loc.add_0.
    wp_bind (! _)%E.
    iInv readN as "(%ver & %log & %abstraction & %actual & %cache & %γ_backup & %γ_backup' & %backup & %backup' & %index & %validated & %t & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes & >%Hidx_wf & >%Hbackup_wf & >%Hvalid_wf)" "Hcl".
    pose proof Hsizes as [Hunboxed Hlenactual Hlencache Hloglen].
    pose proof Hidx_wf as [Hindex Hlenᵢ Hnodup Hrange].
    pose proof Hbackup_wf as [Hlogged Habs_backup Habs_backup' Hdom_eq].
    pose proof Hvalid_wf as [Htag Hcons Hvalidated_iff Hvalidated_sub].
    rewrite Loc.add_0.
    wp_load.
    iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb".
    eapply backup_logged in Hrange as Hbackup_logged; last done.
    destruct Hbackup_logged as [backup'vs Hbackup'vs].
    iMod (history_log_frag_alloc γ_backup' with "●Hhist") as "[●Hhist #◯Hlog]".
    { eassumption. }
    iMod (index_frag_alloc with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ]".
    { by rewrite last_lookup Hlenᵢ in Hindex. }
    iMod ("Hcl" with "[-AU]") as "_".
    { iExists ver, log, abstraction, actual, cache, γ_backup, γ_backup', backup, backup', index, validated, t.
      rewrite Loc.add_0. iFrame_fast. }
    iModIntro. wp_pures.
    wp_smart_apply (wp_array_clone_wk with "[//] [//] [//]").
    { done. }
    iIntros (vers vdst dst) "(Hdst & %Hlen' & %Hsorted & %Hbound & #Hcons)".
    wp_pures.
    wp_apply wp_new_proph; first done.
    iIntros (vs p) "Hp".
    wp_pures.
    wp_bind (! _)%E.
    iInv readN as "(%ver₁ & %log₁ & %abstraction₁ & %actual₁ & %cache₁ & %γ_backup₁ & %γ_backup₁' & %backup₁ & %backup₁' & %index₁ & %validated₁ & %t₁ & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed₁ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₁ & >%Hidx_wf₁ & >%Hbackup_wf₁ & >%Hvalid_wf₁)" "Hcl".
    pose proof Hsizes₁ as [Hunboxed₁ Hlenactual₁ Hlencache₁ Hloglen₁].
    pose proof Hidx_wf₁ as [Hindex₁ Hlenᵢ₁ Hnodup₁ Hrange₁].
    pose proof Hbackup_wf₁ as [Hlogged₁ Habs_backup₁ Habs_backup'₁ Hdom_eq₁].
    pose proof Hvalid_wf₁ as [Htag₁ Hcons₁ Hvalidated_iff₁ Hvalidated_sub₁].
    wp_load.
    destruct (decide (t₁ = 0)) as [-> | Hinvalid₁].
    - rewrite bool_decide_eq_true_2 // in Htag₁.
      destruct Htag₁ as (HEven₁ & <- & <-).
      (* destruct (Nat.even ver₁); last naive_solver. *)
      assert (γ_backup₁ ∈ validated₁) as Hvalidated₁ by naive_solver.
      destruct (extract_int vs) as [ver_proph|] eqn:Hextract; first last.
      { (* Some other value is prophecied: impossible *)
        iMod ("Hcl" with "[-Hp]") as "_".
        { iExists ver₁, log₁, abstraction₁, actual₁, actual₁, γ_backup₁, γ_backup₁, backup₁, backup₁, index₁, validated₁, 0.
          by iFrame_fast. } 
        iModIntro.
        rewrite /is_valid.
        wp_pures.
        wp_bind (Resolve _ _ _)%E.
        iInv readN as "(%ver₂ & %log₂ & %abstraction₂ & %actual₂ & %cache₂ & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index₂ & %validated₂ & %t₂ & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed₂ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₂ & >%Hidx_wf₂ & >%Hbackup_wf₂ & >%Hvalid_wf₂)" "Hcl".
        pose proof Hsizes₂ as [Hunboxed₂ Hlenactual₂ Hlencache₂ Hloglen₂].
        pose proof Hidx_wf₂ as [Hindex₂ Hlenᵢ₂ Hnodup₂ Hrange₂].
        pose proof Hbackup_wf₂ as [Hlogged₂ Habs_backup₂ Habs_backup'₂ Hdom_eq₂].
        pose proof Hvalid_wf₂ as [Htag₂ Hcons₂ Hvalidated_iff₂ Hvalidated_sub₂].
        wp_apply (wp_resolve with "Hp").
        { done. }
        rewrite Loc.add_0.
        wp_load.
        iIntros "!> %pvs' -> _".
        simplify_eq. }
      destruct (decide (Z.of_nat ver = ver_proph)) as [<- | Hneq].
      + iMod "AU" as (vs'') "[[%backup'' Hγ'] [_ Hconsume]]".
        iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
        iMod ("Hconsume" $! dst with "[$]") as "HΦ".
        iPoseProof (history_log_frag_agree with "●Hhist ◯Hlog") as "%Hlookup".
        iMod (index_frag_alloc with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ']".
        { by rewrite last_lookup Hlenᵢ₁ in Hindex₁. }
        iDestruct (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ") as "%Hindexagree".
        iMod (history_log_frag_alloc γ_backup₁ with "●Hhist") as "[●Hhist #◯Hlog']".
        { eassumption. }
        iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ Hlb") as %[_ Hle].
        iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb'".
        (* destruct (decide (backup₁ ∈ validated₁)) as [Hinval | Hninval]; first last.
        { rewrite bool_decide_eq_false_2 // in Hvalagree₁. } *)
        iMod (validated_auth_frag_alloc with "●Hγ_val") as "[●Hγ_val #◯Hγ_val₁]".
        { done. } 
        iMod ("Hcl" with "[-HΦ Hdst Hp]") as "_".
        { iExists ver₁, log₁, abstraction₁, actual₁, actual₁, γ_backup₁, γ_backup₁, backup₁, backup₁, index₁, validated₁, 0.
          by iFrame_fast. }
        iModIntro.
        rewrite /is_valid.
        wp_pures.
        wp_bind (Resolve _ _ _)%E.
        iInv readN as "(%ver₂ & %log₂ & %abstraction₂ & %actual₂ & %cache₂ & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index₂ & %validated₂ & %t₂ & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed₂ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₂ & >%Hidx_wf₂ & >%Hbackup_wf₂ & >%Hvalid_wf₂)" "Hcl".
        pose proof Hsizes₂ as [Hunboxed₂ Hlenactual₂ Hlencache₂ Hloglen₂].
        pose proof Hidx_wf₂ as [Hindex₂ Hlenᵢ₂ Hnodup₂ Hrange₂].
        pose proof Hbackup_wf₂ as [Hlogged₂ Habs_backup₂ Habs_backup'₂ Hdom_eq₂].
        pose proof Hvalid_wf₂ as [Htag₂ Hcons₂ Hvalidated_iff₂ Hvalidated_sub₂].
        wp_apply (wp_resolve with "Hp").
        { done. }
        iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ Hlb'") as %[_ Hle'].
        iPoseProof (history_log_frag_agree with "●Hhist ◯Hlog") as "%Hlookup₂".
        iDestruct (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ") as "%Hindexagree₂".
        rewrite Loc.add_0. wp_load.
        iIntros "!> %pvs' -> Hp".
        simpl in Hextract. simplify_eq.
        pose proof Hindex₁ as Hindex₁'.
        pose proof Hindex₂ as Hindex₂'.
        rewrite last_lookup Hlenᵢ in Hindex.
        rewrite last_lookup Hlenᵢ₁ in Hindex₁.
        rewrite last_lookup Hlenᵢ₂ in Hindex₂.
        replace ver₁ with ver in * by lia.
        clear Hle Hle'.
        destruct (Nat.even ver) eqn:Heven; last naive_solver.
        simplify_eq.
        rewrite Nat.Odd_div2; first last.
        { rewrite Nat.Odd_succ //. }
        rewrite Nat.Odd_div2 in Hlenᵢ Hlenᵢ₁ Hindexagree Hindexagree₂ Hindex Hlenᵢ₂; first last.
        { rewrite Nat.Odd_succ //. }
        simpl in *.
        iFrame "∗ # ∗".
        iAssert (⌜cache = vdst⌝)%I with "[●Hγᵥ]" as "<-".
        { iApply pure_mono.
          { by apply list_eq_same_length. }
          rewrite /vers_cons big_sepL2_forall.
          iDestruct "Hcons" as "[%Heq #Hcons]".
          iIntros (i v v' Hlt Hv Hv').
          assert (i < length vers) as [ver''' Hver''']%lookup_lt_is_Some by lia.
          iPoseProof ("Hcons" with "[//] [//]") as "[#Hlb'' #Hfrag]".
          assert (ver ≤ ver''') as Hle by (by eapply Forall_lookup).
          iPoseProof (mono_nat_auth_lb_own_valid with "●Hγᵥ Hlb''") as "[%Hq %Hge]".
          assert (ver = ver''') as <- by lia.
          clear Hge Hle.
          iPoseProof ("Hfrag" with "[]") as "(%γ_l & %vs & #◯Hindex' & #◯Hlog''' & %Hlookup')".
          { done. }
          iCombine "◯Hγᵢ ◯Hindex'" gives %Hvalid%auth_frag_op_valid_1.
          rewrite singleton_op singleton_valid in Hvalid.
          apply to_agree_op_inv_L in Hvalid as <-.
          iCombine "◯Hlog ◯Hlog'''" gives %Hvalid%auth_frag_op_valid_1.
          rewrite singleton_op singleton_valid in Hvalid.
          apply to_agree_op_inv_L in Hvalid as [=<-].
          by simplify_eq. }
        iMod ("Hcl" with "[-HΦ Hdst]") as "_".
        { iExists ver, log₂, abstraction₂, actual₂, cache, γ_backup₂, γ_backup', backup₂, backup₂', index₂, validated₂, t₂.
          rewrite Loc.add_0 Heven. iFrame_fast. }
        iModIntro.
        wp_pures.
        iApply "HΦ".
        by iFrame_fast.
      + iMod ("Hcl" with "[-AU Hdst Hp]") as "_".
        { iExists ver₁, log₁, abstraction₁, actual₁, actual₁, γ_backup₁, γ_backup₁, backup₁, backup₁, index₁, validated₁, 0.
          iFrame_fast. }
        iModIntro.
        rewrite /is_valid.
        wp_pures.
        wp_bind (Resolve _ _ _)%E.
        iInv readN as "(%ver₂ & %log₂ & %abstraction₂ & %actual₂ & %cache₂ & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index₂ & %validated₂ & %t₂ & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed₂ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₂ & >%Hidx_wf₂ & >%Hbackup_wf₂ & >%Hvalid_wf₂)" "Hcl".
        pose proof Hsizes₂ as [Hunboxed₂ Hlenactual₂ Hlencache₂ Hloglen₂].
        pose proof Hidx_wf₂ as [Hindex₂ Hlenᵢ₂ Hnodup₂ Hrange₂].
        pose proof Hbackup_wf₂ as [Hlogged₂ Habs_backup₂ Habs_backup'₂ Hdom_eq₂].
        pose proof Hvalid_wf₂ as [Htag₂ Hcons₂ Hvalidated_iff₂ Hvalidated_sub₂].
        wp_apply (wp_resolve with "Hp").
        { done. }
        rewrite Loc.add_0.
        wp_load.
        iIntros "!> %pvs' -> Hp".
        iMod ("Hcl" with "[-AU Hdst]") as "_".
        { iExists ver₂, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₂, backup₂', index₂, validated₂, t₂.
          rewrite Loc.add_0. iFrame_fast. }
        iModIntro.
        simpl in Hextract. simplify_eq.
        wp_pures.
        rewrite bool_decide_eq_false_2 //.
        wp_pures. wp_load. wp_pures.
        wp_apply (hazptr.(shield_new_spec) with "[//] [//]") as (s) "S".
        { set_solver. }
        wp_pures.
        awp_apply (hazptr.(shield_protect_tagged_spec) with "[//] [$]").
        { solve_ndisj. }
        rewrite /atomic_acc /=. 
        (* rewrite /atomic_acc. *)
        iInv readN as "(%ver₃ & %log₃ & %abstraction₃ & %actual₃ & %cache₃ & %γ_backup₃ & %γ_backup₃' & %backup₃ & %backup₃' & %index₃ & %validated₃ & %t₃ & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed₃ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₃ & >%Hidx_wf₃ & >%Hbackup_wf₃ & >%Hvalid_wf₃)" "Hcl".
        pose proof Hsizes₃ as [Hunboxed₃ Hlenactual₃ Hlencache₃ Hloglen₃].
        pose proof Hidx_wf₃ as [Hindex₃ Hlenᵢ₃ Hnodup₃ Hrange₃].
        pose proof Hbackup_wf₃ as [Hlogged₃ Habs_backup₃ Habs_backup'₃ Hdom_eq₃].
        pose proof Hvalid_wf₃ as [Htag₃ Hcons₃ Hvalidated_iff₃ Hvalidated_sub₃].
        iMod "AU" as (vs'') "[[%backup'' Hγ'] Hlin]".
        iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
        iFrame "Hbackup_ptr Hbackup_managed₃".
        iModIntro. iSplit.
        { iIntros "[Hbackup Hbackup_managed]".
          iDestruct "Hlin" as "[Habort _]".
          iMod ("Habort" with "[$Hγ']") as "AU".
          iMod ("Hcl" with "[-AU Hdst]") as "_".
          { iExists ver₃, log₃, abstraction₃, actual₃, cache₃, γ_backup₃, γ_backup₃', backup₃, backup₃', index₃, validated₃, t₃.
            iFrame_fast. }
          by iFrame. }
        iIntros "(Hbackup & Hmanaged & Hprotected)".
        iDestruct "Hlin" as "[_ Hcommit]".
        iMod ("Hcommit" $! dst with "[$Hγ']") as "HΦ".
        iMod ("Hcl" with "[-HΦ Hprotected Hdst]") as "_".
          { iExists ver₃, log₃, abstraction₃, actual₃, cache₃, γ_backup₃, γ_backup₃', backup₃, backup₃', index₃, validated₃, t₃.
          iFrame_fast. }
        iModIntro. wp_pures.
        change #(Some (Loc.blk_to_loc backup₃) &ₜ 0) with #backup₃.
        replace (length actual) with (length vdst) by lia.
        wp_apply (wp_array_copy_to_protected _ _ _  actual₃ with "[$]").
        { lia. }
        { lia. }
        iIntros "[Hdst S]". wp_pures.
        wp_apply (hazptr.(shield_drop_spec) with "Hd_domain S") as "_".
        { set_solver. }
        wp_pures. iModIntro.
        iApply "HΦ".
        iFrame_fast.
    - assert (γ_backup₁ ∉ validated₁) as Hinvalidated₁ by naive_solver.
      iMod ("Hcl" with "[-AU Hdst Hp]") as "_".
      { iExists ver₁, log₁, abstraction₁, actual₁, cache₁, γ_backup₁, γ_backup₁', backup₁, backup₁', index₁, validated₁, t₁.
        iFrame_fast. }
      iModIntro.
      rewrite /is_valid.
      wp_pures.
      rewrite bool_decide_eq_false_2; last lia.
      wp_pures.
      wp_bind (! _)%E.
      wp_load.
      wp_pures.
      wp_apply (hazptr.(shield_new_spec) with "[//] [//]") as (s) "S".
      { set_solver. }
      wp_pures.
      awp_apply (hazptr.(shield_protect_tagged_spec) with "[//] [$]").
      { solve_ndisj. }
      rewrite /atomic_acc /=. 
      iInv readN as "(%ver₂ & %log₂ & %abstraction₂ & %actual₂ & %cache₂ & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index₂ & %validated₂ & %t₂ & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed₂ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₂ & >%Hidx_wf₂ & >%Hbackup_wf₂ & >%Hvalid_wf₂)" "Hcl".
      pose proof Hsizes₂ as [Hunboxed₂ Hlenactual₂ Hlencache₂ Hloglen₂].
      pose proof Hidx_wf₂ as [Hindex₂ Hlenᵢ₂ Hnodup₂ Hrange₂].
      pose proof Hbackup_wf₂ as [Hlogged₂ Habs_backup₂ Habs_backup'₂ Hdom_eq₂].
      pose proof Hvalid_wf₂ as [Htag₂ Hcons₂ Hvalidated_iff₂ Hvalidated_sub₂].
      iMod "AU" as (actual') "[[%backup'' Hγ'] Hlin]".
      iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
      iFrame "Hbackup_ptr Hbackup_managed₂".
      iModIntro. iSplit.
      { iIntros "[Hbackup Hbackup_managed]".
        iDestruct "Hlin" as "[Habort _]".
        iMod ("Habort" with "[$Hγ']") as "AU".
        iMod ("Hcl" with "[-AU Hdst Hp]") as "_".
        { iExists ver₂, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₂, backup₂', index₂, validated₂, t₂.
          iFrame_fast. }
        by iFrame. }
      iIntros "(Hbackup & Hmanaged & Hprotected)".
      iDestruct "Hlin" as "[_ Hcommit]".
      iMod ("Hcommit" $! dst with "[$Hγ']") as "HΦ".
      iMod ("Hcl" with "[-HΦ Hprotected Hdst Hp]") as "_".
      { iExists ver₂, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₂, backup₂', index₂, validated₂, t₂.
        iFrame_fast. }
      iModIntro. wp_pures.
      change #(Some (Loc.blk_to_loc backup₂) &ₜ 0) with #backup₂.
      replace n with (length vdst) by lia.
      wp_apply (wp_array_copy_to_protected _ _ _  actual₂ with "[$Hdst $Hprotected]").
      { lia. }
      { lia. }
      iIntros "[Hdst S]". wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "Hd_domain S") as "_".
      { set_solver. }
      wp_pures. iModIntro.
      iApply "HΦ".
      iFrame_fast.
  Qed.

  Lemma read'_spec (actual₁ cache₁ copy : list val) (γ γᵥ γₕ γᵢ γ_val γz γ_abs : gname) 
  (l d : loc) (n ver ver₁ t₁ : nat) (γ_backup₁ γ_backup₁' : gname) 
  (dst backup₁ : blk) (vers : list nat) 
  (log₁ : gmap gname (list val)) s :
    n > 0 →
    length actual₁ = n →
    length cache₁ = n →
    length copy = n →
    StronglySorted Nat.le vers →
    ver ≤ ver₁ →
    Forall (Nat.le ver) vers →
    (if bool_decide (t₁ = 0) then Nat.Even ver₁ ∧ actual₁ = cache₁ ∧ γ_backup₁ = γ_backup₁' else t₁ = 1) →
    (if Nat.even ver₁ then log₁ !! γ_backup₁' = Some cache₁ else t₁ = 1) →
    inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs l n) -∗
    (l +ₗ domain_off) ↦□ #d -∗
    hazptr.(IsHazardDomain) γz d -∗
    mono_nat_lb_own γᵥ ver₁ -∗
    log_frag_own γₕ γ_backup₁ actual₁ -∗
    index_frag_own γᵢ (Nat.div2 (S ver₁)) γ_backup₁' -∗
    vers_cons γᵥ γₕ γᵢ vers copy -∗
      {{{ hazptr.(Shield) γz s (Validated backup₁ γ_backup₁ (node actual₁) n) ∗ dst ↦∗ copy }}}
        read' n #l #ver #(Some (Loc.blk_to_loc backup₁) &ₜ t₁) #dst
      {{{ RET #(); hazptr.(Shield) γz s (Validated backup₁ γ_backup₁ (node actual₁) n) ∗ dst ↦∗ actual₁ }}}.
  Proof using DISJN.
    iIntros (Hpos Hlenactual₁ Hlencache₁ Hlencopy Hsorted Hle Hlb Htag₁ Hevenmatch) "#Hinv #Hd #Hdom #◯Hγᵥ₁ #◯Hγₕ₁ #◯Hγᵢ₁ #Hcons %Φ !# [S Hdst] HΦ".
    wp_rec. wp_pures. wp_rec. wp_pures.
    destruct (decide (t₁ = 0)) as [-> | Hne₁].
    - destruct Htag₁ as (HEven₁ & <- & <-).
      destruct (Nat.even ver₁) eqn:Heven₁; last done. simplify_eq.
      wp_pures.
      wp_bind (! _)%E.
      iInv readN as "(%ver₂ & %log₂ & %abstraction₂ & %actual₂ & %cache₂ & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index₂ & %validated₂ & %t₂ & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed₂ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₂ & >%Hidx_wf₂ & >%Hbackup_wf₂ & >%Hvalid_wf₂)" "Hcl".
      pose proof Hsizes₂ as [Hunboxed₂ Hlenactual₂ Hlencache₂ Hloglen₂].
      pose proof Hidx_wf₂ as [Hindex₂ Hlenᵢ₂ Hnodup₂ Hrange₂].
      pose proof Hbackup_wf₂ as [Hlogged₂ Habs_backup₂ Habs_backup'₂ Hdom_eq₂].
      pose proof Hvalid_wf₂ as [Htag₂ Hcons₂ Hvalidated_iff₂ Hvalidated_sub₂].
      rewrite Loc.add_0.
      iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₁].
      wp_load.
      destruct (decide (ver₂ = ver)) as [-> | Hne₂].
      + assert (ver₁ = ver) as -> by lia.
        iAssert (⌜actual₁ = copy⌝)%I as "<-".
        { iApply pure_mono.
          { eapply list_eq_same_length; eauto. }
          rewrite /vers_cons.
          rewrite big_sepL2_forall.
          iDestruct "Hcons" as "[%Heq #Hcons]".
          iIntros (i v v' Hlt Hv Hv').
          assert (i < length vers) as [ver' Hver']%lookup_lt_is_Some by lia.
          iPoseProof ("Hcons" with "[//] [//]") as "[#Hlb' #Hfrag]".
          assert (ver ≤ ver') as Hle' by (by eapply Forall_lookup).
          iPoseProof (mono_nat_auth_lb_own_valid with "●Hγᵥ Hlb'") as "[_ %Hge]".
          assert (ver = ver') as <- by lia.
          clear Hge Hle.
          iPoseProof ("Hfrag" with "[]") as "(%γ_l & %vs & #◯Hγᵢ & #◯Hγₕ & %Hlookup)".
          { done. }
          iClear "Hfrag Hcons".
          iPoseProof (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ₁") as "%Hagreeᵢ₁".
          iPoseProof (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ") as "%Hagreeᵢ".
          iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ") as "%Hagreeₕ".
          iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ₁") as "%Hagreeₕ₁".
          rewrite -Nat.Even_div2 // in Hagreeᵢ₁.
          by simplify_eq. }
          iMod ("Hcl" with "[-HΦ S Hdst]") as "_".
          { iExists ver, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₂, backup₂', index₂, validated₂, t₂.
            iFrame_fast. rewrite Loc.add_0 //. }
        iModIntro.
        wp_pures.
        iModIntro.
        iApply "HΦ".
        rewrite -Nat.Even_div2 //.
        iFrame_fast.
      + iMod ("Hcl" with "[-HΦ S Hdst]") as "_".
        { iExists ver₂, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₂, backup₂', index₂, validated₂, t₂. iFrame_fast. rewrite Loc.add_0 //. }
        iModIntro.
        wp_pures.
        rewrite (bool_decide_eq_false_2 (Z.of_nat ver₂ = Z.of_nat ver)); last lia.
        wp_pures.
        change #(Some (Loc.blk_to_loc backup₁) &ₜ 0) with #backup₁.
        wp_apply (wp_array_copy_to_protected _ _ copy actual₁ with "[$Hdst $S]").
        { done. }
        { done. }
        iIntros "[Hdst S]". 
        iApply ("HΦ" with "[$]").
    - rewrite (bool_decide_eq_false_2 (Z.of_nat t₁ = 0)) //; last lia.
      wp_pures.
      wp_apply (wp_array_copy_to_protected _ _ copy actual₁ with "[$Hdst S]").
      { lia. }
      { lia. }
      { done. }
      iIntros "[Hdst S]". 
      iApply ("HΦ" with "[$]").
  Qed.

Lemma read'_spec_inv (actual₁ cache₁ copy desired : list val) (γ γᵥ γₕ γᵢ γ_val γz γ_abs γₑ γₗ γₜ : gname) 
  (l d : loc) (n ver ver₁ t₁ : nat) (γ_backup₁ γ_backup₁' : gname) 
  (dst backup₁ : blk) (lexp_src ldes : loc) (vers : list nat) (log₁ : gmap gname (list val)) ψ dq dq' s pvs :
    n > 0 →
    length actual₁ = n →
    length cache₁ = n →
    length copy = n →
    StronglySorted Nat.le vers →
    ver ≤ ver₁ →
    Forall (Nat.le ver) vers →
    (if bool_decide (t₁ = 0) then Nat.Even ver₁ ∧ actual₁ = cache₁ ∧ γ_backup₁ = γ_backup₁' else t₁ = 1) →
    (if Nat.even ver₁ then log₁ !! γ_backup₁' = Some cache₁ else t₁ = 1) →
    inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γz γ_abs l n) -∗
    inv casN (cas_inv ψ γ γₑ γₗ γₜ γ_backup₁ γz backup₁ lexp_src ldes dq dq' actual₁ desired s pvs) -∗
    (l +ₗ domain_off) ↦□ #d -∗
    hazptr.(IsHazardDomain) γz d -∗
    mono_nat_lb_own γᵥ ver₁ -∗
    log_frag_own γₕ γ_backup₁ actual₁ -∗
    index_frag_own γᵢ (Nat.div2 (S ver₁)) γ_backup₁' -∗
    vers_cons γᵥ γₕ γᵢ vers copy -∗
      {{{ token γₜ ∗ dst ↦∗ copy }}}
        read' n #l #ver #(Some (Loc.blk_to_loc backup₁) &ₜ t₁) #dst
      {{{ RET #(); token γₜ ∗ dst ↦∗ actual₁ }}}.
  Proof using DISJN.
    iIntros (Hpos Hlenactual₁ Hlencache₁ Hlencopy Hsorted Hle Hlb Htag₁ Hevenmatch) "#Hinv #Hcasinv #Hd #Hdom #◯Hγᵥ₁ #◯Hγₕ₁ #◯Hγᵢ₁ #Hcons %Φ !# [Hγₜ Hdst] HΦ".
    wp_rec. wp_pures. wp_rec. wp_pures.
    destruct (decide (t₁ = 0)) as [-> | Hne₁].
    - destruct Htag₁ as (HEven₁ & <- & <-).
      destruct (Nat.even ver₁) eqn:Heven₁; last done. simplify_eq.
      wp_pures.
      wp_bind (! _)%E.
      iInv readN as "(%ver₂ & %log₂ & %abstraction₂ & %actual₂ & %cache₂ & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index₂ & %validated₂ & %t₂ & >Hver & >Hbackup_ptr & >Hγ & Hbackup_managed₂ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₂ & >%Hidx_wf₂ & >%Hbackup_wf₂ & >%Hvalid_wf₂)" "Hcl".
      pose proof Hsizes₂ as [Hunboxed₂ Hlenactual₂ Hlencache₂ Hloglen₂].
      pose proof Hidx_wf₂ as [Hindex₂ Hlenᵢ₂ Hnodup₂ Hrange₂].
      pose proof Hbackup_wf₂ as [Hlogged₂ Habs_backup₂ Habs_backup'₂ Hdom_eq₂].
      pose proof Hvalid_wf₂ as [Htag₂ Hcons₂ Hvalidated_iff₂ Hvalidated_sub₂].
      rewrite Loc.add_0.
      iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₁].
      wp_load.
      destruct (decide (ver₂ = ver)) as [-> | Hne₂].
      + assert (ver₁ = ver) as -> by lia.
        iAssert (⌜actual₁ = copy⌝)%I as "<-".
        { iApply pure_mono.
          { eapply list_eq_same_length; eauto. }
          rewrite /vers_cons.
          rewrite big_sepL2_forall.
          iDestruct "Hcons" as "[%Heq #Hcons]".
          iIntros (i v v' Hlt Hv Hv').
          assert (i < length vers) as [ver' Hver']%lookup_lt_is_Some by lia.
          iPoseProof ("Hcons" with "[//] [//]") as "[#Hlb' #Hfrag]".
          assert (ver ≤ ver') as Hle' by (by eapply Forall_lookup).
          iPoseProof (mono_nat_auth_lb_own_valid with "●Hγᵥ Hlb'") as "[_ %Hge]".
          assert (ver = ver') as <- by lia.
          clear Hge Hle.
          iPoseProof ("Hfrag" with "[]") as "(%γ_l & %vs & #◯Hγᵢ & #◯Hγₕ & %Hlookup)".
          { done. }
          iClear "Hfrag Hcons".
          iPoseProof (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ₁") as "%Hagreeᵢ₁".
          iPoseProof (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ") as "%Hagreeᵢ".
          iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ") as "%Hagreeₕ".
          iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ₁") as "%Hagreeₕ₁".
          rewrite -Nat.Even_div2 // in Hagreeᵢ₁.
          by simplify_eq. }
          iMod ("Hcl" with "[-HΦ Hγₜ Hdst]") as "_".
          { iExists ver, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₂, backup₂', index₂, validated₂, t₂.
            iFrame_fast. rewrite Loc.add_0 //. }
        iModIntro.
        wp_pures.
        iModIntro.
        iApply "HΦ".
        rewrite -Nat.Even_div2 //.
        iFrame_fast.
      + iMod ("Hcl" with "[-HΦ Hγₜ Hdst]") as "_".
        { iExists ver₂, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₂, backup₂', index₂, validated₂, t₂. iFrame_fast. rewrite Loc.add_0 //. }
        iModIntro.
        wp_pures.
        rewrite (bool_decide_eq_false_2 (Z.of_nat ver₂ = Z.of_nat ver)); last lia.
        wp_pures.
        change #(Some (Loc.blk_to_loc backup₁) &ₜ 0) with #backup₁.
        wp_apply (wp_array_copy_to_protected_inv _ _ copy actual₁ with "[//] [$Hdst $Hγₜ]").
        { done. }
        { done. }
        iIntros "[Hγₜ Hdst]". 
        iApply ("HΦ" with "[$]").
    - rewrite (bool_decide_eq_false_2 (Z.of_nat t₁ = 0)) //; last lia.
      wp_pures.
      wp_apply (wp_array_copy_to_protected_inv _ _ copy actual₁ with "[//] [$Hdst $Hγₜ]").
      { done. }
      { done. }
      iIntros "[Hγₜ Hdst]". 
      iApply ("HΦ" with "[$]").
  Qed.

  (* It is possible to linearize pending writers while maintaing the registry invariant *)
  Lemma linearize_cas γ γd (γ_actual' : gname) (l_actual l_actual' : blk) (actual actual' : list val) requests abstraction n :
    n > 0 → length actual = n → length actual' = n →
    (* The current and previous logical state should be distinct if swapping backup pointer *)
    actual ≠ actual' →
    (* The current backup pointer has been logged *)
    token γ_actual' -∗
    (* New backup managed by hazard pointers *)
    hazptr.(Managed) γd l_actual' γ_actual' n (node actual') -∗
    (* Points-to predicate of every previously logged backup *)
    log_tokens (dom abstraction) -∗
    (* The logical state has not yet been updated to the new state *)
    ghost_var_frac γ (1/2) (γ_actual', actual') -∗
    (* The registry invariant is satisfied for the current logical state *)
    registry_inv γ γd l_actual actual requests abstraction
    (* We can take frame-preserving updated that linearize the successful CAS,
       alongside all of the other failing CAS's *)
    ={⊤ ∖ ↑readN ∖ ↑mainN}=∗
      token γ_actual' ∗
      hazptr.(Managed) γd l_actual' γ_actual' n (node actual') ∗
      (* Points-to predicate of every previously logged backup *)
      log_tokens (dom abstraction) ∗
      (* Update new logical state to correspond to logical CAS *)
      ghost_var_frac γ (1/2) (γ_actual', actual') ∗
      (* Invariant corresponding to new logical state *)
      registry_inv γ γd l_actual' actual' requests abstraction.
  Proof using DISJN.
    iIntros (Hpos Hlen Hle' Hne) "Htok Hmanaged Hlogtokens Hγ Hreqs". simplify_eq.
    iInduction requests as [|[[γₗ γₑ] γ_exp] requests] "IH".
    - by iFrame.
    - rewrite /registry_inv. do 2 rewrite -> big_sepL_cons by done.
      (* (%Hfresh & Hlin & %Φ & %γₜ' & %lexp' & %ldes & %dq & %dq' & %expected & %desired & Hγₑ & #Hwinv) *)
      iDestruct "Hreqs" as "[(%lexp & %Hlexp_abs & Hlin & %Φ & %γₜ & %lexp' & %ldes & %dq & %dq' & %expected & %desired & %s & %pvs & Hγₑ & #Hcasinv) Hreqs]".
      iMod ("IH" with "Htok Hmanaged Hlogtokens Hγ Hreqs") as "(Htok & Hmanaged & Hlogtokens & Hγ & Hreqinv)".
      iInv casN as "[[S [(>Hcredit & HΦ & [%b >Hγₑ'] & >Hlin') | (>[Hcredit Hcredit'] & AU & >Hγₑ' & >Hlin')]] | (>Hlintok & [%b >Hγₑ'] & [%b' >Hlin'])]" "Hclose".
      + iCombine "Hlin Hlin'" gives %[_ ->].
        iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
        destruct (decide (l_actual' = lexp)) as [-> | Hneqγ].
        { iMod (lc_fupd_elim_later with "Hcredit S") as "Hprotected". 
          iPoseProof (shield_managed_agree with "Hprotected Hmanaged") as "->".
          iPoseProof (log_tokens_impl (dom abstraction) γ_actual' with "Hlogtokens") as "Htok'".
          { rewrite elem_of_dom //. }
          iCombine "Htok Htok'" gives %[]. } 
        (* rewrite bool_decide_eq_false in Hneq. *)
        iMod ("Hclose" with "[HΦ Hγₑ Hlin Hcredit S]") as "_".
        { repeat (iLeft; iFrame). }
        iFrame_fast.
        rewrite /request_inv bool_decide_eq_false_2 //.
      + iCombine "Hlin Hlin'" gives %[_ ->%bool_decide_eq_true].
        iCombine "Hγₑ Hγₑ'" gives %[_ ->%bool_decide_eq_true].
        destruct (decide (l_actual' = lexp)) as [-> | Hneqγ].
        { iMod (lc_fupd_elim_later with "Hcredit S") as "Hprotected". 
          iPoseProof (shield_managed_agree with "Hprotected Hmanaged") as "->".
          iPoseProof (log_tokens_impl (dom abstraction) γ_actual' with "Hlogtokens") as "Htok'".
          { rewrite elem_of_dom //. }
          iCombine "Htok Htok'" gives %[]. }
        iMod (ghost_var_update_halves false with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
        iMod "AU" as (actual'') "[[%backup'' Hγ'] [_ Hconsume]]".
        { set_solver. }
        iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
        rewrite (bool_decide_eq_false_2 (actual' = expected)) //.
        iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
        iMod ("Hconsume" with "[$]") as "HΦ".
        iFrame_fast.
        rewrite (bool_decide_eq_false_2 (l_actual' = lexp)) //.
        iFrame_fast.
        iMod ("Hclose" with "[-]") as "_".
        { iLeft. iFrame. iLeft. iFrame. }
        done.
      + iMod (ghost_var_update_halves (bool_decide (l_actual' = lexp)) with "Hlin Hlin'") as "[Hlin Hlin']".
        iMod (ghost_var_update_halves (bool_decide (actual' = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
        iFrame_fast.
        iMod ("Hclose" with "[-]") as "_".
        { iRight. iFrame. }
        done.
  Qed.

  Lemma log_tokens_insert γ log :
    log_tokens log -∗ token γ -∗ log_tokens ({[ γ ]} ∪ log).
  Proof.
    iIntros "Hlogtokens Htok".
    rewrite /log_tokens.
    destruct (decide (γ ∈ log)) as [Hmem | Hnmem].
    { iPoseProof (big_sepS_elem_of with "Hlogtokens") as "Htok'".
      { done. }
      iCombine "Htok Htok'" gives %[]. }
    rewrite big_sepS_insert //.
    iFrame.
  Qed.

  Lemma own_auth_split_self (dq : dfrac) (γ : gname) (m : gmap gname (agree (list val))) :
    own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ m).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := m).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma own_auth_split_self' (dq : dfrac) (γ : gname) (m : gmap gname (agree nat)) :
    own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ m).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := m).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma own_auth_split_self'' (dq : dfrac) (γ : gname) (m : gmap nat (agree gname)) :
    own γ (●{dq} m) ==∗ own γ (●{dq} m) ∗ own γ (◯ m).
  Proof.
    iIntros "H●".
    iMod (own_update with "H●") as "[H● H◯]".
    { apply auth_update_dfrac_alloc with (b := m).
      - apply _.
      - reflexivity. }
    by iFrame.
  Qed.

  Lemma map_Forall_subseteq `{Countable K} {V} (m m' : gmap K V) P :
    m ⊆ m' → map_Forall P m' → map_Forall P m.
  Proof.
    rewrite /map_Forall. 
    intros Hsub HP k v Hsome.
    by eapply HP, lookup_weaken.
  Qed.

  Lemma even_succ_negb k : Nat.even (S k) = negb (Nat.even k).
  Proof.
    destruct (Nat.even (S k)) eqn:Hsucc; destruct (Nat.even k) eqn:H.
    - exfalso. apply (Nat.Even_Odd_False k).
      + rewrite -Nat.even_spec //.
      + rewrite -Nat.Even_succ -Nat.even_spec //.
    - done.
    - done.
    - exfalso. apply (Nat.Even_Odd_False k).
      + rewrite -Nat.Odd_succ -Nat.odd_spec odd_even_negb //.
      + rewrite -Nat.odd_spec odd_even_negb //.
  Qed.

  Lemma NoDup_lookup_ne {A} (l : list A) i j x y :
    NoDup l →
    i ≠ j →
    l !! i = Some x →
    l !! j = Some y →
    x ≠ y.
  Proof.
    intros Hnd Hij Hi Hj ->. eapply Hij, NoDup_lookup; eauto.
  Qed.

  Lemma even_odd_negb_eq n : Nat.odd n = negb (Nat.even n).
  Proof.
    by apply even_odd_negb.
  Qed.

  (* The “strict” version: no extra assumptions on R *)
  Lemma StronglySorted_lookup_lt {A} (R : A → A → Prop) l i j x y :
    StronglySorted R l →
    i < j →
    l !! i = Some x →
    l !! j = Some y →
    R x y.
  Proof.
    revert i j x y.
    induction l as [|a l IH]; intros i j x y Hsorted Hij Hix Hjy.
    - now rewrite lookup_nil in Hix.
    - destruct i as [| i], j as [| j].
      + lia.
      + simpl in *. simplify_eq. inv Hsorted.
        eapply Forall_lookup_1; eauto.
      + lia.
      + simpl in *. inv Hsorted. apply (IH i j); auto. lia.
  Qed.

  Lemma already_linearized Φ γ γₗ γₑ γᵣ γₜ γ_exp γd (backup lexp : blk) (lexp_src ldes : loc) expected desired actual (dq dq' : dfrac) i abstraction s pvs :
    lexp ≠ backup →
      abstraction !! γ_exp = Some lexp →
      (* inv readN (read_inv γ γᵥ γₕ γᵢ l (length expected)) -∗
        inv mainN (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ l) -∗ *)
        inv casN (cas_inv Φ γ γₑ γₗ γₜ γ_exp γd lexp lexp_src ldes dq dq' expected desired s pvs) -∗
          lexp_src ↦∗{dq} expected -∗
            ldes ↦∗{dq'} desired -∗
              registered γᵣ i γₗ γₑ γ_exp -∗
                request_inv γ γₗ γₑ γ_exp γd backup actual abstraction -∗
                  token γₜ -∗
                    £ 1 ={⊤ ∖ ↑readN ∖ ↑mainN}=∗
                      Φ #false ∗ 
                      Shield hazptr γd s (Validated lexp γ_exp (node expected) (length expected)) ∗
                      request_inv γ γₗ γₑ γ_exp γd backup actual abstraction.
  Proof.
    iIntros (Hne Habs) "#Hcasinv Hlexp Hldes #Hregistered Hreqinv Hγₜ Hcredit".
    rewrite /request_inv.
    iDestruct "Hreqinv" as "(%lexp' & %Hlexp_abs & Hlin & %Φ' & %γₜ' & %lexp_src' & %ldes' & %dq₁ & %dq₁' & %expected' & %desired' & %s' & %pvs' & Hγₑ & _)".
    iInv casN as "[[S [(>Hcredit' & HΦ & [%b >Hγₑ'] & >Hlin') | (>Hcredit' & AU & >Hγₑ' & >Hlin')]] | (>Hlintok & [%b >Hγₑ'] & [%b' >Hlin'])]" "Hclose".
    + iCombine "Hlin Hlin'" gives %[_ Hneq%bool_decide_eq_false].
      iMod (ghost_var_update_halves (bool_decide (actual = expected)) with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']". 
      iMod ("Hclose" with "[Hγₜ Hγₑ Hlin]") as "_".
      { iRight. iFrame. }
      iMod (lc_fupd_elim_later with "Hcredit HΦ") as "HΦ".
      iPoseProof ("HΦ" with "[$]") as "HΦ".
      iFrame_fast.
      rewrite bool_decide_eq_false_2 //.
      iFrame.
      by iMod (lc_fupd_elim_later with "Hcredit' S") as "$".
    + simplify_eq. 
      by iCombine "Hlin Hlin'" gives %[_ ->%bool_decide_eq_true].
    + iCombine "Hγₜ Hlintok" gives %[].
  Qed.

  Lemma wp_try_validate (γ γᵥ γₕ γᵣ γᵢ γ_val γ_vers γₒ γd γ_abs γ_backup : gname) (l l_desired : loc) (backup : blk) (dq : dfrac)
                        (desired : list val) (ver ver₂ idx₂ : nat) (index₂ : list gname)
                        (abstraction : gmap gname blk) (order₂ : gmap gname nat) (n : nat) s :
    n > 0 → 
    length desired = n →
    ver ≤ ver₂ → length index₂ = S (Nat.div2 (S ver₂)) →
      StronglySorted (gmap_mono order₂) index₂ → Forall (.∈ dom order₂) index₂ → map_Forall (λ _ idx, idx ≤ idx₂) order₂ →
        order₂ !! γ_backup = None →
          inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γd γ_abs l n) -∗
            inv mainN (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ γ_abs γd l n) -∗
              mono_nat_lb_own γᵥ ver₂ -∗
                own γᵢ (◯ map_seq O (to_agree <$> index₂)) -∗
                  abstraction_frag_own γ_abs γ_backup backup -∗
                    log_frag_own γₕ γ_backup desired -∗
                      vers_frag_own γₒ γ_backup (S idx₂) -∗
                        own γₒ (◯ (fmap (M := gmap gname) to_agree order₂)) -∗
                          vers_frag_own γ_vers γ_backup ver₂ -∗
                            {{{ l_desired ↦∗{dq} desired ∗ Shield hazptr γd s (Validated backup γ_backup (node desired) n) }}}
                              try_validate n #l #ver #l_desired #backup
                            {{{ RET #(); l_desired ↦∗{dq} desired ∗ Shield hazptr γd s (Validated backup γ_backup (node desired) n) }}}.
  Proof using DISJN.
    iIntros (Hpos Hlen_desired Hle Hlenᵢ₂ Hmono Hindexordered Hubord₂ Hbackup_fresh) "#Hreadinv #Hinv #◯Hγᵥ #◯Hγᵢ #◯Hγ_abs #◯Hγₕ #◯Hγₒ #◯Hγₒcopy #◯Hγ_vers %Φ !# [Hldes Hprotected] HΦ".
    rewrite /try_validate. wp_pures.
    destruct (Nat.even ver) eqn:Heven.
    - rewrite Zrem_even even_inj Heven /=.
      wp_pures.
      wp_bind (CmpXchg _ _ _).
      iInv readN as "(%ver₃ & %log₃ & %abstraction₃ & %actual₃ & %cache₃ & %γ_backup₃ & %γ_backup₃' & %backup₃ & %backup₃' & %index₃ & %validated₃ & %t₃ & >Hver & >Hbackup & >Hγ & Hbackup_managed₃ & Hlogtokens & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₃ & >%Hidx_wf₃ & >%Hbackup_wf₃ & >%Hvalid_wf₃)" "Hcl".
      pose proof Hsizes₃ as [Hunboxed₃ Hlenactual₃ Hlencache₃ Hloglen₃].
      pose proof Hidx_wf₃ as [Hindex₃ Hlenᵢ₃ Hnodup₃ Hrange₃].
      pose proof Hbackup_wf₃ as [Hlogged₃ Habs_backup₃ Habs_backup'₃ Hdom_eq₃].
      pose proof Hvalid_wf₃ as [Htag₃ Hcons₃ Hvalidated_iff₃ Hvalidated_sub₃].
      iInv mainN as "(%ver'' & %log₃' & %abstraction₃' & %actual₃' & %γ_backup₃'' & %backup₃'' & %requests₃ & %vers₃ & %index₃' & %order₃ & %idx₃ & %t₃' & >●Hγᵥ' & >Hbackup₃' & >Hγ' & >●Hhist' & >●Hγᵣ & Hreginv & >●Hγ_vers & >●Hγᵢ' & >●Hγₒ & >%Hmain_backup₃' & >%Hmain_vers₃ & >%Hmain_order₃)" "Hcl'".
      pose proof Hmain_backup₃' as [Hlog₃' Habs₃'].
      pose proof Hmain_vers₃ as [Hdomvers₃ Hvers₃].
      pose proof Hmain_order₃ as [Hdomord₃ Hinj₃ Hidx₃ Hmono₃ Hubord₃].
      iDestruct (history_auth_agree with "●Hhist ●Hhist'") as %[<- <-].
      iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
      simplify_eq.
      destruct (decide (ver₃ = ver)) as [-> | Hneq]; first last.
      { rewrite Loc.add_0.
        wp_cmpxchg_fail.
        iMod ("Hcl'" with "[$Hγ' $●Hhist' $Hreginv $●Hγᵣ $●Hγᵥ' $●Hγ_vers $Hbackup₃' $●Hγᵢ' $●Hγₒ]") as "_".
        { iFrame_fast_pure. }
        iMod ("Hcl" with "[$Hbackup $Hγ $Hlogtokens $●Hγᵢ $●Hγᵥ $Hcache $Hlock Hver $●Hhist $●Hγ_val $Hbackup_managed₃]") as "_".
        { iExists γ_backup₃', backup₃'. iFrame_fast_pure. rewrite Loc.add_0 //. }
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros ">_ !>".
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$]"). }
      rewrite Loc.add_0.
      wp_cmpxchg_suc.
      iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ ◯Hγᵥ") as %[_ Hle₃].
      (* assert (ver₁ = ver) as -> by lia. *)
      assert (ver₂ = ver) as -> by lia.
      rewrite Heven.
      iDestruct "Hlock" as "(●Hγᵢ'' & ●Hγᵥ'' & Hcache₂)".
      iCombine "●Hγᵥ ●Hγᵥ''" as "●Hγᵥ". rewrite Qp.quarter_quarter.
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
      iCombine "●Hγᵥ ●Hγᵥ'" as "●Hγᵥ".
      iPoseProof (vers_auth_frag_agree with "●Hγ_vers ◯Hγ_vers") as "%Hagreevers".
      (* iCombine "●Hγ_vers ◯Hγ_verscopy" gives %(_ & Hvalid%fmap_to_agree_included_subseteq' & _)%auth_both_dfrac_valid_discrete. *)
      destruct (decide (1 < size log₃)) as [Hless | Hge]; first last.
      { rewrite bool_decide_eq_false_2 // in Hvers₃. simplify_eq. }
      rewrite bool_decide_eq_true_2 // in Hvers₃.
      iMod (mono_nat_own_update (S ver) with "●Hγᵥ") as "[(●Hγᵥ & ●Hγᵥ' & ●Hγᵥ'') #Hlb']".
      { lia. }
      (* iCombine "●Hhist ◯Hγₕ" gives %(_ & Hvalid%fmap_to_agree_included_subseteq%map_subseteq_size & _)%auth_both_dfrac_valid_discrete. *)
      destruct Hvers₃ as (ver'' & Hvers₃lookup & Hlevers₃ & Hub₃ & Hinvalid).
      eapply map_Forall_lookup_1 in Hagreevers as Hvalid; eauto.
      simpl in Hvalid.
      assert (ver'' = ver) as -> by lia.
      rewrite bool_decide_eq_true_2 // in Hinvalid.
      simplify_eq.
      iCombine "●Hγᵢ ●Hγᵢ''" as "●Hγᵢ".
      rewrite Qp.quarter_quarter.
      iCombine "●Hγᵢ ●Hγᵢ'" as "●Hγᵢ".
      (* rewrite Nat.Odd_div2 /= in Hlenᵢ₁ Hlenᵢ₂ Hlenᵢ₃; first last.
      { rewrite Nat.Odd_succ -Nat.even_spec //. } *)
      iPoseProof (index_auth_frag_agree' with "●Hγᵢ ◯Hγᵢ") as "%Hprefix".
      apply prefix_length_eq in Hprefix as <-; last lia.
      (* iPoseProof (index_auth_frag_agree' with "●Hγᵢ ◯Hγᵢ₂") as "%Hprefix". *)
      (* apply prefix_length_eq in Hprefix as <-; last lia. *)
      iCombine "●Hγₒ ◯Hγₒcopy" gives %(_ & Hvalidₒ'%fmap_to_agree_included_subseteq' & _)%auth_both_dfrac_valid_discrete.
      (* iCombine "●Hγᵢ ◯Hγᵢ" gives %(_ & Hvalidindex%fmap_to_agree_included_subseteq'' & _)%auth_both_dfrac_valid_discrete. *)
      iMod (index_auth_update γ_backup with "●Hγᵢ") as "[(●Hγᵢ & ●Hγᵢ' & ●Hγᵢ'') ◯Hγᵢ₃]".
      iDestruct (pointsto_agree with "Hbackup Hbackup₃'") as %[=<-%(inj Z.of_nat)].
      iDestruct (history_abs_frag_agree with "●Hhist ◯Hγ_abs") as %Hγ_backup₃.
      simplify_eq.
      replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
      iPoseProof (vers_auth_frag_agree with "●Hγₒ ◯Hγₒ") as "%Hagreeₒ".
      (* assert (order₁ ⊆ order₃) by by etransitivity. *)
      iMod ("Hcl'" with "[$Hbackup₃' $Hγ' $●Hhist' $Hreginv $●Hγᵣ $●Hγ_vers $●Hγᵥ $●Hγᵢ $●Hγₒ]") as "_".
      { iExists idx₃. iFrame_fast_pure. iSplit_facts.
        - rewrite bool_decide_eq_true_2 //.
          exists ver. repeat split; auto.
          rewrite bool_decide_eq_false_2 //.
        - apply StronglySorted_snoc.
          + apply (StronglySorted_subseteq order₂).
            { done. }
            { done. }
            { done. }
          + rewrite Forall_forall.
            intros l' Hmem i j Hts Hts'.
            simplify_eq.
            rewrite Forall_forall in Hindexordered.
            apply Hindexordered in Hmem.
            rewrite elem_of_dom in Hmem.
            destruct Hmem as [ts' Hts''].
            rewrite map_subseteq_spec in Hvalidₒ'.
            apply Hvalidₒ' in Hts'' as ?.
            simplify_eq.
            apply Hubord₂ in Hts''. lia. }
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_add /=.
      (* rewrite Heven in  *)
      (* iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ₁") as "%H'". *)
      (* destruct Hvalidated₃ as [-> | ([=] & _ & _ & _)]. *)
      iModIntro.
      iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ' $●Hγᵥ'' $Hcache $Hbackup Hver $●Hhist $●Hγ_val $Hbackup_managed₃]") as "_".
      { rewrite even_succ_negb Heven /=.
        iExists γ_backup, backup. rewrite Loc.add_0. iFrame_fast "∗". iPureIntro.
        repeat split; rewrite ?even_succ_negb ?Heven /= ?last_snoc; auto.
        - rewrite length_app /= Nat.add_1_r Hlenᵢ₃. do 2 f_equal. rewrite -Nat.Even_div2 // -Nat.even_spec //.
        - apply NoDup_app. repeat split; first done.
          + rewrite Forall_forall in Hindexordered.
            intros γ_l Hγ_l%Hindexordered ->%list_elem_of_singleton. 
            rewrite elem_of_dom in Hγ_l.
            destruct Hγ_l as [ts Hts]. simplify_eq.
          + apply NoDup_singleton.
        - rewrite Forall_app. split; first done. rewrite Forall_singleton.
          rewrite -Hdomord₃ elem_of_dom. eauto.
        - rewrite bool_decide_eq_false_2 //. rewrite bool_decide_eq_false_2 // in Htag₃.
        - rewrite bool_decide_eq_false_2 // in Htag₃.
        - by apply Hvalidated_iff₃.
        - by apply Hvalidated_iff₃. }
      iModIntro.
      wp_pures.
      wp_bind (array_copy_to _ _ _).
      wp_apply (wp_array_copy_to_half _ _ _ _ _ _ _ _ _ cache₃ desired with "[//] [$] [-]").
      { done. }
      { done. }
      iIntros "!> [Hdst Hsrc]".
      wp_pures.
      wp_bind (_ <- _)%E.
      iInv readN as "(%ver₄ & %log₄ & %abstraction₄ & %actual₄ & %cache₄ & %γ_backup₄ & %γ_backup₄' & %backup₄ & %backup₄' & %index₄ & %validated₄ & %t₄ & >Hver & >Hbackup & >Hγ & Hbackup_managed & Hlogtokens & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₄ & >%Hidx_wf₄ & >%Hbackup_wf₄ & >%Hvalid_wf₄)" "Hcl".
      pose proof Hsizes₄ as [Hunboxed₄ Hlenactual₄ Hlencache₄ Hloglen₄].
      pose proof Hidx_wf₄ as [Hindex₄ Hlenᵢ₄ Hnodup₄ Hrange₄].
      pose proof Hbackup_wf₄ as [Hlogged₄ Habs_backup₄ Habs_backup'₄ Hdom_eq₄].
      pose proof Hvalid_wf₄ as [Htag₄ Hcons₄ Hvalidated_iff₄ Hvalidated_sub₄].
      iInv mainN as "(%ver₄' & %log₄' & %abstraction₄' & %actual₄' & %γ_backup₄'' & %backup₄'' & %requests₄ & %vers₄ & %index₄' & %order₄ & %idx₄ & %t₄' & >●Hγᵥ'' & >Hbackup₄' & >Hγ' & >●Hhist' & >●Hγᵣ & Hreginv & >●Hγ_vers & >●Hγᵢ' & >●Hγₒ & >%Hmain_backup₄' & >%Hmain_vers₄ & >%Hmain_order₄)" "Hcl'".
      pose proof Hmain_backup₄' as [Hlog₄' Habs₄'].
      pose proof Hmain_vers₄ as [Hdomvers₄ Hvers₄].
      pose proof Hmain_order₄ as [Hdomord₄ Hinj₄ Hidx₄ Hmono₄ Hubord₄].
      rewrite Loc.add_0.
      wp_store.
      change 2%Z with (Z.of_nat 2). simplify_eq.
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ ->].
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ' ●Hγᵥ''") as %[_ <-].
      iCombine "●Hγᵥ ●Hγᵥ'" as "●Hγᵥ".
      rewrite Qp.quarter_quarter.
      iCombine "●Hγᵥ ●Hγᵥ''" as "●Hγᵥ".
      iMod (mono_nat_own_update (S (S ver)) with "●Hγᵥ") as "[(●Hγᵥ & ●Hγᵥ' & ●Hγᵥ'') #Hlb₃]".
      { lia. }
      iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ''") as %<-.
      iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      iDestruct (history_auth_agree with "●Hhist ●Hhist'") as %[<- <-].
      iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
      replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
      iPoseProof (array_frac_add with "Hcache Hdst") as "[Hcache ->]".
      { lia. }
      rewrite dfrac_op_own Qp.half_half.
      iMod ("Hcl'" with "[$Hbackup₄' $Hγ' $●Hhist' $Hreginv $●Hγᵣ $●Hγ_vers $●Hγᵥ $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame_fast_pure. iSplit_facts.
        destruct (decide (1 < size log₄)).
        - rewrite bool_decide_eq_true_2 //. 
          rewrite bool_decide_eq_true_2 // in Hvers₄.
          destruct Hvers₄ as (ver₄' & Hver₄' & Hle₄ & Hub₄ & Hinvalid₄).
          exists ver₄'. repeat split; auto.
          rewrite bool_decide_eq_false_2 //. lia.
        - rewrite bool_decide_eq_false_2 //. 
          rewrite bool_decide_eq_false_2 // in Hvers₄. }
      rewrite -Nat2Z.inj_add.
      destruct (decide (t₄ = 0)) as [-> | Hinvalid₄].
      { simpl in Htag₄. destruct Htag₄ as [HOdd%Nat.Even_succ _].
        exfalso. apply (Nat.Even_Odd_False ver).
        - rewrite -Nat.even_spec //.
        - done. }
      iDestruct "Hcache" as "[Hcache Hcache']".
      simpl in Hlenᵢ₄.
      iPoseProof (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ₃") as "%Hagreeᵢ₄".
      rewrite Hlenᵢ₂ -Nat.Even_div2 in Hagreeᵢ₄; first last.
      { rewrite -Nat.even_spec //. }
      pose proof Hindex₄ as Hindex₄'.
      rewrite last_lookup Hlenᵢ₄ Hagreeᵢ₄ /= in Hindex₄'.
      injection Hindex₄' as <-.
      iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ") as "%Hbackup₃".
      iDestruct (history_abs_frag_agree with "●Hhist ◯Hγ_abs") as %Hγ_backup₄.
      pose proof Htag₄ as Htag₄'.
      rewrite bool_decide_eq_false_2 // in Htag₄'.
      simplify_eq.
      iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ ●Hγᵢ'' $●Hγᵥ' ●Hγᵥ'' $Hcache Hcache' $Hbackup Hver ●Hhist $●Hγ_val $Hbackup_managed]") as "_".
      { rewrite Loc.add_0. iFrame_fast "∗".
        iSplit_facts;
          solve
            [ auto
            | by rewrite Nat.Odd_div2 // Nat.Odd_succ Nat.Even_succ Nat.Odd_succ -Nat.even_spec
            | by rewrite /= Heven
            | rewrite /= Heven; by iFrame ]. }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros ">_ !>".
      wp_pures.
      wp_bind (CmpXchg _ _ _)%E.
      iClear "Hlock".
      iInv readN as "(%ver₅ & %log₅ & %abstraction₅ & %actual₅ & %cache₅ & %γ_backup₅ & %γ_backup₅' & %backup₅ & %backup₅' & %index₅ & %validated₅ & %t₅ & >Hver & >Hbackup & >Hγ & Hbackup_managed & Hlogtokens & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₅ & >%Hidx_wf₅ & >%Hbackup_wf₅ & >%Hvalid_wf₅)" "Hcl".
      pose proof Hsizes₅ as [Hunboxed₅ Hlenactual₅ Hlencache₅ Hloglen₅].
      pose proof Hidx_wf₅ as [Hindex₅ Hlenᵢ₅ Hnodup₅ Hrange₅].
      pose proof Hbackup_wf₅ as [Hlogged₅ Habs_backup₅ Habs_backup'₅ Hdom_eq₅].
      pose proof Hvalid_wf₅ as [Htag₅ Hcons₅ Hvalidated_iff₅ Hvalidated_sub₅].
      iInv mainN as "(%ver₅' & %log₅' & %abstraction₅' & %actual₅' & %γ_backup₅'' & %backup₅'' & %requests₅ & %vers₅ & %index₅' & %order₅ & %idx₅ & %t₅' & >●Hγᵥ' & >Hbackup₅' & >Hγ' & >●Hhist' & >●Hγᵣ & Hreginv & >●Hγ_vers & >●Hγᵢ' & >●Hγₒ & >%Hmain_backup₅' & >%Hmain_vers₅ & >%Hmain_order₅)" "Hcl'".
      pose proof Hmain_backup₅' as [Hlog₅' Habs₅'].
      pose proof Hmain_vers₅ as [Hdomvers₅ Hvers₅].
      pose proof Hmain_order₅ as [Hdomord₅ Hinj₅ Hidx₅ Hmono₅ Hubord₅].
      iDestruct (pointsto_agree with "Hbackup Hbackup₅'") as %[=<-<-%(inj Z.of_nat)].
      (* change 2%Z with (Z.of_nat 2). simplify_eq. *)
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
      iDestruct (history_auth_agree with "●Hhist ●Hhist'") as %[<- <-].
      iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
      simplify_eq.
      iPoseProof (history_abs_frag_agree with "●Hhist ◯Hγ_abs") as "%Hagree_abs₅".
      simplify_eq.
      destruct (decide (Some (Loc.blk_to_loc backup₅) &ₜ t₅ = Some (Loc.blk_to_loc backup₄') &ₜ 1)) as [[=->->] | Hneq]; first last.
      { wp_cmpxchg_fail.
        iMod ("Hcl'" with "[$Hbackup₅' $Hγ' $●Hhist' $●Hγᵣ $●Hγᵥ' $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
        { iFrame_fast_pure. }
        iMod ("Hcl" with "[$Hγ $Hbackup_managed $●Hhist $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hlogtokens $Hver $Hbackup $●Hγ_val]") as "_".
        { iExists γ_backup₅'. iFrame_fast_pure. }
        iApply fupd_mask_intro.
        { set_solver. }
        iIntros ">_ !>".
        wp_pures.
        iModIntro.
        iApply ("HΦ" with "[$]"). }
      iPoseProof (pointsto_combine with "Hbackup Hbackup₅'") as "[Hbackup _]".
      rewrite dfrac_op_own Qp.half_half.
      wp_cmpxchg_suc.
      { done. }
      iDestruct (shield_managed_agree with "Hprotected Hbackup_managed") as %<-.
      iPoseProof (vers_auth_frag_agree with "●Hγₒ ◯Hγₒ") as "%Hagreeₒ₄". simplify_eq.
      iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ Hlb₃") as %[_ Hless₃].
      iPoseProof (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ₃") as "%Hagreeᵢ₂₄".
      rewrite Hlenᵢ₂ -Nat.Even_div2 in Hagreeᵢ₂₄; first last.
      { rewrite -Nat.even_spec //. }
      destruct (decide (S (S ver) = ver₅)) as [<- | Hneq]; first last.
      { iExFalso.
        destruct ver₅ as [|[|[|ver₄]]]; try lia.
        simpl in Hlenᵢ₅.
        rewrite last_lookup Hlenᵢ₅ /= in Hindex₅.
        assert (Nat.div2 ver < S (Nat.div2 ver₄)) as Hnever.
        { assert (ver ≤ ver₄) as Hmono'%div2_mono by lia. lia. }
        (* apply NoDup_lookup_ne with (i := S (Nat.div2 ver)) (x := ldes') in Hindex₄ as Hneqq; auto; first last.
        { intros [=Heq]. assert (ver ≤ ver₄) as Hmono%div2_mono by lia. lia. } *)
        eapply StronglySorted_lookup_lt with (i := S (Nat.div2 ver)) (j := S (S (Nat.div2 ver₄))) in Hmono₅; eauto; last lia.
        rewrite /gmap_mono in Hmono₄.
        assert (is_Some (order₅ !! γ_backup₅')) as [ts₅ Hts₅].
        { rewrite -elem_of_dom Hdomord₅.
          rewrite Forall_forall in Hrange₅.
          apply Hrange₅. rewrite list_elem_of_lookup.
          eauto. }
          rewrite /gmap_mono in Hmono₅.
        pose proof (Hmono₅ _ _ Hidx₅ Hts₅) as Hle'.
        rewrite map_Forall_lookup in Hubord₄. 
        apply Hubord₅ in Hts₅. lia. }
      iDestruct "Hbackup" as "[Hbackup Hbackup']".
      change #backup₄' with #(Some (Loc.blk_to_loc backup₄') &ₜ O).
      iPoseProof (vers_auth_frag_agree with "●Hγ_vers ◯Hγ_vers") as "%Hagreever".
      iMod ("Hcl'" with "[$Hbackup $Hγ' $●Hhist' $Hreginv $●Hγᵣ $●Hγ_vers $●Hγᵥ' $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame_fast_pure. iSplit_facts.
        destruct (decide (1 < size log₅)).
        { rewrite bool_decide_eq_true_2 //.
          rewrite bool_decide_eq_true_2 // in Hvers₅.
          destruct Hvers₅ as (ver'' & Hvers₅ & Hlever' & Hubvers₅ & Hinvalid₅).
          simplify_eq.
          exists ver. repeat split; auto.
          rewrite bool_decide_eq_false_2 //. lia. }
        { rewrite bool_decide_eq_false_2 //.
          rewrite bool_decide_eq_false_2 // in Hvers₅. } }
      iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ") as "%Hldes₅".
      rewrite Hldes₅ /= in Hlogged₅.
      simplify_eq.
      simpl in Hcons₅.
      rewrite Heven in Hcons₅.
      pose proof Hindex₅ as Hindex₅'.
      rewrite last_lookup Hlenᵢ₅ Nat.Odd_div2 /= in Hindex₅; first last.
      { rewrite Nat.Odd_succ Nat.Even_succ Nat.Odd_succ -Nat.even_spec //. }
      simplify_eq.
      iMod (validated_auth_update γ_backup with "●Hγ_val") as "[●Hγ_val _]".
      iMod ("Hcl" with "[$Hγ $Hlogtokens $●Hγᵢ $●Hγᵥ $Hcache $Hbackup' $Hver $●Hhist $Hlock $●Hγ_val $Hbackup_managed]") as "_".
      { iFrame_fast_pure. iPureIntro.
        - repeat split; auto.
          + rewrite Nat.Even_succ Nat.Odd_succ -Nat.even_spec //.
          + rewrite Hldes₅ /= Heven //.
          + intros _. set_solver.
            (* simpl. rewrite Heven Hldes₅ //=. *)
          + assert (γ_backup ∈ dom log₅).
            { rewrite elem_of_dom //. }
            set_solver. }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros ">_ !>".
      wp_pures.
      iModIntro.
      iApply ("HΦ" with "[$]").
    - rewrite Zrem_odd odd_inj even_odd_negb_eq Heven /=.
      destruct ver as [|ver].
      { done. }
      simpl. wp_pures.
      iApply ("HΦ" with "[$]").
  Qed.

  Lemma fupd_split_right `{!invGS Σ} (E1 E2 E3 : coPset) (P : iProp Σ) :
    E2 ⊆ E3 →
    (|={E1,E3}=> P) ⊢ |={E1,E2}=> |={E2,E3}=> P.
  Proof.
    iIntros (HE) "H".
    iApply (fupd_trans E1 E3 E2).
    (* Goal: |={E1,E3}=> |={E3,E2}=> |={E2,E3}=> P *)
    iApply (fupd_mono with "H").
    iIntros "HP".
    iApply (fupd_mask_intro_subseteq E3 E2); first done.
    iExact "HP".
  Qed.

  Lemma execute_lp 
    (backup backup₁' new_backup : blk) 
    (γ_backup γ_backup₁ γ_backup₁' γ_new_backup : gname)
    (l lexp ldes : loc)
    (expected desired cache actual₁ : list val)
    (abstraction₁ : gmap gname blk)
    (log₁ : gmap gname (list val))
    (requests₁ : list (gname * gname * gname))
    (vers₁ order₁ : gmap gname nat)
    (index₁ : list gname)
    (validated₁ : gset gname)
    (γ γᵥ γₕ γᵣ γᵢ γ_val γ_vers γₒ γd γ_abs γₑ γₗ γₜ : gname)
    (dq dq' : dfrac)
    (Φ : val → iProp Σ)
    (idx₁ ver ver₁ i n : nat) s s' (d : loc) pvs :
    n > 0 →
    length cache = n →
    length expected = n →
    length desired = n →
    expected ≠ desired →
    read_index_wf ver₁ index₁ log₁ γ_backup₁' →
    (if Nat.even ver₁ then log₁ !! γ_backup₁' = Some cache else True) →
    map_Forall (λ _ value, length value = length expected) log₁ →
    validated₁ ⊆ dom log₁ →
    dom log₁ = dom abstraction₁ →
    main_order_wf log₁ order₁ index₁ γ_backup₁ idx₁ →
    (if bool_decide (1 < size log₁) then
      ∃ ver' : nat, ver' ≤ ver₁ ∧ map_Forall (λ _ ver'', ver'' ≤ ver') vers₁
    else vers₁ = ∅) →
    dom vers₁ ⊂ dom log₁ →
    main_backup_wf log₁ abstraction₁ actual₁ γ_backup₁ backup →
    Forall val_is_unboxed desired →
    abstraction₁ !! γ_backup₁' = Some backup₁' →
    cas_succ_res pvs →
    (* Persistent hypotheses *)
    inv readN (read_inv γ γᵥ γₕ γᵢ γ_val γd γ_abs l n) -∗
    inv mainN (cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ γ_abs γd l n) -∗
    inv casN (cas_inv Φ γ γₑ γₗ γₜ γ_backup γd backup lexp ldes dq dq' expected desired s pvs) -∗
    registered γᵣ i γₗ γₑ γ_backup -∗
    abstraction_frag_own γ_abs γ_backup backup -∗
    log_frag_own γₕ γ_backup expected -∗
    (l +ₗ domain_off) ↦□ #d -∗
    hazptr.(IsHazardDomain) γd d -∗
    hazptr.(Managed) γd backup γ_backup₁ n (node actual₁) -∗
    hazptr.(Shield) γd s' (NotValidated new_backup) -∗
    (* Token for linearization *)
    token γₜ -∗
    (* Token for backup *)
    token γ_new_backup -∗
    new_backup ↦∗ desired -∗
    †new_backup…n -∗
    (l +ₗ version_off) ↦ #ver₁ -∗
    log_tokens (dom log₁) -∗
    mono_nat_auth_own_frac γᵥ (1/4) ver₁ -∗
    (l +ₗ cache_off) ↦∗{#1/2} cache -∗
    (if Nat.even ver₁ then
      index_auth_own γᵢ (1/4) index₁ ∗
      mono_nat_auth_own_frac γᵥ (1/4) ver₁ ∗
      (l +ₗ cache_off) ↦∗{#1/2} cache
    else True) -∗
    (▷ read_inv γ γᵥ γₕ γᵢ γ_val γd γ_abs l n ={⊤ ∖ ↑readN, ⊤}=∗ emp) -∗
    mono_nat_auth_own_frac γᵥ (1/2) ver₁ -∗
    registry γᵣ requests₁ -∗
    registry_inv γ γd backup actual₁ requests₁ abstraction₁ -∗
    vers_auth_own γ_vers 1 vers₁ -∗
    index_auth_own γᵢ (1/2) index₁ -∗
    vers_auth_own γₒ 1 order₁ -∗
    (▷ cached_wf_inv γ γᵥ γₕ γᵢ γᵣ γ_vers γₒ γ_abs γd l n ={⊤ ∖ ↑readN ∖ ↑mainN, ⊤ ∖ ↑readN}=∗ emp) -∗
    index_auth_own γᵢ (1/4) index₁ -∗
    validated_auth_own γ_val 1 validated₁ -∗
    ghost_var_frac γ (1/2) (γ_backup₁, actual₁) -∗
    (l +ₗ backup_off) ↦ #(Some (Loc.blk_to_loc new_backup) &ₜ 1%nat) -∗
    history γₕ γ_abs 1 log₁ abstraction₁
    ={⊤ ∖ ↑readN ∖ ↑mainN, ⊤}=∗
      ⌜actual₁ = expected⌝ ∗
      ⌜γ_backup = γ_backup₁⌝ ∗
      ⌜log₁ !! γ_new_backup = None⌝ ∗
      (lexp ↦∗{dq} expected ∗ ldes ↦∗{dq'} desired -∗ Φ #true) ∗
      vers_frag_own γ_vers γ_new_backup ver₁ ∗
      abstraction_frag_own γ_abs γ_new_backup new_backup ∗
      log_frag_own γₕ γ_new_backup desired ∗
      vers_frag_own γₒ γ_new_backup (S idx₁) ∗
      (* Protection for old backup *)
      hazptr.(Shield) γd s (Validated backup γ_backup (node expected) n) ∗
      (* Protection for new backup *)
      hazptr.(Shield) γd s' (Validated new_backup γ_new_backup (node desired) n) ∗
      (* Managed for old backup *)
      Managed hazptr γd backup γ_backup n (node expected).
  Proof using DISJN.
    iIntros (Hpos Hlen_cache Hlen_exp Hlen_des Hne [Hindex₁ Hlenᵢ₁ Hnodup₁ Hrange₁] Hcache₁ Hloglen₁
            Hvallogged Hdomlogabs [Hdomord Hinj₁ Hidx₁ Hmono₁ Hubord₁] Hvers₁ Hdomvers₁ [Hactual₁ Habs]
            Hunboxed Habs' Hsucc).
    iIntros "#Hreadinv #Hinv #Hcasinv #◯Hγᵣ #◯Hγ_abs #◯Hγₕ #Hd #Hdom".
    iIntros "Hmanaged Hshield Hγₜ Htok Hnew_backup †Hnew_backup Hver Hlogtokens ●Hγᵥ Hcache".
    iIntros "Hlock Hcl ●Hγᵥ' ●Hγᵣ Hreginv ●Hγ_vers ●Hγᵢ' ●Hγₒ Hcl' ●Hγᵢ ●Hγ_val Hγ Hbackup₁ ●Hhist".
    iMod (hazptr.(hazard_domain_register) (node desired) with "Hdom [$Hnew_backup †Hnew_backup]") as "Hmanaged'".
    { solve_ndisj. }
    { rewrite Hlen_des. by iFrame. }
    iMod (hazptr.(shield_validate) with "Hdom Hmanaged' Hshield") as "[Hmanaged' Hshield]".
    { solve_ndisj. }
    (* Derive agreement facts from auth-frag combinations *)
    iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hagree".
    iPoseProof (history_abs_frag_agree with "●Hhist ◯Hγ_abs") as "%Hagree_abs".
    iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ") as "%Hlogged₁".
    iAssert (⌜backup ≠ new_backup⌝)%I as %Hnoaba.
    { iIntros (<-). simplify_eq.
      iDestruct (hazptr.(managed_exclusive) with "Hmanaged Hmanaged'") as %[]. }
    rewrite -(take_drop_middle _ _ _ Hagree).
    rewrite /registry_inv big_sepL_app big_sepL_cons /request_inv.
    iDestruct "Hreginv" as "(Hlft & (%lexp' & %Hlexp_abs & Hlin & %Φ' & %γₜ' & %lexp_src' & %ldes' & %dq₁ & %dq₁' & %expected' & %desired' & %s'' & %pvs' & Hγₑ & _) & Hrht)".
    iInv casN as "[[S [(>Hcredit & HΦ & [%b >Hγₑ'] & >Hlin') | (>[Hcredit Hcredit'] & AU & >Hγₑ' & >Hlin')]] | (>Hlintok & [%b >Hγₑ'] & [%b' >Hlin'])]" "Hclose".
    (* Assumes we have already returned, which is impossible *)
    3: iCombine "Hγₜ Hlintok" gives %[].
    { (* Assumes we have already linearized, which again is impossible *)
      iCombine "Hlin Hlin'" gives %[_ ?%bool_decide_eq_false]. simplify_eq. }
    iMod (lc_fupd_elim_later with "Hcredit' S") as "S".
    iDestruct (shield_managed_agree with "S Hmanaged") as %<-.
    iCombine "Hγₑ Hγₑ'" gives %[_ <-%bool_decide_eq_true].
    simplify_eq.
    iMod (ghost_var_update_halves false with "Hγₑ Hγₑ'") as "[Hγₑ Hγₑ']".
    rewrite bool_decide_eq_true_2 //. 
    (* Now update the ghost state. This CAS will linearize first, invalidating all other pending CAS's and causing them to fail *)
    iMod (ghost_var_update_halves false with "Hlin Hlin'") as "[Hlin Hlin']".
    (* Execute our LP *)
    iMod (lc_fupd_elim_later with "Hcredit AU") as "AU".
    iMod "AU" as (vs) "[[%γ_backup'' Hγ'] [_ Hconsume]]".
    { set_solver. }
    rewrite /CachedWF.
    iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
    iMod (ghost_var_update_halves (γ_new_backup, desired) with "Hγ Hγ'") as "[Hγ Hγ']".
    simplify_eq.
    rewrite bool_decide_eq_true_2; last done.
    iMod ("Hconsume" with "[$Hγ']") as "HΦ".
    { iPureIntro. by right. }
    iMod ("Hclose" with "[Hγₜ Hlin' Hγₑ']") as "_".
    { iRight. iFrame. }
    rewrite Hdomlogabs.
    (* Now linearize all other CAS's (in arbitrary order) *)
    iMod (linearize_cas with "Htok Hmanaged' Hlogtokens Hγ Hlft") as "(Htok & Hmanaged' & Hlogtokens & Hγ & Hlft)".
    { lia. }
    { lia. }
    { done. }
    { done. }
    iMod (linearize_cas with "Htok Hmanaged' Hlogtokens Hγ Hrht") as "(Htok & Hmanaged' & Hlogtokens & [Hγ Hγ'] & Hrht)".
    { lia. }
    { lia. }
    { done. }
    { done. }
    replace (1 / 2 / 2)%Qp with (1 / 4)%Qp by compute_done.
    (* We now will insert this backup into the log *)
    (* First, we allocate a token representing the pointsto for the backup *)
    (* Now update the log *)
    rewrite -Hdomlogabs.
    iAssert (⌜γ_new_backup ∉ dom log₁⌝)%I as "%Hγ_new_backup_fresh".
    { rewrite pure_impl. iIntros (Helem_of%log_tokens_impl). 
      iPoseProof (Helem_of with "[$]") as "Htok'".
      iCombine "Htok Htok'" gives %[]. }
    iMod (history_insert γ_new_backup desired new_backup with "●Hhist") as "(●Hhist & ●Hhist' & #◯Hγₕ₁ & #◯Hγ_abs₁)".
    { rewrite -not_elem_of_dom //. }
    { rewrite -not_elem_of_dom //. set_solver. }
    iDestruct "Hbackup₁" as "[Hbackup₁ Hbackup₁']".
    assert (O < size log₁) as Hlogsome₁.
    { assert (size log₁ ≠ 0); last lia.
      rewrite map_size_ne_0_lookup.
      naive_solver. }
    iMod (vers_auth_update γ_new_backup ver₁ with "●Hγ_vers") as "[●Hγ_vers #◯Hγ_vers]".
    { rewrite -not_elem_of_dom. set_solver. }
    (* iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ ◯Hγₒcopy]". *)
    (* iMod (own_auth_split_self' with "●Hγ_vers") as "[●Hγ_vers ◯Hγ_verscopy]". *)
    assert (size (<[γ_new_backup := desired]> log₁) > 1) as Hvers₁multiple.
    { rewrite map_size_insert_None //.
      - lia.
      - rewrite -not_elem_of_dom //.  }
    assert (map_Forall (λ _ ver'', ver'' ≤ ver₁) (<[γ_new_backup := ver₁]> vers₁)) as Hub₁.
    { destruct (decide (size log₁ = 1)) as [Hsing | Hsing].
      - rewrite bool_decide_eq_false_2 in Hvers₁; last lia.
        subst. rewrite insert_empty map_Forall_singleton //.
      - rewrite bool_decide_eq_true_2 in Hvers₁; last lia.
        rewrite map_Forall_insert; first last.
        { rewrite -not_elem_of_dom. set_solver. }
        destruct Hvers₁ as (ver_invalid₁ & Hver_invalid_le₁ & Hub).
        split; first done.
        eapply map_Forall_impl; first done.
        intros l' ver''.
        simpl. lia. }
    iMod (vers_auth_update γ_new_backup (S idx₁) with "●Hγₒ") as "[●Hγₒ ◯Hγₒ]".
    { rewrite -not_elem_of_dom. set_solver. }
    iMod ("Hcl'" with "[$●Hγ_vers $●Hγᵥ' $●Hγᵣ $●Hhist $Hbackup₁ $Hγ Hlft Hrht Hlin Hγₑ $●Hγₒ $●Hγᵢ']") as "_".
    { iExists (S idx₁).
      rewrite (take_drop_middle _ _ _ Hagree).
      iNext. iSplitL.
      { iApply (registry_inv_mono _ _ _ _ _ abstraction₁).
        { apply insert_subseteq. rewrite -not_elem_of_dom. set_solver. }
        rewrite -{3}(take_drop_middle _ _ _ Hagree) /registry_inv.
        iFrame.
        rewrite /request_inv.
        iFrame_fast "#".
        rewrite bool_decide_eq_false_2; last first.
        { intros <-. congruence. }
        rewrite bool_decide_eq_false_2 //.
        iFrame. }
      iPureIntro. split_and!.
      - constructor; by rewrite lookup_insert_eq.
      - constructor.
        + do 2 rewrite dom_insert. set_solver.
        + rewrite bool_decide_eq_true_2; last lia.
          exists ver₁.
          rewrite lookup_insert_eq.
          repeat split; auto.
          rewrite bool_decide_eq_true_2 //.
      - constructor.
        + set_solver.
        + apply gmap_injective_insert; last done.
          intros [loc Hcontra]%elem_of_map_img.
          eapply map_Forall_lookup_1 in Hcontra; last done.
          simpl in Hcontra. lia.
        + rewrite lookup_insert_eq //.
        + apply gmap_mono_alloc; last done.
          rewrite Forall_forall in Hrange₁. auto.
        + rewrite map_Forall_insert //.
          * split; first done.
            eapply map_Forall_impl; eauto.
          * rewrite -not_elem_of_dom. set_solver. }
    assert (γ_backup₁' ≠ γ_new_backup) as Hnoaba'.
    { intros ->. 
      apply last_Some_elem_of in Hindex₁.
      rewrite Forall_forall in Hrange₁.
      apply Hrange₁ in Hindex₁.
      rewrite elem_of_dom in Hindex₁.
      destruct Hindex₁ as [vs Hvs%elem_of_dom_2].
      contradiction. }
    iPoseProof (log_tokens_insert with "Hlogtokens Htok") as "Hlogtokens".
    iMod ("Hcl" with "[$Hγ' $●Hγᵢ $●Hγᵥ $Hcache $Hlock $Hbackup₁' $Hver $●Hhist' $●Hγ_val Hlogtokens Hmanaged']") as "_".
    { iFrame_fast. iExists γ_backup₁', backup₁'. iSplitL "Hmanaged'".
      { iNext. rewrite Hlen_des //. }
      iSplit_facts;
        solve
          [ rewrite map_Forall_insert;
              [ rewrite -Hlen_exp; auto with lia | rewrite -not_elem_of_dom // ]
          | by rewrite dom_insert_L
          | by rewrite lookup_insert_eq
          | by rewrite lookup_insert_ne
          | eapply Forall_impl; first done; simpl; set_solver
          | destruct (Nat.even ver₁) eqn:Heven₁; last done;
              rewrite lookup_insert_ne; auto
          | split; last done; intros Helem_of; set_solver
          | intros Helem_of; set_solver
          | rewrite dom_insert; set_solver
          | do 2 rewrite dom_insert_L; by f_equal ]. }
    iModIntro.
    repeat iSplit; auto.
    { iPureIntro. rewrite -not_elem_of_dom //. }
    rewrite Hlen_des Hlen_exp.
    iFrame_fast.
  Qed.

  Lemma Forall2_symmetric {A} (R : relation A) :
    Symmetric R → Symmetric (Forall2 R).
  Proof.
    intros Hsym xs ys Hxy.
    induction Hxy; by constructor.
  Qed.

  Lemma all_vals_compare_safe vs vs' :
    Forall val_is_unboxed vs →
      length vs = length vs' →
        Forall2 vals_compare_safe vs vs'.
  Proof.
    revert vs'. induction vs as [| v vs IH].
    - intros vs' Hunboxed Hlen. 
      symmetry in Hlen. 
      rewrite length_zero_iff_nil in Hlen. simplify_eq. constructor.
    - intros vs' Hunboxed Hlen.
      destruct vs' as [|v' vs'].
      { done. }
      simplify_eq. inv Hunboxed. constructor.
      + by left.
      + auto.
  Qed.

  Lemma cached_wf_cas_spec :
    big_atomic_cas_spec' cached_wfN hazptrN (cached_wf_cas hazptr) CachedWF IsCachedWF.
  Proof using DISJN.
    iIntros (γ v n lexp ldes dq dq' expected desired p pvs Hlen_exp Hlen_des Hexpunboxed Hdesunboxed) "(%l & %d & %γₕ & %γᵥ & %γᵣ & %γᵢ & %γₒ & %γ_vers & %γ_val & %γ_abs & %γd & %Hpos & -> & #Hd & #Hd_domain & #Hreadinv & #Hinv) Hlexp Hldes Hp %Φ AU".
    iPoseProof (AU_cas_intro with "AU") as "AU". rewrite /AU_cas.
    wp_rec.
    wp_pure credit:"Hcredit".
    wp_pures.
    wp_bind (! _)%E.
    iInv readN as "(%ver & %log & %abstraction & %actual & %cache & %γ_backup & %γ_backup' & %backup & %backup' & %index & %validated & %t & >Hver & >Hbackup & >Hγ & Hbackup_managed & Hlogtokens & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes & >%Hidx_wf & >%Hbackup_wf & >%Hvalid_wf)" "Hcl".
    pose proof Hsizes as [Hunboxed Hlenactual Hlencache Hloglen].
    pose proof Hidx_wf as [Hindex Hlenᵢ Hnodup Hrange].
    pose proof Hbackup_wf as [Hlogged Habs_backup Habs_backup' Hdom_eq].
    pose proof Hvalid_wf as [Htag Hcons Hvalidated_iff Hvalidated_sub].
    wp_load.
    iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#Hlb".
    iMod ("Hcl" with "[-AU Hlexp Hldes Hp]") as "_".
    { iExists ver, log, abstraction, actual, cache, γ_backup, γ_backup', backup, backup', index, validated, t.
    rewrite Loc.add_0. iFrame_fast. }
    iModIntro.
    wp_pures.
    wp_load.
    wp_pure credit:"Hcredit".
    wp_pure credit:"Hcredit'".
    wp_pures.
    wp_apply (hazptr.(shield_new_spec) with "[//] [//]") as (s) "S".
    { set_solver. }
    wp_pures.
    wp_apply (wp_array_clone_wk with "[//] [//] [//]").
    { done. }
    iIntros (vers vdst dst) "(Hdst & %Hlen' & %Hsorted & %Hbound & #Hcons)".
    wp_pures. 
    awp_apply (hazptr.(shield_protect_tagged_spec) with "[//] [$]").
    { solve_ndisj. }
    rewrite /atomic_acc /=. 
    iInv readN as "(%ver₁ & %log₁ & %abstraction₁ & %actual₁ & %cache₁ & %γ_backup₁ & %γ_backup₁' & %backup₁ & %backup₁' & %index₁ & %validated₁ & %t₁ & >Hver & >Hbackup & >Hγ & Hbackup_managed₁ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₁ & >%Hidx_wf₁ & >%Hbackup_wf₁ & >%Hvalid_wf₁)" "Hcl".
    pose proof Hsizes₁ as [Hunboxed₁ Hlenactual₁ Hlencache₁ Hloglen₁].
    pose proof Hidx_wf₁ as [Hindex₁ Hlenᵢ₁ Hnodup₁ Hrange₁].
    pose proof Hbackup_wf₁ as [Hlogged₁ Habs_backup₁ Habs_backup'₁ Hdom_eq₁].
    pose proof Hvalid_wf₁ as [Htag₁ Hcons₁ Hvalidated_iff₁ Hvalidated_sub₁].
    iInv mainN as "(%ver₁' & %log₁' & %abstraction₁' & %actual₁' & %γ_backup₁'' & %backup₁'' & %requests₁ & %vers₁ & %index₁' & %order₁ & %idx₁ & %t₁' & >●Hγᵥ' & >Hbackup' & >Hγ' & >●Hhist' & >●Hγᵣ & Hreginv & >●Hγ_vers & >●Hγᵢ' & >●Hγₒ & >%Hmain_backup₁ & >%Hmain_vers & >%Hmain_order₁)" "Hcl'".
    pose proof Hmain_backup₁ as [Hlog₁ Habs₁].
    pose proof Hmain_vers as [Hdomvers Hvers₁].
    pose proof Hmain_order₁ as [Hdomord₁ Hinj₁ Hidx₁ Hmono₁ Hubord₁].
    iDestruct (history_auth_agree with "●Hhist ●Hhist'") as %[<- <-].
    iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
    iDestruct (pointsto_agree with "Hbackup Hbackup'") as %[=<-<-%(inj Z.of_nat)].
    iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
    iMod "AU" as (actual') "[[%backup'' Hγ''] Hlin]".
    iCombine "Hγ Hγ''" gives %[_ [=<-<-]].
    iFrame "Hbackup Hbackup_managed₁".
    iModIntro. iSplit.
    { iIntros "[Hbackup Hbackup_managed]".
      iDestruct "Hlin" as "[Habort _]".
      iMod ("Habort" with "[$Hγ'']") as "AU".
      iMod ("Hcl'" with "[$●Hγᵥ' $Hbackup' $Hγ' $●Hhist' $●Hγᵣ $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame_fast_pure. }
      iMod ("Hcl" with "[-AU Hdst Hlexp Hldes Hcredit Hcredit' Hp]") as "_".
      { iExists ver₁, log₁, abstraction₁, actual₁, cache₁, γ_backup₁, γ_backup₁', backup₁, backup₁', index₁, validated₁, t₁.
        iFrame_fast. }
      by iFrame. }
    iIntros "(Hbackup & Hmanaged & Hprotected)".
    (* iDestruct (index_auth_frag_agree with "●Hγᵢ ◯Hγᵢ") as "%Hindexagree". *)
    iMod (history_log_frag_alloc γ_backup₁ with "●Hhist") as "[●Hhist #◯Hγₕ₁]".
    { eassumption. }
    iMod (history_abs_frag_alloc γ_backup₁ with "●Hhist") as "[●Hhist #◯Hγ_abs]".
    { eassumption. }
    iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ Hlb") as %[_ Hle].
    iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#◯Hγᵥ₁".
    iMod (index_frag_alloc (Nat.div2 (S ver₁)) with  "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ₁]".
    { by rewrite last_lookup Hlenᵢ₁ in Hindex₁. }
    iMod (validated_auth_frag_alloc' γ_backup₁ with "●Hγ_val") as "[●Hγ_val #◯Hγ_val₁]".
    destruct (decide (actual₁ = expected)) as [-> | Hne]; first last.
    { iDestruct "Hlin" as "[_ Hconsume]".
      rewrite (bool_decide_eq_false_2 (actual₁ = expected)) //.
      iMod ("Hconsume" with "[$Hγ'']") as "HΦ".
      iMod ("Hcl'" with "[$●Hγᵥ' $Hbackup' $Hγ' $●Hhist' $●Hγᵣ $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame_fast_pure. }
      iMod ("Hcl" with "[-Hdst Hlexp Hldes Hcredit Hcredit' Hprotected HΦ Hp]") as "_".
      { iExists ver₁, log₁, abstraction₁, actual₁, cache₁, γ_backup₁, γ_backup₁', backup₁, backup₁', index₁, validated₁, t₁. iFrame_fast "∗". }
      iModIntro. wp_pures.
      wp_apply (read'_spec actual₁ cache₁ vdst with "[//] [//] [//] [//] [//] [//] [//] [$]"); try done.
      iIntros "[S Hcopy]".
      wp_pures.
      wp_apply (wp_array_equal with "[$Hcopy $Hlexp]").
      { lia. }
      { lia. }
      { apply all_vals_compare_safe; auto with lia. }
      iIntros "[Hcopy Hlexp]".
      rewrite (bool_decide_eq_false_2 (actual₁ = expected)) //.
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "[//] [$]").
      { solve_ndisj. }
      iIntros "_".
      wp_pures.
      iModIntro.
      iApply (cas_post_false _ _ _ _ [] with "Hp"); [done | constructor |].
      iApply ("HΦ" with "[$]"). }
    destruct (decide (expected = desired)) as [-> | Hne].
    { iDestruct "Hlin" as "[_ Hconsume]".
      rewrite (bool_decide_eq_true_2 (desired = desired)) //.
      iFrame.
      iMod ("Hconsume" with "[$Hγ'']") as "HΦ".
      { iPureIntro. by left. }
      iMod ("Hcl'" with "[$●Hγᵥ' $Hbackup' $Hγ' $●Hhist' $●Hγᵣ $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame_fast_pure. }
      iMod ("Hcl" with "[-Hdst Hlexp Hldes Hcredit Hcredit' Hprotected HΦ Hp]") as "_".
      { iExists ver₁, log₁, abstraction₁, desired, cache₁, γ_backup₁, γ_backup₁', backup₁, backup₁', index₁, validated₁, t₁. iFrame_fast "∗". }
      iModIntro.
      wp_pures.
      wp_apply (read'_spec desired cache₁ vdst with "[//] [//] [//] [//] [//] [//] [//] [$]"); try done.
      iIntros "[S Hcopy]".
      wp_pures.
      wp_apply (wp_array_equal with "[$Hcopy $Hlexp]").
      { lia. }
      { lia. }
      { apply all_vals_compare_safe; auto with lia. }
      iIntros "[Hcopy Hlexp]".
      rewrite (bool_decide_eq_true_2 (desired = desired)) //.
      wp_pures.
      wp_apply (wp_array_equal with "[$Hlexp Hldes //]").
      { done. }
      { done. }
      { apply all_vals_compare_safe; auto with lia. }
      iIntros "[Hldes Hlexp]".
      rewrite (bool_decide_eq_true_2 (desired = desired)) //.
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "[//] [$]").
      { solve_ndisj. }
      iIntros "_".
      wp_pures. iModIntro.
      iApply (cas_post_true with "Hp").
      iApply ("HΦ" with "[$]"). }
    iMod (ghost_var_alloc true) as "(%γₑ & Hγₑ & Hγₑ')".
    iMod (ghost_var_alloc true) as "(%γₗ & Hγₗ & Hγₗ')".
    iMod token_alloc as "[%γₜ Hγₜ]".
    iMod (registry_update γₗ γₑ γ_backup₁ with "●Hγᵣ") as "[●Hγᵣ #◯Hγᵣ]". 
    iDestruct "Hlin" as "[Hclose _]".
    iMod ("Hclose" with "[$Hγ'']") as "AU".
    iMod (inv_alloc casN _ (cas_inv (cas_post Φ p pvs) γ γₑ γₗ γₜ γ_backup₁ γd backup₁ lexp ldes dq dq' expected desired s pvs) with "[Hγₑ' Hγₗ' AU Hcredit Hcredit' Hprotected]") as "#Hcasinv".
    { iLeft. rewrite Hlen_exp. iFrame. iRight. iCombine "Hcredit Hcredit'" as "$". iFrame. }
    iMod ("Hcl'" with "[$●Hγᵥ' $Hbackup' $Hγ' $●Hhist' $●Hγᵣ Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ Hγₗ Hγₑ]") as "_".
    { iFrame_fast "∗".
      rewrite big_sepL_singleton /request_inv.
      iNext. iExists backup₁. iSplit; [done|].
      rewrite (bool_decide_eq_true_2 (backup₁ = backup₁)) //.
      iFrame "∗ #".
      rewrite (bool_decide_eq_true_2 (expected = expected)) //. }
    iMod ("Hcl" with "[-Hlexp Hldes Hdst Hγₜ Hp]") as "_".
    { iExists ver₁, log₁, abstraction₁, expected, cache₁, γ_backup₁, γ_backup₁', backup₁, backup₁', index₁, validated₁, t₁.
      iFrame_fast "∗". }
    iModIntro.
    wp_pures.
    wp_apply (read'_spec_inv expected cache₁ vdst with "[//] [//] [//] [//] [//] [//] [//] [$] [$]"); try done.
    iIntros "[Hγₜ Hdst]".
    wp_pures.
    wp_apply (wp_array_equal with "[$Hdst $Hlexp]").
    { done. }
    { done. }
    { by apply all_vals_compare_safe. }
    iIntros "[Hdst Hlexp]".
    rewrite (bool_decide_eq_true_2 (expected = expected)) //.
    wp_pures.
    wp_apply (wp_array_equal with "[$Hlexp $Hldes]").
    { done. }
    { done. }
    { apply all_vals_compare_safe; auto with lia. }
    iIntros "[Hlexp Hldes]".
    rewrite (bool_decide_eq_false_2 (expected = desired)) //.
    wp_pures.
    wp_apply (wp_array_clone with "[$]").
    { lia. }
    { lia. }
    iIntros (ldes') "(Hldes & Hldes' & †Hldes')".
    wp_pures.
    wp_apply (hazptr.(shield_new_spec) with "[//] [//]").
    { solve_ndisj. }
    iIntros (s') "S'".
    wp_pures.
    change #ldes' with #(oblk_to_lit (Some ldes')) at 5.
    wp_apply (hazptr.(shield_set_spec) with "[$] [$]").
    { solve_ndisj. }
    iIntros "S'".
    wp_pure credit:"Hcredit".
    wp_pures.
    wp_bind (Resolve (CmpXchg _ _ _) _ _)%E.
    iInv readN as "(%ver₂ & %log₂ & %abstraction₂ & %actual₂ & %cache₂ & %γ_backup₂ & %γ_backup₂' & %backup₂ & %backup₂' & %index₂ & %validated₂ & %t₂ & >Hver & >Hbackup & >Hγ & Hbackup_managed₂ & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₂ & >%Hidx_wf₂ & >%Hbackup_wf₂ & >%Hvalid_wf₂)" "Hcl".
    pose proof Hsizes₂ as [Hunboxed₂ Hlenactual₂ Hlencache₂ Hloglen₂].
    pose proof Hidx_wf₂ as [Hindex₂ Hlenᵢ₂ Hnodup₂ Hrange₂].
    pose proof Hbackup_wf₂ as [Hlogged₂ Habs_backup₂ Habs_backup'₂ Hdom_eq₂].
    pose proof Hvalid_wf₂ as [Htag₂ Hcons₂ Hvalidated_iff₂ Hvalidated_sub₂].
    iInv mainN as "(%ver₂' & %log₂' & %abstraction₂' & %actual₂' & %γ_backup₂'' & %backup₂'' & %requests₂ & %vers₂ & %index₂' & %order₂ & %idx₂ & %t₂' & >●Hγᵥ' & >Hbackup' & >Hγ' & >●Hhist' & >●Hγᵣ & Hreginv & >●Hγ_vers & >●Hγᵢ' & >●Hγₒ & >%Hmain_backup₂ & >%Hmain_vers₂ & >%Hmain_order₂)" "Hcl'".
    iApply (wp_resolve with "Hp"); first done.
    pose proof Hmain_backup₂ as [Hlog₂ Habs₂].
    pose proof Hmain_vers₂ as [Hdomvers₂ Hvers₂].
    pose proof Hmain_order₂ as [Hdomord₂ Hinj₂ Hidx₂ Hmono₂ Hubord₂].
    iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
    iDestruct (history_auth_agree with "●Hhist ●Hhist'") as %[<- <-].
    iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
    iDestruct (pointsto_agree with "Hbackup Hbackup'") as %[=<-<-%(inj Z.of_nat)].
    iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
    rewrite /index_auth_own.
    iMod (own_auth_split_self'' with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ₂]".
    iMod (validated_auth_frag_dup with "●Hγ_val") as "[●Hγ_val #◯Hγ_val₂]".
    iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#◯Hγᵥ₂".
    iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₂].
    iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ₁") as "%Hagreeₕ₁".
    iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₁].
    iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ #◯Hγₒ₂]".
    destruct (decide (Some (Loc.blk_to_loc backup₁) &ₜ t₁ = Some (Loc.blk_to_loc backup₂) &ₜ t₂)) as [[=<- <-%(inj Z.of_nat)] | Hne'].
    - iDestruct (pointsto_combine with "Hbackup Hbackup'") as "[Hbackup _]".
      rewrite dfrac_op_own Qp.half_half.
      iMod token_alloc as "[%γ_new_backup Hγ_new_backup]".
      wp_cmpxchg_suc.
      iIntros "!>" (pvs1 Hpvs1) "Hp".
      assert (cas_succ_res pvs) as Hsucc.
      { rewrite Hpvs1. eexists [], _, _, _. split; [constructor | done]. }
      iMod (execute_lp backup₁ backup₂' ldes' γ_backup₁ γ_backup₂ γ_backup₂' γ_new_backup l lexp ldes expected desired _ actual₂ abstraction₂ log₂ requests₂ vers₂ order₂ index₂ validated₂ with "Hreadinv Hinv Hcasinv ◯Hγᵣ ◯Hγ_abs ◯Hγₕ₁ Hd Hd_domain [Hbackup_managed₂] [$S'] Hγₜ Hγ_new_backup Hldes' †Hldes' Hver Hlog ●Hγᵥ [Hcache] [Hlock] [Hcl] ●Hγᵥ' ●Hγᵣ [Hreginv] ●Hγ_vers ●Hγᵢ' ●Hγₒ [Hcl'] [$●Hγᵢ] ●Hγ_val [Hγ Hγ'] Hbackup [●Hhist ●Hhist']") as "(-> & -> & %Hnew_backup_fresh & HΦ & #◯Hγ_vers₂ & #◯Hγ_abs₂ & #◯Hγₕ₂ & #◯Hγₒ & S & S' & Hmanaged)"; try done.
      { by destruct (Nat.even ver₂). }
      { rewrite Hlen_exp //. }
      { destruct (decide (1 < size log₂)).
        - rewrite bool_decide_eq_true_2 //.
          rewrite bool_decide_eq_true_2 // in Hvers₂.
          destruct Hvers₂ as (ver' & ? & ? & ? & ?).
          exists ver'. eauto.
        - rewrite bool_decide_eq_false_2 //.
          rewrite bool_decide_eq_false_2 // in Hvers₂.  }
      { iCombine "Hγ Hγ'" as "Hγ".
        rewrite Qp.quarter_quarter //. }
      { iApply (history_halves with "●Hhist ●Hhist'"). }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros ">_ !>".
      wp_pures.
      wp_apply (hazptr.(hazard_domain_retire_spec) with "[//] [$]").
      { solve_ndisj. }
      iIntros "_".
      wp_pures.
      wp_apply (wp_try_validate with "[//] [//] [//] [//] [//] [//] [//] [//] [//] [$]").
      { exact inhabitant. }
      { done. }
      { eapply Hlen_des. }
      { lia. }
      { done. }
      { done. }
      { rewrite Hdomord₂ //. }
      { done. }
      { rewrite -not_elem_of_dom Hdomord₂ not_elem_of_dom //. }
      iIntros "[Hldes S']".
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "[//] S").
      { solve_ndisj. }
      iIntros "_".
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "[//] S'").
      { solve_ndisj. }
      iIntros "_".
      wp_pures.
      iModIntro.
      iApply (cas_post_true with "Hp").
      iApply ("HΦ" with "[$]").
    - iPoseProof (history_abs_frag_agree with "●Hhist ◯Hγ_abs") as "%Hagreeabs₂".
      destruct (decide (backup₂ = backup₁)) as [-> | Hne₂]; first last.
      { iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
        iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
        { done. }
        simpl.
        wp_cmpxchg_fail.
        iIntros "!>" (pvs1 Hpvs1) "Hp".
        iMod (already_linearized with "Hcasinv Hlexp Hldes ◯Hγᵣ Hreq Hγₜ Hcredit") as "(HΦ & S & Hreqinv)".
        { done. }
        { done. }
        iSpecialize ("Hreginv" with "Hreqinv").
        iMod ("Hcl'" with "[$●Hγᵥ' $Hbackup' $Hγ' $●Hhist' $●Hγᵣ $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
        { iFrame_fast_pure. }
        iModIntro.
        iMod ("Hcl" with "[-Hdst Hldes' †Hldes' S S' HΦ Hp]") as "_".
        { iExists ver₂, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₂, backup₂', index₂, validated₂, t₂. iFrame_fast "∗". }
        iModIntro.
        wp_pures.
        rewrite (bool_decide_eq_false_2 (#(Some (Loc.blk_to_loc backup₂) &ₜ t₂) = #(Some (Loc.blk_to_loc backup₁) &ₜ 0))); last naive_solver.
        wp_pures.
        wp_apply (hazptr.(shield_drop_spec) with "[//] S").
        { solve_ndisj. }
        iIntros "_".
        wp_pures.
        wp_apply (hazptr.(shield_drop_spec) with "[//] S'").
        { solve_ndisj. }
        iIntros "_".
        wp_pures.
        wp_apply (wp_free _ _ n with "[$Hldes' †Hldes']").
        { lia. }
        { rewrite Hlen_des //. }
        iIntros "_".
        wp_pures.
        iModIntro. iApply (cas_post_false _ _ _ _ [((_, #false)%V, #())] with "Hp HΦ"); [by rewrite Hpvs1 | solve_failed_res]. }
      destruct (decide (t₁ = 0)) as [-> | Hne₁].
      { (* First backup was validated *)
        (* It cannot be the case that the unmarked pointers are equal, as this would imply that it became unvalidated *)
        rewrite (bool_decide_eq_true_2 (γ_backup₁ ∈ validated₁)); last naive_solver.
        iPoseProof (validated_auth_frag_agree with "●Hγ_val ◯Hγ_val₁") as "%Hvalid₁".
        destruct (decide (t₂ = 1%nat)) as [-> | Hvalid₂].
        - assert (γ_backup₂ ∉ validated₂) as Hinvalid₂ by naive_solver.
          iInv casN as "[[S H] | [>Hlintok _]]" "Hclose".
          + wp_cmpxchg_fail.
            iPoseProof (hazptr.(shield_managed_agree) with "S Hbackup_managed₂") as "->".
            set_solver.
          + iCombine "Hγₜ Hlintok" gives %[].
        - destruct (decide (t₂ = 0)) as [-> | Hvalid₂'].
          + rewrite bool_decide_eq_true_2 // in Htag₂.
          + rewrite bool_decide_eq_false_2 // in Htag₂. }
      rewrite bool_decide_eq_false_2 // in Htag₁.
      simplify_eq.
      assert (t₂ ≠ 1) as Hinvalid₂ by naive_solver.
      destruct (decide (t₂ = 0)) as [-> | Hinvalid₂']; first last.
      { rewrite bool_decide_eq_false_2 // in Htag₂. }
      iMod (validated_auth_frag_alloc γ_backup₂ with "●Hγ_val") as "[●Hγ_val #◯Hγ_val₂']".
      { naive_solver. }
      clear Hne₁ Hinvalid₂.
      wp_cmpxchg_fail.
      iIntros "!>" (pvs1 Hpvs1) "Hp".
      iInv casN as "[[S H] | [>Hlintok _]]" "Hclose"; first last.
      { iCombine "Hγₜ Hlintok" gives %[]. }
      iMod (lc_fupd_elim_later with "Hcredit S") as "S".
      iPoseProof (hazptr.(shield_managed_agree) with "S Hbackup_managed₂") as "->".
      iMod ("Hclose" with "[S H]") as "_".
      { iLeft. iFrame. }
      iMod ("Hcl'" with "[$●Hγᵥ' $Hbackup' $Hγ' $●Hhist' $●Hγᵣ $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
      { iFrame_fast_pure. }
      iMod ("Hcl" with "[-Hdst Hlexp Hldes Hldes' †Hldes' S' Hγₜ Hp]") as "_".
      { iExists ver₂, log₂, abstraction₂, actual₂, cache₂, γ_backup₂, γ_backup₂', backup₁, backup₂', index₂, validated₂, 0. iFrame_fast "∗". }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros ">_ !>".
      wp_pure credit:"Hcredit".
      wp_pures.
      wp_bind (Resolve (CmpXchg _ _ _) _ _)%E.
      iInv readN as "(%ver₃ & %log₃ & %abstraction₃ & %actual₃ & %cache₃ & %γ_backup₃ & %γ_backup₃' & %backup₃ & %backup₃' & %index₃ & %validated₃ & %t₃ & >Hver & >Hbackup & >Hγ & Hbackup_managed & Hlog & >●Hhist & >●Hγᵢ & >●Hγᵥ & >Hcache & Hlock & >●Hγ_val & >%Hsizes₃ & >%Hidx_wf₃ & >%Hbackup_wf₃ & >%Hvalid_wf₃)" "Hcl".
      pose proof Hsizes₃ as [Hunboxed₃ Hlenactual₃ Hlencache₃ Hloglen₃].
      pose proof Hidx_wf₃ as [Hindex₃ Hlenᵢ₃ Hnodup₃ Hrange₃].
      pose proof Hbackup_wf₃ as [Hlogged₃ Habs_backup₃ Habs_backup'₃ Hdom_eq₃].
      pose proof Hvalid_wf₃ as [Htag₃ Hcons₃ Hvalidated_iff₃ Hvalidated_sub₃].
      iInv mainN as "(%ver₃' & %log₃' & %abstraction₃' & %actual₃' & %γ_backup₃'' & %backup₃'' & %requests₃ & %vers₃ & %index₃' & %order₃ & %idx₃ & %t₃' & >●Hγᵥ' & >Hbackup' & >Hγ' & >●Hhist' & >●Hγᵣ & Hreginv & >●Hγ_vers & >●Hγᵢ' & >●Hγₒ & >%Hmain_backup₃ & >%Hmain_vers₃ & >%Hmain_order₃)" "Hcl'".
      iApply (wp_resolve with "Hp"); first done.
      pose proof Hmain_backup₃ as [Hlog₃ Habs₃].
      pose proof Hmain_vers₃ as [Hdomvers₃ Hvers₃].
      pose proof Hmain_order₃ as [Hdomord₃ Hinj₃ Hidx₃ Hmono₃ Hubord₃].
      iDestruct (mono_nat_auth_own_agree with "●Hγᵥ ●Hγᵥ'") as %[_ <-].
      iDestruct (history_auth_agree with "●Hhist ●Hhist'") as %[<- <-].
      iDestruct (index_auth_auth_agree with "●Hγᵢ ●Hγᵢ'") as %<-.
      iDestruct (pointsto_agree with "Hbackup Hbackup'") as %[=<-<-%(inj Z.of_nat)].
      iCombine "Hγ Hγ'" gives %[_ [=<-<-]].
      iMod (own_auth_split_self'' with "●Hγᵢ") as "[●Hγᵢ #◯Hγᵢ₃]".
      iMod (validated_auth_frag_dup with "●Hγ_val") as "[●Hγ_val #◯Hγ_val₃]".
      iPoseProof (mono_nat_lb_own_get with "●Hγᵥ") as "#◯Hγᵥ₃".
      iDestruct (mono_nat_auth_lb_own_valid with "●Hγᵥ ◯Hγᵥ₁") as %[_ Hle₃].
      iMod (own_auth_split_self' with "●Hγₒ") as "[●Hγₒ #◯Hγ₃]".
      iPoseProof (history_log_frag_agree with "●Hhist ◯Hγₕ₁") as "%Hagreeₕ₃".
      iDestruct (history_abs_frag_agree with "●Hhist ◯Hγ_abs") as %Hagree_abs₃.
      destruct (decide (backup₃ = backup₁)) as [-> | Hne₃]; first last.
      { iPoseProof (registry_agree with "●Hγᵣ ◯Hγᵣ") as "%Hregistered".
        iPoseProof (big_sepL_lookup_acc with "Hreginv") as "[Hreq Hreginv]".
        { done. }
        simpl.
        wp_cmpxchg_fail.
        iIntros "!>" (pvs2 Hpvs2) "Hp".
        iMod (already_linearized with "Hcasinv Hlexp Hldes ◯Hγᵣ Hreq Hγₜ Hcredit") as "(HΦ & S & Hreqinv)".
        { done. }
        { done. }
        iSpecialize ("Hreginv" with "Hreqinv").
        iMod ("Hcl'" with "[$●Hγᵥ' $Hbackup' $Hγ' $●Hhist' $●Hγᵣ $Hreginv $●Hγ_vers $●Hγᵢ' $●Hγₒ]") as "_".
        { iFrame_fast_pure. }
        iModIntro.
        iMod ("Hcl" with "[-Hdst Hldes' †Hldes' S S' HΦ Hp]") as "_".
        { iExists ver₃, log₃, abstraction₃, actual₃, cache₃, γ_backup₃, γ_backup₃', backup₃, backup₃', index₃, validated₃, t₃. iFrame_fast "∗". }
        iModIntro.
        wp_pures.
        wp_apply (hazptr.(shield_drop_spec) with "[//] S").
        { solve_ndisj. }
        iIntros "_".
        wp_pures.
        wp_apply (hazptr.(shield_drop_spec) with "[//] S'").
        { solve_ndisj. }
        iIntros "_".
        wp_pures.
        wp_apply (wp_free _ _ (length expected) with "[$Hldes' †Hldes']").
        { lia. }
        { rewrite Hlen_des //. }
        iIntros "_".
        wp_pures.
        iModIntro. iApply (cas_post_false _ _ _ _ [((_, #false)%V, #()); ((_, #false)%V, #())] with "Hp HΦ"); [by rewrite Hpvs1 Hpvs2 | solve_failed_res]. }
      destruct (decide (t₃ = 1)) as [-> | Hne₃].
      { assert (γ_backup₃ ∉ validated₃) as Hinvalid₃ by naive_solver.
        iInv casN as "[[S H] | [>Hlintok _]]" "Hclose".
        + wp_cmpxchg_fail.
          iPoseProof (hazptr.(shield_managed_agree) with "S Hbackup_managed") as "->".
          iPoseProof (validated_auth_frag_agree with "●Hγ_val ◯Hγ_val₂'") as "%Hvalid₃".
          set_solver.
        + iCombine "Hγₜ Hlintok" gives %[]. }
      destruct (decide (t₃ = 0)) as [-> | Hvalid₃]; first last.
      { rewrite bool_decide_eq_false_2 // in Htag₃. }
      iDestruct (pointsto_combine with "Hbackup Hbackup'") as "[Hbackup _]".
      rewrite dfrac_op_own Qp.half_half.
      iMod token_alloc as "[%γ_new_backup Hγ_new_backup]".
      wp_cmpxchg_suc.
      { f_equal. }
      iIntros "!>" (pvs2 Hpvs2) "Hp".
      assert (cas_succ_res pvs) as Hsucc.
      { rewrite Hpvs1 Hpvs2. eexists [((_, #false)%V, #())], _, _, _. split; [solve_failed_res | done]. }
      iMod (execute_lp backup₁ backup₃' ldes' γ_backup₂ γ_backup₃ γ_backup₃' γ_new_backup l lexp ldes expected desired _ actual₃ abstraction₃ log₃ requests₃ vers₃ order₃ index₃ validated₃ with "Hreadinv Hinv Hcasinv ◯Hγᵣ ◯Hγ_abs ◯Hγₕ₁ Hd Hd_domain [Hbackup_managed] [$S'] Hγₜ Hγ_new_backup Hldes' †Hldes' Hver Hlog ●Hγᵥ [Hcache] [Hlock] [Hcl] ●Hγᵥ' ●Hγᵣ [Hreginv] ●Hγ_vers ●Hγᵢ' ●Hγₒ [Hcl'] [$●Hγᵢ] ●Hγ_val [Hγ Hγ'] Hbackup [●Hhist ●Hhist']") as "(-> & -> & %Hnew_backup_fresh & HΦ & #◯Hγ_vers₃ & #◯Hγ_abs₃ & #◯Hγₕ₃ & #◯Hγₒ₃ & S & S' & Hmanaged)"; try done.
      { by destruct (Nat.even ver₃). }
      { destruct (decide (1 < size log₃)).
        - rewrite bool_decide_eq_true_2 //.
          rewrite bool_decide_eq_true_2 // in Hvers₃.
          destruct Hvers₃ as (ver' & ? & ? & ? & ?).
          exists ver'. eauto.
        - rewrite bool_decide_eq_false_2 //.
          rewrite bool_decide_eq_false_2 // in Hvers₃.  }
      { iCombine "Hγ Hγ'" as "Hγ".
        rewrite Qp.quarter_quarter //. }
      { iApply (history_halves with "●Hhist ●Hhist'"). }
      iApply fupd_mask_intro.
      { set_solver. }
      iIntros ">_ !>".
      wp_pures.
      wp_apply (hazptr.(hazard_domain_retire_spec) with "[//] [$]").
      { solve_ndisj. }
      iIntros "_".
      wp_pures.
      wp_apply (wp_try_validate with "[//] [//] [//] [//] [//] [//] [//] [//] [//] [$]").
      { exact inhabitant. }
      { done. }
      { eapply Hlen_des. }
      { lia. }
      { done. }
      { done. }
      { rewrite Hdomord₃ //. }
      { done. }
      { rewrite -not_elem_of_dom Hdomord₃ not_elem_of_dom //. }
      iIntros "[Hldes S']".
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "[//] S").
      { solve_ndisj. }
      iIntros "_".
      wp_pures.
      wp_apply (hazptr.(shield_drop_spec) with "[//] S'").
      { solve_ndisj. }
      iIntros "_".
      wp_pures.
      iModIntro.
      iApply (cas_post_true with "Hp").
      iApply ("HΦ" with "[$]").
  Qed.

End cached_wf.
