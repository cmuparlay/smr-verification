From stdpp Require Export namespaces.
From smr.program_logic Require Import atomic.
From smr.lang Require Import proofmode notation.
From smr Require Export smr_common.
From smr.hazptr Require Export spec_hazptr.
From iris.prelude Require Import options.

From smr Require Import helpers.

(** * Hazard pointers with bounded space

    The specification of [spec_hazptr], in a heap that may count space (any
    [hsp]), for an implementation whose memory is bounded:

    - A domain has a fixed number of hazard slots, and creating it costs
      [hp_domain_cost] space credits. Shields take slots of the domain, so they
      cost nothing.
    - Retiring goes through a [Retirer], a thread-local handle that holds the
      retired blocks that have not been freed yet. Creating a retirer costs
      [hp_retirer_cost] credits, which pay for the handle and for all the
      blocks it will ever hold, so [hazard_retire] gives back the credits of
      the retired block at once: from the client's point of view, a retired
      block is freed. Blocks of at most [hp_kmax] cells can be retired.

    Retirers cannot be dropped, so the space they hold stays paid for. *)

Definition RetirerT Σ (N : namespace) : Type :=
  ∀ (γd : gname) (t : loc), iProp Σ.

Section spec.
Context {Σ} `{!heapGS_gen HasLc hsp Σ} (N : namespace).
Variables
  (hazard_domain_new : val)
  (hazard_retirer_new : val)
  (hazard_retire : val)
  (shield_new : val)
  (shield_set : val)
  (shield_unset : val)
  (shield_drop : val)
  (shield_protect_tagged : val).
Variables
  (hp_kmax hp_domain_cost hp_retirer_cost : nat)
  (IsHazardDomain : DomainT Σ N)
  (Managed : ManagedT Σ N)
  (Shield : ShieldT Σ N)
  (Retirer : RetirerT Σ N).

Implicit Types (R : resource Σ).

Definition hazard_domain_new_sp_spec' : Prop :=
  ∀ E,
  {{{ ♢ hp_domain_cost }}}
    hazard_domain_new #() @ E
  {{{ γd d, RET #d; IsHazardDomain γd d }}}.

Definition hazard_domain_register_sp' : Prop :=
  ∀ R E (p : blk) lv γ_p γd d,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  p ↦∗ lv ∗ †p…(length lv) ∗ R p lv γ_p ={E}=∗
  Managed γd p γ_p (length lv) R.

Definition shield_new_sp_spec' : Prop :=
  ∀ E γd d,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  {{{ True }}}
    shield_new #d @ E
  {{{ s, RET #s; Shield γd s Deactivated }}}.

Definition shield_set_sp_spec' : Prop :=
  ∀ p E γd d s s_st,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  {{{ Shield γd s s_st }}}
    shield_set #s #(oblk_to_lit p) @ E
  {{{ RET #(); Shield γd s (if p is Some p then NotValidated p else Deactivated) }}}.

Definition shield_validate_sp' : Prop :=
  ∀ E γd d R p γ_p s size_i,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  Managed γd p γ_p size_i R -∗
  Shield γd s (NotValidated p) ={E}=∗
  Managed γd p γ_p size_i R ∗ Shield γd s (Validated p γ_p R size_i).

Definition shield_protect_tagged_sp_spec' : Prop :=
  ∀ E γd d s s_st (a : loc) dq,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  Shield γd s s_st -∗
  <<{ ∀∀ (p : blk) (t : nat) γ_p size_i R,
      a ↦{dq} #(Some (Loc.blk_to_loc p) &ₜ t) ∗
      ▷ Managed γd p γ_p size_i R }>>
    shield_protect_tagged #s #a @ E,∅,↑(mgmtN N)
  <<{ a ↦{dq} #(Some (Loc.blk_to_loc p) &ₜ t) ∗
      Managed γd p γ_p size_i R ∗
      Shield γd s (Validated p γ_p R size_i) |
      RET #(Some (Loc.blk_to_loc p) &ₜ t) }>>.

Definition shield_acc_sp' : Prop :=
  ∀ E γd R s p γ_p size_i,
  ↑(ptrN N p) ⊆ E →
  Shield γd s (Validated p γ_p R size_i) ={E,E∖↑(ptrN N p)}=∗
  ∃ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ Shield γd s (Validated p γ_p R size_i) ∗
  (∀ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p ={E∖↑(ptrN N p),E}=∗ True).

Definition managed_acc_sp' : Prop :=
  ∀ E γd R p γ_p size_i,
  ↑(ptrN N p) ⊆ E →
  Managed γd p γ_p size_i R ={E,E∖↑(ptrN N p)}=∗
  ∃ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ Managed γd p γ_p size_i R ∗
  (∀ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p ={E∖↑(ptrN N p),E}=∗ True).

Definition managed_exclusive_sp' : Prop :=
  ∀ γd p γ_p γ_p' size_i size_i' R R',
  Managed γd p γ_p size_i R -∗ Managed γd p γ_p' size_i' R' -∗ False.

Definition shield_managed_agree_sp' : Prop :=
  ∀ γd s p γ_p1 γ_p2 R1 R2 size_i1 size_i2,
  Shield γd s (Validated p γ_p1 R1 size_i1) -∗
  Managed γd p γ_p2 size_i2 R2 -∗
  ⌜γ_p1 = γ_p2⌝.

Definition shield_unset_sp_spec' : Prop :=
  ∀ E γd d s s_st,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  {{{ Shield γd s s_st }}}
    shield_unset #s @ E
  {{{ RET #(); Shield γd s Deactivated }}}.

Definition shield_drop_sp_spec' : Prop :=
  ∀ E γd d s s_st,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  {{{ Shield γd s s_st }}}
    shield_drop #s @ E
  {{{ RET #(); True }}}.

Definition hazard_retirer_new_spec' : Prop :=
  ∀ E γd d,
  ↑(mgmtN N) ⊆ E →
  IsHazardDomain γd d -∗
  {{{ ♢ hp_retirer_cost }}}
    hazard_retirer_new #d @ E
  {{{ t, RET #t; Retirer γd t }}}.

(* Detach a registered block; its space is given back at once. *)
Definition hazard_retire_spec' : Prop :=
  ∀ E γd t R p γ_p (s : nat),
  ↑N ⊆ E →
  s ≤ hp_kmax →
  {{{ Retirer γd t ∗ Managed γd p γ_p s R }}}
    hazard_retire #t #p #s @ E
  {{{ RET #(); Retirer γd t ∗ ♢ s }}}.

End spec.

Record hazard_pointer_sp_code : Type := HazardPointerSpCode {
  hpsp_domain_new : val;
  hpsp_retirer_new : val;
  hpsp_retire : val;
  hpsp_shield_new : val;
  hpsp_shield_set : val;
  hpsp_shield_protect_tagged : val;
  hpsp_shield_unset : val;
  hpsp_shield_drop : val;
}.

Record hazard_pointer_sp_spec {Σ} `{!heapGS_gen HasLc hsp Σ} {N : namespace} : Type :=
  HazardPointerSpSpec {
  hazard_pointer_sp_spec_code :> hazard_pointer_sp_code;

  hp_kmax : nat;
  hp_domain_cost : nat;
  hp_retirer_cost : nat;

  IsHazardDomainSp : DomainT Σ N;
  ManagedSp : ManagedT Σ N;
  ShieldSp : ShieldT Σ N;
  Retirer : RetirerT Σ N;

  IsHazardDomainSp_Persistent : ∀ γd d, Persistent (IsHazardDomainSp γd d);

  hazard_domain_new_sp_spec :
    hazard_domain_new_sp_spec' N hazard_pointer_sp_spec_code.(hpsp_domain_new)
      hp_domain_cost IsHazardDomainSp;
  hazard_domain_register_sp : hazard_domain_register_sp' N IsHazardDomainSp ManagedSp;
  shield_new_sp_spec :
    shield_new_sp_spec' N hazard_pointer_sp_spec_code.(hpsp_shield_new) IsHazardDomainSp ShieldSp;
  shield_set_sp_spec :
    shield_set_sp_spec' N hazard_pointer_sp_spec_code.(hpsp_shield_set) IsHazardDomainSp ShieldSp;
  shield_validate_sp : shield_validate_sp' N IsHazardDomainSp ManagedSp ShieldSp;
  shield_protect_tagged_sp_spec :
    shield_protect_tagged_sp_spec' N hazard_pointer_sp_spec_code.(hpsp_shield_protect_tagged)
      IsHazardDomainSp ManagedSp ShieldSp;
  shield_unset_sp_spec :
    shield_unset_sp_spec' N hazard_pointer_sp_spec_code.(hpsp_shield_unset) IsHazardDomainSp ShieldSp;
  shield_drop_sp_spec :
    shield_drop_sp_spec' N hazard_pointer_sp_spec_code.(hpsp_shield_drop) IsHazardDomainSp ShieldSp;
  shield_acc_sp : shield_acc_sp' N ShieldSp;
  managed_acc_sp : managed_acc_sp' N ManagedSp;
  managed_exclusive_sp : managed_exclusive_sp' N ManagedSp;
  shield_managed_agree_sp : shield_managed_agree_sp' N ManagedSp ShieldSp;
  hazard_retirer_new_spec :
    hazard_retirer_new_spec' N hazard_pointer_sp_spec_code.(hpsp_retirer_new)
      hp_retirer_cost IsHazardDomainSp Retirer;
  hazard_retire_spec :
    hazard_retire_spec' N hazard_pointer_sp_spec_code.(hpsp_retire) hp_kmax ManagedSp Retirer;
}.

Global Arguments hazard_pointer_sp_spec _ {_ _} _ : assert.

Global Existing Instances IsHazardDomainSp_Persistent.

Section helpers.
Context {Σ} `{!heapGS_gen HasLc hsp Σ} (N : namespace) {hp : hazard_pointer_sp_spec Σ N}.

Global Instance into_inv_shield_sp γd s p γ_p R size_i :
  IntoInv (hp.(ShieldSp) γd s (Validated p γ_p R size_i)) (ptrN N p) := {}.

Global Instance into_acc_shield_sp E γd s p γ_p R size_i :
  IntoAcc (hp.(ShieldSp) γd s (Validated p γ_p R size_i)) (↑(ptrN N p) ⊆ E) (True%I)
          (fupd E (E∖↑(ptrN N p))) (fupd (E∖↑(ptrN N p)) E)
          (λ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ hp.(ShieldSp) γd s (Validated p γ_p R size_i))%I
          (λ lv, ∃ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (?) "Sh _".
  iMod (hp.(shield_acc_sp) with "Sh") as (lv) "(% & p↦ & R & Sh & CloseSh)"; [solve_ndisj|].
  iExists lv. iSplitL "p↦ R Sh"; [by iFrame|].
  iIntros "!> (% & % & p↦ & R)".
  by iMod ("CloseSh" with "[$p↦ $R]").
Qed.

Global Instance into_inv_managed_sp γd p γ_p size_i R :
  IntoInv (hp.(ManagedSp) γd p γ_p size_i R) (ptrN N p) := {}.

Global Instance into_acc_managed_sp E γd p γ_p size_i R :
  IntoAcc (hp.(ManagedSp) γd p γ_p size_i R) (↑(ptrN N p) ⊆ E) (True%I)
          (fupd E (E∖↑(ptrN N p))) (fupd (E∖↑(ptrN N p)) E)
          (λ lv, ⌜length lv = size_i⌝ ∗ p ↦∗ lv ∗ ▷ R p lv γ_p ∗ hp.(ManagedSp) γd p γ_p size_i R)%I
          (λ lv, ∃ lv', ⌜length lv = length lv'⌝ ∗ p ↦∗ lv' ∗ ▷ R p lv' γ_p)%I (λ _, None)%I.
Proof.
  rewrite /IntoAcc /accessor. iIntros (?) "M _".
  iMod (hp.(managed_acc_sp) with "M") as (lv) "(% & p↦ & R & M & CloseM)"; [solve_ndisj|].
  iExists lv. iSplitL "p↦ R M"; [by iFrame|].
  iIntros "!> (% & % & p↦ & R)".
  by iMod ("CloseM" with "[$p↦ $R]").
Qed.

Lemma shield_read_sp R o E γd s p γ_p size_i :
  ↑(ptrN N p) ⊆ E →
  o < size_i →
  (∀ p lv γ_p, Persistent (R p lv γ_p)) →
  {{{ hp.(ShieldSp) γd s (Validated p γ_p R size_i) }}}
    !#(p +ₗ o) @ E
  {{{ lv v, RET v; hp.(ShieldSp) γd s (Validated p γ_p R size_i) ∗ R p lv γ_p ∗ ⌜lv !! o = Some v⌝ }}}.
Proof.
  intros ???.
  iIntros (Φ) "Sh HΦ".
  iInv "Sh" as (lv <-) "(p↦ & #R & Sh)".
  have [v ?] : is_Some (lv !! o) by apply lookup_lt_is_Some.
  wp_apply (wp_load_offset with "p↦") as "p↦"; [done|].
  iModIntro. iSplitL "p↦".
  { iExists _. by iFrame "∗#%". }
  iApply "HΦ". iFrame "∗#%".
Qed.

End helpers.
