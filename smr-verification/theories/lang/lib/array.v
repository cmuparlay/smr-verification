From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From smr.lang Require Export derived_laws.
From smr.lang Require Import proofmode notation.
From iris.prelude Require Import options.

(** * Array utility functions for SMR language *)

(** ** Definitions *)

Definition array_copy_to : val :=
  rec: "array_copy_to" "dst" "src" "n" :=
    if: "n" ≤ #0 then
      #()
    else
      "dst" <- !"src";;
      "array_copy_to" ("dst" +ₗ #1) ("src" +ₗ #1) ("n" - #1).

Definition array_clone : val :=
  λ: "src" "n",
    let: "dst" := AllocN "n" #() in
    array_copy_to "dst" "src" "n";;
    "dst".

(** ** Specifications *)

Section array.
  Context `{!heapGS_gen HasLc hsp Σ}.
  (* Implicit Types (l : loc) (n : nat) (v : val) (vs : list val). *)

  Lemma wp_array_copy_to stk E (ld ls : loc) vdst vsrc q n :
    length vdst = n → length vsrc = n →
    {{{ ld ↦∗ vdst ∗ ls ↦∗{q} vsrc }}}
      array_copy_to #ld #ls #n @ stk; E
    {{{ RET #(); ld ↦∗ vsrc ∗ ls ↦∗{q} vsrc }}}.
  Proof.
    iIntros (Hlen_dst Hlen_src Φ) "[Hdst Hsrc] HΦ".
    (* iRevert (ld ls Φ) "Hdst Hsrc HΦ". *)
    iInduction (vdst) as [|vd vdst] "IH" forall (ld ls vsrc n Hlen_dst Hlen_src).
    - (* vdst = [] *)
      simplify_list_eq.
      rewrite length_zero_iff_nil in Hlen_src.
      simplify_eq.
      wp_rec. wp_pures. iApply ("HΦ" with "[$]").
    - (* vdst = vd :: vdst *)
      simplify_list_eq.
      destruct vsrc as [|vs vsrc]; first done.
      simplify_list_eq.
      iDestruct (array_cons with "Hdst") as "[Hd Hdst]".
      iDestruct (array_cons with "Hsrc") as "[Hs Hsrc]".
      wp_rec.
      wp_pures.
      wp_load.
      wp_store.
      wp_pures.
      change 1%Z with (Z.of_nat 1).
      rewrite -Nat2Z.inj_sub; last lia.
      rewrite /= Nat.sub_0_r.
      wp_apply ("IH" with "[] [//] [$] [$]").
      { done. }
      iIntros "[Hld Hls]".
      iApply ("HΦ" with "[$]").
  Qed.

  Lemma wp_array_clone_cred stk E l q vs n :
    length vs = n → 0 < length vs →
    {{{ l ↦∗{q} vs ∗ ♢ n }}}
      array_clone #l #n @ stk; E
    {{{ (l' : blk) , RET #l'; l ↦∗{q} vs ∗ l' ↦∗ vs ∗ †l'…n }}}.
  Proof.
    iIntros (Hlen Hpos Φ) "[Hl Hc] HΦ".
    wp_lam. wp_pures.
    wp_apply (wp_allocN_cred with "[Hc]") as (l') "[†l' Hl']"; first lia.
    { by rewrite Nat2Z.id. }
    wp_pures.
    (* rewrite Nat2Z.id -{4}(length_replicate (length vs) #()) //. *)
    wp_apply (wp_array_copy_to _ _ _ _ (replicate (Z.to_nat n) #()) vs with "[$]").
    { rewrite length_replicate. lia. }
    { done. }
    iIntros "[Hl' Hl]".
    wp_pures.
    rewrite Nat2Z.id.
    iApply ("HΦ" with "[$]").
  Qed.
End array.

Section array_nospace.
  Context `{!heapGS Σ}.

  Lemma wp_array_clone stk E l q vs n :
    length vs = n → 0 < length vs →
    {{{ l ↦∗{q} vs }}}
      array_clone #l #n @ stk; E
    {{{ (l' : blk) , RET #l'; l ↦∗{q} vs ∗ l' ↦∗ vs ∗ †l'…n }}}.
  Proof.
    iIntros (Hlen Hpos Φ) "Hl HΦ".
    wp_lam. wp_alloc l' as "Hl'" "†l'".
    { lia. }
    wp_pures.
    (* rewrite Nat2Z.id -{4}(length_replicate (length vs) #()) //. *)
    wp_apply (wp_array_copy_to _ _ _ _ (replicate (Z.to_nat n) #()) vs with "[$]").
    { rewrite length_replicate. lia. }
    { done. }
    iIntros "[Hl' Hl]".
    wp_pures.
    rewrite Nat2Z.id.
    iApply ("HΦ" with "[$]").
  Qed.
End array_nospace.
