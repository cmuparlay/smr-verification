From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr_sp hazptr.code_llsc_thread.
From smr.lang Require Import lib.array.

(** The Cached-WaitFree LL/SC big atomic of [code_cached_wf_llsc] (Algorithm
    "wait-free-load-cas" in the SPAA'26 paper), on hazard pointers with bounded
    space ([spec_hazptr_sp]). The code is the same, except that [retire] goes
    through the thread's retirer, a fourth word of the thread-local state
    (C++ keeps the retired list of a thread in thread-local storage). As the
    big atomic no longer needs its domain, it has the paper's layout: the
    sequence number, the backup pointer and the cache, [n + 2] words.

    A backup pointer is marked (the cache is invalid) iff its tag is [1]. The
    thread-local [expected_tag] is either a sequence number [s], encoded as
    [NULL &ₜ s], or a (possibly marked) backup pointer. *)

(** Big atomic layout *)
Notation seqnum_off := 0 (only parsing).
Notation backup_off := 1 (only parsing).
Notation cache_off := 2 (only parsing).

(** Thread-local state: the hazard slots [h1] and [h2], [expected_tag]
    ([code_llsc_thread]), and the retirer. *)
Notation retirer_off := 3 (only parsing).

Section cached_wf_llsc_sp.

  Variable (hazptr : hazard_pointer_sp_code).

  Definition cached_wf_llsc_new_sp (n : nat) : val :=
    λ: "src" "domain",
      let: "dst" := AllocN #(S (S n)) #0 in
      "dst" +ₗ #backup_off <- array_clone "src" #n;;
      array_copy_to ("dst" +ₗ #cache_off) "src" #n;;
      "dst".

  Definition is_seqnum_sp : val :=
    λ: "t", untag "t" = #NULL.

  Definition is_valid_sp : val :=
    λ: "p", tag "p" = #0.

  Definition cached_wf_llsc_ll_sp (n : nat) : val :=
    λ: "l" "ctx",
      let: "seq" := !("l" +ₗ #seqnum_off) in
      let: "val" := array_clone ("l" +ₗ #cache_off) #n in
      let: "proph" := NewProph in
      let: "p" := !("l" +ₗ #backup_off) in
      if: is_valid_sp "p" && (Resolve !("l" +ₗ #seqnum_off) "proph" #() = "seq") then
        (* fast path *)
        "ctx" +ₗ #expected_tag_off <- #NULL `tag` "seq";;
        "val"
      else
        let: "p" := hazptr.(hpsp_shield_protect_tagged) !("ctx" +ₗ #h1_off) ("l" +ₗ #backup_off) in
        "ctx" +ₗ #expected_tag_off <- "p";;
        array_copy_to "val" (untag "p") #n;;
        "val".

  (** Try to install the cached value *)
  Definition try_validate_sp (n : nat) : val :=
    λ: "l" "seq" "desired" "new_p",
      if: ("seq" `rem` #2 = #0) && ("seq" = !("l" +ₗ #seqnum_off))
          && (CAS ("l" +ₗ #seqnum_off) "seq" ("seq" + #1)) then
        array_copy_to ("l" +ₗ #cache_off) "desired" #n;;
        "l" +ₗ #seqnum_off <- "seq" + #2;;
        CmpXchg ("l" +ₗ #backup_off) "new_p" (untag "new_p");;
        #()
      else #().

  (** The rest of SC, once [p] and [seq] have been set *)
  Definition try_install_sp (n : nat) : val :=
    λ: "l" "ctx" "p" "seq" "desired",
      let: "ptr" := array_clone "desired" #n in
      hazptr.(hpsp_shield_set) !("ctx" +ₗ #h2_off) "ptr";;
      let: "new_p" := "ptr" `tag` #1 in
      (* A failed [cmp_xch] overwrites [p] with the current backup pointer.

         As in [code_cached_wf], we drop the load [backup_ptr.load() == p]
         before the first [cmp_xch]. It is not just an optimization: when it
         fails, [p] is not overwritten, so the retry is skipped even if [p] is
         the marked version of the current backup. The SC then fails
         spuriously, i.e. although no SC succeeded since the LL. *)
      let: "res" := CmpXchg ("l" +ₗ #backup_off) "p" "new_p" in
      if: Snd "res" ||
          ((Fst "res" = untag "p") && (CAS ("l" +ₗ #backup_off) (untag "p") "new_p")) then
        hazptr.(hpsp_retire) !("ctx" +ₗ #retirer_off) (untag "p") #n;;
        try_validate_sp n "l" "seq" "desired" "new_p";;
        #true
      else
        Free #n "ptr";;
        #false.

  Definition cached_wf_llsc_sc_sp (n : nat) : val :=
    λ: "l" "ctx" "desired",
      let: "expected_tag" := !("ctx" +ₗ #expected_tag_off) in
      if: is_seqnum_sp "expected_tag" then
        (* fast path *)
        let: "p" := hazptr.(hpsp_shield_protect_tagged) !("ctx" +ₗ #h1_off) ("l" +ₗ #backup_off) in
        let: "seq" := !("l" +ₗ #seqnum_off) in
        if: is_valid_sp "p" && ("seq" = tag "expected_tag") then
          try_install_sp n "l" "ctx" "p" "seq" "desired"
        else #false
      else
        (* slow path: expected_tag is a pointer *)
        try_install_sp n "l" "ctx" "expected_tag" !("l" +ₗ #seqnum_off) "desired".

  Definition llsc_thread_new_sp : val :=
    λ: "domain",
      let: "ctx" := AllocN #4 #0 in
      "ctx" +ₗ #h1_off <- hazptr.(hpsp_shield_new) "domain";;
      "ctx" +ₗ #h2_off <- hazptr.(hpsp_shield_new) "domain";;
      "ctx" +ₗ #expected_tag_off <- #NULL;;
      "ctx" +ₗ #retirer_off <- hazptr.(hpsp_retirer_new) "domain";;
      "ctx".

  Definition llsc_thread_drop_sp : val :=
    λ: "ctx",
      hazptr.(hpsp_shield_drop) !("ctx" +ₗ #h1_off);;
      hazptr.(hpsp_shield_drop) !("ctx" +ₗ #h2_off);;
      Free #4 "ctx".

End cached_wf_llsc_sp.
