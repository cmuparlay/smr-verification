From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr hazptr.code_llsc_thread.
From smr.lang Require Import lib.array.

(** HeapLang translation of the Cached-MemoryEfficient LL/SC big atomic
    (Algorithm "lock-free-single-header" in the SPAA'26 paper).

    The single header word is either a sequence number or a pointer to a
    backup node. A pointer is an ordinary (untagged) location, and the sequence
    number [s] is the null pointer with tag [s], i.e. [NULL &ₜ s]. In
    particular, the initial header [0] is [NULL]. *)

(** Big atomic layout *)
Notation header_off := 0 (only parsing).
Notation domain_off := 1 (only parsing).
Notation cache_off := 2 (only parsing).

(** Backup node layout: [value] occupies offsets [0 .. n-1], and [seqnum] is
    at offset [n]. *)

Section cached_me.

  Variable (hazptr : hazard_pointer_code).

  Definition cached_me_new (n : nat) : val :=
    λ: "src" "domain",
      let: "dst" := AllocN #(S (S n)) #0 in
      (* header = 0 *)
      "dst" +ₗ #header_off <- #NULL;;
      "dst" +ₗ #domain_off <- "domain";;
      array_copy_to ("dst" +ₗ #cache_off) "src" #n;;
      "dst".

  Definition is_pointer : val :=
    λ: "t", untag "t" ≠ #NULL.

  Definition backup_new (n : nat) : val :=
    λ: "value" "seqnum",
      let: "backup" := AllocN #(S n) #0 in
      array_copy_to "backup" "value" #n;;
      "backup" +ₗ #n <- "seqnum";;
      "backup".

  Definition cached_me_ll (n : nat) : val :=
    rec: "ll" "l" "ctx" :=
      let: "hdr1" := !("l" +ₗ #header_off) in
      let: "val" := array_clone ("l" +ₗ #cache_off) #n in
      let: "hdr2" := !("l" +ₗ #header_off) in
      if: (~ is_pointer "hdr1") && ("hdr1" = "hdr2") then
        "ctx" +ₗ #expected_tag_off <- "hdr1";;
        "val"
      else
        let: "hdr" := hazptr.(shield_protect_tagged) !("ctx" +ₗ #h1_off) ("l" +ₗ #header_off) in
        if: is_pointer "hdr" then
          "ctx" +ₗ #expected_tag_off <- "hdr";;
          array_copy_to "val" "hdr" #n;;
          "val"
        else
          Free #n "val";;
          "ll" "l" "ctx".

  (** Stage 3 of SC, after the cache has been written: replace the installed
      backup by its sequence number, recaching the currently installed backup
      after each failure, and then retire the replaced backup. *)
  Definition install_cache (n : nat) : val :=
    rec: "install_cache" "l" "domain" "h1" "new_backup" "new_seqnum" :=
      if: (!("l" +ₗ #header_off) = "new_backup")
          && (CAS ("l" +ₗ #header_off) "new_backup" (#NULL `tag` "new_seqnum")) then
        hazptr.(hazard_domain_retire) "domain" "new_backup" #(S n)
      else
        let: "new_backup" := hazptr.(shield_protect_tagged) "h1" ("l" +ₗ #header_off) in
        array_copy_to ("l" +ₗ #cache_off) "new_backup" #n;;
        "install_cache" "l" "domain" "h1" "new_backup" !("new_backup" +ₗ #n).

  Definition cached_me_sc (n : nat) : val :=
    λ: "l" "ctx" "v",
      let: "expected_tag" := !("ctx" +ₗ #expected_tag_off) in
      let: "domain" := !("l" +ₗ #domain_off) in
      (* STAGE 1: allocate and protect backup *)
      let: "seqnum" :=
        if: is_pointer "expected_tag" then !("expected_tag" +ₗ #n) else tag "expected_tag" in
      let: "new_seqnum" := "seqnum" + #1 in
      let: "new_backup" := backup_new n "v" "new_seqnum" in
      hazptr.(shield_set) !("ctx" +ₗ #h2_off) "new_backup";;
      (* STAGE 2: try to install backup *)
      let: "cur_tag" := !("l" +ₗ #header_off) in
      (* A failed [cmp_xch] overwrites [cur_tag] with the current header, so
         the first [cmp_xch] succeeded iff [cur_tag] still equals [expected_tag] *)
      let: "cur_tag" :=
        if: "cur_tag" = "expected_tag" then
          Fst (CmpXchg ("l" +ₗ #header_off) "cur_tag" "new_backup")
        else "cur_tag" in
      if: ("cur_tag" = "expected_tag") ||
          (("cur_tag" = #NULL `tag` "seqnum")
            && (CAS ("l" +ₗ #header_off) "cur_tag" "new_backup")) then
        (if: is_pointer "cur_tag" then
          hazptr.(hazard_domain_retire) "domain" "expected_tag" #(S n)
        else
          (* STAGE 3: try to install the cached value *)
          array_copy_to ("l" +ₗ #cache_off) "v" #n;;
          install_cache n "l" "domain" !("ctx" +ₗ #h1_off) "new_backup" "new_seqnum");;
        #true
      else
        Free #(S n) "new_backup";;
        #false.

End cached_me.
