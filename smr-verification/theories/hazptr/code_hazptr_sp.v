From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr_sp.

(** * Hazard pointers with bounded space

    A variant of [code_hazptr] whose memory is bounded, in the style of
    Michael's hazard pointers (IEEE TPDS 2004).

    - A domain is an array of [H] hazard slots, allocated once. A slot is one
      word: [#()] when it is free, and otherwise the pointer it protects, or
      [#NULL]. A shield is (the address of) a slot; [shield_new] takes a free
      one, and waits until one is free if there is none.
    - Every thread retires through a retirer: its domain, the number [c] of
      blocks it holds, an array of [R] entries (pointer and size), and an
      array of [H] words for a snapshot of the slots. When [c] reaches [R], the
      retirer scans: it copies the slots into the snapshot, frees the blocks
      that are not in it, and keeps the others. There are at most [H] of those,
      so if [H < R] a retirer never holds more than [R] blocks.
    - The domain owns a pool of [P] retirers, in the [P] words after its slots:
      a word is a free retirer, or [#NULL] if a thread holds it. A thread takes
      a retirer when it starts ([hazard_retirer_new], which waits until one is
      free), and gives it back with the blocks it still holds when it ends
      ([hazard_retirer_release]); the next owner frees them.

    Nothing is allocated after the domain is created. *)

(** Layout of a retirer *)
Notation rtDomain := 0 (only parsing).
Notation rtCount := 1 (only parsing).
Notation rtEntries := 2 (only parsing).

Section code.
  Variables (H R P : nat).

  Definition hp_snap_off : nat := 2 + 2 * R.
  Definition hp_retirer_size : nat := 2 + 2 * R + H.

  (** Allocate the pool of retirers. *)
  Definition hp_pool_init : val :=
    rec: "loop" "d" "i" :=
      if: "i" = #P then #()
      else
        let: "t" := AllocN #hp_retirer_size #0 in
        "t" +ₗ #rtDomain <- "d";;
        "d" +ₗ (#H + "i") <- "t";;
        "loop" "d" ("i" + #1).

  Definition hazard_domain_new_sp : val :=
    λ: <>,
      let: "d" := AllocN #(H + P) #() in
      hp_pool_init "d" #0;;
      "d".

  Definition shield_new_loop_sp : val :=
    rec: "loop" "d" "i" :=
      if: "i" = #H then "loop" "d" #0
      else if: CAS ("d" +ₗ "i") #() #NULL then "d" +ₗ "i"
      else "loop" "d" ("i" + #1).

  Definition shield_new_sp : val :=
    λ: "d", shield_new_loop_sp "d" #0.

  Definition shield_set_sp : val :=
    λ: "s" "p", "s" <- "p".

  Definition shield_unset_sp : val :=
    λ: "s", "s" <- #NULL.

  Definition shield_drop_sp : val :=
    λ: "s", "s" <- #().

  Definition shield_protect_tagged_loop_sp : val :=
    rec: "loop" "s" "a" "ptr" :=
      shield_set_sp "s" (untag "ptr");;
      let: "ptr'" := !"a" in
      if: "ptr" = "ptr'" then "ptr'"
      else "loop" "s" "a" "ptr'".

  Definition shield_protect_tagged_sp : val :=
    λ: "s" "a", shield_protect_tagged_loop_sp "s" "a" !"a".

  Definition hazard_retirer_new_loop : val :=
    rec: "loop" "d" "i" :=
      if: "i" = #P then "loop" "d" #0
      else
        let: "t" := !("d" +ₗ (#H + "i")) in
        if: ("t" ≠ #NULL) && CAS ("d" +ₗ (#H + "i")) "t" #NULL then "t"
        else "loop" "d" ("i" + #1).

  Definition hazard_retirer_new_sp : val :=
    λ: "d", hazard_retirer_new_loop "d" #0.

  Definition hazard_retirer_release_loop : val :=
    rec: "loop" "d" "t" "i" :=
      if: "i" = #P then "loop" "d" "t" #0
      else if: CAS ("d" +ₗ (#H + "i")) #NULL "t" then #()
      else "loop" "d" "t" ("i" + #1).

  Definition hazard_retirer_release_sp : val :=
    λ: "t", hazard_retirer_release_loop !("t" +ₗ #rtDomain) "t" #0.

  (** Copy the slots into the snapshot. *)
  Definition hp_snapshot_loop : val :=
    rec: "loop" "t" "d" "s" :=
      if: "s" = #H then #()
      else
        "t" +ₗ (#hp_snap_off + "s") <- !("d" +ₗ "s");;
        "loop" "t" "d" ("s" + #1).

  (** Whether [p] is in the snapshot. *)
  Definition hp_snap_contains : val :=
    rec: "loop" "t" "p" "s" :=
      if: "s" = #H then #false
      else if: !("t" +ₗ (#hp_snap_off + "s")) = "p" then #true
      else "loop" "t" "p" ("s" + #1).

  (** Free the entries [j, c) that are not in the snapshot, and move the others
      to [k, …). Returns the number of entries kept. *)
  Definition hp_compact_loop : val :=
    rec: "loop" "t" "c" "j" "k" :=
      if: "j" = "c" then "k"
      else
        let: "p" := !("t" +ₗ (#rtEntries + #2 * "j")) in
        let: "n" := !("t" +ₗ (#rtEntries + #2 * "j" + #1)) in
        if: hp_snap_contains "t" "p" #0 then
          "t" +ₗ (#rtEntries + #2 * "k") <- "p";;
          "t" +ₗ (#rtEntries + #2 * "k" + #1) <- "n";;
          "loop" "t" "c" ("j" + #1) ("k" + #1)
        else
          Free "n" "p";;
          "loop" "t" "c" ("j" + #1) "k".

  Definition hp_reclaim : val :=
    λ: "t" "c",
      hp_snapshot_loop "t" !("t" +ₗ #rtDomain) #0;;
      "t" +ₗ #rtCount <- hp_compact_loop "t" "c" #0 #0.

  Definition hazard_retire_sp : val :=
    λ: "t" "p" "n",
      let: "c" := !("t" +ₗ #rtCount) in
      "t" +ₗ (#rtEntries + #2 * "c") <- "p";;
      "t" +ₗ (#rtEntries + #2 * "c" + #1) <- "n";;
      if: "c" + #1 = #R then hp_reclaim "t" ("c" + #1)
      else "t" +ₗ #rtCount <- "c" + #1.

End code.

Definition hazptr_sp_code (H R P : nat) : hazard_pointer_sp_code := {|
  hpsp_domain_new := hazard_domain_new_sp H R P;
  hpsp_retirer_new := hazard_retirer_new_sp H P;
  hpsp_retirer_release := hazard_retirer_release_sp H P;
  hpsp_retire := hazard_retire_sp H R;
  hpsp_shield_new := shield_new_sp H;
  hpsp_shield_set := shield_set_sp;
  hpsp_shield_protect_tagged := shield_protect_tagged_sp;
  hpsp_shield_unset := shield_unset_sp;
  hpsp_shield_drop := shield_drop_sp;
|}.
