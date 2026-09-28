From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr.

(** Thread-local state of the LL/SC big atomics, i.e. their [static thread_local]
    members [h1], [h2] and [expected_tag]. As in C++, it is shared by all big
    atomics, and it is passed explicitly to LL and SC.

    [expected_tag] is either a sequence number [s], encoded as [NULL &ₜ s], or a
    pointer to a backup. Initially it is the sequence number [0], i.e. [NULL]. *)
Notation h1_off := 0 (only parsing).
Notation h2_off := 1 (only parsing).
Notation expected_tag_off := 2 (only parsing).

Section llsc_thread.

  Variable (hazptr : hazard_pointer_code).

  Definition llsc_thread_new : val :=
    λ: "domain",
      let: "ctx" := AllocN #3 #0 in
      "ctx" +ₗ #h1_off <- hazptr.(shield_new) "domain";;
      "ctx" +ₗ #h2_off <- hazptr.(shield_new) "domain";;
      "ctx" +ₗ #expected_tag_off <- #NULL;;
      "ctx".

  Definition llsc_thread_drop : val :=
    λ: "ctx",
      hazptr.(shield_drop) !("ctx" +ₗ #h1_off);;
      hazptr.(shield_drop) !("ctx" +ₗ #h2_off);;
      Free #3 "ctx".

End llsc_thread.
