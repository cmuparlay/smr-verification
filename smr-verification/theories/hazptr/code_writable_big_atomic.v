From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr hazptr.spec_big_atomic.
From smr.hazptr Require Import code_cached_wf.
From smr.lang Require Import lib.array.

(** HeapLang translation of the wait-free Load/Store/CAS big atomic
    (Algorithm "wait-free-load-store-cas", [WritableBigAtomic], in the SPAA'26
    submission), parametric in the Load/CAS big atomic [Z].

    [Z] holds a [Value] of [n + 2] words: the value, the sequence number and the
    mark. The write buffer [W] holds a pointer to a node with a value, whose tag
    is its mark. The paper does not show a constructor; [W] initially points to a
    node with the initial value, with mark [0] (so the destructor's
    [delete W.load()] is well-defined).

    Ghost code: the load/CAS big atomic's CAS takes a prophecy. [help_write]
    passes a fresh one, and [cas] allocates one and resolves it before
    returning [false] after two failed attempts. *)

(** Layout of a writable big atomic *)
Notation z_off := 0 (only parsing).
Notation w_off := 1 (only parsing).
Notation domain_off := 2 (only parsing).

(** Layout of a [Value] of size [n] *)
Notation seq_off n := (Z.of_nat n) (only parsing).
Notation mark_off n := (Z.of_nat n + 1)%Z (only parsing).

Section writable_big_atomic.

  Variable (hazptr : hazard_pointer_code) (ba : big_atomic_code).

  Definition writable_new (n : nat) : val :=
    λ: "src" "domain",
      let: "l" := AllocN #3 #0 in
      let: "z" := AllocN #(n + 2) #0 in
      array_copy_to "z" "src" #n;;
      let: "Z" := ba.(big_atomic_new) (n + 2) "z" "domain" in
      "l" +ₗ #z_off <- "Z";;
      "l" +ₗ #w_off <- array_clone "src" #n;;
      "l" +ₗ #domain_off <- "domain";;
      "l".

  Definition writable_load (n : nat) : val :=
    λ: "l", ba.(big_atomic_read) (n + 2) !("l" +ₗ #z_off).

  Definition help_write (n : nat) : val :=
    λ: "l",
      let: "z" := ba.(big_atomic_read) (n + 2) !("l" +ₗ #z_off) in
      let: "h" := hazptr.(shield_new) !("l" +ₗ #domain_off) in
      let: "w" := hazptr.(shield_protect_tagged) "h" ("l" +ₗ #w_off) in
      let: "res" :=
        if: !("z" +ₗ #(mark_off n)) ≠ tag "w" then
          let: "z'" := AllocN #(n + 2) #0 in
          array_copy_to "z'" (untag "w") #n;;
          "z'" +ₗ #(seq_off n) <- !("z" +ₗ #(seq_off n)) + #1;;
          "z'" +ₗ #(mark_off n) <- tag "w";;
          ba.(big_atomic_cas) (n + 2) !("l" +ₗ #z_off) "z" "z'" NewProph
        else #true in
      hazptr.(shield_drop) "h";;
      "res".

  Definition writable_store (n : nat) : val :=
    λ: "l" "desired",
      let: "h" := hazptr.(shield_new) !("l" +ₗ #domain_off) in
      let: "w" := hazptr.(shield_protect_tagged) "h" ("l" +ₗ #w_off) in
      let: "z" := ba.(big_atomic_read) (n + 2) !("l" +ₗ #z_off) in
      if: array_equal "z" "desired" #n then
        hazptr.(shield_drop) "h"
      else (
        (if: !("z" +ₗ #(mark_off n)) = tag "w" then
          let: "n" := array_clone "desired" #n `tag` (#1 - !("z" +ₗ #(mark_off n))) in
          if: CAS ("l" +ₗ #w_off) "w" "n" then
            hazptr.(hazard_domain_retire) !("l" +ₗ #domain_off) (untag "w") #n
          else
            Free #n (untag "n")
        else #());;
        (if: ~ help_write n "l" then help_write n "l";; #() else #());;
        hazptr.(shield_drop) "h"
      ).

  Definition writable_cas_loop (n : nat) : val :=
    rec: "loop" "l" "expected" "desired" "p" "i" :=
      if: "i" = #2 then
        (resolve_proph: "p" to: #());;
        #false
      else
        let: "z" := ba.(big_atomic_read) (n + 2) !("l" +ₗ #z_off) in
        if: ~ array_equal "z" "expected" #n then #false
        else if: array_equal "expected" "desired" #n then #true
        else
          help_write n "l";;
          let: "z'" := AllocN #(n + 2) #0 in
          array_copy_to "z'" "desired" #n;;
          "z'" +ₗ #(seq_off n) <- !("z" +ₗ #(seq_off n)) + #1;;
          "z'" +ₗ #(mark_off n) <- !("z" +ₗ #(mark_off n));;
          if: ba.(big_atomic_cas) (n + 2) !("l" +ₗ #z_off) "z" "z'" "p" then #true
          else "loop" "l" "expected" "desired" "p" ("i" + #1).

  Definition writable_cas (n : nat) : val :=
    λ: "l" "expected" "desired",
      let: "p" := NewProph in
      writable_cas_loop n "l" "expected" "desired" "p" #0.

End writable_big_atomic.
