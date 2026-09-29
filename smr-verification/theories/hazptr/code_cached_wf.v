From smr.lang Require Import notation.
From iris.prelude Require Import options.

From smr Require Import hazptr.spec_hazptr.
From smr.lang Require Import lib.array.

Notation version_off := 0 (only parsing).
Notation backup_off := 1 (only parsing).
Notation domain_off := 2 (only parsing).
Notation cache_off := 3 (only parsing).

Section cached_wf.

  Variable (hazptr : hazard_pointer_code).

  Definition cached_wf_new (n : nat) : val :=
    λ: "src" "domain",
      let: "dst" := AllocN #(S (S (S n))) #0 in
      "dst" +ₗ #backup_off <- array_clone "src" #n;;
      "dst" +ₗ #domain_off <- "domain";;
      array_copy_to ("dst" +ₗ #cache_off) "src" #n;;
      "dst".

  Definition is_valid : val :=
    λ: "l", tag "l" = #0.

  Definition cached_wf_read (n : nat) : val :=
    λ: "l",
      let: "ver" := !("l" +ₗ #version_off) in
      let: "data" := array_clone ("l" +ₗ #cache_off) #n in
      let: "p" := NewProph in
      let: "backup" := !("l" +ₗ #backup_off) in
      if: is_valid "backup" && (Resolve !"l" "p" #() = "ver") then (
        "data"
      ) else (
        let: "domain" := !("l" +ₗ #domain_off) in
        let: "shield" := hazptr.(shield_new) "domain" in
        let: "backup'" := hazptr.(shield_protect_tagged) "shield" ("l" +ₗ #backup_off) in
        array_copy_to "data" (untag "backup'") #n;;
        hazptr.(shield_drop) "shield";;
        "data"
      ).

  Definition read' (n : nat) : val :=
    λ: "l" "ver" "backup" "data",
      if: is_valid "backup" && (!"l" = "ver") then 
        #()
      else
        array_copy_to "data" (untag "backup") #n.

  Definition array_equal : val :=
    rec: "array_equal" "l" "l'" "n" :=
      if: "n" ≤ #0 then #true
      else
        (!"l" = !"l'") && ("array_equal" ("l" +ₗ #1) ("l'" +ₗ #1) ("n" - #1)).

  Definition try_validate (n : nat) : val :=
    λ: "l" "ver" "desired" "backup'",
      if: ("ver" `rem` #2 = #0) && (CAS "l" "ver" (#1 + "ver")) then
        (* Lock was successful *)
        (* Perform update *)
        array_copy_to ("l" +ₗ #cache_off) "desired" #n;;
        (* Unlock *)
        "l" <- #2 + "ver";;
        CmpXchg ("l" +ₗ #1) ("backup'" `tag` #1) "backup'";;
        #()
      else #().

  Definition cached_wf_cas (n : nat) : val :=
    λ: "l" "expected" "desired" "p",
      let: "ver" := !("l" +ₗ #version_off) in
      let: "domain" := !("l" +ₗ #domain_off) in
      let: "shield" := hazptr.(shield_new) "domain" in
      let: "old" := array_clone ("l" +ₗ #cache_off) #n in
      let: "backup" := hazptr.(shield_protect_tagged) "shield" ("l" +ₗ #backup_off) in
      read' n "l" "ver" "backup" "old";;
      if: array_equal "old" "expected" #n then (
        if: array_equal "expected" "desired" #n then (
          hazptr.(shield_drop) "shield";;
          #true
        ) else (
          let: "backup'" := array_clone "desired" #n in
          let: "shield'" := hazptr.(shield_new) "domain" in
          hazptr.(shield_set) "shield'" "backup'";;
          (* The compare-exchanges resolve the caller's prophecy [p] (ghost code). *)
          let: "res" := Resolve (CmpXchg ("l" +ₗ #backup_off) "backup" ("backup'" `tag` #1)) "p" #() in
          if: Snd "res" || 
            ((Fst "res" = untag "backup")
              && Snd (Resolve (CmpXchg ("l" +ₗ #backup_off) (untag "backup") ("backup'" `tag` #1)) "p" #())) then
            hazptr.(hazard_domain_retire) "domain" (untag "backup") #n;;
            try_validate n "l" "ver" "desired" "backup'";;
            hazptr.(shield_drop) "shield";;
            hazptr.(shield_drop) "shield'";;
            #true
          else (
            hazptr.(shield_drop) "shield";;
            hazptr.(shield_drop) "shield'";;
            Free #n "backup'";;
            #false
          )
        )
      ) else (
        hazptr.(shield_drop) "shield";;
        #false
      ).

End cached_wf.
