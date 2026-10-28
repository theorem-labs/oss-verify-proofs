(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmFloatCSpecs_u.
Import ListNotations. Import PML.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module STGS.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable STRTOD_SCR : Z.
Definition strtod_g_spec : Prop :=
  forall (s endp sp r : Z) (txt : list Z),
    cps_pure PC_STRTOD r sp STRTOD_SCR [(endp, 8); (TP - 164, 4)]
      (fun R M => entry L R M sp r STRTOD_SCR /\ a0 R s /\ a1 R endp /\ img_ro M /\
                  L5.bytes_at RSEGS M s txt /\ u8 M (s + Z.of_nat (length txt)) 0 /\ PMFC.gtext txt /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.defined M endp 8 /\ sp <= endp /\ endp + 8 <= hl_sptop L /\
                  (s + Z.of_nat (length txt) + 1 <= sp - STRTOD_SCR \/ sp <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= endp \/ endp + 8 <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= TP - 164 \/ TP - 160 <= s) /\
                  L5.defined M s (Z.of_nat (length txt) + 1) /\
                  4096 <= s /\ s + Z.of_nat (length txt) < 2 ^ 47)
      (fun R M R' M' => u64 M' endp (s + Z.of_nat (length txt))).
End Specs.
End STGS.
