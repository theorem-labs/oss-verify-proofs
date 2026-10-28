(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMFX.
(* [comment removed for export] *)
Definition PC_WRITE_DOUBLE : Z := 0x3f2ec.  Definition PC_DUMP_BUFFER : Z := 0x44010.   Definition PC_GRISU3 : Z := 0x44498.
Definition PC_PRETTIFY : Z := 0x44850.      Definition PC_DIGIT_GEN : Z := 0x44d38.     Definition PC_FILL_EXP : Z := 0x4517c.
Definition PC_DTOA_TRUE : Z := 0x456d0.     Definition PC_DTOA_FALSE : Z := 0x457d8.    Definition PC_SNPRINTF : Z := 0xb34bc.
(* [comment removed for export] *)

Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable STRTOD_SCR : Z.

(* [comment removed for export] *)
Definition STR_SCR : Z := PMS.STR_SCR.
Definition SNPRINTF_SCR : Z := 6144.                               (* [comment removed for export] *)
Definition DTOA_FALSE_SCR : Z := 160 + Z.max SNPRINTF_SCR (Z.max (96 + STRTOD_SCR) (96 + STR_SCR)).
Definition DTOA_TRUE_SCR : Z := 144 + Z.max DTOA_FALSE_SCR (Z.max (80 + 80) (64 + 32 + Z.max 464 STR_SCR)).
Definition WD_SCR : Z := 256 + DTOA_TRUE_SCR.                      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FMT_G : Z := 0x12e80.                 (* [comment removed for export] *)
(* [comment removed for export] *)
Definition TXT_INF : list Z := [105; 110; 102].       Definition TXT_NAN : list Z := [110; 97; 110].
Definition gtext (txt : list Z) : Prop := num_final txt \/ In txt [TXT_INF; 45 :: TXT_INF; TXT_NAN; 45 :: TXT_NAN].

(* [comment removed for export] *)
Definition snprintf_g_spec : Prop :=
  forall (buf p v sp r : Z),
    cps_pure PC_SNPRINTF r sp SNPRINTF_SCR [(buf, 100)]
      (fun R M => entry L R M sp r SNPRINTF_SCR /\ a0 R buf /\ a1 R 100 /\ a2 R FMT_G /\ a3 R p /\ (p = 15 \/ p = 17) /\
                  getr R 14%bv = Z_to_bv 64 v /\ 0 <= v < 2 ^ 64 /\ img_ro M /\
                  L5.defined M buf 100 /\ sp <= buf /\ buf + 100 <= hl_sptop L)
      (fun R M R' M' => exists txt, gtext txt /\ 1 <= Z.of_nat (length txt) <= 25 /\ a0 R' (Z.of_nat (length txt)) /\
                                    L5.bytes_at RSEGS M' buf txt /\ u8 M' (buf + Z.of_nat (length txt)) 0 /\ L5.defined M' buf 100).

(* [comment removed for export] *)
Definition decstr_to_double_g_spec : Prop :=
  forall (s dp sp r : Z) (txt : list Z),
    cps_pure PC_DECSTR_DOUBLE r sp (96 + STRTOD_SCR) [(dp, 8); (TP - 164, 4)]
      (fun R M => entry L R M sp r (96 + STRTOD_SCR) /\ a0 R s /\ a1 R (Z.of_nat (length txt)) /\ a2 R dp /\ img_ro M /\
                  L5.bytes_at RSEGS M s txt /\ u8 M (s + Z.of_nat (length txt)) 0 /\ gtext txt /\ Z.of_nat (length txt) < 2 ^ 26 /\
                  L5.defined M dp 8 /\ sp <= dp /\ dp + 8 <= hl_sptop L /\
                  L5.defined M s (Z.of_nat (length txt) + 1) /\ 4096 <= s /\ s + Z.of_nat (length txt) < 2 ^ 47 /\
                  (s + Z.of_nat (length txt) + 1 <= sp - (96 + STRTOD_SCR) \/ sp <= s) /\
                  (s + Z.of_nat (length txt) + 1 <= TP - 164 \/ TP - 160 <= s))
      (fun R M R' M' => a0 R' (s + Z.of_nat (length txt)) /\ exists c, getr R' 11%bv = Z_to_bv 64 c /\ In c [0; 34]).

(* [comment removed for export] *)
End Specs.
Lemma WD_SCR_9600 : WD_SCR 8944 = 9600. Proof. vm_compute. reflexivity. Qed.
End PMFX.
