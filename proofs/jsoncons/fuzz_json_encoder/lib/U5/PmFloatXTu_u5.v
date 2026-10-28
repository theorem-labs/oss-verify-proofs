(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmFloatXSpecs_u5.
Import ListNotations.
Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMFXT.
Import PMFX.
Definition len (bs : list Z) : Z := Z.of_nat (length bs).   (* [comment removed for export] *)
Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Variable STRTOD_SCR : Z.

Definition STRX_SCR : Z := PMES.STRX_SCR.
Definition DB_SCR : Z := 112 + STRX_SCR.                                         (* [comment removed for export] *)
Definition PR_SCR : Z := 64 + 32 + STRX_SCR.                                     (* [comment removed for export] *)
Definition DF_SCR : Z := 160 + Z.max SNPRINTF_SCR (Z.max (96 + STRTOD_SCR) DB_SCR).   (* [comment removed for export] *)
Definition DT_SCR : Z := 144 + Z.max DF_SCR (Z.max (80 + 80) PR_SCR).            (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rd_buf (M : mem) (sp buf n S2 SK : Z) (bs : list Z) : Prop :=
  L5.bytes_at RSEGS M buf bs /\ L5.defined M buf n /\ len bs = n /\ sp <= buf /\ buf + n <= hl_sptop L /\ apart buf n S2 24 /\ apart buf n SK 8.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition dump_buffer_x_specU : Prop :=
  forall (buf n dp : Z) (bs : list Z),
    PMES.stransU L HI PC_DUMP_BUFFER DB_SCR
      (fun _ sp R M SK => a0 R buf /\ a1 R n /\ a2 R dp /\ 0 <= dp < 256 /\ a3 R SK /\ 1 <= n <= 99 /\ exists S2, u64 M SK S2 /\ 0 <= S2 < 2 ^ 64 /\ rd_buf M sp buf n S2 SK bs)
      (fun _ _ => True)
      (fun pay => 1 <= pay <= n + 2) (n + 2).

Definition prettify_x_specU : Prop :=
  forall (buf n k : Z) (bs : list Z),
    PMES.stransU L HI PC_PRETTIFY PR_SCR
      (fun _ sp R M SK => a0 R buf /\ a1 R n /\ a2 R k /\ a3 R (2 ^ 64 - 4) /\ getr R 14%bv = Z_to_bv 64 17 /\ getr R 15%bv = Z_to_bv 64 SK /\
                           1 <= n <= 21 /\ -343 <= k <= 309 /\ exists S2, u64 M SK S2 /\ 0 <= S2 < 2 ^ 64 /\ rd_buf M sp buf n S2 SK bs)
      (fun _ _ => True)
      (fun pay => 2 <= pay <= 27) 27.

Definition dtoa_false_x_specU : Prop :=
  forall (dp : Z),
    PMES.stransU L HI PC_DTOA_FALSE DF_SCR
      (fun _ sp R M SK => a0 R dp /\ 0 <= dp < 256 /\ a1 R SK)
      (fun R' _ => a0 R' 1)
      (fun pay => 1 <= pay <= 27) 27.

Definition dtoa_true_x_specU : Prop :=
  forall (dp : Z),
    PMES.stransU L HI PC_DTOA_TRUE DT_SCR
      (fun _ sp R M SK => a0 R dp /\ 0 <= dp < 256 /\ a1 R SK /\ a2 R 0)
      (fun R' _ => a0 R' 1)
      (fun pay => 1 <= pay <= 28) 28.

End Specs.
Lemma DT_SCR_val : 256 + DT_SCR 8944 = 9600. Proof. vm_compute. reflexivity. Qed.
End PMFXT.
