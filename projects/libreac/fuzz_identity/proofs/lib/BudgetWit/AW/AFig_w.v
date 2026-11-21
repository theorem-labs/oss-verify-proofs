(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFig.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFig.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YK18_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0p_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w AFhy_w AFhz_w AFi0_w AFi4_w AFi9_w AFid_w AFie_w AFif_w.
Import ListNotations. Open Scope Z_scope.
Definition sM5 : nat := 182.
Definition kJQ : nat := 203.
Definition sMF : nat := 224.
Definition sL6 : nat := 218.
Definition CLOB_L6 : list (bv 5) := [12; 13; 14; 15; 16; 17]%bv.
Definition CLOBJ : list (bv 5) := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Definition USH_LEN : sv :=
SAlu ALU_SUB (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_ADD (SOff aMAP 6136) (SOff aN8DS 0)) (SLit 3)) (SLit 1)) (SAlu ALU_SRL (SOff aMAP 6144) (SLit 3)).
Definition U_M5 : sstate := Eval vm_compute in runto 0x94a18 (arm BC_LTU true USH_LEN (SLit 18446744073709551615) T_R).
Definition U_Q : sstate := Eval vm_compute in ss_after_stretch U_M5 (ss_mem U_M5) sM5 CLOB_MS 0x320b4.
Definition joinQ0 (ss : sstate) : sstate :=
noconds (forget (mkSS (ss_pc ss) (ss_regs ss) (trimscratch (-2272) (ss_mem ss)) (ss_resv ss) (ss_facts ss)) kJQ CLOBJ).
Definition U_QJ : sstate := Eval vm_compute in joinQ0 U_Q.
Definition Ue_MF : sstate := Eval vm_compute in runto 0x94a18 (arm BC_EQ true (SOff 10 0) (SOff aN8DS 0) U_QJ).
Definition R_pbS : YP09.region := YP09.mkRegion (Some aPBS) 0 1 0 1 [].
Definition Uo_L6 : sstate := Eval vm_compute in runto 0x320e0 (arm BC_EQ false (SOff 10 0) (SOff aN8DS 0) U_QJ).
Definition Uo_L6lo : sstate := Eval vm_compute in runto 0x32144 (armR BC_GEU true 12 22 Uo_L6).
Definition Uo_L6h : sstate := Eval vm_compute in runto 0x3211c (armR BC_GEU false 12 22 Uo_L6).
Definition Uo_L6h2 : sstate := Eval vm_compute in runto 0x32120 (armR BC_LTU false 17 22 Uo_L6h).
Definition Uo_L6hi : sstate := Eval vm_compute in runto 0x32144 (armR BC_GEU false 16 22 Uo_L6h2).
Definition Uo_P0 : sstate := Eval vm_compute in noconds (forget Uo_L6lo sL6 CLOB_L6).
Definition Uo_P : sstate := Eval vm_compute in addreg R_pbS (pin Uo_P0 10%bv (SOff aPBS 0)).
Definition Uo_MF : sstate := Eval vm_compute in runto 0x94a18 Uo_P.
Definition st_end (ss : sstate) : sstate :=
let a := ss_after_stretch ss (ss_mem ss) sMF CLOB_MS 0x322dc in
runto 0x52ed8 (arm BC_LTU false (SOff aMAP 6128) (SOff aMAP 4112) (runto 0x3230c (arm BC_EQ false (SOff aMAP 6128) (SOff aMAP 4096) (runto 0x32304 a)))).
Definition Ue_RET : sstate := Eval vm_compute in st_end Ue_MF.
Definition Uo_RET : sstate := Eval vm_compute in st_end Uo_MF.
