(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFie.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFie.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w AFhy_w AFhz_w AFi0_w AFi4_w AFi9_w AFid_w.
Import ListNotations. Open Scope Z_scope.
Definition ENOMEM_RETv : Z := 18446744073709551604.
Definition S_R0 : sstate := Eval vm_compute in mkSS 0x643ec (sr_set (ss_regs S_N) 10%bv (SLit ENOMEM_RETv)) (ss_mem S_N ++ NREGS) None FS.
Definition S_R1 : sstate := Eval vm_compute in runtoC 0x36424 S_R0.
Definition S_RET : sstate := Eval vm_compute in runto 0x52ed8 S_R1.
Definition R_map : YP09.region := YP09.mkRegion (Some aMAP) 0 6144 0 6144 [YP09.mkChunk 6129 (CVal 1 (SLit 0))].
Definition S_P0 : sstate := Eval vm_compute in mkSS 0x643ec (sr_set (ss_regs S_N) 10%bv (SOff aMAP 0)) (R_map :: ss_mem S_N) None FS2.
Definition S_P1 : sstate := Eval vm_compute in runtoC 0x36424 S_P0.
Definition S_L1 : sstate := Eval vm_compute in runto 0x53aa4 S_P1.
Definition S_L1l : sstate := Eval vm_compute in runto 0x53c8c (armR BC_GEU true 14 10 S_L1).
Definition S_L1lo : sstate := Eval vm_compute in runto 0x94a18 (armR BC_GEU true 14 11 S_L1l).
Definition S_L1h : sstate := Eval vm_compute in runto 0x53ae4 (armR BC_GEU false 14 10 S_L1).
Definition S_L1h2 : sstate := Eval vm_compute in runto 0x53c8c (armR BC_LTU true 7 10 S_L1h).
Definition S_L1h3 : sstate := Eval vm_compute in runto 0x53ccc (armR BC_GEU false 14 11 S_L1h2).
Definition S_L1hi : sstate := Eval vm_compute in runto 0x94a18 (armR BC_GEU false 5 11 S_L1h3).
Definition S_M1 : sstate := Eval vm_compute in psJ sL1 S_L1lo.
Definition S_P2 : sstate := Eval vm_compute in ss_after_stretch S_M1 (ss_mem S_M1) sM1 CLOB_MS 0x3647c.
Definition S_P3 : sstate := Eval vm_compute in pin S_P2 23%bv (SOff aEND 0).
Definition S_P4 : sstate := Eval vm_compute in pin (runto 0x36488 S_P3) 11%bv (SOff aTL 0).
Definition S_L2 : sstate := Eval vm_compute in runto 0x53aa4 S_P4.
Definition S_L2l : sstate := Eval vm_compute in runto 0x53c8c (armR BC_GEU true 14 10 S_L2).
Definition S_L2lo : sstate := Eval vm_compute in runto 0x94a18 (armR BC_GEU true 14 11 S_L2l).
Definition S_L2h : sstate := Eval vm_compute in runto 0x53ae4 (armR BC_GEU false 14 10 S_L2).
Definition S_L2h2 : sstate := Eval vm_compute in runto 0x53c8c (armR BC_LTU true 7 10 S_L2h).
Definition S_L2h3 : sstate := Eval vm_compute in runto 0x53ccc (armR BC_GEU false 14 11 S_L2h2).
Definition S_L2hi : sstate := Eval vm_compute in runto 0x94a18 (armR BC_GEU false 5 11 S_L2h3).
Definition S_M2 : sstate := Eval vm_compute in psJ sL2 S_L2lo.
Definition S_P5 : sstate := Eval vm_compute in ss_after_stretch S_M2 (ss_mem S_M2) sM2 CLOB_MS 0x3648c.
Definition S_P6 : sstate := Eval vm_compute in arm BC_LTU false (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (SOff aMAP 0) (runto 0x364c4 S_P5).
Definition S_P7 : sstate := Eval vm_compute in arm BC_LTU false (SAlu ALU_ADD (SOff aMS 0) (SOff aMAP 0)) (SAlu ALU_ADD (SOff aMAP 4096) (SOff aND 0)) (runto 0x364c8 S_P6).
Definition S_P8 : sstate := Eval vm_compute in arm BC_NE false (SAlu ALU_SRL (SOff aNCH 0) (SLit 20)) (SLit 0) (runto 0x3651c S_P7).
Definition S_X : sstate := Eval vm_compute in runto 0x365c8 S_P8.
Definition R_qs : YP09.region := YP09.mkRegion (Some aQS) 0 8 0 8 [].
Definition S_Y0 : sstate := Eval vm_compute in runto 0x365e0 (arm BC_EQ false (SOff aNCH 0) (SOff aRES 0) S_X).
