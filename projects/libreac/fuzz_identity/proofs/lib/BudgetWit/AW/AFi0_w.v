(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFi0.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_identity's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from A/AFi0.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w YA0o_w YA0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AB1q AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AF0x_w AFl0_w AFhy_w AFhz_w.
Import ListNotations. Open Scope Z_scope.
Definition hMS1 : nat := 133.
Definition hCL2 : nat := 139.
Definition R_scr2 : YP09.region := YP09.mkRegion (Some 2%nat) (- ASTACK) (- 2272) (- ASTACK) (- 2272) [].
Definition rs_D : smem := match ss_mem SS_PD with r0 :: r1 :: rest => r0 :: trim_lo r1 (-2272) :: rest | l => l end.
Definition SS_2 : sstate := Eval vm_compute in addreg R_scr2 (ss_after_call SS_PD rs_D hD1 0x31fa8).
Definition SS_M0 : sstate := Eval vm_compute in runto 0x31fd0 SS_2.
Definition SS_M : sstate := Eval vm_compute in pin SS_M0 10%bv (SOff aSK 0).
Definition SS_N0 : sstate := Eval vm_compute in runto 0x320a0 SS_M.
Definition SS_N : sstate := Eval vm_compute in pin SS_N0 22%bv (SOff aN8D 0).
Definition SS_O0 : sstate := Eval vm_compute in runto 0x53d04 SS_N.
Definition SS_O : sstate := Eval vm_compute in pin (pin SS_O0 8%bv (SOff aCNT8 0)) 10%bv (SOff aSU 0).
Definition SS_MS1 : sstate := Eval vm_compute in runto 0x94a18 SS_O.
Definition CLOB_MS : list (bv 5) := [11; 12; 13; 14; 15; 16]%bv.
Definition SS_Q : sstate := Eval vm_compute in ss_after_stretch SS_MS1 (ss_mem SS_MS1) hMS1 CLOB_MS 0x320b4.
Definition SS_Qe : sstate := Eval vm_compute in arm BC_EQ true (SOff 10 0) (SOff aN8D 0) SS_Q.
Definition SS_Qo : sstate := Eval vm_compute in arm BC_EQ false (SOff 10 0) (SOff aN8D 0) SS_Q.
Definition R_pb : YP09.region := YP09.mkRegion (Some aPB) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 250))].
Definition SS_P0 : sstate := Eval vm_compute in runto 0x32144 SS_Qo.
Definition SS_Po : sstate := Eval vm_compute in addreg R_pb (pin SS_P0 10%bv (SOff aPB 0)).
Definition CLOB_CL2 : list (bv 5) := [12; 13; 14; 15; 16]%bv.
Definition st_R (ss : sstate) : sstate := runto 0x321a0 ss.
Definition st_S (lo : bool) (ss : sstate) : sstate := noconds (pin (forget (runto 0x3228c (arm BC_LTU (negb lo) (SLit 512) (SOff aND 0) ss)) hCL2 CLOB_CL2) 11%bv (SOff aCL 0)).
Definition st_T (ss : sstate) : sstate := pin (runto 0x32294 ss) 10%bv (SOff aSSLOT 0).
Definition st_V (ss : sstate) : sstate := runto 0x322bc ss.
Definition st_W (small : bool) (ss : sstate) : sstate := noconds (pin (runto 0x322c4 (arm BC_LTU small (SOff 10 0) (SLit 4096) ss)) 12%bv (SOff aFIL 0)).
Definition SS_Re : sstate := Eval vm_compute in st_R SS_Qe.
Definition SS_Se : sstate := Eval vm_compute in st_S true SS_Re.
Definition SS_Te : sstate := Eval vm_compute in st_T SS_Se.
Definition SS_Ve : sstate := Eval vm_compute in st_V SS_Te.
Definition SS_We : sstate := Eval vm_compute in st_W true SS_Ve.
Definition SS_Ro : sstate := Eval vm_compute in st_R SS_Po.
Definition SS_So : sstate := Eval vm_compute in st_S true SS_Ro.
Definition SS_To : sstate := Eval vm_compute in st_T SS_So.
Definition SS_Vo : sstate := Eval vm_compute in st_V SS_To.
Definition SS_Wo : sstate := Eval vm_compute in st_W true SS_Vo.
