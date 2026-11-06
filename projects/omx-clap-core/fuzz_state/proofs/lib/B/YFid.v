(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFid.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0f YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YF0m YF0x YFl0 YFhy YFhz YFi9.
Import ListNotations. Open Scope Z_scope.
Definition armR (cnd : branch_cond) (tk : bool) (r1 r2 : bv 5) (ss : sstate) : sstate :=
arm cnd tk (sr_get (ss_regs ss) r1) (sr_get (ss_regs ss) r2) ss.
Definition CLOB_L : list (bv 5) := [5; 6; 7; 14; 15; 16; 17; 28]%bv.
Definition psLO1 (ss : sstate) : sstate := armR BC_GEU true 14 10 (runto 0x54324 ss).
Definition psLO2 (ss : sstate) : sstate := armR BC_GEU true 14 11 (runto 0x5450c (psLO1 ss)).
Definition psLO (ss : sstate) : sstate := runto 0x54550 (psLO2 ss).
Definition psHI1 (ss : sstate) : sstate := armR BC_GEU false 14 10 (runto 0x54324 ss).
Definition psHI2 (ss : sstate) : sstate := armR BC_LTU true 7 10 (runto 0x54364 (psHI1 ss)).
Definition psHI3 (ss : sstate) : sstate := armR BC_GEU false 14 11 (runto 0x5450c (psHI2 ss)).
Definition psHI4 (ss : sstate) : sstate := armR BC_GEU false 5 11 (runto 0x5454c (psHI3 ss)).
Definition psHI (ss : sstate) : sstate := runto 0x54550 (psHI4 ss).
Definition psJ (k : nat) (ss : sstate) : sstate := noconds (forget ss k CLOB_L).
Definition CLOB_Lt : list (bv 5) := [5; 7; 14; 15; 16; 17; 28]%bv.
Definition psJt (k : nat) (ss : sstate) : sstate := noconds (forget ss k CLOB_Lt).
Definition S_U : sstate := Eval vm_compute in runto 0x5ae80 S0.
Definition srs_U : smem := match ss_mem S_U with r0 :: rest => trim_lo r0 (-64) :: pick rest (seq 0 57) | [] => [] end.
Definition S_1 : sstate := Eval vm_compute in addreg R_bst (addreg R_scr1 (ss_after_call S_U srs_U sU1 0x533e0)).
Definition S_B0 : sstate := Eval vm_compute in runto 0x3213c S_1.
Definition S_B : sstate := Eval vm_compute in pin (pin S_B0 10%bv (SOff aR8 0)) 11%bv (SLit 0).
Definition S_C0 : sstate := Eval vm_compute in runto 0x32178 S_B.
Definition S_C : sstate := Eval vm_compute in pin S_C0 19%bv (SOff aND 0).
Definition S_D0 : sstate := Eval vm_compute in runto 0x3662c S_C.
Definition S_D : sstate := Eval vm_compute in arm BC_GEU true (SAlu ALU_XOR (SOff aND 0) (SLit (-1))) (SLit 8) S_D0.
Definition S_E0 : sstate := Eval vm_compute in runto 0x36958 S_D.
Definition S_E : sstate := Eval vm_compute in arm BC_GEU true (SOff aMS 0) (SOff aND 0) (pin S_E0 18%bv (SOff aMS 0)).
Definition S_G : sstate := Eval vm_compute in runto 0x66530 S_E.
Definition S_N : sstate := Eval vm_compute in runtoC 0x64c68 S_G.
Lemma segS1_stops :
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 S_1) = RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0)) (SLit 7)) (SLit 0)) /\
ss_pc S_B0 = 0x3213c /\ ss_pc S_C0 = 0x32178 /\ ss_pc S_D0 = 0x3662c /\ ss_pc S_E0 = 0x36958 /\ ss_pc S_G = 0x66530 /\ ss_pc S_N = 0x64c68 /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 S_E) = RS_stopped SR_fetch /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 S_G) = RS_ecall /\
sr_get (ss_regs S_B0) 10%bv = SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0) /\
sr_get (ss_regs S_B0) 19%bv = SLit 7 /\
sr_get (ss_regs S_C0) 19%bv = SOff aR8 4096 /\ sr_get (ss_regs S_C0) 20%bv = SLit 2048 /\
sr_get (ss_regs S_E0) 18%bv = SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_AND (SOff aND 4095) (SLit 18446744073709547520)) (SLit 4096)) (SLit 0) /\
map (sr_get (ss_regs S_N)) [1; 10; 11; 12; 13; 14; 15; 17]%bv = [SLit 0x665b8; SLit 0; SOff aMS 0; SLit 3; SLit 34; SLit 18446744073709551615; SLit 0; SLit 222] /\
length (ss_mem S_N) = 60%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
