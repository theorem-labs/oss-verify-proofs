(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the phases start at asan_malloc's entry (AFi9.v S0); the trampoline's run to the unwinder and the unwinder call are gone, and the last phase stops at asan_malloc's ret. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFid.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AFid.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AFid.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YF0m YF0x YFl0 YFhy YFhz YFi9.
Import ListNotations. Open Scope Z_scope.
Definition armR (cnd : branch_cond) (tk : bool) (r1 r2 : bv 5) (ss : sstate) : sstate :=
arm cnd tk (sr_get (ss_regs ss) r1) (sr_get (ss_regs ss) r2) ss.
Definition CLOB_L : list (bv 5) := [5; 6; 7; 14; 15; 16; 17; 28]%bv.
Definition psLO1 (ss : sstate) : sstate := armR BC_GEU true 14 10 (runto 0x57df4 ss).
Definition psLO2 (ss : sstate) : sstate := armR BC_GEU true 14 11 (runto 0x57fdc (psLO1 ss)).
Definition psLO (ss : sstate) : sstate := runto 0x58020 (psLO2 ss).
Definition psHI1 (ss : sstate) : sstate := armR BC_GEU false 14 10 (runto 0x57df4 ss).
Definition psHI2 (ss : sstate) : sstate := armR BC_LTU true 7 10 (runto 0x57e34 (psHI1 ss)).
Definition psHI3 (ss : sstate) : sstate := armR BC_GEU false 14 11 (runto 0x57fdc (psHI2 ss)).
Definition psHI4 (ss : sstate) : sstate := armR BC_GEU false 5 11 (runto 0x5801c (psHI3 ss)).
Definition psHI (ss : sstate) : sstate := runto 0x58020 (psHI4 ss).
Definition psJ (k : nat) (ss : sstate) : sstate := noconds (forget ss k CLOB_L).
Definition CLOB_Lt : list (bv 5) := [5; 7; 14; 15; 16; 17; 28]%bv.
Definition psJt (k : nat) (ss : sstate) : sstate := noconds (forget ss k CLOB_Lt).
Definition S_1 : sstate := S0.
Definition S_B0 : sstate := Eval vm_compute in runto 0x3337c S_1.
Definition S_B : sstate := Eval vm_compute in pin (pin S_B0 10%bv (SOff aR8 0)) 11%bv (SLit 0).
Definition S_C0 : sstate := Eval vm_compute in runto 0x333b8 S_B.
Definition S_C : sstate := Eval vm_compute in pin S_C0 19%bv (SOff aND 0).
Definition S_D0 : sstate := Eval vm_compute in runto 0x37740 S_C.
Definition S_D : sstate := Eval vm_compute in arm BC_GEU true (SAlu ALU_XOR (SOff aND 0) (SLit (-1))) (SLit 8) S_D0.
Definition S_E0 : sstate := Eval vm_compute in runto 0x37a6c S_D.
Definition S_E : sstate := Eval vm_compute in arm BC_GEU true (SOff aMS 0) (SOff aND 0) (pin S_E0 18%bv (SOff aMS 0)).
Definition S_G : sstate := Eval vm_compute in runto 0x6a364 S_E.
Definition S_N : sstate := Eval vm_compute in runtoC 0x68a9c S_G.
Lemma segS1_stops :
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 S_1) = RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0)) (SLit 7)) (SLit 0)) /\
ss_pc S_B0 = 0x3337c /\ ss_pc S_C0 = 0x333b8 /\ ss_pc S_D0 = 0x37740 /\ ss_pc S_E0 = 0x37a6c /\ ss_pc S_G = 0x6a364 /\ ss_pc S_N = 0x68a9c /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 S_E) = RS_stopped SR_fetch /\
snd (sym_run_toN_sh tfibsegs tfibtbl_rtC FUEL 0x7ffffff0 S_G) = RS_ecall /\
sr_get (ss_regs S_B0) 10%bv = SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0) /\
sr_get (ss_regs S_B0) 19%bv = SLit 7 /\
sr_get (ss_regs S_C0) 19%bv = SOff aR8 4096 /\ sr_get (ss_regs S_C0) 20%bv = SLit 2048 /\
sr_get (ss_regs S_E0) 18%bv = SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_AND (SOff aND 4095) (SLit 18446744073709547520)) (SLit 4096)) (SLit 0) /\
map (sr_get (ss_regs S_N)) [1; 10; 11; 12; 13; 14; 15; 17]%bv = [SLit 0x6a3ec; SLit 0; SOff aMS 0; SLit 3; SLit 34; SLit 18446744073709551615; SLit 0; SLit 222] /\
length (ss_mem S_N) = 60%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
