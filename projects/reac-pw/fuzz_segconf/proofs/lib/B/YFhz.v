(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AFhz.v, with its module paths changed and its addresses moved to plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the phases start at asan_malloc's entry (AFhy.v SS0); the trampoline's run to the unwinder and the unwinder call are gone. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/AFhz.v (donor image sha256 c0661b96b5bd), with its module paths changed and its addresses moved to reac-pw/fuzz_segconf's ASan build. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/AFhz.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YB1q YF0m YF0x YFl0 YFhy.
Import ListNotations. Open Scope Z_scope.
Definition runto (pc : Z) (ss : sstate) : sstate := fst (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL pc ss).
Definition pin (ss : sstate) (r : bv 5) (e : sv) : sstate := mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition forget (ss : sstate) (k : nat) (clob : list (bv 5)) : sstate := ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss).
Definition addreg (r : YP09.region) (ss : sstate) : sstate := mkSS (ss_pc ss) (ss_regs ss) (r :: ss_mem ss) (ss_resv ss) (ss_facts ss).
Definition noconds (ss : sstate) : sstate := YP03.prune ss [] [].
Definition arm (c : branch_cond) (taken : bool) (a b : sv) (ss : sstate) : sstate := add_cond ss (mkAC (if taken then c else neg_bc c) a b).
Definition hCL : nat := 80.
Definition hJN : nat := 103.
Definition hD1 : nat := 117.
Definition SS_1 : sstate := SS0.
Definition SS_A : sstate := Eval vm_compute in runto 0x332a8 SS_1.
Definition SS_A1 : sstate := Eval vm_compute in runto 0x33314 (arm BC_GEU false (SOff 10 0) (SLit 97) SS_A).
Definition SS_A2' : sstate := Eval vm_compute in runto 0x332b8 (arm BC_GEU true (SOff 10 0) (SLit 97) SS_A).
Definition SS_A2 : sstate := Eval vm_compute in runto 0x33314 (arm BC_GEU false (SOff 10 0) (SLit 449) SS_A2').
Definition SS_A3' : sstate := Eval vm_compute in runto 0x332cc (arm BC_GEU true (SOff 10 0) (SLit 449) SS_A2').
Definition SS_A3 : sstate := Eval vm_compute in runto 0x33314 (arm BC_GEU false (SOff 10 0) (SLit 3969) SS_A3').
Definition SS_A4' : sstate := Eval vm_compute in runto 0x332e0 (arm BC_GEU true (SOff 10 0) (SLit 3969) SS_A3').
Definition SS_A4 : sstate := Eval vm_compute in runto 0x33314 (arm BC_GEU false (SOff 10 0) (SLit 16129) SS_A4').
Definition SS_A5' : sstate := Eval vm_compute in runto 0x332f4 (arm BC_GEU true (SOff 10 0) (SLit 16129) SS_A4').
Definition SS_A5 : sstate := Eval vm_compute in runto 0x33314 (arm BC_GEU false (SOff 10 0) (SLit 32257) SS_A5').
Definition SS_A6' : sstate := Eval vm_compute in runto 0x33308 (arm BC_GEU true (SOff 10 0) (SLit 32257) SS_A5').
Definition SS_A6 : sstate := Eval vm_compute in runto 0x33314 SS_A6'.
Definition SS_L : sstate := Eval vm_compute in noconds (pin SS_A1 19%bv (SOff aKL 0)).
Lemma SS_L_2 : noconds (pin SS_A2 19%bv (SOff aKL 0)) = SS_L. Proof. vm_compute. reflexivity. Qed.
Lemma SS_L_3 : noconds (pin SS_A3 19%bv (SOff aKL 0)) = SS_L. Proof. vm_compute. reflexivity. Qed.
Lemma SS_L_4 : noconds (pin SS_A4 19%bv (SOff aKL 0)) = SS_L. Proof. vm_compute. reflexivity. Qed.
Lemma SS_L_5 : noconds (pin SS_A5 19%bv (SOff aKL 0)) = SS_L. Proof. vm_compute. reflexivity. Qed.
Lemma SS_L_6 : noconds (pin SS_A6 19%bv (SOff aKL 0)) = SS_L. Proof. vm_compute. reflexivity. Qed.
Definition SS_B0 : sstate := Eval vm_compute in runto 0x3337c SS_L.
Definition SS_B : sstate := Eval vm_compute in pin (pin SS_B0 10%bv (SOff aR8 0)) 11%bv (SLit 0).
Definition SS_B1 : sstate := Eval vm_compute in runto 0x33390 SS_B.
Definition SS_B2 : sstate := Eval vm_compute in pin SS_B1 20%bv (SOff aRZ 0).
Definition SS_B3 : sstate := Eval vm_compute in runto 0x333a0 SS_B2.
Definition SS_B4 : sstate := Eval vm_compute in pin SS_B3 19%bv (SOff aND 0).
Definition SS_C0 : sstate := Eval vm_compute in runto 0x37740 SS_B4.
Definition SS_C : sstate := Eval vm_compute in arm BC_GEU true (SAlu ALU_XOR (SOff aND 0) (SLit (-1))) (SLit 8) SS_C0.
Definition SS_D : sstate := Eval vm_compute in runto 0x3779c SS_C.
Definition SS_Dlo : sstate := Eval vm_compute in runto 0x378ac (arm BC_LTU false (SLit 512) (SOff aND 0) SS_D).
Definition SS_Dhi : sstate := Eval vm_compute in runto 0x378ac (arm BC_LTU true (SLit 512) (SOff aND 0) SS_D).
Definition CL_lo : sv := Eval vm_compute in sr_get (ss_regs SS_Dlo) 8%bv.
Definition CL_hi : sv := Eval vm_compute in sr_get (ss_regs SS_Dhi) 8%bv.
Definition CLOB_CL : list (bv 5) := [5; 6; 12; 14; 15; 16; 17]%bv.
Definition SS_E : sstate := Eval vm_compute in noconds (pin (forget SS_Dlo hCL CLOB_CL) 8%bv (SOff aCL 0)).
Lemma SS_E_hi : noconds (pin (forget SS_Dhi hCL CLOB_CL) 8%bv (SOff aCL 0)) = SS_E. Proof. vm_compute. reflexivity. Qed.
Definition SS_F0 : sstate := Eval vm_compute in runto 0x378c4 SS_E.
Definition SS_F : sstate := Eval vm_compute in pin SS_F0 9%bv (SOff aP 0).
Definition CLOBJ : list (bv 5) := [1; 5; 6; 7; 14; 15; 16; 17; 19; 20; 28; 29; 30; 31]%bv.
Definition SS_JN : sstate := Eval vm_compute in noconds (forget (runto 0x378cc SS_F) hJN CLOBJ).
Definition SS_G0 : sstate := Eval vm_compute in runto 0x378ec SS_JN.
Definition SS_G : sstate := Eval vm_compute in pin SS_G0 14%bv (SOff aPV (-16)).
Definition SS_H0 : sstate := Eval vm_compute in runto 0x33444 SS_G.
Definition SS_H : sstate := Eval vm_compute in pin SS_H0 10%bv (SOff aK 0).
Definition SS_I0 : sstate := Eval vm_compute in runto 0x33450 SS_H.
Definition SS_I : sstate := Eval vm_compute in pin SS_I0 20%bv (SOff aU 0).
Definition SS_J0 : sstate := Eval vm_compute in runto 0x33468 SS_I.
Definition SS_J : sstate := Eval vm_compute in arm BC_LTU false (SAlu ALU_ADD (SOff aK 0) (SOff aND 0)) (SAlu ALU_ADD (SOff 10 0) (SOff aU 0)) SS_J0.
Definition SS_K0 : sstate := Eval vm_compute in runto 0x33490 SS_J.
Definition SS_K : sstate := Eval vm_compute in arm BC_NE false (SAlu ALU_SRL (SOff 10 0) (SLit 48)) (SLit 0) SS_K0.
Definition SS_PD : sstate := Eval vm_compute in runto 0x76de0 SS_K.
Lemma seg1_stops :
snd (sym_run_toN_sh tfibsegs tfibtbl_rtA FUEL 0x7ffffff0 SS_1) = RS_stopped (SR_branch BC_GEU (SOff 10 0) (SLit 97)) /\
ss_pc SS_B0 = 0x3337c /\ ss_pc SS_B1 = 0x33390 /\ ss_pc SS_B3 = 0x333a0 /\ ss_pc SS_C0 = 0x37740 /\ ss_pc SS_D = 0x3779c /\
ss_pc SS_Dlo = 0x378ac /\ ss_pc SS_Dhi = 0x378ac /\ ss_pc SS_F0 = 0x378c4 /\ ss_pc SS_JN = 0x378cc /\ ss_pc SS_G0 = 0x378ec /\ ss_pc SS_H0 = 0x33444 /\
ss_pc SS_I0 = 0x33450 /\ ss_pc SS_J0 = 0x33468 /\ ss_pc SS_K0 = 0x33490 /\ ss_pc SS_PD = 0x76de0 /\
sr_get (ss_regs SS_B0) 10%bv = SAlu ALU_ADD (SAlu ALU_AND (SOff 10 7) (SLit 18446744073709551608)) (SLit 0) /\
sr_get (ss_regs SS_B1) 20%bv = SAluw ALU_SLL (SLit 16) (SOff aKL 0) /\
sr_get (ss_regs SS_B3) 19%bv = SAlu ALU_ADD (SOff aR8 0) (SOff aRZ 0) /\
CL_lo = SAlu ALU_SRL (SOff aND 31) (SLit 5) /\ svpure CL_hi = true /\ sv_only aND CL_hi = true /\
sr_get (ss_regs SS_I0) 20%bv = SAlu ALU_ADD (SOff aK 0) (SOff aRZ 0) /\
sr_get (ss_regs SS_PD) 1%bv = SLit 0x33550 /\ sr_get (ss_regs SS_PD) 10%bv = SOff 11 16 /\ sr_get (ss_regs SS_PD) 11%bv = SOff aLEN 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
