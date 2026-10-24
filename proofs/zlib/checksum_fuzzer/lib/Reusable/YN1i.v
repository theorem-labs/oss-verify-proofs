(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02 YN2j YN0j YN1k YN0b YN1g YN1h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition PS_L : Z := src0_A_alloc_slot + 0x51c.
Definition PS_X : Z := src0_A_alloc_slot + 0x530.
Definition PS_S : Z := src0_A_alloc_slot + 0x550.
Definition aBITS2 := 55%nat.
Definition aT1 := 56%nat. Definition aT0 := 57%nat. Definition aA4 := 58%nat. Definition aA6 := 59%nat. Definition aA3 := 60%nat. Definition aNB := 61%nat.
Definition R_m2S : region := mkRegion (Some 48%nat) 0 40 0 0
[mkChunk 8 (CVal 8 (SOff 48 0)); mkChunk 16 (CVal 8 (SOff aG2 0)); mkChunk 24 (CVal 4 (SLit 0)); mkChunk 32 (CVal 8 (SOff aBITS2 0))].
Definition R_g2w (b : sv) : region := mkRegion (Some aG2) 0 16 8 9 [mkChunk 8 (CVal 1 b)].
Definition s_atoms : list (nat * afact) := c_atoms ++ [(aBITS2, mkAF 0 (2 ^ 64 - 1) 0); (36%nat, F_sct); (35%nat, F_sz)].
Definition ADDRSCT2 : sv := SAlu ALU_ADD (SLit SCT) (SAlu ALU_AND (SAlu ALU_SRL (SOff aBITS2 0) (SLit 5)) (SLit 126)).
Definition MEM_S (b : sv) : smem := [R_m2S; R_g2w b; R_sct] ++ R_actW (SOff 48 0) :: tl (ss_mem ss_hd).
Definition ss_S : sstate :=
mkSS PS_C (ss_regs ss_gamma) (MEM_S (SOff aAI2 0)) None (mkFacts (s_atoms ++ f_atoms (ss_facts ss_hd)) [C_c12] [(ADDRSCT2, SOff 36 0)]).
Definition SS_Sa : sstate := Eval vm_compute in closeF ss_S PS_L.
Lemma Sa_run_ok : run_to_ok PS_L ss_S (fst (sym_run_toN src0segs src0tbl FUEL PS_L ss_S)). Proof. split; vm_compute; reflexivity. Qed.
Lemma SS_Sa_eq : closeF ss_S PS_L = SS_Sa. Proof. vm_compute. reflexivity. Qed.
Definition AIDX : sv := SAlu ALU_AND (SOff aAI2 0) (SLit 31).
Definition SIZE : sv := SAlu ALU_SLL (SOff 35 0) (SLit 4).
Definition SPAN0 : sv := SAluw ALU_ADD (SMd M_MUL SIZE (SAlu ALU_ADD AIDX (SLit 2))) (SLit 16).
Definition SEND0 : sv := SAluw ALU_ADD (SMd M_MUL (SAlu ALU_ADD (SAlu ALU_SLL AIDX (SLit 4)) (SLit 48)) (SOff 35 0)) (SLit 15).
Lemma SS_Sa_shape : ss_pc SS_Sa = PS_L /\ ss_resv SS_Sa = None /\ ss_mem SS_Sa = MEM_S (SOff aAI2 0) /\ ss_facts SS_Sa = ss_facts ss_S /\
sr_get (ss_regs SS_Sa) 5 = SPAN0 /\ sr_get (ss_regs SS_Sa) 16 = SEND0 /\ sr_get (ss_regs SS_Sa) 14 = SAlu ALU_ADD AIDX (SLit 1) /\
sr_get (ss_regs SS_Sa) 15 = SIZE /\ sr_get (ss_regs SS_Sa) 17 = SLit 4096 /\
sr_get (ss_regs SS_Sa) 13 = SOff aBITS2 0 /\ sr_get (ss_regs SS_Sa) 12 = SOff aAI2 0 /\ sr_get (ss_regs SS_Sa) 11 = SOff aG2 0 /\ sr_get (ss_regs SS_Sa) 10 = SOff 48 0 /\
ss_atoms_lt 56 SS_Sa = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition updS : list (reg * sv) := [(6%bv, SOff aT1 0); (5%bv, SOff aT0 0); (14%bv, SOff aA4 0); (16%bv, SOff aA6 0); (13%bv, SOff aA3 0); (12%bv, SOff aNB 0)].
Definition F_nb : afact := mkAF 0 255 0.
Definition ss_Sc : sstate := Eval vm_compute in add_atom (set_regs_pc SS_Sa updS PS_S) aNB F_nb.
Lemma ss_Sc_eq : add_atom (set_regs_pc SS_Sa updS PS_S) aNB F_nb = ss_Sc. Proof. vm_compute. reflexivity. Qed.
Definition SS_Sc : sstate := Eval vm_compute in closeF ss_Sc PS_D.
Lemma Sc_run_ok : run_to_ok PS_D ss_Sc (fst (sym_run_toN src0segs src0tbl FUEL PS_D ss_Sc)). Proof. split; vm_compute; reflexivity. Qed.
Lemma SS_Sc_eq : closeF ss_Sc PS_D = SS_Sc. Proof. vm_compute. reflexivity. Qed.
Lemma merge_Sc : ss_atoms_lt 80 SS_Sc = true /\ mergeb ss_delta (junk_regs JD 80 SS_Sc) = true. Proof. vm_compute. split; reflexivity. Qed.
Lemma ss_Sc_shape : ss_mem ss_Sc = MEM_S (SOff aAI2 0) /\ ss_pc ss_Sc = PS_S.
Proof. vm_compute. split; reflexivity. Qed.
Lemma SS_Sc_shape : ss_mem SS_Sc = MEM_S (SOff aNB 0) /\ sr_get (ss_regs SS_Sc) 10 = SOff 48 0 /\ ss_pc SS_Sc = PS_D.
Proof. vm_compute. repeat split; reflexivity. Qed.
End a.
