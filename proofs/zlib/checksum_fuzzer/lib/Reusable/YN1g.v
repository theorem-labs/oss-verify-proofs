(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02 YN0j YN1k YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition DEB : Z := src0_D_debruijn32.
Definition DBJ : Z := 125613361.
Definition PS_HD : Z := src0_A_alloc_slot + 0x60.
Definition aAV := 42%nat. Definition aTQ := 43%nat. Definition aJ := 44%nat.
Definition R_m0 : region := mkRegion (Some 34%nat) 0 40 24 28 [mkChunk 24 (CVal 4 (SOff aAV 0))].
Definition R_tqj : region := mkRegion (Some aTQ) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff aJ 0))].
Definition MASKX : sv := SExt true 32 (SOff aAV 0).
Definition LOWBIT : sv := SAlu ALU_AND MASKX (SAluw ALU_SUB (SLit 0) MASKX).
Definition AVAIL' : sv := SAluw ALU_SUB MASKX LOWBIT.
Definition TQADDR : sv := SAlu ALU_ADD (SLit DEB) (SAluw ALU_SRL (SMd M_MUL LOWBIT (SLit DBJ)) (SLit 27)).
Definition C_mask : acond := mkAC BC_NE MASKX (SLit 0).
Definition C_lb : acond := mkAC BC_NE LOWBIT (SLit 0).
Definition f1_atoms : list (nat * afact) := [(34%nat, mkAF 4096 (2 ^ 63) 3); (aAV, mkAF 1 (2 ^ 32 - 1) 0); (aTQ, mkAF DEB (DEB + 31) 0); (aJ, mkAF 0 31 0)].
Definition f1_facts : facts := mkFacts (f1_atoms ++ f_atoms (ss_facts ss_hd)) [C_mask; C_lb] [(TQADDR, SOff aTQ 0)].
Definition ss_F1 : sstate := mkSS (ss_pc ss_hd) (ss_regs ss_hd) ([R_m0; R_tqj] ++ ss_mem ss_hd) None f1_facts.
Definition SSF1 : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL PS_JR ss_F1)) f1_facts.
Definition R_m0' : region := mkRegion (Some 34%nat) 0 40 24 28 [mkChunk 24 (CVal 4 AVAIL')].
Lemma ss_hd_pc : ss_pc ss_hd = PS_HD. Proof. vm_compute. reflexivity. Qed.
Lemma ss_hd_atoms : ss_atoms_lt 40 ss_hd = true. Proof. vm_compute. reflexivity. Qed.
Lemma F1_run_ok : run_to_ok PS_JR ss_F1 (fst (sym_run_toN src0segs src0tbl FUEL PS_JR ss_F1)).
Proof. split; vm_compute; reflexivity. Qed.
Lemma SSF1_shape :
ss_pc SSF1 = PS_JR /\ ss_resv SSF1 = None /\ ss_mem SSF1 = [R_m0'; R_tqj] ++ ss_mem ss_hd /\
sr_get (ss_regs SSF1) 1 = SOff 1 0 /\ sr_get (ss_regs SSF1) 10 = SOff aJ 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Theorem F1_run E ms md :
st_ok src0segs E ss_F1 ms -> m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg ms md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E SSF1 ms1 /\ frame_of E (ss_mem ss_F1) (ms_mem ms) (ms_mem ms1)).
Proof.
intros HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to PS_JR); [exact HS | apply F1_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
unfold SSF1. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS)].
Qed.
End a.
