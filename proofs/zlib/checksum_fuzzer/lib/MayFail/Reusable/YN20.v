(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN20.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition aK := 33%nat.
Definition aE := 34%nat.
Definition aP := 35%nat.
Definition aTQ1 := 36%nat.
Definition aT1 := 37%nat.
Definition aTQ2 := 38%nat.
Definition aT2 := 39%nat.
Definition aTQ3 := 40%nat.
Definition F_spE : afact := mkAF (CEIL_MIN + 8192) (2 ^ 63 - 1) 4.
Definition R_frame0 : region := mkRegion (Some 2%nat) (-48) 0 (-48) 0 [].
Definition R_tq1 : region := mkRegion (Some aTQ1) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff aE 0))].
Definition R_tq2 : region := mkRegion (Some aTQ2) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff aT1 0))].
Definition R_tq3 : region := mkRegion (Some aTQ3) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff aT2 0))].
Definition AL_k : sv * sv := (SAlu ALU_SRL (SOff 10 3) (SLit 4), SOff aK 0).
Definition smx : sv := SOff aK 1.
Definition sm1 : sv := SAlu ALU_OR (SAlu ALU_OR (SAluw ALU_SRL smx (SLit 2)) smx) (SAluw ALU_SRL smx (SLit 1)).
Definition sm2 : sv := SAlu ALU_OR (SAluw ALU_SRL sm1 (SLit 2)) (SAluw ALU_SRL smx (SLit 1)).
Definition sm3 : sv := SAlu ALU_OR (SAlu ALU_SRL sm2 (SLit 4)) sm2.
Definition sm4 : sv := SAlu ALU_OR (SAlu ALU_SRL sm3 (SLit 8)) sm3.
Definition sm5 : sv := SAlu ALU_OR (SAlu ALU_SRL (SAlu ALU_SLL sm4 (SLit 33)) (SLit 49)) sm4.
Definition ANDX : sv := SAlu ALU_AND (SAlu ALU_ADD sm5 (SLit 1)) (SAlu ALU_XOR sm5 (SLit (-1))).
Definition AL_p : sv * sv := (ANDX, SOff aP 0).
Definition DBJ : Z := 125613361.
Definition TQ1X : sv := SAlu ALU_ADD (SLit DEB) (SAluw ALU_SRL (SMd M_MUL (SOff aP 0) (SLit DBJ)) (SLit 27)).
Definition C4X : sv := SAlu ALU_XOR (SAlu ALU_SLL (SOff aE 0) (SLit 2)) (SLit 124).
Definition TQ2X : sv := SAlu ALU_ADD (SLit SCT) (SAlu ALU_SLL (SAlu ALU_SUB (SLit 121) C4X) (SLit 1)).
Definition I2C (b1 : bool) : Z := if b1 then 120 else 122.
Definition TQ3X (b1 : bool) : sv := SAlu ALU_ADD (SLit SCT) (SAlu ALU_SLL (SAlu ALU_SUB (SLit (I2C b1)) C4X) (SLit 1)).
Definition AL_q1 : sv * sv := (TQ1X, SOff aTQ1 0).
Definition AL_q2 : sv * sv := (TQ2X, SOff aTQ2 0).
Definition AL_q3 (b1 : bool) : sv * sv := (TQ3X b1, SOff aTQ3 0).
Definition C_b1 (b1 : bool) : acond := mkAC (if b1 then BC_LTU else BC_GEU) (SOff aK 0) (SOff aT1 0).
Definition RESX (b1 : bool) : sv :=
SAlu ALU_OR (SAlu ALU_SUB (SLit (I2C b1)) C4X) (SAlu ALU_XOR (SAlu ALU_SLTU (SOff aK 0) (SOff aT2 0)) (SLit 1)).
Definition t0s_facts : facts := mkFacts [(2%nat, F_spE); (10%nat, mkAF 0 156 0); (aK, mkAF 0 9 0)] [] [AL_k].
Definition t0b_atoms : list (nat * afact) :=
[(2%nat, F_spE); (10%nat, mkAF 157 131051 0); (aK, mkAF 10 8190 0); (aE, mkAF 3 12 0); (aP, mkAF 8 4096 0);
(aTQ1, mkAF DEB (DEB + 31) 0); (aT1, mkAF 0 8191 0); (aTQ2, mkAF SCT (SCT + 94) 1); (aT2, mkAF 0 8191 0); (aTQ3, mkAF SCT (SCT + 94) 1)].
Definition t0b_facts (b1 : bool) : facts := mkFacts t0b_atoms [C_b1 b1] [AL_k; AL_p; AL_q1; AL_q2; AL_q3 b1].
Definition t0s_mem : smem := [R_frame0].
Definition t0b_mem : smem := [R_frame0; R_tq1; R_tq2; R_tq3].
Definition ss_T0s : sstate := mkSS src0_A_malloc (regs_lit [(4%nat, TP)]) t0s_mem None t0s_facts.
Definition ss_T0b (b1 : bool) : sstate := mkSS src0_A_malloc (regs_lit [(4%nat, TP)]) t0b_mem None (t0b_facts b1).
Definition SST0s : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL PA ss_T0s)) t0s_facts.
Definition SST0b (b1 : bool) : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL PA (ss_T0b b1))) (t0b_facts b1).
Definition R_frame1 : region := mkRegion (Some 2%nat) (-48) 0 (-48) 0
[mkChunk (-48) (CVal 8 (SOff 20 0)); mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0));
mkChunk (-24) (CVal 8 (SOff 9 0)); mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition T0_VIEW : list nat := ([2; 4; 8; 9; 19; 20]%nat ++ CSAVED).
Lemma T0s_run_ok : run_to_ok PA ss_T0s (fst (sym_run_toN src0segs src0tbl FUEL PA ss_T0s)).
Proof. split; vm_compute; reflexivity. Qed.
Lemma T0b_run_ok b1 : run_to_ok PA (ss_T0b b1) (fst (sym_run_toN src0segs src0tbl FUEL PA (ss_T0b b1))).
Proof. destruct b1; split; vm_compute; reflexivity. Qed.
Lemma SST0s_view :
cview T0_VIEW SST0s = (PA, None, [R_frame1], [SOff 2 (-48); SLit TP; SOff 10 0; SLit LOCK; SLit DEB; SOff aK 0] ++ csaved_svs).
Proof. vm_compute. reflexivity. Qed.
Lemma SST0b_view b1 :
cview T0_VIEW (SST0b b1) = (PA, None, R_frame1 :: tl t0b_mem, [SOff 2 (-48); SLit TP; SOff 10 0; SLit LOCK; SLit DEB; RESX b1] ++ csaved_svs).
Proof. destruct b1; vm_compute; reflexivity. Qed.
Theorem T0s_run E ms md :
st_ok src0segs E ss_T0s ms -> m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg ms md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E SST0s ms1 /\ frame_of E t0s_mem (ms_mem ms) (ms_mem ms1)).
Proof.
intros HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to PA); [exact HS | apply T0s_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
unfold SST0s. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS)].
Qed.
Theorem T0b_run b1 E ms md :
st_ok src0segs E (ss_T0b b1) ms -> m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg ms md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E (SST0b b1) ms1 /\ frame_of E t0b_mem (ms_mem ms) (ms_mem ms1)).
Proof.
intros HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to PA); [exact HS | apply T0b_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
unfold SST0b. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS)].
Qed.
End a.
