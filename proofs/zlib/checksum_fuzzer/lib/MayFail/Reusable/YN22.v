(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN22.v, with its module paths changed. *)
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
Definition aAV := 42%nat.
Definition aTQ := 43%nat.
Definition aJ := 44%nat.
Definition DBJ : Z := 125613361.
Definition R_gw : region := mkRegion (Some 18%nat) 0 40 24 28 [mkChunk 24 (CVal 4 (SOff aAV 0))].
Definition R_tqj : region := mkRegion (Some aTQ) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff aJ 0))].
Definition MASKX : sv := SExt true 32 (SOff aAV 0).
Definition LOWBIT : sv := SAlu ALU_AND MASKX (SAluw ALU_SUB (SLit 0) MASKX).
Definition TQADDR : sv := SAlu ALU_ADD (SLit DEB) (SAluw ALU_SRL (SMd M_MUL LOWBIT (SLit DBJ)) (SLit 27)).
Definition AVAIL' : sv := SAluw ALU_SUB MASKX LOWBIT.
Definition C_lb : acond := mkAC BC_NE LOWBIT (SLit 0).
Definition t2f_facts : facts :=
mkFacts [(18%nat, mkAF 4096 (2 ^ 63) 3); (aAV, mkAF 1 (2 ^ 32 - 1) 0); (aTQ, mkAF DEB (DEB + 31) 0); (aJ, mkAF 0 31 0); (2%nat, F_sp48)]
[C_lb] [(TQADDR, SOff aTQ 0)].
Definition t2f_mem : smem := [R_gw; R_tqj].
Definition ss_T2f : sstate :=
mkSS PB (regs_sv [(10%nat, MASKX); (9%nat, SLit LOCK); (19%nat, SLit DEB); (4%nat, SLit TP)]) t2f_mem None t2f_facts.
Definition SST2f : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL PC ss_T2f)) t2f_facts.
Definition R_gw' : region := mkRegion (Some 18%nat) 0 40 24 28 [mkChunk 24 (CVal 4 AVAIL')].
Definition T2_VIEW : list nat := ([18; 19; 2; 4; 8; 9]%nat ++ CSAVED).
Lemma T2f_run_ok : run_to_ok PC ss_T2f (fst (sym_run_toN src0segs src0tbl FUEL PC ss_T2f)).
Proof. split; vm_compute; reflexivity. Qed.
Lemma SST2f_view :
cview T2_VIEW SST2f = (PC, None, [R_gw'; R_tqj], [SOff 18 0; SOff aJ 0; SOff 2 0; SLit TP; SOff 8 0; SLit LOCK] ++ csaved_svs).
Proof. vm_compute. reflexivity. Qed.
Theorem T2f_run E ms md :
st_ok src0segs E ss_T2f ms -> m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg ms md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E SST2f ms1 /\ frame_of E t2f_mem (ms_mem ms) (ms_mem ms1)).
Proof.
intros HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to PC); [exact HS | apply T2f_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
unfold SST2f. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS)].
Qed.
Definition t2c_facts : facts := mkFacts [(20%nat, mkAF 0 47 0); (8%nat, mkAF 0 131051 0); (2%nat, F_sp48)] [] [].
Definition ss_T2c : sstate := mkSS PB (regs_lit [(10%nat, 0); (9%nat, LOCK); (19%nat, DEB); (4%nat, TP)]) [] None t2c_facts.
Definition SST2c : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL ASLOT ss_T2c)) t2c_facts.
Definition T2c_VIEW : list nat := ([1; 10; 11; 18; 20; 2; 4; 8; 9; 19]%nat ++ CSAVED).
Lemma T2c_run_ok : run_to_ok ASLOT ss_T2c (fst (sym_run_toN src0segs src0tbl FUEL ASLOT ss_T2c)).
Proof. split; vm_compute; reflexivity. Qed.
Lemma SST2c_view :
cview T2c_VIEW SST2c = (ASLOT, None, [], [SLit RA_AS; SOff 20 0; SOff 8 0; SOff 20 0; SOff 20 0; SOff 2 0; SLit TP; SOff 8 0; SLit LOCK; SLit DEB] ++ csaved_svs).
Proof. vm_compute. reflexivity. Qed.
Theorem T2c_run E ms md :
st_ok src0segs E ss_T2c ms -> m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg ms md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E SST2c ms1 /\ frame_of E [] (ms_mem ms) (ms_mem ms1)).
Proof.
intros HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to ASLOT); [exact HS | apply T2c_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
unfold SST2c. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS)].
Qed.
Definition aACT := 40%nat.
Definition aG := 41%nat.
Definition AL4 : sv * sv := (SAlu ALU_SLL (SOff 18 0) (SLit 3), SOff aACT (-(CTX+80))).
Definition R_act4 : region := mkRegion (Some aACT) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff aG 0))].
Definition t4ok_facts : facts :=
mkFacts [(10%nat, mkAF 0 31 0); (18%nat, mkAF 0 47 0); (2%nat, F_sp48); (aACT, mkAF (CTX+80) (CTX+80+8*47) 3); (aG, mkAF 4096 (2^63) 3)] [] [AL4].
Definition ss_T4ok : sstate := mkSS RA_AS (regs_lit [(9%nat, LOCK); (4%nat, TP)]) [R_act4] None t4ok_facts.
Definition SST4ok : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL PC ss_T4ok)) t4ok_facts.
Lemma T4ok_run_ok : run_to_ok PC ss_T4ok (fst (sym_run_toN src0segs src0tbl FUEL PC ss_T4ok)).
Proof. split; vm_compute; reflexivity. Qed.
Lemma SST4ok_view :
cview T2_VIEW SST4ok = (PC, None, [R_act4], [SOff aG 0; SOff 10 0; SOff 2 0; SLit TP; SOff 8 0; SLit LOCK] ++ csaved_svs).
Proof. vm_compute. reflexivity. Qed.
Theorem T4ok_run E ms md :
st_ok src0segs E ss_T4ok ms -> m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg ms md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E SST4ok ms1 /\ frame_of E [R_act4] (ms_mem ms) (ms_mem ms1)).
Proof.
intros HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to PC); [exact HS | apply T4ok_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
unfold SST4ok. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS)].
Qed.
Definition t4f_facts : facts := mkFacts [(2%nat, F_sp48)] [] [].
Definition t4f_mem : smem := [R_frame; R_lock].
Definition ss_T4f : sstate := mkSS RA_AS (regs_lit [(10%nat, -1); (9%nat, LOCK); (4%nat, TP)]) t4f_mem None t4f_facts.
Definition SST4f : sstate := set_facts (fst (sym_run_toN src0segs src0tbl FUEL FRET ss_T4f)) t4f_facts.
Definition T4f_VIEW : list nat := ([1; 2; 4; 8; 9; 10; 18; 19; 20]%nat ++ CSAVED).
Lemma T4f_run_ok : run_to_ok FRET ss_T4f (fst (sym_run_toN src0segs src0tbl FUEL FRET ss_T4f)).
Proof. split; vm_compute; reflexivity. Qed.
Lemma SST4f_view :
cview T4f_VIEW SST4f = (FRET, None, t4f_mem,
[SOff aRA 0; SOff 2 48; SLit TP; SOff aS0 0; SOff aS1 0; SLit 0; SOff aS2 0; SOff aS3 0; SOff aS4 0] ++ csaved_svs).
Proof. vm_compute. reflexivity. Qed.
Theorem T4f_run E ms md :
st_ok src0segs E ss_T4f ms -> m_halted md = None -> m_vm_lazy md = [] ->
SR src0segs (mkCfg ms md)
(fun c' => exists ms1, c' = mkCfg ms1 md /\ st_ok src0segs E SST4f ms1 /\ frame_of E t4f_mem (ms_mem ms) (ms_mem ms1)).
Proof.
intros HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to FRET); [exact HS | apply T4f_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [|exact HF].
unfold SST4f. apply st_ok_refacts; [exact HS1 | exact (st_ok_facts_ok _ _ _ _ HS)].
Qed.
End a.
