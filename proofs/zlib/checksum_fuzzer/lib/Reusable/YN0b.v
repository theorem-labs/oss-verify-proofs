(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition EV (xv : nat -> Z) : env := mkEnv (fun n => Z_to_bv 64 (xv n)) (fun _ => []).
Definition regs_init : list sv := SLit 0 :: map (fun i => SOff i 0) (seq 1 31).
Definition aRA := 1%nat. Definition aSP := 2%nat. Definition aTP := 4%nat. Definition aP := 10%nat.
Definition aG := 40%nat. Definition aMEM := 41%nat. Definition aOFF := 42%nat. Definition aH3 := 43%nat.
Definition aIDX := 44%nat. Definition aRSV := 45%nat. Definition aBITS := 46%nat. Definition aAV := 47%nat.
Definition aFR := 48%nat. Definition aAREA := 49%nat. Definition aSC := 50%nat. Definition aTQ := 51%nat.
Definition aSCL := 52%nat. Definition aLAST := 53%nat. Definition aML := 54%nat. Definition aMP := 55%nat.
Definition aEND := 57%nat. Definition aPN := 58%nat. Definition aEP := 59%nat.
Definition aSEC := 39%nat.
Definition aBASE := 60%nat. Definition aLEN := 61%nat. Definition aERR := 62%nat.
Definition TBL : Z := src0_D_size_classes.
Definition CEIL : Z := alloc_ceiling.
Definition FREE_RET : Z := src0_A_libc_free + 0x1c8.
Definition FREE_AFTER_NT : Z := src0_A_libc_free + 0x174.
Definition MUNMAP_ECALL : Z := src0_A_munmap + 0x28.
Inductive kcase := K1 | K2 | K3a | K3b.
Inductive rcase := R0 | R14 | R5 | R6.
Definition common_atoms : list (nat * afact) :=
[ (aSP, mkAF (CEIL_MIN + 8192) (2^63 - 1) 4);
(aP, mkAF 4096 (2^63 - 1) 4);
(aG, mkAF 4096 (2^63 - 1) 0);
(aMEM, mkAF 4096 (2^63 - 1) 0);
(aOFF, mkAF 0 65535 0);
(aAV, mkAF 0 (2^32 - 1) 0);
(aFR, mkAF 0 (2^32 - 1) 0);
(aAREA, mkAF 4096 (2^63 - 1) 0);
(aEND, mkAF 4096 (2^63 - 1) 0);
(aEP, mkAF 0 (2^63 - 1) 0) ].
Definition k_atoms (k : kcase) : list (nat * afact) :=
match k with
| K1 => [(aIDX, mkAF 0 31 0); (aBITS, mkAF 0 4095 0); (aSC, mkAF 0 47 0); (aTQ, mkAF TBL (TBL + 94) 0); (aSCL, mkAF 1 8191 0); (aLAST, mkAF 0 31 0)]
| K2 => [(aIDX, mkAF 0 31 0); (aBITS, mkAF 4096 (2^64-1) 0); (aML, mkAF 1 (2^52-1) 0); (aSC, mkAF 0 47 0); (aTQ, mkAF TBL (TBL + 94) 0); (aSCL, mkAF 1 8191 0); (aLAST, mkAF 1 31 0)]
| K3a => [(aIDX, mkAF 0 0 0); (aBITS, mkAF 4096 (2^64-1) 0); (aML, mkAF 1 (2^52-1) 0); (aMP, mkAF 4096 (2^63-1) 0); (aSC, mkAF 0 47 0); (aTQ, mkAF TBL (TBL + 94) 0); (aSCL, mkAF 1 8191 0); (aLAST, mkAF 0 0 0)]
| K3b => [(aIDX, mkAF 0 0 0); (aBITS, mkAF 4096 (2^64-1) 0); (aML, mkAF 1 (2^52-1) 0); (aMP, mkAF 4096 (2^63-1) 0); (aLAST, mkAF 0 0 0)]
end.
Definition r_atoms (r : rcase) : list (nat * afact) :=
match r with
| R0 => [(aH3, mkAF 0 31 0)]
| R14 => [(aH3, mkAF 32 159 0); (aRSV, mkAF 1 4 0); (aPN, mkAF 4096 (2^63 - 1) 0)]
| R5 => [(aH3, mkAF 160 191 0); (aRSV, mkAF 5 5 0)]
| R6 => [(aH3, mkAF 160 191 0); (aRSV, mkAF 6 (2^32 - 1) 0); (aPN, mkAF 4096 (2^63 - 1) 0)]
end.
Definition SELF : sv := SAluw ALU_SLL (SLit 1) (SOff aIDX 0).
Definition MASK : sv := SAlu ALU_OR (SExt true 32 (SOff aAV 0)) (SExt true 32 (SOff aFR 0)).
Definition ALL : sv := SAluw ALU_ADD (SAluw ALU_SLL (SLit 2) (SOff aBITS 0)) (SLit (-1)).
Definition FREED : sv := SExt true 32 (SOff aFR 0).
Definition common_conds : list acond :=
[ mkAC BC_GEU (SOff aLAST 0) (SOff aIDX 0);
mkAC BC_EQ (SAlu ALU_AND (SExt true 32 (SOff aAV 0)) SELF) (SLit 0);
mkAC BC_EQ (SAlu ALU_AND (SExt true 32 (SOff aFR 0)) SELF) (SLit 0);
mkAC BC_EQ (SAlu ALU_AND MASK SELF) (SLit 0) ].
Definition MLCHK : sv := SAlu ALU_ADD (SAlu ALU_SLL (SOff aML 0) (SLit 8)) (SLit (-1)).
Definition k_conds (k : kcase) : list acond :=
match k with
| K1 => [ mkAC BC_GEU (SOff aOFF 0) (SMd M_MUL (SOff aSCL 0) (SOff aIDX 0));
mkAC BC_LTU (SOff aOFF 0) (SMd M_MUL (SOff aIDX 1) (SOff aSCL 0)) ]
| K2 | K3a => [ mkAC BC_GEU (SOff aOFF 0) (SMd M_MUL (SOff aSCL 0) (SOff aIDX 0));
mkAC BC_LTU (SOff aOFF 0) (SMd M_MUL (SOff aIDX 1) (SOff aSCL 0));
mkAC BC_GEU MLCHK (SOff aOFF 0) ]
| K3b => [ mkAC BC_GEU MLCHK (SOff aOFF 0) ]
end.
Definition r_conds (r : rcase) : list acond :=
match r with
| R0 => []
| _ => [ mkAC BC_GEU (SOff aEP 0) (SOff aRSV 0) ]
end.
Definition STR16 : sv := SAlu ALU_SLL (SOff aSCL 0) (SLit 4).
Definition XCL : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff aMEM 0) STR16) (SMd M_MUL STR16 (SOff aIDX 0)).
Definition XPG : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff aMEM (-16)) (SOff aMP 0)) (SMd M_MUL (SOff aMP (-16)) (SOff aIDX 0)).
Definition common_alias : list (sv * sv) :=
[ (SAlu ALU_AND (SOff aH3 0) (SLit 31), SOff aIDX 0);
(SAlu ALU_SUB (SOff aP 0) (SAlu ALU_SLL (SOff aOFF 0) (SLit 4)), SOff aMEM 16);
(SAlu ALU_AND (SOff aG 0) (SLit (-4096)), SOff aAREA 0);
(SAlu ALU_SUB (SOff aEND 0) (SOff aP 0), SOff aEP 0) ].
Definition k_alias (k : kcase) : list (sv * sv) :=
match k with
| K1 => [ (SAlu ALU_AND (SOff aBITS 0) (SLit 31), SOff aLAST 0);
(SAlu ALU_SRL (SAlu ALU_SLL (SOff aBITS 0) (SLit 52)) (SLit 58), SOff aSC 0);
(SAlu ALU_SLL (SOff aSC 0) (SLit 1), SOff aTQ (- TBL));
(SAlu ALU_SRL (SOff aBITS 0) (SLit 12), SLit 0);
(SAlu ALU_AND (SAlu ALU_SRL (SOff aBITS 0) (SLit 5)) (SLit 126), SOff aTQ (- TBL));
(XCL, SOff aEND (-12)) ]
| K2 => [ (SAlu ALU_AND (SOff aBITS 0) (SLit 31), SOff aLAST 0);
(SAlu ALU_SRL (SAlu ALU_SLL (SOff aBITS 0) (SLit 52)) (SLit 58), SOff aSC 0);
(SAlu ALU_SLL (SOff aSC 0) (SLit 1), SOff aTQ (- TBL));
(SAlu ALU_SRL (SOff aBITS 0) (SLit 12), SOff aML 0);
(SAlu ALU_AND (SAlu ALU_SRL (SOff aBITS 0) (SLit 5)) (SLit 126), SOff aTQ (- TBL));
(XCL, SOff aEND (-12)) ]
| K3a => [ (SAlu ALU_AND (SOff aBITS 0) (SLit 31), SLit 0);
(SAlu ALU_SRL (SAlu ALU_SLL (SOff aBITS 0) (SLit 52)) (SLit 58), SOff aSC 0);
(SAlu ALU_SLL (SOff aSC 0) (SLit 1), SOff aTQ (- TBL));
(SAlu ALU_SRL (SOff aBITS 0) (SLit 12), SOff aML 0);
(SAlu ALU_AND (SOff aBITS 0) (SLit (-4096)), SOff aMP 0);
(XPG, SOff aEND (-12)) ]
| K3b => [ (SAlu ALU_AND (SOff aBITS 0) (SLit 31), SLit 0);
(SAlu ALU_SRL (SAlu ALU_SLL (SOff aBITS 0) (SLit 52)) (SLit 58), SLit 63);
(SAlu ALU_SRL (SOff aBITS 0) (SLit 12), SOff aML 0);
(SAlu ALU_AND (SOff aBITS 0) (SLit (-4096)), SOff aMP 0);
(XPG, SOff aEND (-12)) ]
end.
Definition r_alias (r : rcase) : list (sv * sv) :=
match r with
| R0 => [ (SAlu ALU_SRL (SOff aH3 0) (SLit 5), SLit 0) ]
| R14 => [ (SAlu ALU_SRL (SOff aH3 0) (SLit 5), SOff aRSV 0); (SAlu ALU_SUB (SOff aEND 0) (SOff aRSV 0), SOff aPN 0) ]
| R5 => [ (SAlu ALU_SRL (SOff aH3 0) (SLit 5), SLit 5); (SAlu ALU_SUB (SOff aEND 0) (SOff aRSV 0), SOff aEND (-5)) ]
| R6 => [ (SAlu ALU_SRL (SOff aH3 0) (SLit 5), SLit 5); (SAlu ALU_SUB (SOff aEND 0) (SOff aRSV 0), SOff aPN 0) ]
end.
Definition reg_hdr : region :=
mkRegion (Some aP) (-4) 0 (-3) 0 [mkChunk (-4) (CVal 1 (SLit 0)); mkChunk (-3) (CVal 1 (SOff aH3 0)); mkChunk (-2) (CVal 2 (SOff aOFF 0))].
Definition reg_grp : region := mkRegion (Some aMEM) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff aG 0))].
Definition reg_meta : region :=
mkRegion (Some aG) 16 40 28 32 [mkChunk 16 (CVal 8 (SOff aMEM 0)); mkChunk 24 (CVal 4 (SOff aAV 0)); mkChunk 28 (CVal 4 (SOff aFR 0)); mkChunk 32 (CVal 8 (SOff aBITS 0))].
Definition reg_area : region := mkRegion (Some aAREA) 0 8 0 0 [mkChunk 0 (CVal 8 (SOff aSEC 0))].
Definition reg_ctx : region :=
mkRegion None src0_D_malloc_context (src0_D_malloc_context + 8) 0 0 [mkChunk src0_D_malloc_context (CVal 8 (SOff aSEC 0))].
Definition reg_nl : region :=
mkRegion None (src0_D_libc + 3) (src0_D_libc + 4) 0 0 [mkChunk (src0_D_libc + 3) (CVal 1 (SLit 0))].
Definition reg_stk : region := mkRegion (Some aSP) (-8192) 0 (-8192) 0 [].
Definition reg_tq : region := mkRegion (Some aTQ) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff aSCL 0))].
Definition reg_end1 : region := mkRegion (Some aEND) 0 1 0 0 [mkChunk 0 (CVal 1 (SLit 0))].
Definition reg_end5 : region :=
mkRegion (Some aEND) (-5) 1 0 0 [mkChunk (-5) (CVal 1 (SLit 0)); mkChunk (-4) (CVal 4 (SOff aRSV 0)); mkChunk 0 (CVal 1 (SLit 0))].
Definition reg_pn : region := mkRegion (Some aPN) 0 1 0 0 [mkChunk 0 (CVal 1 (SLit 0))].
Definition common_mem : smem := [reg_hdr; reg_grp; reg_meta; reg_area; reg_ctx; reg_nl; reg_stk].
Definition k_mem (k : kcase) : smem := match k with K3b => [] | _ => [reg_tq] end.
Definition r_mem (r : rcase) : smem :=
match r with
| R0 => [reg_end1]
| R14 => [reg_end1; reg_pn]
| R5 => [reg_end5]
| R6 => [reg_end5; reg_pn]
end.
Definition free_facts (k : kcase) (r : rcase) : facts :=
mkFacts (common_atoms ++ k_atoms k ++ r_atoms r) (common_conds ++ k_conds k ++ r_conds r) (common_alias ++ k_alias k ++ r_alias r).
Definition free_mem (k : kcase) (r : rcase) : smem := common_mem ++ k_mem k ++ r_mem r.
Definition ss_free (k : kcase) (r : rcase) : sstate :=
mkSS src0_A_free regs_init (free_mem k r) None (free_facts k r).
Definition cond_fastA : acond := mkAC BC_NE FREED (SLit 0).
Definition cond_fastB : acond := mkAC BC_NE (SAluw ALU_ADD MASK SELF) ALL.
Definition cond_slowA : acond := mkAC BC_EQ FREED (SLit 0).
Definition cond_slowB : acond := mkAC BC_EQ (SAluw ALU_ADD MASK SELF) ALL.
Definition ss_fast (k : kcase) (r : rcase) : sstate := add_cond (add_cond (ss_free k r) cond_fastA) cond_fastB.
Definition ss_slowA (k : kcase) (r : rcase) : sstate := add_cond (ss_free k r) cond_slowA.
Definition ss_slowB (k : kcase) (r : rcase) : sstate := add_cond (add_cond (ss_free k r) cond_fastA) cond_slowB.
Definition SSF (k : kcase) (r : rcase) : sstate :=
set_facts (fst (sym_run_toN src0segs src0tbl FUEL FREE_RET (ss_fast k r))) (free_facts k r).
Definition SSNA (k : kcase) (r : rcase) : sstate :=
set_facts (fst (sym_run_toN src0segs src0tbl FUEL src0_A_nontrivial_free (ss_slowA k r))) (free_facts k r).
Definition SSNB (k : kcase) (r : rcase) : sstate :=
set_facts (fst (sym_run_toN src0segs src0tbl FUEL src0_A_nontrivial_free (ss_slowB k r))) (free_facts k r).
Section b.
Definition run_to_ok (stop : Z) (ss ss1 : sstate) : Prop :=
sym_run_toN src0segs src0tbl FUEL stop ss = (ss1, RS_running) /\ ss_pc ss1 = stop.
Lemma SR_run_to : forall stop E ss ss1 ms model,
st_ok src0segs E ss ms -> run_to_ok stop ss ss1 ->
m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok src0segs E ss1 ms1 /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros stop E ss ss1 ms model HS [Hrun Hpc] Hh Hlz.
eapply (SR_run_to_gen src0segs src0tbl src0tbl_ok FUEL stop E ss ss1 RS_running ms model _ Hh Hlz HS Hrun).
intros ms1 HS1 HF. apply SR_ret. exists ms1. auto.
Qed.
Definition run_ecall_ok (ss ss1 : sstate) : Prop :=
sym_runN src0segs src0tbl FUEL ss = (ss1, RS_ecall).
Lemma SR_run_ecall' : forall E ss ss1 ms model,
st_ok src0segs E ss ms -> run_ecall_ok ss ss1 ->
m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok_ecall src0segs E ss1 ms1 /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros E ss ss1 ms model HS Hrun Hh Hlz.
eapply (SR_run_ecall src0segs src0tbl src0tbl_ok FUEL E ss ss1 ms model _ Hh Hlz HS Hrun).
intros ms1 HS1 HF. apply SR_ret. exists ms1. auto.
Qed.
Lemma st_ok_refacts : forall E ss ms G,
st_ok src0segs E ss ms -> facts_ok E G -> st_ok src0segs E (set_facts ss G) ms.
Proof. intros. apply st_ok_set_facts; assumption. Qed.
End b.
Lemma free_fast_run_ok : forall k r, run_to_ok FREE_RET (ss_fast k r) (fst (sym_run_toN src0segs src0tbl FUEL FREE_RET (ss_fast k r))).
Proof. intros k r. split; destruct k, r; vm_compute; reflexivity. Qed.
Lemma free_slowA_run_ok : forall k r,
run_to_ok src0_A_nontrivial_free (ss_slowA k r) (fst (sym_run_toN src0segs src0tbl FUEL src0_A_nontrivial_free (ss_slowA k r))).
Proof. intros k r. split; destruct k, r; vm_compute; reflexivity. Qed.
Lemma free_slowB_run_ok : forall k r,
run_to_ok src0_A_nontrivial_free (ss_slowB k r) (fst (sym_run_toN src0segs src0tbl FUEL src0_A_nontrivial_free (ss_slowB k r))).
Proof. intros k r. split; destruct k, r; vm_compute; reflexivity. Qed.
Lemma facts_ok_add_cond_inv : forall E ss c, facts_ok E (ss_facts (add_cond ss c)) -> facts_ok E (ss_facts ss).
Proof.
intros E ss c (Ha & Hc & Hal). cbn in *. split; [exact Ha|]. split; [|exact Hal]. destruct Hc as [_ Hc]. exact Hc.
Qed.
Theorem free_fast_run : forall k r E ms model,
st_ok src0segs E (ss_fast k r) ms -> m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok src0segs E (SSF k r) ms1 /\
frame_of E (free_mem k r) (ms_mem ms) (ms_mem ms1)).
Proof.
intros k r E ms model HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to FREE_RET); [exact HS | apply free_fast_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split.
- unfold SSF. apply st_ok_refacts; [exact HS1|].
apply (facts_ok_add_cond_inv E (ss_free k r) cond_fastA). apply (facts_ok_add_cond_inv E _ cond_fastB).
exact (st_ok_facts_ok _ _ _ _ HS).
- exact HF.
Qed.
Theorem free_slowA_run : forall k r E ms model,
st_ok src0segs E (ss_slowA k r) ms -> m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok src0segs E (SSNA k r) ms1 /\
frame_of E (free_mem k r) (ms_mem ms) (ms_mem ms1)).
Proof.
intros k r E ms model HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to src0_A_nontrivial_free); [exact HS | apply free_slowA_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split.
- unfold SSNA. apply st_ok_refacts; [exact HS1|].
apply (facts_ok_add_cond_inv E (ss_free k r) cond_slowA). exact (st_ok_facts_ok _ _ _ _ HS).
- exact HF.
Qed.
Theorem free_slowB_run : forall k r E ms model,
st_ok src0segs E (ss_slowB k r) ms -> m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok src0segs E (SSNB k r) ms1 /\
frame_of E (free_mem k r) (ms_mem ms) (ms_mem ms1)).
Proof.
intros k r E ms model HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to src0_A_nontrivial_free); [exact HS | apply free_slowB_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split.
- unfold SSNB. apply st_ok_refacts; [exact HS1|].
apply (facts_ok_add_cond_inv E (ss_free k r) cond_fastA). apply (facts_ok_add_cond_inv E _ cond_slowB).
exact (st_ok_facts_ok _ _ _ _ HS).
- exact HF.
Qed.
Definition junk (i : nat) : sv := SOff (64 + i) 0.
Definition regs_after (lenz : bool) : list sv :=
[SLit 0; junk 1; SOff aSP (-48); SOff 3 0; SOff aTP 0; junk 5; junk 6; junk 7;
SOff aIDX 0; SOff aP 0;
(if lenz then SLit 0 else SOff aBASE 0); (if lenz then SLit 0 else SOff aLEN 0);
junk 12; junk 13; junk 14; junk 15; junk 16; junk 17;
SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
junk 28; junk 29; junk 30; junk 31].
Definition reg_lock : region :=
mkRegion None src0_D_malloc_lock (src0_D_malloc_lock + 4) 0 0 [mkChunk src0_D_malloc_lock (CVal 4 (SLit 0))].
Definition reg_errno : region :=
mkRegion (Some aTP) (-164) (-160) (-164) (-160) [mkChunk (-164) (CVal 4 (SOff aERR 0))].
Definition reg_stk_after : region :=
mkRegion (Some aSP) (-8192) 0 (-8192) 0
[mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0));
mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff aRA 0))].
Definition after_mem : smem := [reg_lock; reg_errno; reg_stk_after].
Definition after_atoms (lenz : bool) : list (nat * afact) :=
[ (aSP, mkAF (CEIL_MIN + 8192) (2^63 - 1) 4); (aTP, mkAF 4096 (2^63 - 1) 0); (aERR, mkAF 0 (2^32 - 1) 0) ]
++ (if lenz then [] else [ (aBASE, mkAF 4096 (2^63 - 1) 0); (aLEN, mkAF 1 (2^62) 0) ]).
Definition ss_after (lenz : bool) : sstate :=
mkSS FREE_AFTER_NT (regs_after lenz) after_mem None (mkFacts (after_atoms lenz) [] []).
Definition SST0 : sstate := fst (sym_run_toN src0segs src0tbl FUEL FREE_RET (ss_after true)).
Lemma free_tail0_run_ok : run_to_ok FREE_RET (ss_after true) SST0.
Proof. split; vm_compute; reflexivity. Qed.
Theorem free_tail0_run : forall E ms model,
st_ok src0segs E (ss_after true) ms -> m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok src0segs E SST0 ms1 /\
frame_of E after_mem (ms_mem ms) (ms_mem ms1)).
Proof.
intros E ms model HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to FREE_RET); [exact HS | apply free_tail0_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [exact HS1 | exact HF].
Qed.
Definition SST1 : sstate := fst (sym_runN src0segs src0tbl FUEL (ss_after false)).
Lemma free_tail1_run_ok : run_ecall_ok (ss_after false) SST1 /\ ss_pc SST1 = MUNMAP_ECALL /\ ss_resv SST1 = None.
Proof. split; [|split]; vm_compute; reflexivity. Qed.
Theorem free_tail1_run : forall E ms model,
st_ok src0segs E (ss_after false) ms -> m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok_ecall src0segs E SST1 ms1 /\
frame_of E after_mem (ms_mem ms) (ms_mem ms1)).
Proof.
intros E ms model HS Hh Hlz.
eapply SR_mono; [eapply SR_run_ecall'; [exact HS | apply (proj1 free_tail1_run_ok) | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [exact HS1 | exact HF].
Qed.
Definition ss_post_ecall : sstate := resume SST1 (SLit 0) (ss_mem SST1) (ss_facts SST1).
Definition SST2 : sstate := fst (sym_run_toN src0segs src0tbl FUEL FREE_RET ss_post_ecall).
Lemma free_tail2_run_ok : run_to_ok FREE_RET ss_post_ecall SST2.
Proof. split; vm_compute; reflexivity. Qed.
Theorem free_tail2_run : forall E ms model,
st_ok src0segs E ss_post_ecall ms -> m_halted model = None -> m_vm_lazy model = [] ->
SR src0segs (mkCfg ms model)
(fun c' => exists ms1, c' = mkCfg ms1 model /\ st_ok src0segs E SST2 ms1 /\
frame_of E (ss_mem ss_post_ecall) (ms_mem ms) (ms_mem ms1)).
Proof.
intros E ms model HS Hh Hlz.
eapply SR_mono; [eapply (SR_run_to FREE_RET); [exact HS | apply free_tail2_run_ok | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). exists ms1. split; [reflexivity|]. split; [exact HS1 | exact HF].
Qed.
Definition callee_view (ss : sstate) : list sv :=
map (fun i => sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat i))) [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition callee_view0 : list sv :=
[SOff 1 0; SOff 2 0; SOff 3 0; SOff 4 0; SOff 8 0; SOff 9 0; SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0;
SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0].
Lemma SSF_shape : forall k r,
ss_pc (SSF k r) = FREE_RET /\ ss_resv (SSF k r) = None /\ callee_view (SSF k r) = callee_view0 /\
ss_mem (SSF k r) =
mkRegion (Some aP) (-4) 0 (-3) 0 [mkChunk (-2) (CVal 2 (SLit 0)); mkChunk (-3) (CVal 1 (SLit 18446744073709551615)); mkChunk (-4) (CVal 1 (SLit 0))]
:: reg_grp
:: mkRegion (Some aG) 16 40 28 32 [mkChunk 28 (CVal 4 (SAluw ALU_ADD FREED SELF)); mkChunk 16 (CVal 8 (SOff aMEM 0)); mkChunk 24 (CVal 4 (SOff aAV 0)); mkChunk 32 (CVal 8 (SOff aBITS 0))]
:: reg_area :: reg_ctx :: reg_nl
:: mkRegion (Some aSP) (-8192) 0 (-8192) 0
[mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0));
mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))]
:: k_mem k ++ r_mem r.
Proof. intros k r. destruct k, r; vm_compute; repeat split; reflexivity. Qed.
Definition nt_view (ss : sstate) : list sv :=
map (fun i => sr_get (ss_regs ss) (Z_to_bv 5 (Z.of_nat i))) [1; 2; 3; 4; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Definition nt_view0 : list sv :=
[SLit FREE_AFTER_NT; SOff 2 (-48); SOff 3 0; SOff 4 0; SOff aIDX 0; SOff aP 0; SOff aG 0; SOff aIDX 0;
SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0].
Definition mem_at_nt (k : kcase) (r : rcase) : smem :=
mkRegion (Some aP) (-4) 0 (-3) 0 [mkChunk (-2) (CVal 2 (SLit 0)); mkChunk (-3) (CVal 1 (SLit 18446744073709551615)); mkChunk (-4) (CVal 1 (SLit 0))]
:: reg_grp :: reg_meta :: reg_area :: reg_ctx :: reg_nl
:: mkRegion (Some aSP) (-8192) 0 (-8192) 0
[mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0));
mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff 1 0))]
:: k_mem k ++ r_mem r.
Lemma SSNA_shape : forall k r,
ss_pc (SSNA k r) = src0_A_nontrivial_free /\ ss_resv (SSNA k r) = None /\ nt_view (SSNA k r) = nt_view0 /\
ss_mem (SSNA k r) = mem_at_nt k r.
Proof. intros k r. destruct k, r; vm_compute; repeat split; reflexivity. Qed.
Lemma SSNB_shape : forall k r,
ss_pc (SSNB k r) = src0_A_nontrivial_free /\ ss_resv (SSNB k r) = None /\ nt_view (SSNB k r) = nt_view0 /\
ss_mem (SSNB k r) = mem_at_nt k r.
Proof. intros k r. destruct k, r; vm_compute; repeat split; reflexivity. Qed.
Lemma SST0_shape :
ss_pc SST0 = FREE_RET /\ ss_resv SST0 = None /\ callee_view SST0 = callee_view0 /\ ss_mem SST0 = after_mem.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma SST1_shape :
ss_pc SST1 = MUNMAP_ECALL /\ ss_resv SST1 = None /\
sr_get (ss_regs SST1) 17 = SLit 215 /\ sr_get (ss_regs SST1) 10 = SOff aBASE 0 /\ sr_get (ss_regs SST1) 11 = SOff aLEN 0 /\
ss_mem SST1 = reg_lock :: reg_errno
:: [mkRegion (Some aSP) (-8192) 0 (-8192) 0
[mkChunk (-72) (CVal 8 (SOff aLEN 0)); mkChunk (-64) (CVal 8 (SOff aBASE 0)); mkChunk (-56) (CVal 8 (SLit (src0_A_libc_free + 0x1a4)));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0));
mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff aRA 0))]].
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma SST2_shape :
ss_pc SST2 = FREE_RET /\ ss_resv SST2 = None /\ callee_view SST2 = callee_view0 /\
ss_mem SST2 = reg_lock :: mkRegion (Some aTP) (-164) (-160) (-164) (-160) [mkChunk (-164) (CVal 4 (SExt true 32 (SOff aERR 0)))]
:: [mkRegion (Some aSP) (-8192) 0 (-8192) 0
[mkChunk (-72) (CVal 8 (SOff aLEN 0)); mkChunk (-64) (CVal 8 (SOff aBASE 0)); mkChunk (-56) (CVal 8 (SLit (src0_A_libc_free + 0x1a4)));
mkChunk (-40) (CVal 8 (SOff 19 0)); mkChunk (-32) (CVal 8 (SOff 18 0)); mkChunk (-24) (CVal 8 (SOff 9 0));
mkChunk (-16) (CVal 8 (SOff 8 0)); mkChunk (-8) (CVal 8 (SOff aRA 0))]].
Proof. vm_compute. repeat split; reflexivity. Qed.
End a.
