(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK15 YK0n YK0v YK02 YP0n YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a YO0c YN2e YN2j.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH00 YH03 YH02 YN0j YN1k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition PS_CN : Z := src0_A_alloc_slot + 0x634.
Definition PS_MM : Z := src0_A_alloc_slot + 0x6a4.
Definition cnrun_ (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL PS_CN ss).
Definition mmrun_ (ss : sstate) : sstate := fst (sym_run_toN src0segs src0tbl FUEL PS_MM ss).
Definition a5_1 : sv := SAlu ALU_AND (SOff 10 0) (SLit 1).
Definition a5_3 : sv := SAlu ALU_AND (SOff 10 0) (SLit 3).
Definition conds_r (r : Z) : list acond :=
[mkAC (if Z.even r then BC_EQ else BC_NE) a5_1 (SLit 0);
mkAC (if r =? 1 then BC_EQ else BC_NE) a5_3 (SLit 1);
mkAC (if r =? 2 then BC_EQ else BC_NE) a5_3 (SLit 2);
mkAC (if r =? 0 then BC_EQ else BC_NE) a5_3 (SLit 0)].
Definition ss_M1r (r : Z) : sstate := fold_left add_cond (conds_r r) ss_M1.
Definition R_use2 : region := mkRegion (Some 33%nat) 480 488 0 0 [mkChunk 480 (CVal 8 (SOff 73 0))].
Definition F_use2 : afact := mkAF 0 (2 ^ 48) 0.
Definition stU2 (ss : sstate) : sstate :=
mkSS (ss_pc ss) (ss_regs ss) (R_use2 :: ss_mem ss) None (mkFacts ((73%nat, F_use2) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Definition ss_b0_ : sstate := Eval vm_compute in cnrun_ (ss_M1r 0).
Lemma gs_b0_ : sym_run_toN src0segs src0tbl FUEL PS_CN (ss_M1r 0) = (ss_b0_, RS_stopped (SR_branch BC_LT (SLit 31) (SOff 10 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_T : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_ (mkAC BC_LT (SLit 31) (SOff 10 0))).
Lemma gs_b0_T : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_ (mkAC BC_LT (SLit 31) (SOff 10 0))) = (ss_b0_T, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_T (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b0_TT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_T (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b0_TT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_T (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b0_TF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_T (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b0_TF, RS_stopped (SR_branch BC_NE (SOff 67 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TF (mkAC BC_NE (SOff 67 0) (SLit 0))).
Lemma gs_b0_TFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TF (mkAC BC_NE (SOff 67 0) (SLit 0))) = (ss_b0_TFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TF (mkAC BC_EQ (SOff 67 0) (SLit 0))).
Lemma gs_b0_TFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TF (mkAC BC_EQ (SOff 67 0) (SLit 0))) = (ss_b0_TFF, RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFF (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b0_TFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFF (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b0_TFFT, RS_stopped (SR_branch BC_LTU (SLit 32768) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFTT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFFT (mkAC BC_LTU (SLit 32768) (SOff 62 0))).
Lemma gs_b0_TFFTT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFFT (mkAC BC_LTU (SLit 32768) (SOff 62 0))) = (ss_b0_TFFTT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFTF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFFT (mkAC BC_GEU (SLit 32768) (SOff 62 0))).
Lemma gs_b0_TFFTF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFFT (mkAC BC_GEU (SLit 32768) (SOff 62 0))) = (ss_b0_TFFTF, RS_stopped (SR_branch BC_GEU (SLit 8192) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFTFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFFTF (mkAC BC_GEU (SLit 8192) (SOff 62 0))).
Lemma gs_b0_TFFTFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFFTF (mkAC BC_GEU (SLit 8192) (SOff 62 0))) = (ss_b0_TFFTFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFTFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFFTF (mkAC BC_LTU (SLit 8192) (SOff 62 0))).
Lemma gs_b0_TFFTFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFFTF (mkAC BC_LTU (SLit 8192) (SOff 62 0))) = (ss_b0_TFFTFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFF (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b0_TFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFF (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b0_TFFF, RS_stopped (SR_branch BC_LTU (SLit 32768) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFFF (mkAC BC_LTU (SLit 32768) (SOff 62 0))).
Lemma gs_b0_TFFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFFF (mkAC BC_LTU (SLit 32768) (SOff 62 0))) = (ss_b0_TFFFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFFF (mkAC BC_GEU (SLit 32768) (SOff 62 0))).
Lemma gs_b0_TFFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFFF (mkAC BC_GEU (SLit 32768) (SOff 62 0))) = (ss_b0_TFFFF, RS_stopped (SR_branch BC_GEU (SLit 8192) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFFFF (mkAC BC_GEU (SLit 8192) (SOff 62 0))).
Lemma gs_b0_TFFFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFFFF (mkAC BC_GEU (SLit 8192) (SOff 62 0))) = (ss_b0_TFFFFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_TFFFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_TFFFF (mkAC BC_LTU (SLit 8192) (SOff 62 0))).
Lemma gs_b0_TFFFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_TFFFF (mkAC BC_LTU (SLit 8192) (SOff 62 0))) = (ss_b0_TFFFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_F : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_ (mkAC BC_GE (SLit 31) (SOff 10 0))).
Lemma gs_b0_F : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_ (mkAC BC_GE (SLit 31) (SOff 10 0))) = (ss_b0_F, RS_stopped (SR_load (Some 33%nat) 480)).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_Fu : sstate := Eval vm_compute in cnrun_ (stU2 ss_b0_F).
Lemma gs_b0_Fu : sym_run_toN src0segs src0tbl FUEL PS_CN (stU2 ss_b0_F) = (ss_b0_Fu, RS_stopped (SR_branch BC_GEU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_Fu (mkAC BC_GEU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b0_FT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_Fu (mkAC BC_GEU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b0_FT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_Fu (mkAC BC_LTU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b0_FF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_Fu (mkAC BC_LTU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b0_FF, RS_stopped (SR_branch BC_NE (SOff 67 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FF (mkAC BC_NE (SOff 67 0) (SLit 0))).
Lemma gs_b0_FFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FF (mkAC BC_NE (SOff 67 0) (SLit 0))) = (ss_b0_FFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FF (mkAC BC_EQ (SOff 67 0) (SLit 0))).
Lemma gs_b0_FFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FF (mkAC BC_EQ (SOff 67 0) (SLit 0))) = (ss_b0_FFF, RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFF (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b0_FFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFF (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b0_FFFT, RS_stopped (SR_branch BC_LTU (SLit 32768) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFTT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFFT (mkAC BC_LTU (SLit 32768) (SOff 62 0))).
Lemma gs_b0_FFFTT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFFT (mkAC BC_LTU (SLit 32768) (SOff 62 0))) = (ss_b0_FFFTT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFTF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFFT (mkAC BC_GEU (SLit 32768) (SOff 62 0))).
Lemma gs_b0_FFFTF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFFT (mkAC BC_GEU (SLit 32768) (SOff 62 0))) = (ss_b0_FFFTF, RS_stopped (SR_branch BC_GEU (SLit 8192) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFTFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFFTF (mkAC BC_GEU (SLit 8192) (SOff 62 0))).
Lemma gs_b0_FFFTFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFFTF (mkAC BC_GEU (SLit 8192) (SOff 62 0))) = (ss_b0_FFFTFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFTFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFFTF (mkAC BC_LTU (SLit 8192) (SOff 62 0))).
Lemma gs_b0_FFFTFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFFTF (mkAC BC_LTU (SLit 8192) (SOff 62 0))) = (ss_b0_FFFTFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFF (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b0_FFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFF (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b0_FFFF, RS_stopped (SR_branch BC_LTU (SLit 32768) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFFF (mkAC BC_LTU (SLit 32768) (SOff 62 0))).
Lemma gs_b0_FFFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFFF (mkAC BC_LTU (SLit 32768) (SOff 62 0))) = (ss_b0_FFFFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFFF (mkAC BC_GEU (SLit 32768) (SOff 62 0))).
Lemma gs_b0_FFFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFFF (mkAC BC_GEU (SLit 32768) (SOff 62 0))) = (ss_b0_FFFFF, RS_stopped (SR_branch BC_GEU (SLit 8192) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFFFF (mkAC BC_GEU (SLit 8192) (SOff 62 0))).
Lemma gs_b0_FFFFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFFFF (mkAC BC_GEU (SLit 8192) (SOff 62 0))) = (ss_b0_FFFFFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b0_FFFFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b0_FFFFF (mkAC BC_LTU (SLit 8192) (SOff 62 0))).
Lemma gs_b0_FFFFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b0_FFFFF (mkAC BC_LTU (SLit 8192) (SOff 62 0))) = (ss_b0_FFFFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_ : sstate := Eval vm_compute in cnrun_ (ss_M1r 1).
Lemma gs_b1_ : sym_run_toN src0segs src0tbl FUEL PS_CN (ss_M1r 1) = (ss_b1_, RS_stopped (SR_branch BC_LT (SLit 31) (SOff 10 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_T : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_ (mkAC BC_LT (SLit 31) (SOff 10 0))).
Lemma gs_b1_T : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_ (mkAC BC_LT (SLit 31) (SOff 10 0))) = (ss_b1_T, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_TT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_T (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b1_TT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_T (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b1_TT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_TF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_T (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b1_TF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_T (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b1_TF, RS_stopped (SR_branch BC_NE (SOff 67 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_TFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_TF (mkAC BC_NE (SOff 67 0) (SLit 0))).
Lemma gs_b1_TFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_TF (mkAC BC_NE (SOff 67 0) (SLit 0))) = (ss_b1_TFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_TFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_TF (mkAC BC_EQ (SOff 67 0) (SLit 0))).
Lemma gs_b1_TFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_TF (mkAC BC_EQ (SOff 67 0) (SLit 0))) = (ss_b1_TFF, RS_stopped (SR_branch BC_GEU (SLit 32768) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_TFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_TFF (mkAC BC_GEU (SLit 32768) (SOff 62 0))).
Lemma gs_b1_TFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_TFF (mkAC BC_GEU (SLit 32768) (SOff 62 0))) = (ss_b1_TFFT, RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_TFFTT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_TFFT (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b1_TFFTT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_TFFT (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b1_TFFTT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_TFFTF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_TFFT (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b1_TFFTF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_TFFT (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b1_TFFTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_TFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_TFF (mkAC BC_LTU (SLit 32768) (SOff 62 0))).
Lemma gs_b1_TFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_TFF (mkAC BC_LTU (SLit 32768) (SOff 62 0))) = (ss_b1_TFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_F : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_ (mkAC BC_GE (SLit 31) (SOff 10 0))).
Lemma gs_b1_F : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_ (mkAC BC_GE (SLit 31) (SOff 10 0))) = (ss_b1_F, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_FT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_F (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b1_FT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_F (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b1_FT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_FF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_F (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b1_FF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_F (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b1_FF, RS_stopped (SR_branch BC_NE (SOff 67 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_FFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_FF (mkAC BC_NE (SOff 67 0) (SLit 0))).
Lemma gs_b1_FFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_FF (mkAC BC_NE (SOff 67 0) (SLit 0))) = (ss_b1_FFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_FFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_FF (mkAC BC_EQ (SOff 67 0) (SLit 0))).
Lemma gs_b1_FFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_FF (mkAC BC_EQ (SOff 67 0) (SLit 0))) = (ss_b1_FFF, RS_stopped (SR_branch BC_GEU (SLit 32768) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_FFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_FFF (mkAC BC_GEU (SLit 32768) (SOff 62 0))).
Lemma gs_b1_FFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_FFF (mkAC BC_GEU (SLit 32768) (SOff 62 0))) = (ss_b1_FFFT, RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_FFFTT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_FFFT (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b1_FFFTT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_FFFT (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b1_FFFTT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_FFFTF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_FFFT (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b1_FFFTF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_FFFT (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b1_FFFTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b1_FFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b1_FFF (mkAC BC_LTU (SLit 32768) (SOff 62 0))).
Lemma gs_b1_FFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b1_FFF (mkAC BC_LTU (SLit 32768) (SOff 62 0))) = (ss_b1_FFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_ : sstate := Eval vm_compute in cnrun_ (ss_M1r 2).
Lemma gs_b2_ : sym_run_toN src0segs src0tbl FUEL PS_CN (ss_M1r 2) = (ss_b2_, RS_stopped (SR_branch BC_LT (SLit 31) (SOff 10 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_T : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_ (mkAC BC_LT (SLit 31) (SOff 10 0))).
Lemma gs_b2_T : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_ (mkAC BC_LT (SLit 31) (SOff 10 0))) = (ss_b2_T, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_TT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_T (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b2_TT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_T (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b2_TT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_TF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_T (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b2_TF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_T (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b2_TF, RS_stopped (SR_branch BC_NE (SOff 67 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_TFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_TF (mkAC BC_NE (SOff 67 0) (SLit 0))).
Lemma gs_b2_TFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_TF (mkAC BC_NE (SOff 67 0) (SLit 0))) = (ss_b2_TFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_TFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_TF (mkAC BC_EQ (SOff 67 0) (SLit 0))).
Lemma gs_b2_TFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_TF (mkAC BC_EQ (SOff 67 0) (SLit 0))) = (ss_b2_TFF, RS_stopped (SR_branch BC_GEU (SLit 16384) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_TFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_TFF (mkAC BC_GEU (SLit 16384) (SOff 62 0))).
Lemma gs_b2_TFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_TFF (mkAC BC_GEU (SLit 16384) (SOff 62 0))) = (ss_b2_TFFT, RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_TFFTT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_TFFT (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b2_TFFTT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_TFFT (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b2_TFFTT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_TFFTF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_TFFT (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b2_TFFTF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_TFFT (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b2_TFFTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_TFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_TFF (mkAC BC_LTU (SLit 16384) (SOff 62 0))).
Lemma gs_b2_TFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_TFF (mkAC BC_LTU (SLit 16384) (SOff 62 0))) = (ss_b2_TFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_F : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_ (mkAC BC_GE (SLit 31) (SOff 10 0))).
Lemma gs_b2_F : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_ (mkAC BC_GE (SLit 31) (SOff 10 0))) = (ss_b2_F, RS_stopped (SR_load (Some 33%nat) 480)).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_Fu : sstate := Eval vm_compute in cnrun_ (stU2 ss_b2_F).
Lemma gs_b2_Fu : sym_run_toN src0segs src0tbl FUEL PS_CN (stU2 ss_b2_F) = (ss_b2_Fu, RS_stopped (SR_branch BC_GEU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_FT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_Fu (mkAC BC_GEU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b2_FT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_Fu (mkAC BC_GEU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b2_FT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_FF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_Fu (mkAC BC_LTU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b2_FF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_Fu (mkAC BC_LTU (SAlu ALU_ADD (SOff 56 0) (SOff 73 0)) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b2_FF, RS_stopped (SR_branch BC_NE (SOff 67 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_FFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_FF (mkAC BC_NE (SOff 67 0) (SLit 0))).
Lemma gs_b2_FFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_FF (mkAC BC_NE (SOff 67 0) (SLit 0))) = (ss_b2_FFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_FFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_FF (mkAC BC_EQ (SOff 67 0) (SLit 0))).
Lemma gs_b2_FFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_FF (mkAC BC_EQ (SOff 67 0) (SLit 0))) = (ss_b2_FFF, RS_stopped (SR_branch BC_GEU (SLit 16384) (SOff 62 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_FFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_FFF (mkAC BC_GEU (SLit 16384) (SOff 62 0))).
Lemma gs_b2_FFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_FFF (mkAC BC_GEU (SLit 16384) (SOff 62 0))) = (ss_b2_FFFT, RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_FFFTT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_FFFT (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b2_FFFTT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_FFFT (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b2_FFFTT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_FFFTF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_FFFT (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b2_FFFTF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_FFFT (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b2_FFFTF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b2_FFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b2_FFF (mkAC BC_LTU (SLit 16384) (SOff 62 0))).
Lemma gs_b2_FFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b2_FFF (mkAC BC_LTU (SLit 16384) (SOff 62 0))) = (ss_b2_FFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_ : sstate := Eval vm_compute in cnrun_ (ss_M1r 3).
Lemma gs_b3_ : sym_run_toN src0segs src0tbl FUEL PS_CN (ss_M1r 3) = (ss_b3_, RS_stopped (SR_branch BC_LT (SLit 31) (SOff 10 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_T : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_ (mkAC BC_LT (SLit 31) (SOff 10 0))).
Lemma gs_b3_T : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_ (mkAC BC_LT (SLit 31) (SOff 10 0))) = (ss_b3_T, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_TT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_T (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b3_TT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_T (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b3_TT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_TF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_T (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b3_TF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_T (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b3_TF, RS_stopped (SR_branch BC_NE (SOff 67 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_TFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_TF (mkAC BC_NE (SOff 67 0) (SLit 0))).
Lemma gs_b3_TFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_TF (mkAC BC_NE (SOff 67 0) (SLit 0))) = (ss_b3_TFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_TFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_TF (mkAC BC_EQ (SOff 67 0) (SLit 0))).
Lemma gs_b3_TFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_TF (mkAC BC_EQ (SOff 67 0) (SLit 0))) = (ss_b3_TFF, RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_TFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_TFF (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b3_TFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_TFF (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b3_TFFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_TFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_TFF (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b3_TFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_TFF (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b3_TFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_F : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_ (mkAC BC_GE (SLit 31) (SOff 10 0))).
Lemma gs_b3_F : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_ (mkAC BC_GE (SLit 31) (SOff 10 0))) = (ss_b3_F, RS_stopped (SR_branch BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_FT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_F (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b3_FT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_F (mkAC BC_GEU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b3_FT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_FF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_F (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))).
Lemma gs_b3_FF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_F (mkAC BC_LTU (SOff 56 0) (SAlu ALU_SLL (SOff 61 0) (SLit 2)))) = (ss_b3_FF, RS_stopped (SR_branch BC_NE (SOff 67 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_FFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_FF (mkAC BC_NE (SOff 67 0) (SLit 0))).
Lemma gs_b3_FFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_FF (mkAC BC_NE (SOff 67 0) (SLit 0))) = (ss_b3_FFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_FFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_FF (mkAC BC_EQ (SOff 67 0) (SLit 0))).
Lemma gs_b3_FFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_FF (mkAC BC_EQ (SOff 67 0) (SLit 0))) = (ss_b3_FFF, RS_stopped (SR_branch BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_FFFT : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_FFF (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b3_FFFT : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_FFF (mkAC BC_NE (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b3_FFFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_b3_FFFF : sstate := Eval vm_compute in cnrun_ (add_cond ss_b3_FFF (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))).
Lemma gs_b3_FFFF : sym_run_toN src0segs src0tbl FUEL PS_CN (add_cond ss_b3_FFF (mkAC BC_EQ (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 10 0) (SLit 3)) (SLit 1)) (SAlu ALU_SLTU (SLit 32768) (SOff 62 0))) (SLit 0))) = (ss_b3_FFFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition CN_JUNK : list reg := [25; 10; 19; 15; 16; 17; 5]%bv.
Definition facts_CN : facts := mkFacts ((74%nat, mkAF 1 32 0) :: (75%nat, mkAF 0 (2 ^ 49) 0) :: f_atoms (ss_facts ss_M1)) (f_conds (ss_facts ss_M1)) [].
Definition ss_CN : sstate := Eval vm_compute in setfacts facts_CN (setmem (ss_mem ss_M1) (junk_regs CN_JUNK 74 ss_b1_TT)).
Definition cn_check (ss : sstate) : bool :=
ss_atoms_lt 74 ss && facts_subb (ss_facts ss_M1) (ss_facts ss) && mergeb ss_CN (setfacts facts_CN (junk_regs CN_JUNK 74 ss)).
Lemma ss_CN_pc : ss_pc ss_CN = PS_CN. Proof. reflexivity. Qed.
Lemma cn_b0_TT : cn_check ss_b0_TT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_TFT : cn_check ss_b0_TFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_TFFTT : cn_check ss_b0_TFFTT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_TFFTFT : cn_check ss_b0_TFFTFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_TFFTFF : cn_check ss_b0_TFFTFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_TFFFT : cn_check ss_b0_TFFFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_TFFFFT : cn_check ss_b0_TFFFFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_TFFFFF : cn_check ss_b0_TFFFFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_FT : cn_check ss_b0_FT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_FFT : cn_check ss_b0_FFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_FFFTT : cn_check ss_b0_FFFTT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_FFFTFT : cn_check ss_b0_FFFTFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_FFFTFF : cn_check ss_b0_FFFTFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_FFFFT : cn_check ss_b0_FFFFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_FFFFFT : cn_check ss_b0_FFFFFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b0_FFFFFF : cn_check ss_b0_FFFFFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_TT : cn_check ss_b1_TT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_TFT : cn_check ss_b1_TFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_TFFTT : cn_check ss_b1_TFFTT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_TFFTF : cn_check ss_b1_TFFTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_TFFF : cn_check ss_b1_TFFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_FT : cn_check ss_b1_FT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_FFT : cn_check ss_b1_FFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_FFFTT : cn_check ss_b1_FFFTT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_FFFTF : cn_check ss_b1_FFFTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b1_FFFF : cn_check ss_b1_FFFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_TT : cn_check ss_b2_TT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_TFT : cn_check ss_b2_TFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_TFFTT : cn_check ss_b2_TFFTT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_TFFTF : cn_check ss_b2_TFFTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_TFFF : cn_check ss_b2_TFFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_FT : cn_check ss_b2_FT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_FFT : cn_check ss_b2_FFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_FFFTT : cn_check ss_b2_FFFTT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_FFFTF : cn_check ss_b2_FFFTF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b2_FFFF : cn_check ss_b2_FFFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b3_TT : cn_check ss_b3_TT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b3_TFT : cn_check ss_b3_TFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b3_TFFT : cn_check ss_b3_TFFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b3_TFFF : cn_check ss_b3_TFFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b3_FT : cn_check ss_b3_FT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b3_FFT : cn_check ss_b3_FFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b3_FFFT : cn_check ss_b3_FFFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma cn_b3_FFFF : cn_check ss_b3_FFFF = true. Proof. vm_compute. reflexivity. Qed.
Definition ss_c_ : sstate := Eval vm_compute in mmrun_ ss_CN.
Lemma gs_c_ : sym_run_toN src0segs src0tbl FUEL PS_MM ss_CN = (ss_c_, RS_stopped (SR_branch BC_NE (SOff 67 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_T : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_ (mkAC BC_NE (SOff 67 0) (SLit 0))).
Lemma gs_c_T : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_ (mkAC BC_NE (SOff 67 0) (SLit 0))) = (ss_c_T, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_F : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_ (mkAC BC_EQ (SOff 67 0) (SLit 0))).
Lemma gs_c_F : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_ (mkAC BC_EQ (SOff 67 0) (SLit 0))) = (ss_c_F, RS_stopped (SR_branch BC_LTU (SLit 7) (SOff 74 0))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FT : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_F (mkAC BC_LTU (SLit 7) (SOff 74 0))).
Lemma gs_c_FT : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_F (mkAC BC_LTU (SLit 7) (SOff 74 0))) = (ss_c_FT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FF : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_F (mkAC BC_GEU (SLit 7) (SOff 74 0))).
Lemma gs_c_FF : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_F (mkAC BC_GEU (SLit 7) (SOff 74 0))) = (ss_c_FF, RS_stopped (SR_branch BC_GEU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FFT : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_FF (mkAC BC_GEU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)))).
Lemma gs_c_FFT : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_FF (mkAC BC_GEU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)))) = (ss_c_FFT, RS_stopped (SR_branch BC_LTU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SLit 16384))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FFTT : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_FFT (mkAC BC_LTU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SLit 16384))).
Lemma gs_c_FFTT : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_FFT (mkAC BC_LTU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SLit 16384))) = (ss_c_FFTT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FFTF : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_FFT (mkAC BC_GEU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SLit 16384))).
Lemma gs_c_FFTF : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_FFT (mkAC BC_GEU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SLit 16384))) = (ss_c_FFTF, RS_stopped (SR_branch BC_LTU (SOff 75 0) (SAlu ALU_SLL (SOff 74 0) (SLit 1)))).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FFTFT : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_FFTF (mkAC BC_LTU (SOff 75 0) (SAlu ALU_SLL (SOff 74 0) (SLit 1)))).
Lemma gs_c_FFTFT : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_FFTF (mkAC BC_LTU (SOff 75 0) (SAlu ALU_SLL (SOff 74 0) (SLit 1)))) = (ss_c_FFTFT, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FFTFF : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_FFTF (mkAC BC_GEU (SOff 75 0) (SAlu ALU_SLL (SOff 74 0) (SLit 1)))).
Lemma gs_c_FFTFF : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_FFTF (mkAC BC_GEU (SOff 75 0) (SAlu ALU_SLL (SOff 74 0) (SLit 1)))) = (ss_c_FFTFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition ss_c_FFF : sstate := Eval vm_compute in mmrun_ (add_cond ss_c_FF (mkAC BC_LTU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)))).
Lemma gs_c_FFF : sym_run_toN src0segs src0tbl FUEL PS_MM (add_cond ss_c_FF (mkAC BC_LTU (SAlu ALU_ADD (SAlu ALU_ADD (SOff 11 0) (SAlu ALU_AND (SAlu ALU_SUB (SLit 0) (SOff 11 20)) (SLit 4095))) (SLit 20)) (SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16)))) = (ss_c_FFF, RS_running).
Proof. vm_compute. reflexivity. Qed.
Definition MM_JUNK : list reg := [19; 25; 11; 15; 16]%bv.
Definition facts_MM : facts := mkFacts ((81%nat, mkAF 4096 1048576 12) :: (82%nat, mkAF 1 32 0) :: f_atoms facts_CN) (f_conds facts_CN) [].
Definition ss_MM : sstate := Eval vm_compute in setfacts facts_MM (junk_regs MM_JUNK 81 ss_c_T).
Definition mm_check (ss : sstate) : bool :=
ss_atoms_lt 81 ss && facts_subb (ss_facts ss_M1) (ss_facts ss) && mergeb ss_MM (setfacts facts_MM (junk_regs MM_JUNK 81 ss)).
Lemma ss_MM_pc : ss_pc ss_MM = PS_MM. Proof. reflexivity. Qed.
Lemma mm_c_T : mm_check ss_c_T = true. Proof. vm_compute. reflexivity. Qed.
Lemma mm_c_FT : mm_check ss_c_FT = true. Proof. vm_compute. reflexivity. Qed.
Lemma mm_c_FFTT : mm_check ss_c_FFTT = true. Proof. vm_compute. reflexivity. Qed.
Lemma mm_c_FFTFT : mm_check ss_c_FFTFT = true. Proof. vm_compute. reflexivity. Qed.
Lemma mm_c_FFTFF : mm_check ss_c_FFTFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma mm_c_FFF : mm_check ss_c_FFF = true. Proof. vm_compute. reflexivity. Qed.
Lemma CN_regs : regs_at ss_CN [1; 2; 4; 8; 9; 10; 11; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 41 0; SOff 2 (-144); SLit TP; SOff 10 0; SOff 40 0; SOff 75 0; SLit 4096; SAlu ALU_ADD (SAlu ALU_SLL (SOff 35 0) (SLit 4)) (SLit 16); SOff 67 0; SOff 62 0;
SOff 11 0; SOff 76 0; SLit GUARD; SOff 33 88; SLit LOCK; SOff 33 0; SAlu ALU_SLL (SOff 35 0) (SLit 4); SOff 74 0; SOff 26 0; SOff 27 0].
Proof. vm_compute. reflexivity. Qed.
Lemma MM_regs : regs_at ss_MM [1; 2; 4; 8; 9; 10; 12; 13; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv =
[SOff 41 0; SOff 2 (-144); SLit TP; SOff 10 0; SOff 40 0; SLit 0; SLit 3; SLit 34; SLit 18446744073709551615;
SLit 18446744073709551615; SOff 81 0; SLit GUARD; SOff 33 88; SLit LOCK; SOff 33 0; SAlu ALU_SLL (SOff 35 0) (SLit 4); SOff 82 0; SOff 26 0; SOff 27 0].
Proof. vm_compute. reflexivity. Qed.
End a.
