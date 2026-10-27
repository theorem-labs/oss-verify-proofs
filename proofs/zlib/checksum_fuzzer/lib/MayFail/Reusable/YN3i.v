(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3i.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN32.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_lit : forall (p : word) (w : bv 32),
clookup src0tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word src0segs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply src0tbl_ok. exact H.
Qed.
End e.
Ltac ftac := apply fetch_lit; vm_compute; reflexivity.
Ltac stepiv' F D vv tac := let F' := litF F in stepiv F' D vv tac.
Ltac stepi' F D := let F' := litF F in stepi F' D.
Ltac exact_lit F := let F' := litF F in exact F'.
Ltac rodc :=
let v1 := eval cbv in src0_D_const_HIGHS_0x8080808080808080 in
let v2 := eval cbv in src0_D_const_ONES_0x0101010101010100 in
let H1 := fresh "HrodH" in let H2 := fresh "HrodO" in
assert (H1 : src0_D_const_HIGHS_0x8080808080808080 = v1) by reflexivity;
assert (H2 : src0_D_const_ONES_0x0101010101010100 = v2) by reflexivity.
Ltac msteps_done :=
lazymatch goal with
| |- msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
first [ apply mst_refl
| replace q with p by (symmetry; bveq); apply mst_refl ]
end.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma FM_000 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x0)) = Some (0x0ff5f593%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_000 : decode_any (0x0ff5f593%bv : bv 32) = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_004 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x4)) = Some (0x00757693%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_004 : decode_any (0x00757693%bv : bv 32) = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_008 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x8)) = Some (0x00c03733%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_008 : decode_any (0x00c03733%bv : bv 32) = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_00c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xc)) = Some (0x02068c63%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_00c : decode_any (0x02068c63%bv : bv 32) = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_010 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x10)) = Some (0x02060a63%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_010 : decode_any (0x02060a63%bv : bv 32) = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_014 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x14)) = Some (0x00150793%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_014 : decode_any (0x00150793%bv : bv 32) = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_018 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x18)) = Some (0x00100813%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_018 : decode_any (0x00100813%bv : bv 32) = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_01c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x1c)) = Some (0x00054703%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_01c : decode_any (0x00054703%bv : bv 32) = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_020 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x20)) = Some (0x00060693%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_020 : decode_any (0x00060693%bv : bv 32) = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_024 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x24)) = Some (0x06b70e63%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_024 : decode_any (0x06b70e63%bv : bv 32) = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_028 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x28)) = Some (0x00150513%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_028 : decode_any (0x00150513%bv : bv 32) = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_02c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x2c)) = Some (0xfff68613%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_02c : decode_any (0xfff68613%bv : bv 32) = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_030 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x30)) = Some (0x0077f893%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_030 : decode_any (0x0077f893%bv : bv 32) = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_034 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x34)) = Some (0x00c03733%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_034 : decode_any (0x00c03733%bv : bv 32) = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_038 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x38)) = Some (0x00088663%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_038 : decode_any (0x00088663%bv : bv 32) = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_03c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x3c)) = Some (0x00178793%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_03c : decode_any (0x00178793%bv : bv 32) = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_040 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x40)) = Some (0xfd069ee3%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_040 : decode_any (0xfd069ee3%bv : bv 32) = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_044 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x44)) = Some (0x06070863%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_044 : decode_any (0x06070863%bv : bv 32) = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_048 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x48)) = Some (0x00054683%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_048 : decode_any (0x00054683%bv : bv 32) = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_04c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x4c)) = Some (0x04b68663%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_04c : decode_any (0x04b68663%bv : bv 32) = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_050 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x50)) = Some (0x00800693%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_050 : decode_any (0x00800693%bv : bv 32) = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_054 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x54)) = Some (0x04d66263%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_054 : decode_any (0x04d66263%bv : bv 32) = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_068 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x68)) = Some (0x00168793%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_068 : decode_any (0x00168793%bv : bv 32) = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_06c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x6c)) = Some (0x02f587b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_06c : decode_any (0x02f587b3%bv : bv 32) = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_070 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x70)) = Some (0x00700813%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_070 : decode_any (0x00700813%bv : bv 32) = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_074 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x74)) = Some (0x00053883%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_074 : decode_any (0x00053883%bv : bv 32) = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_078 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x78)) = Some (0x00f8c8b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_078 : decode_any (0x00f8c8b3%bv : bv 32) = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_07c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x7c)) = Some (0x411682b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_07c : decode_any (0x411682b3%bv : bv 32) = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_080 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x80)) = Some (0x0112e8b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_080 : decode_any (0x0112e8b3%bv : bv 32) = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_084 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x84)) = Some (0x00e8f8b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_084 : decode_any (0x00e8f8b3%bv : bv 32) = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_088 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x88)) = Some (0x02e89a63%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_088 : decode_any (0x02e89a63%bv : bv 32) = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_08c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x8c)) = Some (0xff860613%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_08c : decode_any (0xff860613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_090 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x90)) = Some (0x00850513%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_090 : decode_any (0x00850513%bv : bv 32) = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_094 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x94)) = Some (0xfec860e3%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_094 : decode_any (0xfec860e3%bv : bv 32) = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_098 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x98)) = Some (0x00060693%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_098 : decode_any (0x00060693%bv : bv 32) = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_09c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x9c)) = Some (0x00060c63%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_09c : decode_any (0x00060c63%bv : bv 32) = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0a0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xa0)) = Some (0x00054603%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0a0 : decode_any (0x00054603%bv : bv 32) = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0a4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xa4)) = Some (0x00b60a63%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0a4 : decode_any (0x00b60a63%bv : bv 32) = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0a8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xa8)) = Some (0xfff68693%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0a8 : decode_any (0xfff68693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0ac : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xac)) = Some (0x00150513%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0ac : decode_any (0x00150513%bv : bv 32) = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0b0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xb0)) = Some (0xfe0698e3%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0b0 : decode_any (0xfe0698e3%bv : bv 32) = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0b4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xb4)) = Some (0x00000513%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0b4 : decode_any (0x00000513%bv : bv 32) = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0b8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xb8)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0b8 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0bc : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xbc)) = Some (0x00060693%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0bc : decode_any (0x00060693%bv : bv 32) = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0c0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xc0)) = Some (0x00054603%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0c0 : decode_any (0x00054603%bv : bv 32) = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0c4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xc4)) = Some (0xfeb612e3%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0c4 : decode_any (0xfeb612e3%bv : bv 32) = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_0c8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0xc8)) = Some (0xff1ff06f%bv : bv 32).
Proof. ftac. Qed.
Lemma DM_0c8 : decode_any (0xff1ff06f%bv : bv 32) = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl_bv. Qed.
Definition tblw (t : ctable) (pc : Z) : Z := match clookup t pc with Some w => w | None => 0 end.
Definition auipc_imm20 (w : Z) : Z :=
match decode_any (Z_to_bv 32 w) with Some (Auipc _ imm, _) => bv_unsigned imm | _ => 0 end.
Definition ld_imm12 (w : Z) : Z :=
match decode_any (Z_to_bv 32 w) with Some (Load _ _ _ _ imm, _) => bv_unsigned imm | _ => 0 end.
Definition src0_memchr_w058 : Z := Eval vm_compute in tblw src0tbl (src0_A_memchr + 0x58).
Definition src0_memchr_w05c : Z := Eval vm_compute in tblw src0tbl (src0_A_memchr + 0x5c).
Definition src0_memchr_w060 : Z := Eval vm_compute in tblw src0tbl (src0_A_memchr + 0x60).
Definition src0_memchr_w064 : Z := Eval vm_compute in tblw src0tbl (src0_A_memchr + 0x64).
Definition src0_memchr_i058 : Z := Eval vm_compute in auipc_imm20 src0_memchr_w058.
Definition src0_memchr_i05c : Z := Eval vm_compute in ld_imm12 src0_memchr_w05c.
Definition src0_memchr_i060 : Z := Eval vm_compute in auipc_imm20 src0_memchr_w060.
Definition src0_memchr_i064 : Z := Eval vm_compute in ld_imm12 src0_memchr_w064.
Definition src0_memchr_aui1 : Z := Eval vm_compute in
bv_unsigned (v_auipc (Z_to_bv 64 (src0_A_memchr + 0x58)) (Z.shiftl (bv_signed (Z_to_bv 20 src0_memchr_i058)) 12)).
Definition src0_memchr_aui2 : Z := Eval vm_compute in
bv_unsigned (v_auipc (Z_to_bv 64 (src0_A_memchr + 0x60)) (Z.shiftl (bv_signed (Z_to_bv 20 src0_memchr_i060)) 12)).
Lemma FM_058 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x58)) = Some (Z_to_bv 32 src0_memchr_w058).
Proof. ftac. Qed.
Lemma DM_058 : decode_any (Z_to_bv 32 src0_memchr_w058) = Some (Auipc 13 (Z_to_bv 20 src0_memchr_i058), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_05c : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x5c)) = Some (Z_to_bv 32 src0_memchr_w05c).
Proof. ftac. Qed.
Lemma DM_05c : decode_any (Z_to_bv 32 src0_memchr_w05c) = Some (Load SZ8 true 13 13 (Z_to_bv 12 src0_memchr_i05c), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_060 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x60)) = Some (Z_to_bv 32 src0_memchr_w060).
Proof. ftac. Qed.
Lemma DM_060 : decode_any (Z_to_bv 32 src0_memchr_w060) = Some (Auipc 14 (Z_to_bv 20 src0_memchr_i060), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FM_064 : fetch_word src0segs (Z_to_bv 64 (src0_A_memchr + 0x64)) = Some (Z_to_bv 32 src0_memchr_w064).
Proof. ftac. Qed.
Lemma DM_064 : decode_any (Z_to_bv 32 src0_memchr_w064) = Some (Load SZ8 true 14 14 (Z_to_bv 12 src0_memchr_i064), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma src0_memchr_ld_targets :
bv_unsigned (v_addi (Z_to_bv 64 src0_memchr_aui1) (bv_signed (Z_to_bv 12 src0_memchr_i05c))) = src0_D_const_ONES_0x0101010101010100 /\
bv_unsigned (v_addi (Z_to_bv 64 src0_memchr_aui2) (bv_signed (Z_to_bv 12 src0_memchr_i064))) = src0_D_const_HIGHS_0x8080808080808080.
Proof. vm_compute. split; reflexivity. Qed.
Lemma FS_000 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x0)) = Some (0xfe010113%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_000 : decode_any (0xfe010113%bv : bv 32) = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_004 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x4)) = Some (0x00113c23%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_004 : decode_any (0x00113c23%bv : bv 32) = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_008 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x8)) = Some (0x00813823%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_008 : decode_any (0x00813823%bv : bv 32) = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_00c : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0xc)) = Some (0x00913423%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_00c : decode_any (0x00913423%bv : bv 32) = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_010 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x10)) = Some (0x00058413%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_010 : decode_any (0x00058413%bv : bv 32) = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_014 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x14)) = Some (0x00050493%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_014 : decode_any (0x00050493%bv : bv 32) = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_018 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x18)) = Some (0x00000593%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_018 : decode_any (0x00000593%bv : bv 32) = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_01c : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x1c)) = Some (0x00040613%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_01c : decode_any (0x00040613%bv : bv 32) = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_020 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x20)) = Some (0x024000ef%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_020 : decode_any (0x024000ef%bv : bv 32) = Some (Jal 1 36, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_024 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x24)) = Some (0x00050463%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_024 : decode_any (0x00050463%bv : bv 32) = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_028 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x28)) = Some (0x40950433%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_028 : decode_any (0x40950433%bv : bv 32) = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_02c : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x2c)) = Some (0x00040513%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_02c : decode_any (0x00040513%bv : bv 32) = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_030 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x30)) = Some (0x01813083%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_030 : decode_any (0x01813083%bv : bv 32) = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_034 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x34)) = Some (0x01013403%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_034 : decode_any (0x01013403%bv : bv 32) = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_038 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x38)) = Some (0x00813483%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_038 : decode_any (0x00813483%bv : bv 32) = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_03c : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x3c)) = Some (0x02010113%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_03c : decode_any (0x02010113%bv : bv 32) = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FS_040 : fetch_word src0segs (Z_to_bv 64 (src0_A_strnlen + 0x40)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma DS_040 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma bv_eqb_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.
Lemma nth_app_nul_in : forall (s : list byte) j, (j < length s)%nat -> In (nth j (s ++ [NUL]) NUL) s.
Proof. intros s j Hj. rewrite app_nth1 by lia. apply nth_In. lia. Qed.
Lemma nth_app_nul_last : forall s : list byte, nth (length s) (s ++ [NUL]) NUL = NUL.
Proof. intros s. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma rdn_total : forall segs mem n (a : word),
(forall k, (k < n)%nat -> rdn segs mem (a + nat_to_word k) 1 <> None) ->
exists bs, rdn segs mem a n = Some bs.
Proof.
intros segs mem n. induction n as [|n IH]; intros a Hk.
- exists []. reflexivity.
- pose proof (Hk 0%nat ltac:(lia)) as H0. rewrite word_add_nat_0 in H0.
cbn [rdn] in H0 |- *.
destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|exfalso; apply H0; reflexivity].
destruct (IH (a + 1)%bv) as [bs Hbs].
{ intros k Hk'. replace (a + 1 + nat_to_word k)%bv with (a + nat_to_word (S k))%bv
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply Hk. lia. }
rewrite Hbs. eexists. reflexivity.
Qed.
Lemma rdn_ext1 : forall segs n m1 m2 (a : word),
(forall k, (k < n)%nat -> rdn segs m1 (a + nat_to_word k) 1 = rdn segs m2 (a + nat_to_word k) 1) ->
rdn segs m1 a n = rdn segs m2 a n.
Proof.
intros segs n. induction n as [|n IH]; intros m1 m2 a Hk; [reflexivity|].
pose proof (Hk 0%nat ltac:(lia)) as H0. rewrite word_add_nat_0 in H0.
cbn [rdn] in H0 |- *.
destruct (match m1 a with Some b => Some b | None => seg_rom segs a end) as [b1|];
destruct (match m2 a with Some b => Some b | None => seg_rom segs a end) as [b2|];
try discriminate H0.
- injection H0 as ->. rewrite (IH m1 m2 (a + 1)%bv); [reflexivity|].
intros k Hk'. replace (a + 1 + nat_to_word k)%bv with (a + nat_to_word (S k))%bv
by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
apply Hk. lia.
- reflexivity.
Qed.
Lemma rom_reads_of_None : forall segs (mem : word -> option byte) (lo hi : Z),
(forall a : word, lo <= bv_unsigned a < hi -> mem a = None) ->
forall a : Z, 0 <= lo -> hi <= 2^64 -> lo <= a < hi ->
rdn segs mem (Z_to_bv 64 a) 1 = rdn segs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Proof.
intros segs mem lo hi Hnone a Hlo Hhi Ha. cbn [rdn].
rewrite Hnone by (rewrite u_Z2bv by lia; lia). reflexivity.
Qed.
Definition C1 : Z := 72340172838076672.
Lemma ALLONES_ones : HZ.ALLONES = Z.ones 64.
Proof. reflexivity. Qed.
Lemma sub_C1_lxor : forall x, 0 <= x < 2^64 ->
(C1 - x) mod 2^64 = Z.lxor ((x + HZ.ONESNEG) mod 2^64) HZ.ALLONES.
Proof.
intros x Hx.
set (y := (x + HZ.ONESNEG) mod 2^64).
assert (Hy : 0 <= y < 2^64) by (subst y; apply Z.mod_pos_bound; lia).
assert (E1 : (C1 - x) mod 2^64 = 2^64 - 1 - y).
{ subst y. unfold C1, HZ.ONESNEG.
destruct (Z_lt_dec (x + 18374403900871474943) (2^64)) as [Hl|Hg].
- rewrite (Z.mod_small (x + _)) by lia.
symmetry. apply Z.mod_unique_pos with (q := 0); lia.
- replace ((x + 18374403900871474943) mod 2^64) with (x + 18374403900871474943 - 2^64)
by (apply Z.mod_unique_pos with (q := 1); lia).
symmetry. apply Z.mod_unique_pos with (q := -1); lia. }
rewrite E1. apply Z.bits_inj'. intros i Hi.
rewrite Z.lxor_spec, ALLONES_ones, Z.testbit_ones_nonneg by lia.
replace (2 ^ 64 - 1 - y) with ((Z.lnot y) mod 2^64).
2:{ unfold Z.lnot. rewrite <- (Z.mod_add (Z.pred (-y)) 1 (2^64)) by lia.
rewrite Z.mod_small by lia. lia. }
rewrite Z.testbit_mod_pow2, Z.lnot_spec by lia.
destruct (i <? 64) eqn:Ei; cbn [andb].
- destruct (Z.testbit y i); reflexivity.
- rewrite (Z_testbit_high 64 y i); [reflexivity|lia|lia|apply Z.ltb_ge in Ei; lia].
Qed.
Lemma haszero_ref_Z : forall x, 0 <= x < 2^64 ->
Z.land (Z.lor ((C1 - x) mod 2^64) x) HZ.HIGHS = HZ.HIGHS - HZ.Tz x.
Proof.
intros x Hx. rewrite sub_C1_lxor by exact Hx.
set (y := (x + HZ.ONESNEG) mod 2^64).
assert (Hy : 0 <= y < 2^64) by (subst y; apply Z.mod_pos_bound; lia).
unfold HZ.Tz. fold y.
set (U := Z.land (Z.lor (Z.lxor y HZ.ALLONES) x) HZ.HIGHS).
set (T := Z.land (Z.land y (Z.lxor x HZ.ALLONES)) HZ.HIGHS).
assert (Hdisj : Z.land U T = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.bits_0. subst U T.
rewrite ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec, ?Z.lxor_spec.
rewrite ALLONES_ones, Z.testbit_ones_nonneg by lia.
destruct (i <? 64) eqn:Ei.
- destruct (Z.testbit y i), (Z.testbit x i), (Z.testbit HZ.HIGHS i); reflexivity.
- apply Z.ltb_ge in Ei.
rewrite (Z_testbit_high 64 y i), (Z_testbit_high 64 x i) by lia. reflexivity. }
assert (Hunion : Z.lor U T = HZ.HIGHS).
{ apply Z.bits_inj'. intros i Hi. subst U T.
rewrite ?Z.lor_spec, ?Z.land_spec, ?Z.lor_spec, ?Z.lxor_spec, ?Z.land_spec, ?Z.lxor_spec.
rewrite ALLONES_ones, Z.testbit_ones_nonneg by lia.
destruct (i <? 64) eqn:Ei.
- destruct (Z.testbit y i), (Z.testbit x i), (Z.testbit HZ.HIGHS i); reflexivity.
- apply Z.ltb_ge in Ei.
rewrite (Z_testbit_high 64 HZ.HIGHS i) by (unfold HZ.HIGHS; lia).
rewrite !andb_false_r. reflexivity. }
pose proof (Z.add_nocarry_lxor U T Hdisj) as Hsum.
rewrite (Z.lxor_lor U T Hdisj), Hunion in Hsum. lia.
Qed.
Lemma haszero_ref : forall v : word,
bv_unsigned (v_and (v_or (v_sub (Z_to_bv 64 C1) v) v) (Z_to_bv 64 HZ.HIGHS))
= HZ.HIGHS - HZ.Tz (bv_unsigned v).
Proof.
intros v. pose proof (u64_range v) as Hv.
pose proof (HZ.Tz_range (bv_unsigned v)) as HT.
unfold v_and, v_or, v_sub.
rewrite (u_Z2bv C1) by (unfold C1; lia).
rewrite (u_Z2bv HZ.HIGHS) by (unfold HZ.HIGHS; lia).
rewrite (Z_to_bv_unsigned 64 (C1 - _)), bv_wrap64_mod.
assert (H1 : 0 <= (C1 - bv_unsigned v) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
assert (H2 : 0 <= Z.lor ((C1 - bv_unsigned v) mod 2 ^ 64) (bv_unsigned v) < 2^64)
by (apply Z_lor_range; lia).
rewrite (u_Z2bv (Z.lor _ _)) by lia.
rewrite u_Z2bv.
- apply haszero_ref_Z. exact Hv.
- apply Z.land_nonneg. right. unfold HZ.HIGHS. lia.
- pose proof (HZ.land_le_r (Z.lor ((C1 - bv_unsigned v) mod 2 ^ 64) (bv_unsigned v)) HZ.HIGHS ltac:(unfold HZ.HIGHS; lia)).
unfold HZ.HIGHS in *. lia.
Qed.
Lemma step_op_at : forall segs regs pc mem rom w op rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
alu64 op (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_op_gen segs regs pc mem rom w op rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
End f.
Ltac stepov F0 D vv tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_op_at with (v := vv);
[ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Ltac steplbu F0 D tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Ltac stepbt F0 D tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_branch_tk_gen; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Ltac stepbf F0 D tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_branch_ft_gen; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Ltac stepret F0 D := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_jalr_x0; [ exact F | reflexivity | exact D | gr; reflexivity ]
| step_simpl; imm_norm ].
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma u_lit0 : bv_unsigned (Z_to_bv 64 0) = 0.
Proof. reflexivity. Qed.
Lemma eqb_w_true : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a = b ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = true.
Proof. intros a b Ha Hb Hab. unfold bv_eqb. rewrite !u_Z2bv by lia. apply Z.eqb_eq. exact Hab. Qed.
Lemma eqb_w_false : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> a <> b ->
bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof. intros a b Ha Hb Hab. unfold bv_eqb. rewrite !u_Z2bv by lia. apply Z.eqb_neq. exact Hab. Qed.
Lemma ltu_w : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z.ltb a b.
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.
Section h.
Variable s : list byte.
Variable p : word.
Variable n : word.
Variable mem rom : word -> option byte.
Definition P : Z := bv_unsigned p.
Definition L : Z := Z.of_nat (length s).
Definition E : Z := P + L.
Definition N : Z := bv_unsigned n.
Hypothesis Hnul : ~ In NUL s.
Hypothesis Hfit : bv_unsigned p + Z.of_nat (length s) + 8 < 2^64.
Hypothesis Hn : Z.of_nat (length s) + 8 <= bv_unsigned n.
Hypothesis Hstr : forall j, (j <= length s)%nat ->
rdn src0segs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Lemma E_eq : E = bv_unsigned p + Z.of_nat (length s). Proof. reflexivity. Qed.
Lemma P_eq : P = bv_unsigned p. Proof. reflexivity. Qed.
Lemma L_eq : L = Z.of_nat (length s). Proof. reflexivity. Qed.
Ltac epl := pose proof E_eq; pose proof P_eq; pose proof L_eq; pose proof (u64_range p).
Lemma str_byte_nz : forall j, (j < length s)%nat -> nth j (s ++ [NUL]) NUL <> NUL.
Proof. intros j Hj Hc. apply Hnul. rewrite <- Hc. apply nth_app_nul_in. exact Hj. Qed.
Lemma mc_tail : forall d regs (c : Z),
(d <= length s)%nat ->
getr regs 10 = Z_to_bv 64 (E - Z.of_nat d) ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 13 = Z_to_bv 64 c ->
Z.of_nat d < c -> c < 2^64 ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0xa0)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 E
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 13 = Z_to_bv 64 (c - Z.of_nat d)
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr regs r).
Proof.
unfold E, P, L.
induction d as [|d IH]; intros regs c Hd H10 H11 H13 Hdc Hc.
- pose proof (u64_range p) as Hp.
eexists. split.
+ norm_pc.
chain_step; [reflexivity| | ].
{ eapply step_lbu; [exact_lit FM_0a0 | reflexivity | exact DM_0a0 | ].
rewrite H10. imm_norm. rewrite v_addi_0.
replace (bv_unsigned p + Z.of_nat (length s) - Z.of_nat 0) with (bv_unsigned p + Z.of_nat (length s)) by lia.
apply (Hstr (length s)). lia. }
step_simpl. rewrite nth_app_nul_last.
chain_step; [reflexivity| | ].
{ eapply step_branch_tk_gen; [exact_lit FM_0a4 | reflexivity | exact DM_0a4 | ].
gr. rewrite H11. vm_compute. reflexivity. }
step_simpl.
chain_step; [reflexivity| | ].
{ eapply step_jalr_x0; [exact_lit FM_0b8 | reflexivity | exact DM_0b8 | ].
gr. reflexivity. }
step_simpl. imm_norm. msteps_done.
+ split; [gr; rewrite H10; f_equal; lia|].
split; [gr; reflexivity|].
split; [gr; rewrite H13; f_equal; lia|].
intros r Hr10 Hr12 Hr13. rewrite !getr_other by assumption. reflexivity.
- pose proof (u64_range p) as Hp.
set (b := nth (length s - S d) (s ++ [NUL]) NUL).
assert (Hb : b <> NUL) by (apply str_byte_nz; lia).
set (regs1 := regupd (regupd (regupd regs 12 (Z_to_bv 64 (bv_unsigned b)))
13 (Z_to_bv 64 (c - 1))) 10 (Z_to_bv 64 (bv_unsigned p + Z.of_nat (length s) - Z.of_nat d))).
destruct (IH regs1 (c - 1)) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. exact H11. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
chain_step; [reflexivity| | ].
{ eapply step_lbu; [exact_lit FM_0a0 | reflexivity | exact DM_0a0 | ].
rewrite H10. imm_norm. rewrite v_addi_0.
replace (bv_unsigned p + Z.of_nat (length s) - Z.of_nat (S d)) with (bv_unsigned p + Z.of_nat (length s - S d)) by lia.
apply Hstr. lia. }
step_simpl. fold b.
chain_step; [reflexivity| | ].
{ eapply step_branch_ft_gen; [exact_lit FM_0a4 | reflexivity | exact DM_0a4 | ].
gr. rewrite H11. cbn [branch_taken]. unfold bv_eqb. rewrite u_zext8.
change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. apply byte_nz_u. exact Hb. }
step_simpl.
stepiv' FM_0a8 DM_0a8 (Z_to_bv 64 (c - 1))
ltac:(gr; rewrite H13; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; reflexivity).
stepiv' FM_0ac DM_0ac (Z_to_bv 64 (bv_unsigned p + Z.of_nat (length s) - Z.of_nat d))
ltac:(gr; rewrite H10; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
chain_step; [reflexivity| | ].
{ eapply step_branch_tk_gen; [exact_lit FM_0b0 | reflexivity | exact DM_0b0 | ].
gr. cbn [branch_taken]. apply negb_true_iff. unfold bv_eqb.
rewrite u_Z2bv by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. apply Z.eqb_neq. lia. }
step_simpl. subst regs1. msteps_done.
+ split; [exact H10'|]. split; [exact H12'|]. split; [rewrite H13'; f_equal; lia|].
intros r Hr10 Hr12 Hr13. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Hypothesis Hrd : forall a : Z,
bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn src0segs mem (Z_to_bv 64 a) 1 <> None.
Lemma mc_found : forall regs (c : Z),
E mod 8 <= L ->
getr regs 10 = Z_to_bv 64 (E - E mod 8) ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = Z_to_bv 64 c ->
E mod 8 < c -> c < 2^64 ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0xbc)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 E
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 13 = Z_to_bv 64 (c - E mod 8)
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr regs r).
Proof.
intros regs c HrL H10 H11 H12 Hrc Hc.
pose proof (u64_range p) as Hp.
assert (Hr : 0 <= E mod 8 < 8) by (apply Z.mod_pos_bound; lia).
unfold E, P, L in *.
set (r := Z.to_nat ((bv_unsigned p + Z.of_nat (length s)) mod 8)).
assert (HrZ : Z.of_nat r = (bv_unsigned p + Z.of_nat (length s)) mod 8) by (subst r; lia).
rewrite <- HrZ in *.
set (b := nth (length s - r) (s ++ [NUL]) NUL).
set (regs1 := regupd (regupd regs 13 (Z_to_bv 64 c)) 12 (Z_to_bv 64 (bv_unsigned b))).
assert (Hpre : msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0xbc)) mem rom)
(mkst regs1 (Z_to_bv 64 (src0_A_memchr + 0xc4)) mem rom)).
{ norm_pc.
stepiv' FM_0bc DM_0bc (Z_to_bv 64 c) ltac:(gr; rewrite H12; imm_norm; apply v_addi_0).
steplbu FM_0c0 DM_0c0
ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0;
replace (bv_unsigned p + Z.of_nat (length s) - Z.of_nat r) with (bv_unsigned p + Z.of_nat (length s - r)) by lia;
apply Hstr; lia).
subst regs1 b. msteps_done. }
destruct (Nat.eq_dec r 0) as [Hr0|Hr0].
-
assert (Hb : b = NUL) by (subst b; rewrite Hr0, Nat.sub_0_r; apply nth_app_nul_last).
eexists. split.
+ eapply msteps_trans; [exact Hpre|]. norm_pc.
stepbf FM_0c4 DM_0c4 ltac:(subst regs1; gr; rewrite H11, Hb; vm_compute; reflexivity).
stepj' FM_0c8 DM_0c8.
replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
+ subst regs1. split; [gr; rewrite H10; f_equal; lia|]. split; [gr; rewrite Hb; reflexivity|].
split; [gr; f_equal; lia|].
intros x Hx10 Hx12 Hx13. rewrite !getr_other by assumption. reflexivity.
-
assert (Hb : b <> NUL) by (apply str_byte_nz; lia).
set (regs2 := regupd (regupd regs1 13 (Z_to_bv 64 (c - 1))) 10
(Z_to_bv 64 (bv_unsigned p + Z.of_nat (length s) - Z.of_nat (r - 1)))).
destruct (mc_tail (r - 1) regs2 (c - 1)) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
{ subst regs2 regs1. gr. unfold E, P, L. reflexivity. }
{ subst regs2 regs1. gr. exact H11. }
{ subst regs2 regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_0c4 DM_0c4
ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
stepiv' FM_0a8 DM_0a8 (Z_to_bv 64 (c - 1))
ltac:(subst regs1; gr; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; reflexivity).
stepiv' FM_0ac DM_0ac (Z_to_bv 64 (bv_unsigned p + Z.of_nat (length s) - Z.of_nat (r - 1)))
ltac:(subst regs1; gr; rewrite H10; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepbt FM_0b0 DM_0b0
ltac:(gr; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
rewrite u_Z2bv, u_lit0 by lia; apply Z.eqb_neq; lia).
subst regs2 regs1. msteps_done.
+ split; [exact H10'|]. split; [exact H12'|]. split; [rewrite H13'; f_equal; lia|].
intros x Hx10 Hx12 Hx13. rewrite (Hfr x Hx10 Hx12 Hx13). subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma word_at : forall w, P <= w -> w + 8 <= E - E mod 8 + 8 ->
exists bs, rdn src0segs mem (Z_to_bv 64 w) 8 = Some bs /\ length bs = 8%nat /\
(forall i, (i < 8)%nat -> w + Z.of_nat i <= E ->
nth i bs NUL = nth (Z.to_nat (w - P) + i) (s ++ [NUL]) NUL).
Proof.
intros w Hlo Hhi. unfold E, P, L in *.
pose proof (u64_range p) as Hp.
assert (Hm : 0 <= bv_unsigned p mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hm2 : 0 <= (bv_unsigned p + Z.of_nat (length s)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
destruct (rdn_total src0segs mem 8 (Z_to_bv 64 w)) as [bs Hbs].
{ intros k Hk. rewrite word_add_nat, u_Z2bv by lia.
destruct (Z_lt_le_dec (bv_unsigned p + Z.of_nat (length s)) (w + Z.of_nat k)) as [Hpast|Hin].
- apply Hrd. lia.
- replace (w + Z.of_nat k) with (bv_unsigned p + Z.of_nat (Z.to_nat (w - bv_unsigned p) + k)) by lia.
rewrite Hstr by lia. discriminate. }
exists bs. split; [exact Hbs|]. split; [exact (rdn_length _ _ _ _ _ Hbs)|].
intros i Hi HiE.
pose proof (rdn_nth src0segs mem 8 (Z_to_bv 64 w) bs i Hbs ltac:(lia)) as H1.
rewrite word_add_nat, u_Z2bv in H1 by lia.
pose proof (Hstr (Z.to_nat (w - bv_unsigned p) + i)%nat ltac:(lia)) as H2.
replace (bv_unsigned p + Z.of_nat (Z.to_nat (w - bv_unsigned p) + i)) with (w + Z.of_nat i) in H2 by lia.
rewrite H1 in H2. injection H2 as H3. exact H3.
Qed.
Lemma v_xor_0 : forall v : word, v_xor v (Z_to_bv 64 0) = v.
Proof. intros v. unfold v_xor. rewrite u_lit0, Z.lxor_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma mc_words : forall k regs (w c : Z),
w + 8 * Z.of_nat k = E - E mod 8 ->
P <= w ->
getr regs 10 = Z_to_bv 64 w ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = Z_to_bv 64 c ->
getr regs 13 = Z_to_bv 64 C1 ->
getr regs 14 = Z_to_bv 64 HZ.HIGHS ->
getr regs 15 = Z_to_bv 64 0 ->
getr regs 16 = Z_to_bv 64 7 ->
8 * Z.of_nat k + 8 <= c -> c < 2^64 ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0x74)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 E
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 13 = Z_to_bv 64 (c - (E - w))
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 17%bv ->
getr regs' r = getr regs r).
Proof.
induction k as [|k IH]; intros regs w c Hk Hpw H10 H11 H12 H13 H14 H15 H16 Hkc Hc.
all: epl.
all: assert (Hm2 : 0 <= E mod 8 < 8) by (apply Z.mod_pos_bound; lia).
all: assert (HmE : E mod 8 <= E) by (apply Z.mod_le; lia).
all: destruct (word_at w) as (bs & Hbs & Hlen & Hnth); [lia|lia|].
all: set (x := bytes_le_to_Z bs).
all: pose proof (bytes_le_to_Z_range bs Hlen) as Hx; fold x in Hx.
all: set (v := Z_to_bv 64 x).
all: assert (Hv : bv_unsigned v = x) by (subst v; apply u_Z2bv; lia).
all: set (tw := v_and (v_or (v_sub (Z_to_bv 64 C1) v) v) (Z_to_bv 64 HZ.HIGHS)).
all: set (regs5 := regupd (regupd (regupd (regupd (regupd regs 17 v) 17 v) 5 (v_sub (Z_to_bv 64 C1) v))
17 (v_or (v_sub (Z_to_bv 64 C1) v) v)) 17 tw).
all: assert (Hpre : msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0x74)) mem rom)
(mkst regs5 (Z_to_bv 64 (src0_A_memchr + 0x88)) mem rom)).
1,3: norm_pc;
(chain_step; [reflexivity | eapply step_ld with (bs := bs) (v := v);
[exact_lit FM_074 | reflexivity | exact DM_074
| rewrite H10; imm_norm; rewrite v_addi_0; exact Hbs
| rewrite Hv; reflexivity ] | step_simpl ]);
stepov FM_078 DM_078 v ltac:(rewrite alu_xor; gr; rewrite H15; apply v_xor_0);
stepov FM_07c DM_07c (v_sub (Z_to_bv 64 C1) v) ltac:(rewrite alu_sub; gr; rewrite H13; reflexivity);
stepov FM_080 DM_080 (v_or (v_sub (Z_to_bv 64 C1) v) v) ltac:(rewrite alu_or; gr; reflexivity);
stepov FM_084 DM_084 tw ltac:(rewrite alu_and; gr; rewrite H14; reflexivity);
subst regs5; msteps_done.
all: assert (Htw : bv_unsigned tw = HZ.HIGHS - HZ.Tz x) by (subst tw; rewrite haszero_ref, Hv; reflexivity).
all: pose proof (HZ.Tz_range x) as HT.
-
assert (Hw : w = E - E mod 8) by lia.
assert (HTnz : HZ.Tz x <> 0).
{ apply (HZ.Tz_haszero x (Z.to_nat (E mod 8))); [lia|lia| |].
- subst x. rewrite zb_of_bytes by lia. fold NUL. rewrite Hnth by lia.
replace (Z.to_nat (w - P) + Z.to_nat (E mod 8))%nat with (length s) by lia.
rewrite nth_app_nul_last. reflexivity.
- intros j Hj. subst x. rewrite zb_of_bytes by lia. fold NUL. rewrite Hnth by lia.
apply byte_nz_u. apply str_byte_nz. lia. }
destruct (mc_found regs5 c) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
{ subst regs5. gr. rewrite H10. f_equal. lia. }
{ subst regs5. gr. exact H11. }
{ subst regs5. gr. exact H12. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs5 1) by (subst regs5; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_088 DM_088
ltac:(subst regs5; gr; rewrite H14; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
rewrite Htw, u_Z2bv by (unfold HZ.HIGHS; lia); apply Z.eqb_neq; lia).
msteps_done.
+ split; [exact H10'|]. split; [exact H12'|]. split; [rewrite H13'; f_equal; lia|].
intros r Hr5 Hr10 Hr12 Hr13 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs5.
rewrite !getr_other by assumption. reflexivity.
-
assert (HTz : HZ.Tz x = 0).
{ apply HZ.Tz_nozero; [lia|]. intros i Hi. subst x. rewrite zb_of_bytes by lia. fold NUL.
rewrite Hnth by lia. apply byte_nz_u. apply str_byte_nz. lia. }
set (regs7 := regupd (regupd regs5 12 (Z_to_bv 64 (c - 8))) 10 (Z_to_bv 64 (w + 8))).
destruct (IH regs7 (w + 8) (c - 8)) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
all: try (subst regs7 regs5; gr; first [reflexivity | assumption]).
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs7 1) by (subst regs7 regs5; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_088 DM_088
ltac:(subst regs5; gr; rewrite H14; cbn [branch_taken]; unfold bv_eqb;
rewrite Htw, HTz, u_Z2bv by (unfold HZ.HIGHS; lia); rewrite Z.sub_0_r, Z.eqb_refl; reflexivity).
stepiv' FM_08c DM_08c (Z_to_bv 64 (c - 8))
ltac:(subst regs5; gr; rewrite H12; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepiv' FM_090 DM_090 (Z_to_bv 64 (w + 8))
ltac:(subst regs5; gr; rewrite H10; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; reflexivity).
stepbt FM_094 DM_094
ltac:(subst regs5; gr; rewrite H16; cbn [branch_taken]; rewrite ltu_w by lia; apply Z.ltb_lt; lia).
subst regs7 regs5. msteps_done.
+ split; [exact H10'|]. split; [exact H12'|]. split; [rewrite H13'; f_equal; lia|].
intros r Hr5 Hr10 Hr12 Hr13 Hr17. rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr17). subst regs7 regs5.
rewrite !getr_other by assumption. reflexivity.
Qed.
Hypothesis Hrom : forall a : Z, src0_D_const_HIGHS_0x8080808080808080 <= a < (src0_D_const_ONES_0x0101010101010100 + 8) ->
rdn src0segs mem (Z_to_bv 64 a) 1 = rdn src0segs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Lemma rd_C1 : exists bs, rdn src0segs mem (Z_to_bv 64 src0_D_const_ONES_0x0101010101010100) 8 = Some bs /\ bytes_le_to_Z bs = C1.
Proof.
rodc.
rewrite (rdn_ext1 src0segs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 src0_D_const_ONES_0x0101010101010100)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros k Hk. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. lia.
Qed.
Lemma rd_HIGHS : exists bs, rdn src0segs mem (Z_to_bv 64 src0_D_const_HIGHS_0x8080808080808080) 8 = Some bs /\ bytes_le_to_Z bs = HZ.HIGHS.
Proof.
rodc.
rewrite (rdn_ext1 src0segs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 src0_D_const_HIGHS_0x8080808080808080)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros k Hk. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. lia.
Qed.
Lemma mc_aligned : forall regs (q c : Z),
P <= q <= E -> q mod 8 = 0 ->
getr regs 10 = Z_to_bv 64 q ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = Z_to_bv 64 c ->
getr regs 14 = Z_to_bv 64 1 ->
E - q + 8 <= c -> c < 2^64 ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0x44)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 E
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 13 = Z_to_bv 64 (c - (E - q))
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs q c Hq Hq8 H10 H11 H12 H14 Hqc Hc. epl.
set (b := nth (Z.to_nat (q - P)) (s ++ [NUL]) NUL).
set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned b))).
assert (Hpre : msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0x44)) mem rom)
(mkst regs1 (Z_to_bv 64 (src0_A_memchr + 0x4c)) mem rom)).
{ norm_pc.
stepbf FM_044 DM_044 ltac:(gr; rewrite H14; vm_compute; reflexivity).
steplbu FM_048 DM_048
ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0;
replace (Z_to_bv 64 q) with (Z_to_bv 64 (bv_unsigned p + Z.of_nat (Z.to_nat (q - P)))) by (f_equal; lia);
apply Hstr; lia).
subst regs1 b. msteps_done. }
destruct (Z.eq_dec q E) as [HqE|HqE].
-
assert (Hb : b = NUL).
{ subst b. replace (Z.to_nat (q - P)) with (length s) by lia. apply nth_app_nul_last. }
set (regs2 := regupd regs1 13 (Z_to_bv 64 c)).
destruct (mc_tail 0 regs2 c) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
{ subst regs2 regs1. gr. rewrite H10. f_equal. lia. }
{ subst regs2 regs1. gr. exact H11. }
{ subst regs2 regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_04c DM_04c ltac:(subst regs1; gr; rewrite H11, Hb; vm_compute; reflexivity).
stepiv' FM_098 DM_098 (Z_to_bv 64 c) ltac:(subst regs1; gr; rewrite H12; imm_norm; apply v_addi_0).
stepbf FM_09c DM_09c
ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; apply eqb_w_false; lia).
subst regs2 regs1. msteps_done.
+ split; [exact H10'|]. split; [exact H12'|]. split; [rewrite H13'; f_equal; lia|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
-
assert (Hb : b <> NUL) by (apply str_byte_nz; lia).
destruct rd_C1 as (bs1 & Hbs1 & Hv1).
destruct rd_HIGHS as (bs2 & Hbs2 & Hv2).
set (regs2 := regupd (regupd (regupd (regupd (regupd (regupd (regupd regs1
13 (Z_to_bv 64 8))
13 (Z_to_bv 64 src0_memchr_aui1)) 13 (Z_to_bv 64 C1))
14 (Z_to_bv 64 src0_memchr_aui2)) 14 (Z_to_bv 64 HZ.HIGHS))
15 (Z_to_bv 64 (C1 + 1))) 15 (Z_to_bv 64 0)).
set (regs3 := regupd regs2 16 (Z_to_bv 64 7)).
assert (HE8 : E = 8 * (E / 8) + E mod 8) by (apply Z.div_mod; lia).
assert (Hq8' : q = 8 * (q / 8)) by (pose proof (Z.div_mod q 8 ltac:(lia)); lia).
assert (Hm2 : 0 <= E mod 8 < 8) by (apply Z.mod_pos_bound; lia).
destruct (mc_words (Z.to_nat (E / 8 - q / 8)) regs3 q c) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
all: try (subst regs3 regs2 regs1; gr; first [reflexivity | assumption]).
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs3 1) by (subst regs3 regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_04c DM_04c
ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
stepiv' FM_050 DM_050 (Z_to_bv 64 8) ltac:(gr; reflexivity).
stepbf FM_054 DM_054
ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; rewrite ltu_w by lia; apply Z.ltb_ge; lia).
stepiv' FM_058 DM_058 (Z_to_bv 64 src0_memchr_aui1) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs1) (v := Z_to_bv 64 C1);
[ exact_lit FM_05c | reflexivity | exact DM_05c
| gr; match goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 src0_D_const_ONES_0x0101010101010100) by bveq end; exact Hbs1
| rewrite Hv1; reflexivity ] | step_simpl ].
stepiv' FM_060 DM_060 (Z_to_bv 64 src0_memchr_aui2) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs2) (v := Z_to_bv 64 HZ.HIGHS);
[ exact_lit FM_064 | reflexivity | exact DM_064
| gr; match goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 src0_D_const_HIGHS_0x8080808080808080) by bveq end; exact Hbs2
| rewrite Hv2; reflexivity ] | step_simpl ].
stepiv' FM_068 DM_068 (Z_to_bv 64 (C1 + 1)) ltac:(gr; reflexivity).
stepiv' FM_06c DM_06c (Z_to_bv 64 0)
ltac:(subst regs1; gr; rewrite H11; unfold v_mul; rewrite u_lit0, Z.mul_0_l; reflexivity).
stepiv' FM_070 DM_070 (Z_to_bv 64 7) ltac:(gr; reflexivity).
subst regs3 regs2 regs1. msteps_done.
+ split; [exact H10'|]. split; [exact H12'|]. split; [exact H13'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr17). subst regs3 regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma N_eq : N = bv_unsigned n. Proof. reflexivity. Qed.
Lemma mc_prologue : forall m regs (j : nat),
P mod 8 <> 0 ->
(0 < m)%nat -> Z.of_nat j + Z.of_nat m = 8 - P mod 8 ->
(j <= length s)%nat ->
getr regs 10 = Z_to_bv 64 (P + Z.of_nat j) ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = Z_to_bv 64 (N - Z.of_nat j) ->
getr regs 15 = Z_to_bv 64 (P + Z.of_nat j + 1) ->
getr regs 16 = Z_to_bv 64 1 ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0x1c)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 E
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 13 = Z_to_bv 64 (N - L)
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
induction m as [|m IH]; intros regs j HA Hm Hjm Hj H10 H11 H12 H15 H16; [lia|].
epl. pose proof N_eq. pose proof (u64_range n).
assert (HA8 : 0 <= P mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (HP8 : P = 8 * (P / 8) + P mod 8) by (apply Z.div_mod; lia).
set (b := nth j (s ++ [NUL]) NUL).
set (regs1 := regupd (regupd regs 14 (Z_to_bv 64 (bv_unsigned b))) 13 (Z_to_bv 64 (N - Z.of_nat j))).
assert (Hpre : msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0x1c)) mem rom)
(mkst regs1 (Z_to_bv 64 (src0_A_memchr + 0x24)) mem rom)).
{ norm_pc.
steplbu FM_01c DM_01c ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0; apply Hstr; lia).
stepiv' FM_020 DM_020 (Z_to_bv 64 (N - Z.of_nat j)) ltac:(gr; rewrite H12; imm_norm; apply v_addi_0).
subst regs1 b. msteps_done. }
destruct (Nat.eq_dec j (length s)) as [HjL|HjL].
-
assert (Hb : b = NUL) by (subst b j; apply nth_app_nul_last).
destruct (mc_tail 0 regs1 (N - L)) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
{ subst regs1. gr. rewrite H10. f_equal. lia. }
{ subst regs1. gr. exact H11. }
{ subst regs1. gr. f_equal. lia. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_024 DM_024 ltac:(subst regs1; gr; rewrite H11, Hb; vm_compute; reflexivity).
msteps_done.
+ split; [exact H10'|]. split; [exact H12'|]. split; [rewrite H13'; f_equal; lia|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs1.
rewrite !getr_other by assumption. reflexivity.
-
assert (Hb : b <> NUL) by (apply str_byte_nz; lia).
set (regs2 := regupd (regupd (regupd (regupd regs1
10 (Z_to_bv 64 (P + Z.of_nat j + 1)))
12 (Z_to_bv 64 (N - Z.of_nat j - 1)))
17 (Z_to_bv 64 ((P + Z.of_nat j + 1) mod 8)))
14 (Z_to_bv 64 1)).
assert (Hmid : msteps src0segs (mkst regs1 (Z_to_bv 64 (src0_A_memchr + 0x24)) mem rom)
(mkst regs2 (Z_to_bv 64 (src0_A_memchr + 0x38)) mem rom)).
{ norm_pc.
stepbf FM_024 DM_024
ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
stepiv' FM_028 DM_028 (Z_to_bv 64 (P + Z.of_nat j + 1))
ltac:(subst regs1; gr; rewrite H10; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; reflexivity).
stepiv' FM_02c DM_02c (Z_to_bv 64 (N - Z.of_nat j - 1))
ltac:(subst regs1; gr; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepiv' FM_030 DM_030 (Z_to_bv 64 ((P + Z.of_nat j + 1) mod 8))
ltac:(subst regs1; gr; rewrite H15; imm_norm; unfold v_andi; rewrite u_Z2bv by lia;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
stepov FM_034 DM_034 (Z_to_bv 64 1)
ltac:(rewrite alu_sltu; subst regs1; gr; unfold v_sltu, c_ltu; rewrite ltu_w by lia;
replace (0 <? N - Z.of_nat j - 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
subst regs2 regs1. msteps_done. }
assert (Hm8 : 0 <= (P + Z.of_nat j + 1) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
destruct (Z.eq_dec ((P + Z.of_nat j + 1) mod 8) 0) as [Hal|Hal].
+
destruct (mc_aligned regs2 (P + Z.of_nat j + 1) (N - Z.of_nat j - 1))
as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
all: try (subst regs2 regs1; gr; first [reflexivity | assumption]).
exists regs'. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_038 DM_038 ltac:(subst regs2; gr; rewrite Hal; vm_compute; reflexivity).
msteps_done.
* split; [exact H10'|]. split; [exact H12'|]. split; [rewrite H13'; f_equal; lia|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17).
subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
+
assert (Hm' : (0 < m)%nat).
{ destruct m; [|lia]. exfalso. apply Hal.
replace (P + Z.of_nat j + 1) with (8 * (P / 8 + 1)) by lia.
rewrite Z.mul_comm. apply Z_mod_mult. }
set (regs3 := regupd regs2 15 (Z_to_bv 64 (P + Z.of_nat (S j) + 1))).
destruct (IH regs3 (S j)) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
all: try (subst regs3 regs2 regs1; gr; first [reflexivity | assumption | f_equal; lia]).
exists regs'. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs3 1) by (subst regs3 regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_038 DM_038 ltac:(subst regs2; gr; cbn [branch_taken]; apply eqb_w_false; lia).
stepiv' FM_03c DM_03c (Z_to_bv 64 (P + Z.of_nat (S j) + 1))
ltac:(subst regs2 regs1; gr; rewrite H15; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepbt FM_040 DM_040
ltac:(subst regs2 regs1; gr; rewrite H16; cbn [branch_taken]; apply negb_true_iff; apply eqb_w_false; lia).
subst regs3 regs2 regs1. msteps_done.
* split; [exact H10'|]. split; [exact H12'|]. split; [exact H13'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17).
subst regs3 regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma ref_memchr_sec : forall regs,
getr regs 10 = p ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = n ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0x0)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (bv_unsigned p + Z.of_nat (length s))
/\ getr regs' 11 = Z_to_bv 64 0
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 13 = Z_to_bv 64 (bv_unsigned n - Z.of_nat (length s))
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs H10 H11 H12. epl. pose proof N_eq. pose proof (u64_range n).
assert (HA8 : 0 <= P mod 8 < 8) by (apply Z.mod_pos_bound; lia).
set (regs1 := regupd (regupd (regupd regs 11 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (P mod 8))) 14 (Z_to_bv 64 1)).
assert (Hpre : msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_memchr + 0x0)) mem rom)
(mkst regs1 (Z_to_bv 64 (src0_A_memchr + 0xc)) mem rom)).
{ norm_pc.
stepiv' FM_000 DM_000 (Z_to_bv 64 0) ltac:(gr; rewrite H11; bveq).
stepiv' FM_004 DM_004 (Z_to_bv 64 (P mod 8))
ltac:(gr; rewrite H10; imm_norm; unfold v_andi;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
stepov FM_008 DM_008 (Z_to_bv 64 1)
ltac:(rewrite alu_sltu; gr; rewrite H12; unfold v_sltu, c_ltu, bv_ltu; rewrite u_lit0;
replace (0 <? bv_unsigned n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
subst regs1. msteps_done. }
destruct (Z.eq_dec (P mod 8) 0) as [HA|HA].
-
destruct (mc_aligned regs1 P N) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
{ subst regs1. gr. rewrite H10. symmetry. apply Z_to_bv_bv_unsigned. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. rewrite H12. symmetry. apply Z_to_bv_bv_unsigned. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_00c DM_00c ltac:(subst regs1; gr; rewrite HA; vm_compute; reflexivity).
msteps_done.
+ split; [rewrite H10'; f_equal; lia|]. split; [rewrite Hfr by reg_neq_tac; subst regs1; gr; reflexivity|].
split; [exact H12'|]. split; [rewrite H13'; f_equal; lia|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17).
subst regs1. rewrite !getr_other by assumption. reflexivity.
-
set (regs2 := regupd (regupd regs1 15 (Z_to_bv 64 (P + Z.of_nat 0 + 1))) 16 (Z_to_bv 64 1)).
destruct (mc_prologue (Z.to_nat (8 - P mod 8)) regs2 0) as (regs' & Hms & H10' & H12' & H13' & Hfr); try lia.
{ subst regs2 regs1. gr. rewrite H10, Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
{ subst regs2 regs1. gr. reflexivity. }
{ subst regs2 regs1. gr. rewrite H12, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
{ subst regs2 regs1. gr. reflexivity. }
{ subst regs2 regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_00c DM_00c ltac:(subst regs1; gr; cbn [branch_taken]; apply eqb_w_false; lia).
stepbf FM_010 DM_010
ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; unfold bv_eqb; rewrite u_lit0; apply Z.eqb_neq; lia).
stepiv' FM_014 DM_014 (Z_to_bv 64 (P + Z.of_nat 0 + 1))
ltac:(subst regs1; gr; rewrite H10; imm_norm; unfold v_addi; f_equal; lia).
stepiv' FM_018 DM_018 (Z_to_bv 64 1) ltac:(gr; reflexivity).
subst regs2 regs1. msteps_done.
+ split; [rewrite H10'; f_equal; lia|]. split; [rewrite Hfr by reg_neq_tac; subst regs2 regs1; gr; reflexivity|].
split; [exact H12'|]. split; [rewrite H13'; f_equal; lia|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17).
subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
End h.
Lemma bv_eqb_false_neq : forall {k} (a b : bv k), bv_eqb a b = false -> a <> b.
Proof.
intros k a b H Hc. subst b. rewrite bv_eqb_refl in H. discriminate H.
Qed.
Lemma wbytes_out : forall bs m (addr x : word),
bv_unsigned addr + Z.of_nat (length bs) <= 2^64 ->
(bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x) ->
wbytes m addr bs x = m x.
Proof.
intros bs m addr x Hnw [Hlt|Hge].
- apply wbytes_below; assumption.
- apply wbytes_above; assumption.
Qed.
Section o.
Variable s : list byte.
Variable p : word.
Variable n : word.
Variable sp ra : word.
Variable mem rom : word -> option byte.
Hypothesis Hnul : ~ In NUL s.
Hypothesis Hfit : bv_unsigned p + Z.of_nat (length s) + 8 < 2^64.
Hypothesis Hn : Z.of_nat (length s) + 8 <= bv_unsigned n.
Hypothesis Hp0 : 0 < bv_unsigned p.
Hypothesis Hstr : forall j, (j <= length s)%nat ->
rdn src0segs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL].
Hypothesis Hrd : forall a : Z,
bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn src0segs mem (Z_to_bv 64 a) 1 <> None.
Hypothesis Hrom : forall a : Z, src0_D_const_HIGHS_0x8080808080808080 <= a < (src0_D_const_ONES_0x0101010101010100 + 8) ->
rdn src0segs mem (Z_to_bv 64 a) 1 = rdn src0segs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Hypothesis Hstk : store_ok src0segs mem (Z_to_bv 64 (bv_unsigned sp - 24)) 24 = true.
Hypothesis Hdisj : bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8
<= bv_unsigned sp - 24
\/ bv_unsigned sp <= bv_unsigned p.
Hypothesis Hdisj2 : (src0_D_const_ONES_0x0101010101010100 + 8) <= bv_unsigned sp - 24 \/ bv_unsigned sp <= src0_D_const_HIGHS_0x8080808080808080.
Hypothesis Hsp32 : 32 <= bv_unsigned sp.
Definition strnlen_mem (s0 s1 : word) : word -> option byte :=
wbytes (wbytes (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
(Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
(Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 s1).
Lemma strnlen_mem_out : forall s0 s1 (x : word),
(bv_unsigned x < bv_unsigned sp - 24 \/ bv_unsigned sp <= bv_unsigned x) ->
strnlen_mem s0 s1 x = mem x.
Proof.
intros s0 s1 x Hx. pose proof (u64_range sp). unfold strnlen_mem.
rewrite !wbytes_out; rewrite ?length_N_to_le_bytes, ?u_Z2bv; cbn [Z.of_nat Pos.to_nat]; try lia.
reflexivity.
Qed.
Lemma strnlen_mem_rdn1 : forall s0 s1 (a : Z),
0 <= a < 2^64 ->
(a < bv_unsigned sp - 24 \/ bv_unsigned sp <= a) ->
rdn src0segs (strnlen_mem s0 s1) (Z_to_bv 64 a) 1 = rdn src0segs mem (Z_to_bv 64 a) 1.
Proof.
intros s0 s1 a Ha Hout. apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia|].
intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply strnlen_mem_out. lia.
Qed.
Lemma ref_strnlen_sec : forall regs,
getr regs 10 = p ->
getr regs 11 = n ->
getr regs 2 = sp ->
getr regs 1 = ra ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_strnlen + 0x0)) mem rom)
(mkst regs' (v_jalr ra 0) (strnlen_mem (getr regs 8) (getr regs 9)) rom)
/\ getr regs' 10 = Z_to_bv 64 (Z.of_nat (length s))
/\ getr regs' 11 = Z_to_bv 64 0
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 13 = Z_to_bv 64 (bv_unsigned n - Z.of_nat (length s))
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs H10 H11 H2 H1. rodc.
pose proof (u64_range sp) as Hspr. pose proof (u64_range p) as Hpr. pose proof (u64_range n) as Hnr.
assert (Hm1 : 0 <= bv_unsigned p mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hm2 : 0 <= (bv_unsigned p + Z.of_nat (length s)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hm3 : (bv_unsigned p + Z.of_nat (length s)) mod 8 <= bv_unsigned p + Z.of_nat (length s)) by (apply Z.mod_le; lia).
set (SP := bv_unsigned sp).
set (m1 := wbytes mem (Z_to_bv 64 (SP - 8)) (word_to_le_bytes 8 ra)).
set (m2 := wbytes m1 (Z_to_bv 64 (SP - 16)) (word_to_le_bytes 8 (getr regs 8))).
set (m3 := wbytes m2 (Z_to_bv 64 (SP - 24)) (word_to_le_bytes 8 (getr regs 9))).
assert (Em3 : m3 = strnlen_mem (getr regs 8) (getr regs 9)) by reflexivity.
let l := word_lit constr:(Z_to_bv 64 (src0_A_strnlen + 0x20)) in
set (regs3 := regupd (regupd (regupd (regupd (regupd (regupd regs
2 (Z_to_bv 64 (SP - 32))) 8 n) 9 p) 11 (Z_to_bv 64 0)) 12 n) 1 (v_addi l 4)).
assert (Hpre : msteps src0segs (mkst regs (Z_to_bv 64 (src0_A_strnlen + 0x0)) mem rom)
(mkst regs3 (Z_to_bv 64 (src0_A_memchr + 0x0)) m3 rom)).
{ norm_pc.
stepiv' FS_000 DS_000 (Z_to_bv 64 (SP - 32)) ltac:(gr; rewrite H2; imm_norm; unfold v_addi; f_equal; lia).
chain_step; [reflexivity | eapply step_sd_at with (a := Z_to_bv 64 (SP - 8)) (v := ra);
[ exact_lit FS_004 | reflexivity | exact DS_004
| gr; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia
| gr; exact H1
| eapply store_ok_sub; [ | exact Hstk | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.to_nat]; lia ]
| step_simpl ].
fold m1.
chain_step; [reflexivity | eapply step_sd_at with (a := Z_to_bv 64 (SP - 16)) (v := getr regs 8);
[ exact_lit FS_008 | reflexivity | exact DS_008
| gr; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia
| gr; reflexivity
| eapply store_ok_mono; [apply wbytes_grows|];
eapply store_ok_sub; [ | exact Hstk | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.to_nat]; lia ]
| step_simpl ].
fold m2.
chain_step; [reflexivity | eapply step_sd_at with (a := Z_to_bv 64 (SP - 24)) (v := getr regs 9);
[ exact_lit FS_00c | reflexivity | exact DS_00c
| gr; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia
| gr; reflexivity
| eapply store_ok_mono; [eapply mem_grows_trans; apply wbytes_grows|];
eapply store_ok_sub; [ | exact Hstk | | ]; rewrite ?u_Z2bv by lia; cbn [Z.of_nat Pos.to_nat]; lia ]
| step_simpl ].
fold m3.
stepiv' FS_010 DS_010 n ltac:(gr; rewrite H11; imm_norm; apply v_addi_0).
stepiv' FS_014 DS_014 p ltac:(gr; rewrite H10; imm_norm; apply v_addi_0).
stepiv' FS_018 DS_018 (Z_to_bv 64 0) ltac:(gr; reflexivity).
stepiv' FS_01c DS_01c n ltac:(gr; imm_norm; apply v_addi_0).
stepj' FS_020 DS_020.
subst regs3. msteps_done. }
destruct (ref_memchr_sec s p n m3 rom Hnul Hfit Hn) with (regs := regs3)
as (regs4 & Hms & H10' & H11' & H12' & H13' & Hfr).
{ intros j Hj. rewrite Em3, strnlen_mem_rdn1 by lia. apply Hstr. exact Hj. }
{ intros a Ha. rewrite Em3, strnlen_mem_rdn1 by lia. apply Hrd. exact Ha. }
{ intros a Ha. rewrite Em3, strnlen_mem_rdn1 by lia. apply Hrom. exact Ha. }
{ subst regs3. gr. exact H10. }
{ subst regs3. gr. reflexivity. }
{ subst regs3. gr. reflexivity. }
let l := word_lit constr:(Z_to_bv 64 (src0_A_strnlen + 0x20)) in
replace (getr regs3 1) with (v_addi l 4) in Hms by (subst regs3; gr; reflexivity).
assert (Hr2 : getr regs4 2 = Z_to_bv 64 (SP - 32)) by (rewrite (Hfr 2%bv) by reg_neq_tac; subst regs3; gr; reflexivity).
assert (Hr9 : getr regs4 9 = p) by (rewrite (Hfr 9%bv) by reg_neq_tac; subst regs3; gr; reflexivity).
assert (Hld1 : rdn src0segs m3 (Z_to_bv 64 (SP - 8)) 8 = Some (word_to_le_bytes 8 ra)).
{ subst m3 m2 m1. rewrite 2 rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.to_nat]; try lia.
apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
assert (Hld2 : rdn src0segs m3 (Z_to_bv 64 (SP - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
{ subst m3 m2 m1. rewrite rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.to_nat]; try lia.
apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
assert (Hld3 : rdn src0segs m3 (Z_to_bv 64 (SP - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
{ subst m3. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
eexists. split; [|split; [|split; [|split; [|split]]]].
- eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hms|].
rewrite <- Em3. norm_pc.
stepbf FS_024 DS_024 ltac:(gr; rewrite H10'; cbn [branch_taken]; apply eqb_w_false; lia).
stepiv' FS_028 DS_028 (Z_to_bv 64 (Z.of_nat (length s)))
ltac:(rewrite H10', Hr9; unfold v_sub; rewrite u_Z2bv by lia; f_equal; lia).
stepiv' FS_02c DS_02c (Z_to_bv 64 (Z.of_nat (length s))) ltac:(gr; imm_norm; apply v_addi_0).
chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 ra) (v := ra);
[ exact_lit FS_030 | reflexivity | exact DS_030
| gr; rewrite Hr2; imm_norm; unfold v_addi; rewrite u_Z2bv by lia;
replace (SP - 32 + 24) with (SP - 8) by lia; exact Hld1
| apply bytes_le_to_Z_8 ] | step_simpl ].
chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (getr regs 8)) (v := getr regs 8);
[ exact_lit FS_034 | reflexivity | exact DS_034
| gr; rewrite Hr2; imm_norm; unfold v_addi; rewrite u_Z2bv by lia;
replace (SP - 32 + 16) with (SP - 16) by lia; exact Hld2
| apply bytes_le_to_Z_8 ] | step_simpl ].
chain_step; [reflexivity | eapply step_ld with (bs := word_to_le_bytes 8 (getr regs 9)) (v := getr regs 9);
[ exact_lit FS_038 | reflexivity | exact DS_038
| gr; rewrite Hr2; imm_norm; unfold v_addi; rewrite u_Z2bv by lia;
replace (SP - 32 + 8) with (SP - 24) by lia; exact Hld3
| apply bytes_le_to_Z_8 ] | step_simpl ].
stepiv' FS_03c DS_03c sp
ltac:(gr; rewrite Hr2; imm_norm; unfold v_addi; rewrite u_Z2bv by lia;
replace (SP - 32 + 32) with SP by lia; apply Z_to_bv_bv_unsigned).
chain_step; [reflexivity | eapply step_jalr_x0; [exact_lit FS_040 | reflexivity | exact DS_040 | gr; reflexivity] | step_simpl; imm_norm ].
apply mst_refl.
- gr. reflexivity.
- gr. exact H11'.
- gr. exact H12'.
- gr. exact H13'.
- intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17.
destruct (bv_eqb r 2) eqn:E2; [apply bv_eqb_eq in E2; subst r; gr; symmetry; exact H2 | apply bv_eqb_false_neq in E2].
destruct (bv_eqb r 9) eqn:E9; [apply bv_eqb_eq in E9; subst r; gr; reflexivity | apply bv_eqb_false_neq in E9].
destruct (bv_eqb r 8) eqn:E8; [apply bv_eqb_eq in E8; subst r; gr; reflexivity | apply bv_eqb_false_neq in E8].
destruct (bv_eqb r 1) eqn:E1; [apply bv_eqb_eq in E1; subst r; gr; symmetry; exact H1 | apply bv_eqb_false_neq in E1].
rewrite !getr_other by assumption.
rewrite (Hfr r) by assumption. subst regs3. rewrite !getr_other by assumption. reflexivity.
Qed.
End o.
Theorem src0_memchr :
forall (s : list byte) (p n : word) (mem rom : word -> option byte) regs,
~ In NUL s ->
bv_unsigned p + Z.of_nat (length s) + 8 < 2^64 ->
Z.of_nat (length s) + 8 <= bv_unsigned n ->
(forall j, (j <= length s)%nat ->
rdn src0segs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL]) ->
(forall a : Z,
bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn src0segs mem (Z_to_bv 64 a) 1 <> None) ->
(forall a : Z, src0_D_const_HIGHS_0x8080808080808080 <= a < (src0_D_const_ONES_0x0101010101010100 + 8) ->
rdn src0segs mem (Z_to_bv 64 a) 1 = rdn src0segs (fun _ : word => @None byte) (Z_to_bv 64 a) 1) ->
getr regs 10 = p ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = n ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 src0_A_memchr) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (bv_unsigned p + Z.of_nat (length s))
/\ getr regs' 11 = Z_to_bv 64 0
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 13 = Z_to_bv 64 (bv_unsigned n - Z.of_nat (length s))
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof. intros. change (Z_to_bv 64 src0_A_memchr) with (Z_to_bv 64 (src0_A_memchr + 0x0)). eapply ref_memchr_sec; eassumption. Qed.
Theorem src0_strnlen :
forall (s : list byte) (p n sp ra : word) (mem rom : word -> option byte) regs,
~ In NUL s ->
bv_unsigned p + Z.of_nat (length s) + 8 < 2^64 ->
Z.of_nat (length s) + 8 <= bv_unsigned n ->
0 < bv_unsigned p ->
(forall j, (j <= length s)%nat ->
rdn src0segs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL]) ->
(forall a : Z,
bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn src0segs mem (Z_to_bv 64 a) 1 <> None) ->
(forall a : Z, src0_D_const_HIGHS_0x8080808080808080 <= a < (src0_D_const_ONES_0x0101010101010100 + 8) ->
rdn src0segs mem (Z_to_bv 64 a) 1 = rdn src0segs (fun _ : word => @None byte) (Z_to_bv 64 a) 1) ->
store_ok src0segs mem (Z_to_bv 64 (bv_unsigned sp - 24)) 24 = true ->
(bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8
<= bv_unsigned sp - 24
\/ bv_unsigned sp <= bv_unsigned p) ->
((src0_D_const_ONES_0x0101010101010100 + 8) <= bv_unsigned sp - 24 \/ bv_unsigned sp <= src0_D_const_HIGHS_0x8080808080808080) ->
32 <= bv_unsigned sp ->
getr regs 10 = p ->
getr regs 11 = n ->
getr regs 2 = sp ->
getr regs 1 = ra ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 src0_A_strnlen) mem rom)
(mkst regs' (v_jalr ra 0) (strnlen_mem sp ra mem (getr regs 8) (getr regs 9)) rom)
/\ getr regs' 10 = Z_to_bv 64 (Z.of_nat (length s))
/\ getr regs' 11 = Z_to_bv 64 0
/\ getr regs' 12 = Z_to_bv 64 0
/\ getr regs' 13 = Z_to_bv 64 (bv_unsigned n - Z.of_nat (length s))
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof. intros. change (Z_to_bv 64 src0_A_strnlen) with (Z_to_bv 64 (src0_A_strnlen + 0x0)). eapply ref_strnlen_sec; eassumption. Qed.
End g.
