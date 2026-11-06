(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSRipA AsanWMemcpyF1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Definition AMC_WORDS : list (Z * Z) :=
  [(0x0, 0x81010113); (0x4, 0x7e113423); (0x8, 0x7e813023); (0xc, 0x7c913c23); (0x10, 0x7d213823);
   (0x14, 0x7d313423); (0x18, 0x7d413023); (0x1c, 0x7b513c23); (0x20, 0x7b613823); (0x24, 0x7b713423);
   (0x28, 0x7b813023); (0x2c, 0x7f010413); (0x30, 0xf8010113); (0x3c, 0x0006c683); (0x40, 0x0e068a63);
   (0x44, 0x80040a93); (0x48, 0xf98a8a93); (0x4c, 0x00c589b3); (0x50, 0x00c50a33); (0x54, 0x00b50663);
   (0x58, 0x0145f463); (0x5c, 0x1b356e63); (0x60, 0xfff5c693); (0x64, 0x26c6e863); (0x68, 0xfbf60b13);
   (0x6c, 0xfbf00693); (0x70, 0x2f66f663); (0x7c, 0x0006b703); (0x80, 0xfff98993); (0x84, 0x0035d693);
   (0x88, 0x0039d793); (0x8c, 0x00d706b3); (0x90, 0x00f70733); (0x94, 0xff86f793); (0x98, 0xff877813);
   (0x9c, 0x0007b783); (0xa0, 0x00083803); (0xa4, 0x00f867b3); (0xa8, 0x2a079e63); (0xac, 0xfff54693);
   (0xb0, 0x0cc6ee63); (0xb4, 0xfbf00693); (0xb8, 0x1566fc63); (0xc4, 0x0006b703); (0xc8, 0xfffa0a13);
   (0xcc, 0x00355693); (0xd0, 0x003a5793); (0xd4, 0x00d706b3); (0xd8, 0x00f70733); (0xdc, 0xff86f793);
   (0xe0, 0xff877813); (0xe4, 0x0007b783); (0xe8, 0x00083803); (0xec, 0x00f867b3); (0xf0, 0x36079a63);
   (0xfc, 0x000680e7); (0x100, 0x08010113); (0x104, 0x7e813083); (0x108, 0x7e013403); (0x10c, 0x7d813483);
   (0x110, 0x7d013903); (0x114, 0x7c813983); (0x118, 0x7c013a03); (0x11c, 0x7b813a83); (0x120, 0x7b013b03);
   (0x124, 0x7a813b83); (0x128, 0x7a013c03); (0x12c, 0x7f010113); (0x130, 0x00008067); (0x35c, 0x02061e63);
   (0x360, 0xd4dff06f); (0x398, 0x00050b93); (0x39c, 0x00058513); (0x3a0, 0x00058c13); (0x3a4, 0x00060593);
   (0x3a8, 0x00060493); (0x3b0, 0x000c0593); (0x3b4, 0x00048613); (0x3b8, 0x00050913);
   (0x3bc, 0x000b8513); (0x3c0, 0xce0906e3); (0x210, 0x28061463); (0x214, 0xee1ff06f); (0x498, 0x00050493);
   (0x49c, 0x00058b13); (0x4a0, 0x00060593); (0x4a4, 0x00060913); (0x4ac, 0x000b0593);
   (0x4b0, 0x00090613); (0x4b4, 0x00050993); (0x4b8, 0x00048513); (0x4bc, 0xc2098ce3)]%Z.

Lemma DA_81010113 : decode_any (Z_to_bv 32 0x81010113) = Some (OpImm ALU_ADD 2 2 2064, 4%Z). Proof. wdec. Qed.
Lemma DA_7e113423 : decode_any (Z_to_bv 32 0x7e113423) = Some (Store SZ8 2 1 2024, 4%Z). Proof. wdec. Qed.
Lemma DA_7e813023 : decode_any (Z_to_bv 32 0x7e813023) = Some (Store SZ8 2 8 2016, 4%Z). Proof. wdec. Qed.
Lemma DA_7c913c23 : decode_any (Z_to_bv 32 0x7c913c23) = Some (Store SZ8 2 9 2008, 4%Z). Proof. wdec. Qed.
Lemma DA_7d213823 : decode_any (Z_to_bv 32 0x7d213823) = Some (Store SZ8 2 18 2000, 4%Z). Proof. wdec. Qed.
Lemma DA_7d313423 : decode_any (Z_to_bv 32 0x7d313423) = Some (Store SZ8 2 19 1992, 4%Z). Proof. wdec. Qed.
Lemma DA_7d413023 : decode_any (Z_to_bv 32 0x7d413023) = Some (Store SZ8 2 20 1984, 4%Z). Proof. wdec. Qed.
Lemma DA_7b513c23 : decode_any (Z_to_bv 32 0x7b513c23) = Some (Store SZ8 2 21 1976, 4%Z). Proof. wdec. Qed.
Lemma DA_7b613823 : decode_any (Z_to_bv 32 0x7b613823) = Some (Store SZ8 2 22 1968, 4%Z). Proof. wdec. Qed.
Lemma DA_7b713423 : decode_any (Z_to_bv 32 0x7b713423) = Some (Store SZ8 2 23 1960, 4%Z). Proof. wdec. Qed.
Lemma DA_7b813023 : decode_any (Z_to_bv 32 0x7b813023) = Some (Store SZ8 2 24 1952, 4%Z). Proof. wdec. Qed.
Lemma DA_7f010413 : decode_any (Z_to_bv 32 0x7f010413) = Some (OpImm ALU_ADD 8 2 2032, 4%Z). Proof. wdec. Qed.
Lemma DA_f8010113 : decode_any (Z_to_bv 32 0xf8010113) = Some (OpImm ALU_ADD 2 2 3968, 4%Z). Proof. wdec. Qed.
Lemma DA_0006c683 : decode_any (Z_to_bv 32 0x0006c683) = Some (Load SZ1 false 13 13 0, 4%Z). Proof. wdec. Qed.
Lemma DA_0e068a63 : decode_any (Z_to_bv 32 0x0e068a63) = Some (Branch BC_EQ 13 0 244, 4%Z). Proof. wdec. Qed.
Lemma DA_80040a93 : decode_any (Z_to_bv 32 0x80040a93) = Some (OpImm ALU_ADD 21 8 2048, 4%Z). Proof. wdec. Qed.
Lemma DA_f98a8a93 : decode_any (Z_to_bv 32 0xf98a8a93) = Some (OpImm ALU_ADD 21 21 3992, 4%Z). Proof. wdec. Qed.
Lemma DA_00c589b3 : decode_any (Z_to_bv 32 0x00c589b3) = Some (Op ALU_ADD 19 11 12, 4%Z). Proof. wdec. Qed.
Lemma DA_00c50a33 : decode_any (Z_to_bv 32 0x00c50a33) = Some (Op ALU_ADD 20 10 12, 4%Z). Proof. wdec. Qed.
Lemma DA_00b50663 : decode_any (Z_to_bv 32 0x00b50663) = Some (Branch BC_EQ 10 11 12, 4%Z). Proof. wdec. Qed.
Lemma DA_0145f463 : decode_any (Z_to_bv 32 0x0145f463) = Some (Branch BC_GEU 11 20 8, 4%Z). Proof. wdec. Qed.
Lemma DA_1b356e63 : decode_any (Z_to_bv 32 0x1b356e63) = Some (Branch BC_LTU 10 19 444, 4%Z). Proof. wdec. Qed.
Lemma DA_fff5c693 : decode_any (Z_to_bv 32 0xfff5c693) = Some (OpImm ALU_XOR 13 11 4095, 4%Z). Proof. wdec. Qed.
Lemma DA_26c6e863 : decode_any (Z_to_bv 32 0x26c6e863) = Some (Branch BC_LTU 13 12 624, 4%Z). Proof. wdec. Qed.
Lemma DA_fbf60b13 : decode_any (Z_to_bv 32 0xfbf60b13) = Some (OpImm ALU_ADD 22 12 4031, 4%Z). Proof. wdec. Qed.
Lemma DA_fbf00693 : decode_any (Z_to_bv 32 0xfbf00693) = Some (OpImm ALU_ADD 13 0 4031, 4%Z). Proof. wdec. Qed.
Lemma DA_2f66f663 : decode_any (Z_to_bv 32 0x2f66f663) = Some (Branch BC_GEU 13 22 748, 4%Z). Proof. wdec. Qed.
Lemma DA_0006b703 : decode_any (Z_to_bv 32 0x0006b703) = Some (Load SZ8 true 14 13 0, 4%Z). Proof. wdec. Qed.
Lemma DA_fff98993 : decode_any (Z_to_bv 32 0xfff98993) = Some (OpImm ALU_ADD 19 19 4095, 4%Z). Proof. wdec. Qed.
Lemma DA_0035d693 : decode_any (Z_to_bv 32 0x0035d693) = Some (ShiftImm ALU_SRL 13 11 3, 4%Z). Proof. wdec. Qed.
Lemma DA_0039d793 : decode_any (Z_to_bv 32 0x0039d793) = Some (ShiftImm ALU_SRL 15 19 3, 4%Z). Proof. wdec. Qed.
Lemma DA_00d706b3 : decode_any (Z_to_bv 32 0x00d706b3) = Some (Op ALU_ADD 13 14 13, 4%Z). Proof. wdec. Qed.
Lemma DA_00f70733 : decode_any (Z_to_bv 32 0x00f70733) = Some (Op ALU_ADD 14 14 15, 4%Z). Proof. wdec. Qed.
Lemma DA_ff86f793 : decode_any (Z_to_bv 32 0xff86f793) = Some (OpImm ALU_AND 15 13 4088, 4%Z). Proof. wdec. Qed.
Lemma DA_ff877813 : decode_any (Z_to_bv 32 0xff877813) = Some (OpImm ALU_AND 16 14 4088, 4%Z). Proof. wdec. Qed.
Lemma DA_0007b783 : decode_any (Z_to_bv 32 0x0007b783) = Some (Load SZ8 true 15 15 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00083803 : decode_any (Z_to_bv 32 0x00083803) = Some (Load SZ8 true 16 16 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00f867b3 : decode_any (Z_to_bv 32 0x00f867b3) = Some (Op ALU_OR 15 16 15, 4%Z). Proof. wdec. Qed.
Lemma DA_2a079e63 : decode_any (Z_to_bv 32 0x2a079e63) = Some (Branch BC_NE 15 0 700, 4%Z). Proof. wdec. Qed.
Lemma DA_fff54693 : decode_any (Z_to_bv 32 0xfff54693) = Some (OpImm ALU_XOR 13 10 4095, 4%Z). Proof. wdec. Qed.
Lemma DA_0cc6ee63 : decode_any (Z_to_bv 32 0x0cc6ee63) = Some (Branch BC_LTU 13 12 220, 4%Z). Proof. wdec. Qed.
Lemma DA_1566fc63 : decode_any (Z_to_bv 32 0x1566fc63) = Some (Branch BC_GEU 13 22 344, 4%Z). Proof. wdec. Qed.
Lemma DA_fffa0a13 : decode_any (Z_to_bv 32 0xfffa0a13) = Some (OpImm ALU_ADD 20 20 4095, 4%Z). Proof. wdec. Qed.
Lemma DA_00355693 : decode_any (Z_to_bv 32 0x00355693) = Some (ShiftImm ALU_SRL 13 10 3, 4%Z). Proof. wdec. Qed.
Lemma DA_003a5793 : decode_any (Z_to_bv 32 0x003a5793) = Some (ShiftImm ALU_SRL 15 20 3, 4%Z). Proof. wdec. Qed.
Lemma DA_36079a63 : decode_any (Z_to_bv 32 0x36079a63) = Some (Branch BC_NE 15 0 884, 4%Z). Proof. wdec. Qed.
Lemma DA_000680e7 : decode_any (Z_to_bv 32 0x000680e7) = Some (Jalr 1 13 0, 4%Z). Proof. wdec. Qed.
Lemma DA_08010113 : decode_any (Z_to_bv 32 0x08010113) = Some (OpImm ALU_ADD 2 2 128, 4%Z). Proof. wdec. Qed.
Lemma DA_7e813083 : decode_any (Z_to_bv 32 0x7e813083) = Some (Load SZ8 true 1 2 2024, 4%Z). Proof. wdec. Qed.
Lemma DA_7e013403 : decode_any (Z_to_bv 32 0x7e013403) = Some (Load SZ8 true 8 2 2016, 4%Z). Proof. wdec. Qed.
Lemma DA_7d813483 : decode_any (Z_to_bv 32 0x7d813483) = Some (Load SZ8 true 9 2 2008, 4%Z). Proof. wdec. Qed.
Lemma DA_7d013903 : decode_any (Z_to_bv 32 0x7d013903) = Some (Load SZ8 true 18 2 2000, 4%Z). Proof. wdec. Qed.
Lemma DA_7c813983 : decode_any (Z_to_bv 32 0x7c813983) = Some (Load SZ8 true 19 2 1992, 4%Z). Proof. wdec. Qed.
Lemma DA_7c013a03 : decode_any (Z_to_bv 32 0x7c013a03) = Some (Load SZ8 true 20 2 1984, 4%Z). Proof. wdec. Qed.
Lemma DA_7b813a83 : decode_any (Z_to_bv 32 0x7b813a83) = Some (Load SZ8 true 21 2 1976, 4%Z). Proof. wdec. Qed.
Lemma DA_7b013b03 : decode_any (Z_to_bv 32 0x7b013b03) = Some (Load SZ8 true 22 2 1968, 4%Z). Proof. wdec. Qed.
Lemma DA_7a813b83 : decode_any (Z_to_bv 32 0x7a813b83) = Some (Load SZ8 true 23 2 1960, 4%Z). Proof. wdec. Qed.
Lemma DA_7a013c03 : decode_any (Z_to_bv 32 0x7a013c03) = Some (Load SZ8 true 24 2 1952, 4%Z). Proof. wdec. Qed.
Lemma DA_7f010113 : decode_any (Z_to_bv 32 0x7f010113) = Some (OpImm ALU_ADD 2 2 2032, 4%Z). Proof. wdec. Qed.
Lemma DA_00008067 : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. wdec. Qed.
Lemma DA_02061e63 : decode_any (Z_to_bv 32 0x02061e63) = Some (Branch BC_NE 12 0 60, 4%Z). Proof. wdec. Qed.
Lemma DA_d4dff06f : decode_any (Z_to_bv 32 0xd4dff06f) = Some (Jal 0 2096460, 4%Z). Proof. wdec. Qed.
Lemma DA_00050b93 : decode_any (Z_to_bv 32 0x00050b93) = Some (OpImm ALU_ADD 23 10 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00058513 : decode_any (Z_to_bv 32 0x00058513) = Some (OpImm ALU_ADD 10 11 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00058c13 : decode_any (Z_to_bv 32 0x00058c13) = Some (OpImm ALU_ADD 24 11 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00060593 : decode_any (Z_to_bv 32 0x00060593) = Some (OpImm ALU_ADD 11 12 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00060493 : decode_any (Z_to_bv 32 0x00060493) = Some (OpImm ALU_ADD 9 12 0, 4%Z). Proof. wdec. Qed.
Lemma DA_000c0593 : decode_any (Z_to_bv 32 0x000c0593) = Some (OpImm ALU_ADD 11 24 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00048613 : decode_any (Z_to_bv 32 0x00048613) = Some (OpImm ALU_ADD 12 9 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00050913 : decode_any (Z_to_bv 32 0x00050913) = Some (OpImm ALU_ADD 18 10 0, 4%Z). Proof. wdec. Qed.
Lemma DA_000b8513 : decode_any (Z_to_bv 32 0x000b8513) = Some (OpImm ALU_ADD 10 23 0, 4%Z). Proof. wdec. Qed.
Lemma DA_ce0906e3 : decode_any (Z_to_bv 32 0xce0906e3) = Some (Branch BC_EQ 18 0 7404, 4%Z). Proof. wdec. Qed.
Lemma DA_28061463 : decode_any (Z_to_bv 32 0x28061463) = Some (Branch BC_NE 12 0 648, 4%Z). Proof. wdec. Qed.
Lemma DA_ee1ff06f : decode_any (Z_to_bv 32 0xee1ff06f) = Some (Jal 0 2096864, 4%Z). Proof. wdec. Qed.
Lemma DA_00050493 : decode_any (Z_to_bv 32 0x00050493) = Some (OpImm ALU_ADD 9 10 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00058b13 : decode_any (Z_to_bv 32 0x00058b13) = Some (OpImm ALU_ADD 22 11 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00060913 : decode_any (Z_to_bv 32 0x00060913) = Some (OpImm ALU_ADD 18 12 0, 4%Z). Proof. wdec. Qed.
Lemma DA_000b0593 : decode_any (Z_to_bv 32 0x000b0593) = Some (OpImm ALU_ADD 11 22 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00090613 : decode_any (Z_to_bv 32 0x00090613) = Some (OpImm ALU_ADD 12 18 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00050993 : decode_any (Z_to_bv 32 0x00050993) = Some (OpImm ALU_ADD 19 10 0, 4%Z). Proof. wdec. Qed.
Lemma DA_00048513 : decode_any (Z_to_bv 32 0x00048513) = Some (OpImm ALU_ADD 10 9 0, 4%Z). Proof. wdec. Qed.
Lemma DA_c2098ce3 : decode_any (Z_to_bv 32 0xc2098ce3) = Some (Branch BC_EQ 19 0 7224, 4%Z). Proof. wdec. Qed.

(* [comment removed for export] *)
Record AmcCode (segs : list Segment) (b gI gK gR : Z) : Prop := {
  amc_W : words_ok segs b AMC_WORDS = true;
  amc_pI : pair_ok segs b 0x34 13 13 gI = true;
  amc_pK1 : pair_ok segs b 0x74 13 13 gK = true;
  amc_pK2 : pair_ok segs b 0xbc 13 13 gK = true;
  amc_pR : pair_ok segs b 0xf4 13 13 gR = true
}.

Section AmcFetch.
Variable segs : list Segment.
Variables b gI gK gR : Z.
Hypothesis HA : AmcCode segs b gI gK gR.

Local Ltac fw := apply (words_get' segs b AMC_WORDS); [exact (amc_W _ _ _ _ _ HA) | vm_compute; reflexivity | lia].

Lemma FA_0 : fetch_word segs (pcw b 0x0) = Some (Z_to_bv 32 0x81010113). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_4 : fetch_word segs (pcw b 0x4) = Some (Z_to_bv 32 0x7e113423). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_8 : fetch_word segs (pcw b 0x8) = Some (Z_to_bv 32 0x7e813023). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_c : fetch_word segs (pcw b 0xc) = Some (Z_to_bv 32 0x7c913c23). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_10 : fetch_word segs (pcw b 0x10) = Some (Z_to_bv 32 0x7d213823). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_14 : fetch_word segs (pcw b 0x14) = Some (Z_to_bv 32 0x7d313423). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_18 : fetch_word segs (pcw b 0x18) = Some (Z_to_bv 32 0x7d413023). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_1c : fetch_word segs (pcw b 0x1c) = Some (Z_to_bv 32 0x7b513c23). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_20 : fetch_word segs (pcw b 0x20) = Some (Z_to_bv 32 0x7b613823). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_24 : fetch_word segs (pcw b 0x24) = Some (Z_to_bv 32 0x7b713423). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_28 : fetch_word segs (pcw b 0x28) = Some (Z_to_bv 32 0x7b813023). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_2c : fetch_word segs (pcw b 0x2c) = Some (Z_to_bv 32 0x7f010413). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_30 : fetch_word segs (pcw b 0x30) = Some (Z_to_bv 32 0xf8010113). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_3c : fetch_word segs (pcw b 0x3c) = Some (Z_to_bv 32 0x0006c683). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_40 : fetch_word segs (pcw b 0x40) = Some (Z_to_bv 32 0x0e068a63). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_44 : fetch_word segs (pcw b 0x44) = Some (Z_to_bv 32 0x80040a93). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_48 : fetch_word segs (pcw b 0x48) = Some (Z_to_bv 32 0xf98a8a93). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_4c : fetch_word segs (pcw b 0x4c) = Some (Z_to_bv 32 0x00c589b3). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_50 : fetch_word segs (pcw b 0x50) = Some (Z_to_bv 32 0x00c50a33). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_54 : fetch_word segs (pcw b 0x54) = Some (Z_to_bv 32 0x00b50663). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_58 : fetch_word segs (pcw b 0x58) = Some (Z_to_bv 32 0x0145f463). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_5c : fetch_word segs (pcw b 0x5c) = Some (Z_to_bv 32 0x1b356e63). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_60 : fetch_word segs (pcw b 0x60) = Some (Z_to_bv 32 0xfff5c693). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_64 : fetch_word segs (pcw b 0x64) = Some (Z_to_bv 32 0x26c6e863). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_68 : fetch_word segs (pcw b 0x68) = Some (Z_to_bv 32 0xfbf60b13). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_6c : fetch_word segs (pcw b 0x6c) = Some (Z_to_bv 32 0xfbf00693). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_70 : fetch_word segs (pcw b 0x70) = Some (Z_to_bv 32 0x2f66f663). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_7c : fetch_word segs (pcw b 0x7c) = Some (Z_to_bv 32 0x0006b703). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_80 : fetch_word segs (pcw b 0x80) = Some (Z_to_bv 32 0xfff98993). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_84 : fetch_word segs (pcw b 0x84) = Some (Z_to_bv 32 0x0035d693). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_88 : fetch_word segs (pcw b 0x88) = Some (Z_to_bv 32 0x0039d793). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_8c : fetch_word segs (pcw b 0x8c) = Some (Z_to_bv 32 0x00d706b3). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_90 : fetch_word segs (pcw b 0x90) = Some (Z_to_bv 32 0x00f70733). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_94 : fetch_word segs (pcw b 0x94) = Some (Z_to_bv 32 0xff86f793). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_98 : fetch_word segs (pcw b 0x98) = Some (Z_to_bv 32 0xff877813). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_9c : fetch_word segs (pcw b 0x9c) = Some (Z_to_bv 32 0x0007b783). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_a0 : fetch_word segs (pcw b 0xa0) = Some (Z_to_bv 32 0x00083803). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_a4 : fetch_word segs (pcw b 0xa4) = Some (Z_to_bv 32 0x00f867b3). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_a8 : fetch_word segs (pcw b 0xa8) = Some (Z_to_bv 32 0x2a079e63). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_ac : fetch_word segs (pcw b 0xac) = Some (Z_to_bv 32 0xfff54693). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_b0 : fetch_word segs (pcw b 0xb0) = Some (Z_to_bv 32 0x0cc6ee63). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_b4 : fetch_word segs (pcw b 0xb4) = Some (Z_to_bv 32 0xfbf00693). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_b8 : fetch_word segs (pcw b 0xb8) = Some (Z_to_bv 32 0x1566fc63). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_c4 : fetch_word segs (pcw b 0xc4) = Some (Z_to_bv 32 0x0006b703). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_c8 : fetch_word segs (pcw b 0xc8) = Some (Z_to_bv 32 0xfffa0a13). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_cc : fetch_word segs (pcw b 0xcc) = Some (Z_to_bv 32 0x00355693). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_d0 : fetch_word segs (pcw b 0xd0) = Some (Z_to_bv 32 0x003a5793). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_d4 : fetch_word segs (pcw b 0xd4) = Some (Z_to_bv 32 0x00d706b3). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_d8 : fetch_word segs (pcw b 0xd8) = Some (Z_to_bv 32 0x00f70733). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_dc : fetch_word segs (pcw b 0xdc) = Some (Z_to_bv 32 0xff86f793). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_e0 : fetch_word segs (pcw b 0xe0) = Some (Z_to_bv 32 0xff877813). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_e4 : fetch_word segs (pcw b 0xe4) = Some (Z_to_bv 32 0x0007b783). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_e8 : fetch_word segs (pcw b 0xe8) = Some (Z_to_bv 32 0x00083803). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_ec : fetch_word segs (pcw b 0xec) = Some (Z_to_bv 32 0x00f867b3). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_f0 : fetch_word segs (pcw b 0xf0) = Some (Z_to_bv 32 0x36079a63). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_fc : fetch_word segs (pcw b 0xfc) = Some (Z_to_bv 32 0x000680e7). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_100 : fetch_word segs (pcw b 0x100) = Some (Z_to_bv 32 0x08010113). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_104 : fetch_word segs (pcw b 0x104) = Some (Z_to_bv 32 0x7e813083). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_108 : fetch_word segs (pcw b 0x108) = Some (Z_to_bv 32 0x7e013403). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_10c : fetch_word segs (pcw b 0x10c) = Some (Z_to_bv 32 0x7d813483). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_110 : fetch_word segs (pcw b 0x110) = Some (Z_to_bv 32 0x7d013903). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_114 : fetch_word segs (pcw b 0x114) = Some (Z_to_bv 32 0x7c813983). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_118 : fetch_word segs (pcw b 0x118) = Some (Z_to_bv 32 0x7c013a03). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_11c : fetch_word segs (pcw b 0x11c) = Some (Z_to_bv 32 0x7b813a83). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_120 : fetch_word segs (pcw b 0x120) = Some (Z_to_bv 32 0x7b013b03). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_124 : fetch_word segs (pcw b 0x124) = Some (Z_to_bv 32 0x7a813b83). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_128 : fetch_word segs (pcw b 0x128) = Some (Z_to_bv 32 0x7a013c03). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_12c : fetch_word segs (pcw b 0x12c) = Some (Z_to_bv 32 0x7f010113). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_130 : fetch_word segs (pcw b 0x130) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_35c : fetch_word segs (pcw b 0x35c) = Some (Z_to_bv 32 0x02061e63). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_360 : fetch_word segs (pcw b 0x360) = Some (Z_to_bv 32 0xd4dff06f). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_398 : fetch_word segs (pcw b 0x398) = Some (Z_to_bv 32 0x00050b93). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_39c : fetch_word segs (pcw b 0x39c) = Some (Z_to_bv 32 0x00058513). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_3a0 : fetch_word segs (pcw b 0x3a0) = Some (Z_to_bv 32 0x00058c13). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_3a4 : fetch_word segs (pcw b 0x3a4) = Some (Z_to_bv 32 0x00060593). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_3a8 : fetch_word segs (pcw b 0x3a8) = Some (Z_to_bv 32 0x00060493). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_3b0 : fetch_word segs (pcw b 0x3b0) = Some (Z_to_bv 32 0x000c0593). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_3b4 : fetch_word segs (pcw b 0x3b4) = Some (Z_to_bv 32 0x00048613). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_3b8 : fetch_word segs (pcw b 0x3b8) = Some (Z_to_bv 32 0x00050913). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_3bc : fetch_word segs (pcw b 0x3bc) = Some (Z_to_bv 32 0x000b8513). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_3c0 : fetch_word segs (pcw b 0x3c0) = Some (Z_to_bv 32 0xce0906e3). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_210 : fetch_word segs (pcw b 0x210) = Some (Z_to_bv 32 0x28061463). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_214 : fetch_word segs (pcw b 0x214) = Some (Z_to_bv 32 0xee1ff06f). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_498 : fetch_word segs (pcw b 0x498) = Some (Z_to_bv 32 0x00050493). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_49c : fetch_word segs (pcw b 0x49c) = Some (Z_to_bv 32 0x00058b13). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_4a0 : fetch_word segs (pcw b 0x4a0) = Some (Z_to_bv 32 0x00060593). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_4a4 : fetch_word segs (pcw b 0x4a4) = Some (Z_to_bv 32 0x00060913). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_4ac : fetch_word segs (pcw b 0x4ac) = Some (Z_to_bv 32 0x000b0593). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_4b0 : fetch_word segs (pcw b 0x4b0) = Some (Z_to_bv 32 0x00090613). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_4b4 : fetch_word segs (pcw b 0x4b4) = Some (Z_to_bv 32 0x00050993). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_4b8 : fetch_word segs (pcw b 0x4b8) = Some (Z_to_bv 32 0x00048513). Proof. fw. Qed.   (* [comment removed for export] *)
Lemma FA_4bc : fetch_word segs (pcw b 0x4bc) = Some (Z_to_bv 32 0xc2098ce3). Proof. fw. Qed.   (* [comment removed for export] *)

End AmcFetch.
