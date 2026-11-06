(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec CatExec SeqExec StoreOk ShapeAlg ShapeAlgCfg RefMemcpyLib.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanWMemset AsanWMemcpy AsanWMcStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Definition MCF_WORDS : list (Z * Z) :=
  [(0x8, 0x02060e63); (0xc, 0x00158713); (0x10, 0x00100793); (0x14, 0x00050693); (0x18, 0x0005c883);
   (0x1c, 0x00060813); (0x20, 0x00158593); (0x24, 0x00377293); (0x28, 0x01168023); (0x2c, 0x00168693);
   (0x30, 0xfff60613); (0x34, 0x00028a63); (0x38, 0x00170713); (0x3c, 0xfcf81ee3); (0x40, 0x0080006f);
   (0x44, 0x00050693); (0x48, 0x0036f793); (0x4c, 0x0c078a63); (0x50, 0x02000713); (0x54, 0x02e67063);
   (0x58, 0x01000713); (0x5c, 0x24e67863); (0x60, 0x00867713); (0x64, 0x2c071e63); (0x68, 0x00467713);
   (0x6c, 0x32071463); (0x70, 0x3500006f); (0x74, 0x0005a703); (0x78, 0x00300813); (0x7c, 0x11078e63);
   (0x80, 0x00200813); (0x84, 0x19079c63); (0x88, 0x00875793); (0x8c, 0xffe60613); (0x90, 0x00e68023);
   (0x94, 0x00f680a3); (0x98, 0x00268693); (0x9c, 0x01058593); (0xa0, 0x01100793); (0xa4, 0x0107581b);
   (0xa8, 0xff45a883); (0xac, 0xff85a283); (0xb0, 0xffc5a303); (0xb4, 0x0005a703); (0xb8, 0x01089393);
   (0xbc, 0x0108d89b); (0xc0, 0x0103e833); (0xc4, 0x01029393); (0xc8, 0x0102d29b); (0xcc, 0x0113e8b3);
   (0xd0, 0x01031393); (0xd4, 0x0103531b); (0xd8, 0x0053e2b3); (0xdc, 0x01071393); (0xe0, 0x0063e333);
   (0xe4, 0xff060613); (0xe8, 0x0106a023); (0xec, 0x0116a223); (0xf0, 0x0056a423); (0xf4, 0x0066a623);
   (0xf8, 0x01068693); (0xfc, 0x01058593); (0x100, 0xfac7e2e3); (0x104, 0xff258593); (0x108, 0x01000713);
   (0x10c, 0xf4e66ae3); (0x110, 0x19c0006f); (0x198, 0x00e68023); (0x19c, 0x00168693); (0x1a0, 0xfff60613);
   (0x1a4, 0x01058593); (0x1a8, 0x01200793); (0x1ac, 0x0087581b); (0x1b0, 0xff45a883); (0x1b4, 0xff85a283);
   (0x1b8, 0xffc5a303); (0x1bc, 0x0005a703); (0x1c0, 0x01889393); (0x1c4, 0x0088d89b); (0x1c8, 0x0103e833);
   (0x1cc, 0x01829393); (0x1d0, 0x0082d29b); (0x1d4, 0x0113e8b3); (0x1d8, 0x01831393); (0x1dc, 0x0083531b);
   (0x1e0, 0x0053e2b3); (0x1e4, 0x01871393); (0x1e8, 0x0063e333); (0x1ec, 0xff060613); (0x1f0, 0x0106a023);
   (0x1f4, 0x0116a223); (0x1f8, 0x0056a423); (0x1fc, 0x0066a623); (0x200, 0x01068693); (0x204, 0x01058593);
   (0x208, 0xfac7e2e3); (0x20c, 0xff158593); (0x210, 0x01000713); (0x214, 0xe4e666e3); (0x218, 0x0940006f);
   (0x21c, 0x00875793); (0x220, 0x01075813); (0x224, 0xffd60613); (0x228, 0x00e68023); (0x22c, 0x00f680a3);
   (0x230, 0x01068123); (0x234, 0x00368693); (0x238, 0x01058593); (0x23c, 0x01000793); (0x240, 0x0187581b);
   (0x244, 0xff45a883); (0x248, 0xff85a283); (0x24c, 0xffc5a303); (0x250, 0x0005a703); (0x254, 0x00889393);
   (0x258, 0x0188d89b); (0x25c, 0x0103e833); (0x260, 0x00829393); (0x264, 0x0182d29b); (0x268, 0x0113e8b3);
   (0x26c, 0x00831393); (0x270, 0x0183531b); (0x274, 0x0053e2b3); (0x278, 0x00871393); (0x27c, 0x0063e333);
   (0x280, 0xff060613); (0x284, 0x0106a023); (0x288, 0x0116a223); (0x28c, 0x0056a423); (0x290, 0x0066a623);
   (0x294, 0x01068693); (0x298, 0x01058593); (0x29c, 0xfac7e2e3); (0x2a0, 0xff358593); (0x2a4, 0x01000713);
   (0x2a8, 0xdae66ce3); (0x2ac, 0x0005c703); (0x2b0, 0x0015c783); (0x2b4, 0x0025c803); (0x2b8, 0x0035c883);
   (0x2bc, 0x0045c283); (0x2c0, 0x0055c303); (0x2c4, 0x0065c383); (0x2c8, 0x0075ce03); (0x2cc, 0x00e68023);
   (0x2d0, 0x00f680a3); (0x2d4, 0x01068123); (0x2d8, 0x011681a3); (0x2dc, 0x0085c703); (0x2e0, 0x0095c783);
   (0x2e4, 0x00a5c803); (0x2e8, 0x00b5c883); (0x2ec, 0x00568223); (0x2f0, 0x006682a3); (0x2f4, 0x00768323);
   (0x2f8, 0x01c683a3); (0x2fc, 0x00c5c283); (0x300, 0x00d5c303); (0x304, 0x00e5c383); (0x308, 0x00f5ce03);
   (0x30c, 0x01058593); (0x310, 0x00e68423); (0x314, 0x00f684a3); (0x318, 0x01068523); (0x31c, 0x011685a3);
   (0x320, 0x01068713); (0x324, 0x00568623); (0x328, 0x006686a3); (0x32c, 0x00768723); (0x330, 0x01c687a3);
   (0x334, 0x00070693); (0x338, 0x00867713); (0x33c, 0xd20706e3); (0x340, 0x0005c703); (0x344, 0x0015c783);
   (0x348, 0x0025c803); (0x34c, 0x0035c883); (0x350, 0x0045c283); (0x354, 0x0055c303); (0x358, 0x0065c383);
   (0x35c, 0x0075ce03); (0x360, 0x00858593); (0x364, 0x00e68023); (0x368, 0x00f680a3); (0x36c, 0x01068123);
   (0x370, 0x011681a3); (0x374, 0x00868713); (0x378, 0x00568223); (0x37c, 0x006682a3); (0x380, 0x00768323);
   (0x384, 0x01c683a3); (0x388, 0x00070693); (0x38c, 0x00467713); (0x390, 0x02070863); (0x394, 0x0005c703);
   (0x398, 0x0015c783); (0x39c, 0x0025c803); (0x3a0, 0x0035c883); (0x3a4, 0x00458593); (0x3a8, 0x00468293);
   (0x3ac, 0x00e68023); (0x3b0, 0x00f680a3); (0x3b4, 0x01068123); (0x3b8, 0x011681a3); (0x3bc, 0x00028693)]%Z.

Record MCFCode (segs : list Segment) (e : Z) : Prop := {
  mcf_al : MCCode segs e;
  mcf_W : words_ok segs e MCF_WORDS = true
}.

Lemma words_get' : forall segs base ws (o w : Z),
  words_ok segs base ws = true -> existsb (fun ow => (Z.eqb (fst ow) o && Z.eqb (snd ow) w)%bool) ws = true ->
  (0 <= w < 2 ^ 32)%Z -> fetch_word segs (Z_to_bv 64 (base + o)) = Some (Z_to_bv 32 w).
Proof.
  intros segs base ws o w H Hin Hw. apply (words_get segs base ws); [exact H | | exact Hw].
  apply existsb_exists in Hin. destruct Hin as ([o' w'] & Hi & E). cbn [fst snd] in E.
  apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst. exact Hi.
Qed.

Local Ltac dec := wdec.
Lemma DW_02060e63 : decode_any (Z_to_bv 32 0x02060e63) = Some (Branch BC_EQ 12 0 60, 4%Z). Proof. dec. Qed.
Lemma DW_00158713 : decode_any (Z_to_bv 32 0x00158713) = Some (OpImm ALU_ADD 14 11 1, 4%Z). Proof. dec. Qed.
Lemma DW_00100793 : decode_any (Z_to_bv 32 0x00100793) = Some (OpImm ALU_ADD 15 0 1, 4%Z). Proof. dec. Qed.
Lemma DW_00050693 : decode_any (Z_to_bv 32 0x00050693) = Some (OpImm ALU_ADD 13 10 0, 4%Z). Proof. dec. Qed.
Lemma DW_0005c883 : decode_any (Z_to_bv 32 0x0005c883) = Some (Load SZ1 false 17 11 0, 4%Z). Proof. dec. Qed.
Lemma DW_00060813 : decode_any (Z_to_bv 32 0x00060813) = Some (OpImm ALU_ADD 16 12 0, 4%Z). Proof. dec. Qed.
Lemma DW_00158593 : decode_any (Z_to_bv 32 0x00158593) = Some (OpImm ALU_ADD 11 11 1, 4%Z). Proof. dec. Qed.
Lemma DW_00377293 : decode_any (Z_to_bv 32 0x00377293) = Some (OpImm ALU_AND 5 14 3, 4%Z). Proof. dec. Qed.
Lemma DW_01168023 : decode_any (Z_to_bv 32 0x01168023) = Some (Store SZ1 13 17 0, 4%Z). Proof. dec. Qed.
Lemma DW_00168693 : decode_any (Z_to_bv 32 0x00168693) = Some (OpImm ALU_ADD 13 13 1, 4%Z). Proof. dec. Qed.
Lemma DW_fff60613 : decode_any (Z_to_bv 32 0xfff60613) = Some (OpImm ALU_ADD 12 12 4095, 4%Z). Proof. dec. Qed.
Lemma DW_00028a63 : decode_any (Z_to_bv 32 0x00028a63) = Some (Branch BC_EQ 5 0 20, 4%Z). Proof. dec. Qed.
Lemma DW_00170713 : decode_any (Z_to_bv 32 0x00170713) = Some (OpImm ALU_ADD 14 14 1, 4%Z). Proof. dec. Qed.
Lemma DW_fcf81ee3 : decode_any (Z_to_bv 32 0xfcf81ee3) = Some (Branch BC_NE 16 15 8156, 4%Z). Proof. dec. Qed.
Lemma DW_0080006f : decode_any (Z_to_bv 32 0x0080006f) = Some (Jal 0 8, 4%Z). Proof. dec. Qed.
Lemma DW_0036f793 : decode_any (Z_to_bv 32 0x0036f793) = Some (OpImm ALU_AND 15 13 3, 4%Z). Proof. dec. Qed.
Lemma DW_0c078a63 : decode_any (Z_to_bv 32 0x0c078a63) = Some (Branch BC_EQ 15 0 212, 4%Z). Proof. dec. Qed.
Lemma DW_02000713 : decode_any (Z_to_bv 32 0x02000713) = Some (OpImm ALU_ADD 14 0 32, 4%Z). Proof. dec. Qed.
Lemma DW_02e67063 : decode_any (Z_to_bv 32 0x02e67063) = Some (Branch BC_GEU 12 14 32, 4%Z). Proof. dec. Qed.
Lemma DW_01000713 : decode_any (Z_to_bv 32 0x01000713) = Some (OpImm ALU_ADD 14 0 16, 4%Z). Proof. dec. Qed.
Lemma DW_24e67863 : decode_any (Z_to_bv 32 0x24e67863) = Some (Branch BC_GEU 12 14 592, 4%Z). Proof. dec. Qed.
Lemma DW_00867713 : decode_any (Z_to_bv 32 0x00867713) = Some (OpImm ALU_AND 14 12 8, 4%Z). Proof. dec. Qed.
Lemma DW_2c071e63 : decode_any (Z_to_bv 32 0x2c071e63) = Some (Branch BC_NE 14 0 732, 4%Z). Proof. dec. Qed.
Lemma DW_00467713 : decode_any (Z_to_bv 32 0x00467713) = Some (OpImm ALU_AND 14 12 4, 4%Z). Proof. dec. Qed.
Lemma DW_32071463 : decode_any (Z_to_bv 32 0x32071463) = Some (Branch BC_NE 14 0 808, 4%Z). Proof. dec. Qed.
Lemma DW_3500006f : decode_any (Z_to_bv 32 0x3500006f) = Some (Jal 0 848, 4%Z). Proof. dec. Qed.
Lemma DW_0005a703 : decode_any (Z_to_bv 32 0x0005a703) = Some (Load SZ4 true 14 11 0, 4%Z). Proof. dec. Qed.
Lemma DW_00300813 : decode_any (Z_to_bv 32 0x00300813) = Some (OpImm ALU_ADD 16 0 3, 4%Z). Proof. dec. Qed.
Lemma DW_11078e63 : decode_any (Z_to_bv 32 0x11078e63) = Some (Branch BC_EQ 15 16 284, 4%Z). Proof. dec. Qed.
Lemma DW_00200813 : decode_any (Z_to_bv 32 0x00200813) = Some (OpImm ALU_ADD 16 0 2, 4%Z). Proof. dec. Qed.
Lemma DW_19079c63 : decode_any (Z_to_bv 32 0x19079c63) = Some (Branch BC_NE 15 16 408, 4%Z). Proof. dec. Qed.
Lemma DW_00875793 : decode_any (Z_to_bv 32 0x00875793) = Some (ShiftImm ALU_SRL 15 14 8, 4%Z). Proof. dec. Qed.
Lemma DW_ffe60613 : decode_any (Z_to_bv 32 0xffe60613) = Some (OpImm ALU_ADD 12 12 4094, 4%Z). Proof. dec. Qed.
Lemma DW_00e68023 : decode_any (Z_to_bv 32 0x00e68023) = Some (Store SZ1 13 14 0, 4%Z). Proof. dec. Qed.
Lemma DW_00f680a3 : decode_any (Z_to_bv 32 0x00f680a3) = Some (Store SZ1 13 15 1, 4%Z). Proof. dec. Qed.
Lemma DW_00268693 : decode_any (Z_to_bv 32 0x00268693) = Some (OpImm ALU_ADD 13 13 2, 4%Z). Proof. dec. Qed.
Lemma DW_01058593 : decode_any (Z_to_bv 32 0x01058593) = Some (OpImm ALU_ADD 11 11 16, 4%Z). Proof. dec. Qed.
Lemma DW_01100793 : decode_any (Z_to_bv 32 0x01100793) = Some (OpImm ALU_ADD 15 0 17, 4%Z). Proof. dec. Qed.
Lemma DW_0107581b : decode_any (Z_to_bv 32 0x0107581b) = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z). Proof. dec. Qed.
Lemma DW_ff45a883 : decode_any (Z_to_bv 32 0xff45a883) = Some (Load SZ4 true 17 11 4084, 4%Z). Proof. dec. Qed.
Lemma DW_ff85a283 : decode_any (Z_to_bv 32 0xff85a283) = Some (Load SZ4 true 5 11 4088, 4%Z). Proof. dec. Qed.
Lemma DW_ffc5a303 : decode_any (Z_to_bv 32 0xffc5a303) = Some (Load SZ4 true 6 11 4092, 4%Z). Proof. dec. Qed.
Lemma DW_01089393 : decode_any (Z_to_bv 32 0x01089393) = Some (ShiftImm ALU_SLL 7 17 16, 4%Z). Proof. dec. Qed.
Lemma DW_0108d89b : decode_any (Z_to_bv 32 0x0108d89b) = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z). Proof. dec. Qed.
Lemma DW_0103e833 : decode_any (Z_to_bv 32 0x0103e833) = Some (Op ALU_OR 16 7 16, 4%Z). Proof. dec. Qed.
Lemma DW_01029393 : decode_any (Z_to_bv 32 0x01029393) = Some (ShiftImm ALU_SLL 7 5 16, 4%Z). Proof. dec. Qed.
Lemma DW_0102d29b : decode_any (Z_to_bv 32 0x0102d29b) = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z). Proof. dec. Qed.
Lemma DW_0113e8b3 : decode_any (Z_to_bv 32 0x0113e8b3) = Some (Op ALU_OR 17 7 17, 4%Z). Proof. dec. Qed.
Lemma DW_01031393 : decode_any (Z_to_bv 32 0x01031393) = Some (ShiftImm ALU_SLL 7 6 16, 4%Z). Proof. dec. Qed.
Lemma DW_0103531b : decode_any (Z_to_bv 32 0x0103531b) = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z). Proof. dec. Qed.
Lemma DW_0053e2b3 : decode_any (Z_to_bv 32 0x0053e2b3) = Some (Op ALU_OR 5 7 5, 4%Z). Proof. dec. Qed.
Lemma DW_01071393 : decode_any (Z_to_bv 32 0x01071393) = Some (ShiftImm ALU_SLL 7 14 16, 4%Z). Proof. dec. Qed.
Lemma DW_0063e333 : decode_any (Z_to_bv 32 0x0063e333) = Some (Op ALU_OR 6 7 6, 4%Z). Proof. dec. Qed.
Lemma DW_ff060613 : decode_any (Z_to_bv 32 0xff060613) = Some (OpImm ALU_ADD 12 12 4080, 4%Z). Proof. dec. Qed.
Lemma DW_0106a023 : decode_any (Z_to_bv 32 0x0106a023) = Some (Store SZ4 13 16 0, 4%Z). Proof. dec. Qed.
Lemma DW_0116a223 : decode_any (Z_to_bv 32 0x0116a223) = Some (Store SZ4 13 17 4, 4%Z). Proof. dec. Qed.
Lemma DW_0056a423 : decode_any (Z_to_bv 32 0x0056a423) = Some (Store SZ4 13 5 8, 4%Z). Proof. dec. Qed.
Lemma DW_0066a623 : decode_any (Z_to_bv 32 0x0066a623) = Some (Store SZ4 13 6 12, 4%Z). Proof. dec. Qed.
Lemma DW_01068693 : decode_any (Z_to_bv 32 0x01068693) = Some (OpImm ALU_ADD 13 13 16, 4%Z). Proof. dec. Qed.
Lemma DW_fac7e2e3 : decode_any (Z_to_bv 32 0xfac7e2e3) = Some (Branch BC_LTU 15 12 8100, 4%Z). Proof. dec. Qed.
Lemma DW_ff258593 : decode_any (Z_to_bv 32 0xff258593) = Some (OpImm ALU_ADD 11 11 4082, 4%Z). Proof. dec. Qed.
Lemma DW_f4e66ae3 : decode_any (Z_to_bv 32 0xf4e66ae3) = Some (Branch BC_LTU 12 14 8020, 4%Z). Proof. dec. Qed.
Lemma DW_19c0006f : decode_any (Z_to_bv 32 0x19c0006f) = Some (Jal 0 412, 4%Z). Proof. dec. Qed.
Lemma DW_01200793 : decode_any (Z_to_bv 32 0x01200793) = Some (OpImm ALU_ADD 15 0 18, 4%Z). Proof. dec. Qed.
Lemma DW_0087581b : decode_any (Z_to_bv 32 0x0087581b) = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z). Proof. dec. Qed.
Lemma DW_01889393 : decode_any (Z_to_bv 32 0x01889393) = Some (ShiftImm ALU_SLL 7 17 24, 4%Z). Proof. dec. Qed.
Lemma DW_0088d89b : decode_any (Z_to_bv 32 0x0088d89b) = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z). Proof. dec. Qed.
Lemma DW_01829393 : decode_any (Z_to_bv 32 0x01829393) = Some (ShiftImm ALU_SLL 7 5 24, 4%Z). Proof. dec. Qed.
Lemma DW_0082d29b : decode_any (Z_to_bv 32 0x0082d29b) = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z). Proof. dec. Qed.
Lemma DW_01831393 : decode_any (Z_to_bv 32 0x01831393) = Some (ShiftImm ALU_SLL 7 6 24, 4%Z). Proof. dec. Qed.
Lemma DW_0083531b : decode_any (Z_to_bv 32 0x0083531b) = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z). Proof. dec. Qed.
Lemma DW_01871393 : decode_any (Z_to_bv 32 0x01871393) = Some (ShiftImm ALU_SLL 7 14 24, 4%Z). Proof. dec. Qed.
Lemma DW_ff158593 : decode_any (Z_to_bv 32 0xff158593) = Some (OpImm ALU_ADD 11 11 4081, 4%Z). Proof. dec. Qed.
Lemma DW_e4e666e3 : decode_any (Z_to_bv 32 0xe4e666e3) = Some (Branch BC_LTU 12 14 7756, 4%Z). Proof. dec. Qed.
Lemma DW_0940006f : decode_any (Z_to_bv 32 0x0940006f) = Some (Jal 0 148, 4%Z). Proof. dec. Qed.
Lemma DW_01075813 : decode_any (Z_to_bv 32 0x01075813) = Some (ShiftImm ALU_SRL 16 14 16, 4%Z). Proof. dec. Qed.
Lemma DW_ffd60613 : decode_any (Z_to_bv 32 0xffd60613) = Some (OpImm ALU_ADD 12 12 4093, 4%Z). Proof. dec. Qed.
Lemma DW_01068123 : decode_any (Z_to_bv 32 0x01068123) = Some (Store SZ1 13 16 2, 4%Z). Proof. dec. Qed.
Lemma DW_00368693 : decode_any (Z_to_bv 32 0x00368693) = Some (OpImm ALU_ADD 13 13 3, 4%Z). Proof. dec. Qed.
Lemma DW_01000793 : decode_any (Z_to_bv 32 0x01000793) = Some (OpImm ALU_ADD 15 0 16, 4%Z). Proof. dec. Qed.
Lemma DW_0187581b : decode_any (Z_to_bv 32 0x0187581b) = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z). Proof. dec. Qed.
Lemma DW_00889393 : decode_any (Z_to_bv 32 0x00889393) = Some (ShiftImm ALU_SLL 7 17 8, 4%Z). Proof. dec. Qed.
Lemma DW_0188d89b : decode_any (Z_to_bv 32 0x0188d89b) = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z). Proof. dec. Qed.
Lemma DW_00829393 : decode_any (Z_to_bv 32 0x00829393) = Some (ShiftImm ALU_SLL 7 5 8, 4%Z). Proof. dec. Qed.
Lemma DW_0182d29b : decode_any (Z_to_bv 32 0x0182d29b) = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z). Proof. dec. Qed.
Lemma DW_00831393 : decode_any (Z_to_bv 32 0x00831393) = Some (ShiftImm ALU_SLL 7 6 8, 4%Z). Proof. dec. Qed.
Lemma DW_0183531b : decode_any (Z_to_bv 32 0x0183531b) = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z). Proof. dec. Qed.
Lemma DW_00871393 : decode_any (Z_to_bv 32 0x00871393) = Some (ShiftImm ALU_SLL 7 14 8, 4%Z). Proof. dec. Qed.
Lemma DW_ff358593 : decode_any (Z_to_bv 32 0xff358593) = Some (OpImm ALU_ADD 11 11 4083, 4%Z). Proof. dec. Qed.
Lemma DW_dae66ce3 : decode_any (Z_to_bv 32 0xdae66ce3) = Some (Branch BC_LTU 12 14 7608, 4%Z). Proof. dec. Qed.
Lemma DW_0005c703 : decode_any (Z_to_bv 32 0x0005c703) = Some (Load SZ1 false 14 11 0, 4%Z). Proof. dec. Qed.
Lemma DW_0015c783 : decode_any (Z_to_bv 32 0x0015c783) = Some (Load SZ1 false 15 11 1, 4%Z). Proof. dec. Qed.
Lemma DW_0025c803 : decode_any (Z_to_bv 32 0x0025c803) = Some (Load SZ1 false 16 11 2, 4%Z). Proof. dec. Qed.
Lemma DW_0035c883 : decode_any (Z_to_bv 32 0x0035c883) = Some (Load SZ1 false 17 11 3, 4%Z). Proof. dec. Qed.
Lemma DW_0045c283 : decode_any (Z_to_bv 32 0x0045c283) = Some (Load SZ1 false 5 11 4, 4%Z). Proof. dec. Qed.
Lemma DW_0055c303 : decode_any (Z_to_bv 32 0x0055c303) = Some (Load SZ1 false 6 11 5, 4%Z). Proof. dec. Qed.
Lemma DW_0065c383 : decode_any (Z_to_bv 32 0x0065c383) = Some (Load SZ1 false 7 11 6, 4%Z). Proof. dec. Qed.
Lemma DW_0075ce03 : decode_any (Z_to_bv 32 0x0075ce03) = Some (Load SZ1 false 28 11 7, 4%Z). Proof. dec. Qed.
Lemma DW_011681a3 : decode_any (Z_to_bv 32 0x011681a3) = Some (Store SZ1 13 17 3, 4%Z). Proof. dec. Qed.
Lemma DW_0085c703 : decode_any (Z_to_bv 32 0x0085c703) = Some (Load SZ1 false 14 11 8, 4%Z). Proof. dec. Qed.
Lemma DW_0095c783 : decode_any (Z_to_bv 32 0x0095c783) = Some (Load SZ1 false 15 11 9, 4%Z). Proof. dec. Qed.
Lemma DW_00a5c803 : decode_any (Z_to_bv 32 0x00a5c803) = Some (Load SZ1 false 16 11 10, 4%Z). Proof. dec. Qed.
Lemma DW_00b5c883 : decode_any (Z_to_bv 32 0x00b5c883) = Some (Load SZ1 false 17 11 11, 4%Z). Proof. dec. Qed.
Lemma DW_00568223 : decode_any (Z_to_bv 32 0x00568223) = Some (Store SZ1 13 5 4, 4%Z). Proof. dec. Qed.
Lemma DW_006682a3 : decode_any (Z_to_bv 32 0x006682a3) = Some (Store SZ1 13 6 5, 4%Z). Proof. dec. Qed.
Lemma DW_00768323 : decode_any (Z_to_bv 32 0x00768323) = Some (Store SZ1 13 7 6, 4%Z). Proof. dec. Qed.
Lemma DW_01c683a3 : decode_any (Z_to_bv 32 0x01c683a3) = Some (Store SZ1 13 28 7, 4%Z). Proof. dec. Qed.
Lemma DW_00c5c283 : decode_any (Z_to_bv 32 0x00c5c283) = Some (Load SZ1 false 5 11 12, 4%Z). Proof. dec. Qed.
Lemma DW_00d5c303 : decode_any (Z_to_bv 32 0x00d5c303) = Some (Load SZ1 false 6 11 13, 4%Z). Proof. dec. Qed.
Lemma DW_00e5c383 : decode_any (Z_to_bv 32 0x00e5c383) = Some (Load SZ1 false 7 11 14, 4%Z). Proof. dec. Qed.
Lemma DW_00f5ce03 : decode_any (Z_to_bv 32 0x00f5ce03) = Some (Load SZ1 false 28 11 15, 4%Z). Proof. dec. Qed.
Lemma DW_00e68423 : decode_any (Z_to_bv 32 0x00e68423) = Some (Store SZ1 13 14 8, 4%Z). Proof. dec. Qed.
Lemma DW_00f684a3 : decode_any (Z_to_bv 32 0x00f684a3) = Some (Store SZ1 13 15 9, 4%Z). Proof. dec. Qed.
Lemma DW_01068523 : decode_any (Z_to_bv 32 0x01068523) = Some (Store SZ1 13 16 10, 4%Z). Proof. dec. Qed.
Lemma DW_011685a3 : decode_any (Z_to_bv 32 0x011685a3) = Some (Store SZ1 13 17 11, 4%Z). Proof. dec. Qed.
Lemma DW_01068713 : decode_any (Z_to_bv 32 0x01068713) = Some (OpImm ALU_ADD 14 13 16, 4%Z). Proof. dec. Qed.
Lemma DW_00568623 : decode_any (Z_to_bv 32 0x00568623) = Some (Store SZ1 13 5 12, 4%Z). Proof. dec. Qed.
Lemma DW_006686a3 : decode_any (Z_to_bv 32 0x006686a3) = Some (Store SZ1 13 6 13, 4%Z). Proof. dec. Qed.
Lemma DW_00768723 : decode_any (Z_to_bv 32 0x00768723) = Some (Store SZ1 13 7 14, 4%Z). Proof. dec. Qed.
Lemma DW_01c687a3 : decode_any (Z_to_bv 32 0x01c687a3) = Some (Store SZ1 13 28 15, 4%Z). Proof. dec. Qed.
Lemma DW_00070693 : decode_any (Z_to_bv 32 0x00070693) = Some (OpImm ALU_ADD 13 14 0, 4%Z). Proof. dec. Qed.
Lemma DW_d20706e3 : decode_any (Z_to_bv 32 0xd20706e3) = Some (Branch BC_EQ 14 0 7468, 4%Z). Proof. dec. Qed.
Lemma DW_00858593 : decode_any (Z_to_bv 32 0x00858593) = Some (OpImm ALU_ADD 11 11 8, 4%Z). Proof. dec. Qed.
Lemma DW_00868713 : decode_any (Z_to_bv 32 0x00868713) = Some (OpImm ALU_ADD 14 13 8, 4%Z). Proof. dec. Qed.
Lemma DW_02070863 : decode_any (Z_to_bv 32 0x02070863) = Some (Branch BC_EQ 14 0 48, 4%Z). Proof. dec. Qed.
Lemma DW_00458593 : decode_any (Z_to_bv 32 0x00458593) = Some (OpImm ALU_ADD 11 11 4, 4%Z). Proof. dec. Qed.
Lemma DW_00468293 : decode_any (Z_to_bv 32 0x00468293) = Some (OpImm ALU_ADD 5 13 4, 4%Z). Proof. dec. Qed.
Lemma DW_00028693 : decode_any (Z_to_bv 32 0x00028693) = Some (OpImm ALU_ADD 13 5 0, 4%Z). Proof. dec. Qed.

Lemma lw_LWv : forall l, load_word SZ4 true l = LWv l.
Proof.
  intros l. unfold load_word, LWv, v_lw, sext, le_bytes_to_word. apply bv_eq.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned. f_equal.
  unfold bv_signed. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_swrap_wrap.
Qed.

Lemma st4_w2le : forall v, store_bytes SZ4 v = word_to_le_bytes 4 v.
Proof.
  intros v. unfold store_bytes, word_to_le_bytes, low32. rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply (Z_to_le_bytes_wrap 4 32). cbn. lia.
Qed.

Lemma st1_byte : forall v, store_bytes SZ1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof.
  intros v. unfold store_bytes. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
  rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_bv_wrap. lia.
Qed.

Lemma sll_slli : forall v (s : bv 6), alu64 ALU_SLL v (zext 64 s) = v_slli v (bv_unsigned s).
Proof.
  intros v s. unfold alu64, alu, v_slli, zext. apply bv_eq.
  rewrite bv_shiftl_unsigned, Z_to_bv_unsigned, bv_and_unsigned, bv_zero_extend_unsigned by lia.
  f_equal. f_equal. pose proof (bv_unsigned_in_range _ s) as Hs. change (bv_modulus 6) with 64%Z in Hs.
  change (bv_unsigned (Z_to_bv 64 63)) with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma srl_srli : forall v (s : bv 6), alu64 ALU_SRL v (zext 64 s) = v_srli v (bv_unsigned s).
Proof.
  intros v s. unfold alu64, alu, v_srli, zext. apply bv_eq.
  rewrite bv_shiftr_unsigned, Z_to_bv_unsigned, bv_and_unsigned, bv_zero_extend_unsigned by lia.
  pose proof (bv_unsigned_in_range _ s) as Hs. change (bv_modulus 6) with 64%Z in Hs.
  change (bv_unsigned (Z_to_bv 64 63)) with (Z.ones 6). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  symmetry. apply bv_wrap_small. pose proof (bv_unsigned_in_range _ v). split; [apply Z.shiftr_nonneg; lia|].
  rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  change (bv_modulus 64) with (2^64)%Z in *. pose proof (Z.pow_pos_nonneg 2 (bv_unsigned s) ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma srlw_srliw : forall v (s : bv 5), sext 64 (alu32 ALU_SRL (low32 v) (zext 32 s)) = v_srliw v (bv_unsigned s).
Proof.
  intros v s. unfold alu32, alu, v_srliw, zext, sext, low32. apply bv_eq.
  rewrite bv_sign_extend_unsigned, Z_to_bv_unsigned. f_equal. unfold bv_signed. f_equal.
  rewrite bv_shiftr_unsigned, bv_and_unsigned, bv_zero_extend_unsigned, bv_extract_unsigned, Z.shiftr_0_r by lia.
  pose proof (bv_unsigned_in_range _ s) as Hs. change (bv_modulus 5) with 32%Z in Hs.
  change (bv_unsigned (Z_to_bv 32 31)) with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma or_vor : forall a b : word, alu64 ALU_OR a b = v_or a b.
Proof.
  intros a b. unfold alu64, alu, v_or. apply bv_eq. rewrite Z_to_bv_unsigned, <- bv_or_unsigned.
  symmetry. apply bv_wrap_bv_unsigned.
Qed.

Lemma sb_lw0 : forall l, length l = 4%nat -> store_bytes SZ1 (LWv l) = firstn 1 l.
Proof.
  intros l Hl. rewrite st1_byte.
  pose proof (sb_byte_srli_LWv l 0 Hl ltac:(lia)) as H. unfold v_srli in H. rewrite Z.shiftr_0_r, Z_to_bv_bv_unsigned in H.
  rewrite H. destruct l as [|b l]; [cbn in Hl; lia|]. reflexivity.
Qed.

Lemma sb_srli : forall l (q : nat), length l = 4%nat -> (q <= 3)%nat ->
  store_bytes SZ1 (v_srli (LWv l) (8 * Z.of_nat q)) = firstn 1 (skipn q l).
Proof.
  intros l q Hl Hq. rewrite st1_byte, (sb_byte_srli_LWv l q Hl Hq).
  assert (E : forall (l' : list byte) q', (q' < length l')%nat -> firstn 1 (skipn q' l') = [nth q' l' (Z_to_bv 8 0)]).
  { induction l' as [|b l' IH]; intros q' Hq'; [cbn in Hq'; lia|]. destruct q' as [|q']; [reflexivity|].
    cbn [skipn nth]. apply IH. cbn in Hq'. lia. }
  rewrite E by lia. reflexivity.
Qed.

Lemma merge_sub : forall (l : list byte) (j c : nat), (c <= 4)%nat ->
  skipn c (firstn 4 (skipn j l)) ++ firstn c (firstn 4 (skipn (j + 4) l)) = firstn 4 (skipn (j + c) l).
Proof.
  intros l j c Hc. rewrite skipn_firstn_comm, firstn_firstn. replace (Nat.min c 4) with c by lia.
  replace 4%nat with ((4 - c) + c)%nat at 3 by lia. rewrite firstn_add. f_equal.
  - rewrite skipn_skipn. f_equal. f_equal. lia.
  - rewrite !skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma wacc_ShiftImm32 : forall segs ms w isz op rd rs1 (shamt : bv 5),
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm32 op rd rs1 shamt, isz) ->
  RiscvSemantics.step_accesses segs ms =
  MachineOk (@mkAccessReport machine_state (setx ms rd (sext 64 (alu32 op (low32 (rg ms rs1)) (zext 32 shamt)))
                  (ms_pc_val ms + Z_to_bv 64 isz) (ms_resv ms) (ms_mem ms)) []).
Proof.
  intros segs ms w isz op rd rs1 shamt Hfetch Hecall Hdecode.
  wacc_pipeline Hfetch Hecall Hdecode.
  unfold setx, rg; destruct (is_x0 rd); cbv beta iota; reflexivity.
Qed.

Local Ltac r32 r :=
  let H := fresh in
  assert (H : (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9
               \/ r = 10 \/ r = 11 \/ r = 12 \/ r = 13 \/ r = 14 \/ r = 15 \/ r = 16 \/ r = 17 \/ r = 18 \/ r = 19
               \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ r = 28 \/ r = 29
               \/ r = 30 \/ r = 31)%Z) by lia;
  repeat (destruct H as [H|H]; [subst r; vm_compute; intuition discriminate|]); subst r; vm_compute; intuition discriminate.

Lemma c8_0 : forall r, (0 <= r < 32)%Z -> Z.land r 8 = 0%Z -> (r mod 16 = r mod 8 /\ 0 <= r mod 8 < 8)%Z.
Proof. intros r Hr. r32 r. Qed.
Lemma c8_1 : forall r, (0 <= r < 32)%Z -> Z.land r 8 <> 0%Z -> (r mod 16 = 8 + r mod 8 /\ 0 <= r mod 8 < 8)%Z.
Proof. intros r Hr. r32 r. Qed.
Lemma c4_0 : forall r, (0 <= r < 32)%Z -> Z.land r 4 = 0%Z -> (r mod 8 = r mod 4 /\ 0 <= r mod 4 < 4)%Z.
Proof. intros r Hr. r32 r. Qed.
Lemma c4_1 : forall r, (0 <= r < 32)%Z -> Z.land r 4 <> 0%Z -> (r mod 8 = 4 + r mod 4 /\ 0 <= r mod 4 < 4)%Z.
Proof. intros r Hr. r32 r. Qed.
Lemma c16 : forall r, (16 <= r < 32)%Z -> (r mod 16 = r - 16)%Z.
Proof. intros r Hr. symmetry. apply Z.mod_unique with 1%Z; lia. Qed.
Lemma c16s : forall r, (0 <= r < 16)%Z -> (r mod 16 = r)%Z.
Proof. intros r Hr. apply Z.mod_small. lia. Qed.

Definition MCF_CLOB : list reg := [5; 6; 7; 28; 11; 12; 13; 14; 15; 16; 17].

Lemma HCLF : forall r, In r MC_CLOB -> In r MCF_CLOB.
Proof. intros r Hr. cbn [In MC_CLOB MCF_CLOB] in *. intuition. Qed.
Lemma HCL1F : ~ In 1 MCF_CLOB.
Proof. cbn. intuition discriminate. Qed.

Ltac in_litF := cbn [In MCF_CLOB]; repeat first [ left; reflexivity | right ].
Ltac mcf_chain HS :=
  repeat first
   [ (eapply MCR_store; [ | rewrite ?resv_setx; reflexivity ])
   | (eapply MCR_setx; [ | first [ left; reflexivity | right; solve [ in_litF ] ]
                      | rewrite ?resv_setx; reflexivity | rewrite ?mem_setx; reflexivity ]) ];
  exact HS.

Set Default Proof Using "All".

Section MCF.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable e : Z.
Hypothesis HF : MCFCode segs e.

Local Ltac fw := apply (words_get' segs e MCF_WORDS); [exact (mcf_W _ _ HF) | vm_compute; reflexivity | lia].

Lemma FF_8 : fetch_word segs (pcw e 0x8) = Some (Z_to_bv 32 0x02060e63). Proof. fw. Qed.
Lemma FF_c : fetch_word segs (pcw e 0xc) = Some (Z_to_bv 32 0x00158713). Proof. fw. Qed.
Lemma FF_10 : fetch_word segs (pcw e 0x10) = Some (Z_to_bv 32 0x00100793). Proof. fw. Qed.
Lemma FF_14 : fetch_word segs (pcw e 0x14) = Some (Z_to_bv 32 0x00050693). Proof. fw. Qed.
Lemma FF_18 : fetch_word segs (pcw e 0x18) = Some (Z_to_bv 32 0x0005c883). Proof. fw. Qed.
Lemma FF_1c : fetch_word segs (pcw e 0x1c) = Some (Z_to_bv 32 0x00060813). Proof. fw. Qed.
Lemma FF_20 : fetch_word segs (pcw e 0x20) = Some (Z_to_bv 32 0x00158593). Proof. fw. Qed.
Lemma FF_24 : fetch_word segs (pcw e 0x24) = Some (Z_to_bv 32 0x00377293). Proof. fw. Qed.
Lemma FF_28 : fetch_word segs (pcw e 0x28) = Some (Z_to_bv 32 0x01168023). Proof. fw. Qed.
Lemma FF_2c : fetch_word segs (pcw e 0x2c) = Some (Z_to_bv 32 0x00168693). Proof. fw. Qed.
Lemma FF_30 : fetch_word segs (pcw e 0x30) = Some (Z_to_bv 32 0xfff60613). Proof. fw. Qed.
Lemma FF_34 : fetch_word segs (pcw e 0x34) = Some (Z_to_bv 32 0x00028a63). Proof. fw. Qed.
Lemma FF_38 : fetch_word segs (pcw e 0x38) = Some (Z_to_bv 32 0x00170713). Proof. fw. Qed.
Lemma FF_3c : fetch_word segs (pcw e 0x3c) = Some (Z_to_bv 32 0xfcf81ee3). Proof. fw. Qed.
Lemma FF_40 : fetch_word segs (pcw e 0x40) = Some (Z_to_bv 32 0x0080006f). Proof. fw. Qed.
Lemma FF_44 : fetch_word segs (pcw e 0x44) = Some (Z_to_bv 32 0x00050693). Proof. fw. Qed.
Lemma FF_48 : fetch_word segs (pcw e 0x48) = Some (Z_to_bv 32 0x0036f793). Proof. fw. Qed.
Lemma FF_4c : fetch_word segs (pcw e 0x4c) = Some (Z_to_bv 32 0x0c078a63). Proof. fw. Qed.
Lemma FF_50 : fetch_word segs (pcw e 0x50) = Some (Z_to_bv 32 0x02000713). Proof. fw. Qed.
Lemma FF_54 : fetch_word segs (pcw e 0x54) = Some (Z_to_bv 32 0x02e67063). Proof. fw. Qed.
Lemma FF_58 : fetch_word segs (pcw e 0x58) = Some (Z_to_bv 32 0x01000713). Proof. fw. Qed.
Lemma FF_5c : fetch_word segs (pcw e 0x5c) = Some (Z_to_bv 32 0x24e67863). Proof. fw. Qed.
Lemma FF_60 : fetch_word segs (pcw e 0x60) = Some (Z_to_bv 32 0x00867713). Proof. fw. Qed.
Lemma FF_64 : fetch_word segs (pcw e 0x64) = Some (Z_to_bv 32 0x2c071e63). Proof. fw. Qed.
Lemma FF_68 : fetch_word segs (pcw e 0x68) = Some (Z_to_bv 32 0x00467713). Proof. fw. Qed.
Lemma FF_6c : fetch_word segs (pcw e 0x6c) = Some (Z_to_bv 32 0x32071463). Proof. fw. Qed.
Lemma FF_70 : fetch_word segs (pcw e 0x70) = Some (Z_to_bv 32 0x3500006f). Proof. fw. Qed.
Lemma FF_74 : fetch_word segs (pcw e 0x74) = Some (Z_to_bv 32 0x0005a703). Proof. fw. Qed.
Lemma FF_78 : fetch_word segs (pcw e 0x78) = Some (Z_to_bv 32 0x00300813). Proof. fw. Qed.
Lemma FF_7c : fetch_word segs (pcw e 0x7c) = Some (Z_to_bv 32 0x11078e63). Proof. fw. Qed.
Lemma FF_80 : fetch_word segs (pcw e 0x80) = Some (Z_to_bv 32 0x00200813). Proof. fw. Qed.
Lemma FF_84 : fetch_word segs (pcw e 0x84) = Some (Z_to_bv 32 0x19079c63). Proof. fw. Qed.
Lemma FF_88 : fetch_word segs (pcw e 0x88) = Some (Z_to_bv 32 0x00875793). Proof. fw. Qed.
Lemma FF_8c : fetch_word segs (pcw e 0x8c) = Some (Z_to_bv 32 0xffe60613). Proof. fw. Qed.
Lemma FF_90 : fetch_word segs (pcw e 0x90) = Some (Z_to_bv 32 0x00e68023). Proof. fw. Qed.
Lemma FF_94 : fetch_word segs (pcw e 0x94) = Some (Z_to_bv 32 0x00f680a3). Proof. fw. Qed.
Lemma FF_98 : fetch_word segs (pcw e 0x98) = Some (Z_to_bv 32 0x00268693). Proof. fw. Qed.
Lemma FF_9c : fetch_word segs (pcw e 0x9c) = Some (Z_to_bv 32 0x01058593). Proof. fw. Qed.
Lemma FF_a0 : fetch_word segs (pcw e 0xa0) = Some (Z_to_bv 32 0x01100793). Proof. fw. Qed.
Lemma FF_a4 : fetch_word segs (pcw e 0xa4) = Some (Z_to_bv 32 0x0107581b). Proof. fw. Qed.
Lemma FF_a8 : fetch_word segs (pcw e 0xa8) = Some (Z_to_bv 32 0xff45a883). Proof. fw. Qed.
Lemma FF_ac : fetch_word segs (pcw e 0xac) = Some (Z_to_bv 32 0xff85a283). Proof. fw. Qed.
Lemma FF_b0 : fetch_word segs (pcw e 0xb0) = Some (Z_to_bv 32 0xffc5a303). Proof. fw. Qed.
Lemma FF_b4 : fetch_word segs (pcw e 0xb4) = Some (Z_to_bv 32 0x0005a703). Proof. fw. Qed.
Lemma FF_b8 : fetch_word segs (pcw e 0xb8) = Some (Z_to_bv 32 0x01089393). Proof. fw. Qed.
Lemma FF_bc : fetch_word segs (pcw e 0xbc) = Some (Z_to_bv 32 0x0108d89b). Proof. fw. Qed.
Lemma FF_c0 : fetch_word segs (pcw e 0xc0) = Some (Z_to_bv 32 0x0103e833). Proof. fw. Qed.
Lemma FF_c4 : fetch_word segs (pcw e 0xc4) = Some (Z_to_bv 32 0x01029393). Proof. fw. Qed.
Lemma FF_c8 : fetch_word segs (pcw e 0xc8) = Some (Z_to_bv 32 0x0102d29b). Proof. fw. Qed.
Lemma FF_cc : fetch_word segs (pcw e 0xcc) = Some (Z_to_bv 32 0x0113e8b3). Proof. fw. Qed.
Lemma FF_d0 : fetch_word segs (pcw e 0xd0) = Some (Z_to_bv 32 0x01031393). Proof. fw. Qed.
Lemma FF_d4 : fetch_word segs (pcw e 0xd4) = Some (Z_to_bv 32 0x0103531b). Proof. fw. Qed.
Lemma FF_d8 : fetch_word segs (pcw e 0xd8) = Some (Z_to_bv 32 0x0053e2b3). Proof. fw. Qed.
Lemma FF_dc : fetch_word segs (pcw e 0xdc) = Some (Z_to_bv 32 0x01071393). Proof. fw. Qed.
Lemma FF_e0 : fetch_word segs (pcw e 0xe0) = Some (Z_to_bv 32 0x0063e333). Proof. fw. Qed.
Lemma FF_e4 : fetch_word segs (pcw e 0xe4) = Some (Z_to_bv 32 0xff060613). Proof. fw. Qed.
Lemma FF_e8 : fetch_word segs (pcw e 0xe8) = Some (Z_to_bv 32 0x0106a023). Proof. fw. Qed.
Lemma FF_ec : fetch_word segs (pcw e 0xec) = Some (Z_to_bv 32 0x0116a223). Proof. fw. Qed.
Lemma FF_f0 : fetch_word segs (pcw e 0xf0) = Some (Z_to_bv 32 0x0056a423). Proof. fw. Qed.
Lemma FF_f4 : fetch_word segs (pcw e 0xf4) = Some (Z_to_bv 32 0x0066a623). Proof. fw. Qed.
Lemma FF_f8 : fetch_word segs (pcw e 0xf8) = Some (Z_to_bv 32 0x01068693). Proof. fw. Qed.
Lemma FF_fc : fetch_word segs (pcw e 0xfc) = Some (Z_to_bv 32 0x01058593). Proof. fw. Qed.
Lemma FF_100 : fetch_word segs (pcw e 0x100) = Some (Z_to_bv 32 0xfac7e2e3). Proof. fw. Qed.
Lemma FF_104 : fetch_word segs (pcw e 0x104) = Some (Z_to_bv 32 0xff258593). Proof. fw. Qed.
Lemma FF_108 : fetch_word segs (pcw e 0x108) = Some (Z_to_bv 32 0x01000713). Proof. fw. Qed.
Lemma FF_10c : fetch_word segs (pcw e 0x10c) = Some (Z_to_bv 32 0xf4e66ae3). Proof. fw. Qed.
Lemma FF_110 : fetch_word segs (pcw e 0x110) = Some (Z_to_bv 32 0x19c0006f). Proof. fw. Qed.
Lemma FF_198 : fetch_word segs (pcw e 0x198) = Some (Z_to_bv 32 0x00e68023). Proof. fw. Qed.
Lemma FF_19c : fetch_word segs (pcw e 0x19c) = Some (Z_to_bv 32 0x00168693). Proof. fw. Qed.
Lemma FF_1a0 : fetch_word segs (pcw e 0x1a0) = Some (Z_to_bv 32 0xfff60613). Proof. fw. Qed.
Lemma FF_1a4 : fetch_word segs (pcw e 0x1a4) = Some (Z_to_bv 32 0x01058593). Proof. fw. Qed.
Lemma FF_1a8 : fetch_word segs (pcw e 0x1a8) = Some (Z_to_bv 32 0x01200793). Proof. fw. Qed.
Lemma FF_1ac : fetch_word segs (pcw e 0x1ac) = Some (Z_to_bv 32 0x0087581b). Proof. fw. Qed.
Lemma FF_1b0 : fetch_word segs (pcw e 0x1b0) = Some (Z_to_bv 32 0xff45a883). Proof. fw. Qed.
Lemma FF_1b4 : fetch_word segs (pcw e 0x1b4) = Some (Z_to_bv 32 0xff85a283). Proof. fw. Qed.
Lemma FF_1b8 : fetch_word segs (pcw e 0x1b8) = Some (Z_to_bv 32 0xffc5a303). Proof. fw. Qed.
Lemma FF_1bc : fetch_word segs (pcw e 0x1bc) = Some (Z_to_bv 32 0x0005a703). Proof. fw. Qed.
Lemma FF_1c0 : fetch_word segs (pcw e 0x1c0) = Some (Z_to_bv 32 0x01889393). Proof. fw. Qed.
Lemma FF_1c4 : fetch_word segs (pcw e 0x1c4) = Some (Z_to_bv 32 0x0088d89b). Proof. fw. Qed.
Lemma FF_1c8 : fetch_word segs (pcw e 0x1c8) = Some (Z_to_bv 32 0x0103e833). Proof. fw. Qed.
Lemma FF_1cc : fetch_word segs (pcw e 0x1cc) = Some (Z_to_bv 32 0x01829393). Proof. fw. Qed.
Lemma FF_1d0 : fetch_word segs (pcw e 0x1d0) = Some (Z_to_bv 32 0x0082d29b). Proof. fw. Qed.
Lemma FF_1d4 : fetch_word segs (pcw e 0x1d4) = Some (Z_to_bv 32 0x0113e8b3). Proof. fw. Qed.
Lemma FF_1d8 : fetch_word segs (pcw e 0x1d8) = Some (Z_to_bv 32 0x01831393). Proof. fw. Qed.
Lemma FF_1dc : fetch_word segs (pcw e 0x1dc) = Some (Z_to_bv 32 0x0083531b). Proof. fw. Qed.
Lemma FF_1e0 : fetch_word segs (pcw e 0x1e0) = Some (Z_to_bv 32 0x0053e2b3). Proof. fw. Qed.
Lemma FF_1e4 : fetch_word segs (pcw e 0x1e4) = Some (Z_to_bv 32 0x01871393). Proof. fw. Qed.
Lemma FF_1e8 : fetch_word segs (pcw e 0x1e8) = Some (Z_to_bv 32 0x0063e333). Proof. fw. Qed.
Lemma FF_1ec : fetch_word segs (pcw e 0x1ec) = Some (Z_to_bv 32 0xff060613). Proof. fw. Qed.
Lemma FF_1f0 : fetch_word segs (pcw e 0x1f0) = Some (Z_to_bv 32 0x0106a023). Proof. fw. Qed.
Lemma FF_1f4 : fetch_word segs (pcw e 0x1f4) = Some (Z_to_bv 32 0x0116a223). Proof. fw. Qed.
Lemma FF_1f8 : fetch_word segs (pcw e 0x1f8) = Some (Z_to_bv 32 0x0056a423). Proof. fw. Qed.
Lemma FF_1fc : fetch_word segs (pcw e 0x1fc) = Some (Z_to_bv 32 0x0066a623). Proof. fw. Qed.
Lemma FF_200 : fetch_word segs (pcw e 0x200) = Some (Z_to_bv 32 0x01068693). Proof. fw. Qed.
Lemma FF_204 : fetch_word segs (pcw e 0x204) = Some (Z_to_bv 32 0x01058593). Proof. fw. Qed.
Lemma FF_208 : fetch_word segs (pcw e 0x208) = Some (Z_to_bv 32 0xfac7e2e3). Proof. fw. Qed.
Lemma FF_20c : fetch_word segs (pcw e 0x20c) = Some (Z_to_bv 32 0xff158593). Proof. fw. Qed.
Lemma FF_210 : fetch_word segs (pcw e 0x210) = Some (Z_to_bv 32 0x01000713). Proof. fw. Qed.
Lemma FF_214 : fetch_word segs (pcw e 0x214) = Some (Z_to_bv 32 0xe4e666e3). Proof. fw. Qed.
Lemma FF_218 : fetch_word segs (pcw e 0x218) = Some (Z_to_bv 32 0x0940006f). Proof. fw. Qed.
Lemma FF_21c : fetch_word segs (pcw e 0x21c) = Some (Z_to_bv 32 0x00875793). Proof. fw. Qed.
Lemma FF_220 : fetch_word segs (pcw e 0x220) = Some (Z_to_bv 32 0x01075813). Proof. fw. Qed.
Lemma FF_224 : fetch_word segs (pcw e 0x224) = Some (Z_to_bv 32 0xffd60613). Proof. fw. Qed.
Lemma FF_228 : fetch_word segs (pcw e 0x228) = Some (Z_to_bv 32 0x00e68023). Proof. fw. Qed.
Lemma FF_22c : fetch_word segs (pcw e 0x22c) = Some (Z_to_bv 32 0x00f680a3). Proof. fw. Qed.
Lemma FF_230 : fetch_word segs (pcw e 0x230) = Some (Z_to_bv 32 0x01068123). Proof. fw. Qed.
Lemma FF_234 : fetch_word segs (pcw e 0x234) = Some (Z_to_bv 32 0x00368693). Proof. fw. Qed.
Lemma FF_238 : fetch_word segs (pcw e 0x238) = Some (Z_to_bv 32 0x01058593). Proof. fw. Qed.
Lemma FF_23c : fetch_word segs (pcw e 0x23c) = Some (Z_to_bv 32 0x01000793). Proof. fw. Qed.
Lemma FF_240 : fetch_word segs (pcw e 0x240) = Some (Z_to_bv 32 0x0187581b). Proof. fw. Qed.
Lemma FF_244 : fetch_word segs (pcw e 0x244) = Some (Z_to_bv 32 0xff45a883). Proof. fw. Qed.
Lemma FF_248 : fetch_word segs (pcw e 0x248) = Some (Z_to_bv 32 0xff85a283). Proof. fw. Qed.
Lemma FF_24c : fetch_word segs (pcw e 0x24c) = Some (Z_to_bv 32 0xffc5a303). Proof. fw. Qed.
Lemma FF_250 : fetch_word segs (pcw e 0x250) = Some (Z_to_bv 32 0x0005a703). Proof. fw. Qed.
Lemma FF_254 : fetch_word segs (pcw e 0x254) = Some (Z_to_bv 32 0x00889393). Proof. fw. Qed.
Lemma FF_258 : fetch_word segs (pcw e 0x258) = Some (Z_to_bv 32 0x0188d89b). Proof. fw. Qed.
Lemma FF_25c : fetch_word segs (pcw e 0x25c) = Some (Z_to_bv 32 0x0103e833). Proof. fw. Qed.
Lemma FF_260 : fetch_word segs (pcw e 0x260) = Some (Z_to_bv 32 0x00829393). Proof. fw. Qed.
Lemma FF_264 : fetch_word segs (pcw e 0x264) = Some (Z_to_bv 32 0x0182d29b). Proof. fw. Qed.
Lemma FF_268 : fetch_word segs (pcw e 0x268) = Some (Z_to_bv 32 0x0113e8b3). Proof. fw. Qed.
Lemma FF_26c : fetch_word segs (pcw e 0x26c) = Some (Z_to_bv 32 0x00831393). Proof. fw. Qed.
Lemma FF_270 : fetch_word segs (pcw e 0x270) = Some (Z_to_bv 32 0x0183531b). Proof. fw. Qed.
Lemma FF_274 : fetch_word segs (pcw e 0x274) = Some (Z_to_bv 32 0x0053e2b3). Proof. fw. Qed.
Lemma FF_278 : fetch_word segs (pcw e 0x278) = Some (Z_to_bv 32 0x00871393). Proof. fw. Qed.
Lemma FF_27c : fetch_word segs (pcw e 0x27c) = Some (Z_to_bv 32 0x0063e333). Proof. fw. Qed.
Lemma FF_280 : fetch_word segs (pcw e 0x280) = Some (Z_to_bv 32 0xff060613). Proof. fw. Qed.
Lemma FF_284 : fetch_word segs (pcw e 0x284) = Some (Z_to_bv 32 0x0106a023). Proof. fw. Qed.
Lemma FF_288 : fetch_word segs (pcw e 0x288) = Some (Z_to_bv 32 0x0116a223). Proof. fw. Qed.
Lemma FF_28c : fetch_word segs (pcw e 0x28c) = Some (Z_to_bv 32 0x0056a423). Proof. fw. Qed.
Lemma FF_290 : fetch_word segs (pcw e 0x290) = Some (Z_to_bv 32 0x0066a623). Proof. fw. Qed.
Lemma FF_294 : fetch_word segs (pcw e 0x294) = Some (Z_to_bv 32 0x01068693). Proof. fw. Qed.
Lemma FF_298 : fetch_word segs (pcw e 0x298) = Some (Z_to_bv 32 0x01058593). Proof. fw. Qed.
Lemma FF_29c : fetch_word segs (pcw e 0x29c) = Some (Z_to_bv 32 0xfac7e2e3). Proof. fw. Qed.
Lemma FF_2a0 : fetch_word segs (pcw e 0x2a0) = Some (Z_to_bv 32 0xff358593). Proof. fw. Qed.
Lemma FF_2a4 : fetch_word segs (pcw e 0x2a4) = Some (Z_to_bv 32 0x01000713). Proof. fw. Qed.
Lemma FF_2a8 : fetch_word segs (pcw e 0x2a8) = Some (Z_to_bv 32 0xdae66ce3). Proof. fw. Qed.
Lemma FF_2ac : fetch_word segs (pcw e 0x2ac) = Some (Z_to_bv 32 0x0005c703). Proof. fw. Qed.
Lemma FF_2b0 : fetch_word segs (pcw e 0x2b0) = Some (Z_to_bv 32 0x0015c783). Proof. fw. Qed.
Lemma FF_2b4 : fetch_word segs (pcw e 0x2b4) = Some (Z_to_bv 32 0x0025c803). Proof. fw. Qed.
Lemma FF_2b8 : fetch_word segs (pcw e 0x2b8) = Some (Z_to_bv 32 0x0035c883). Proof. fw. Qed.
Lemma FF_2bc : fetch_word segs (pcw e 0x2bc) = Some (Z_to_bv 32 0x0045c283). Proof. fw. Qed.
Lemma FF_2c0 : fetch_word segs (pcw e 0x2c0) = Some (Z_to_bv 32 0x0055c303). Proof. fw. Qed.
Lemma FF_2c4 : fetch_word segs (pcw e 0x2c4) = Some (Z_to_bv 32 0x0065c383). Proof. fw. Qed.
Lemma FF_2c8 : fetch_word segs (pcw e 0x2c8) = Some (Z_to_bv 32 0x0075ce03). Proof. fw. Qed.
Lemma FF_2cc : fetch_word segs (pcw e 0x2cc) = Some (Z_to_bv 32 0x00e68023). Proof. fw. Qed.
Lemma FF_2d0 : fetch_word segs (pcw e 0x2d0) = Some (Z_to_bv 32 0x00f680a3). Proof. fw. Qed.
Lemma FF_2d4 : fetch_word segs (pcw e 0x2d4) = Some (Z_to_bv 32 0x01068123). Proof. fw. Qed.
Lemma FF_2d8 : fetch_word segs (pcw e 0x2d8) = Some (Z_to_bv 32 0x011681a3). Proof. fw. Qed.
Lemma FF_2dc : fetch_word segs (pcw e 0x2dc) = Some (Z_to_bv 32 0x0085c703). Proof. fw. Qed.
Lemma FF_2e0 : fetch_word segs (pcw e 0x2e0) = Some (Z_to_bv 32 0x0095c783). Proof. fw. Qed.
Lemma FF_2e4 : fetch_word segs (pcw e 0x2e4) = Some (Z_to_bv 32 0x00a5c803). Proof. fw. Qed.
Lemma FF_2e8 : fetch_word segs (pcw e 0x2e8) = Some (Z_to_bv 32 0x00b5c883). Proof. fw. Qed.
Lemma FF_2ec : fetch_word segs (pcw e 0x2ec) = Some (Z_to_bv 32 0x00568223). Proof. fw. Qed.
Lemma FF_2f0 : fetch_word segs (pcw e 0x2f0) = Some (Z_to_bv 32 0x006682a3). Proof. fw. Qed.
Lemma FF_2f4 : fetch_word segs (pcw e 0x2f4) = Some (Z_to_bv 32 0x00768323). Proof. fw. Qed.
Lemma FF_2f8 : fetch_word segs (pcw e 0x2f8) = Some (Z_to_bv 32 0x01c683a3). Proof. fw. Qed.
Lemma FF_2fc : fetch_word segs (pcw e 0x2fc) = Some (Z_to_bv 32 0x00c5c283). Proof. fw. Qed.
Lemma FF_300 : fetch_word segs (pcw e 0x300) = Some (Z_to_bv 32 0x00d5c303). Proof. fw. Qed.
Lemma FF_304 : fetch_word segs (pcw e 0x304) = Some (Z_to_bv 32 0x00e5c383). Proof. fw. Qed.
Lemma FF_308 : fetch_word segs (pcw e 0x308) = Some (Z_to_bv 32 0x00f5ce03). Proof. fw. Qed.
Lemma FF_30c : fetch_word segs (pcw e 0x30c) = Some (Z_to_bv 32 0x01058593). Proof. fw. Qed.
Lemma FF_310 : fetch_word segs (pcw e 0x310) = Some (Z_to_bv 32 0x00e68423). Proof. fw. Qed.
Lemma FF_314 : fetch_word segs (pcw e 0x314) = Some (Z_to_bv 32 0x00f684a3). Proof. fw. Qed.
Lemma FF_318 : fetch_word segs (pcw e 0x318) = Some (Z_to_bv 32 0x01068523). Proof. fw. Qed.
Lemma FF_31c : fetch_word segs (pcw e 0x31c) = Some (Z_to_bv 32 0x011685a3). Proof. fw. Qed.
Lemma FF_320 : fetch_word segs (pcw e 0x320) = Some (Z_to_bv 32 0x01068713). Proof. fw. Qed.
Lemma FF_324 : fetch_word segs (pcw e 0x324) = Some (Z_to_bv 32 0x00568623). Proof. fw. Qed.
Lemma FF_328 : fetch_word segs (pcw e 0x328) = Some (Z_to_bv 32 0x006686a3). Proof. fw. Qed.
Lemma FF_32c : fetch_word segs (pcw e 0x32c) = Some (Z_to_bv 32 0x00768723). Proof. fw. Qed.
Lemma FF_330 : fetch_word segs (pcw e 0x330) = Some (Z_to_bv 32 0x01c687a3). Proof. fw. Qed.
Lemma FF_334 : fetch_word segs (pcw e 0x334) = Some (Z_to_bv 32 0x00070693). Proof. fw. Qed.
Lemma FF_338 : fetch_word segs (pcw e 0x338) = Some (Z_to_bv 32 0x00867713). Proof. fw. Qed.
Lemma FF_33c : fetch_word segs (pcw e 0x33c) = Some (Z_to_bv 32 0xd20706e3). Proof. fw. Qed.
Lemma FF_340 : fetch_word segs (pcw e 0x340) = Some (Z_to_bv 32 0x0005c703). Proof. fw. Qed.
Lemma FF_344 : fetch_word segs (pcw e 0x344) = Some (Z_to_bv 32 0x0015c783). Proof. fw. Qed.
Lemma FF_348 : fetch_word segs (pcw e 0x348) = Some (Z_to_bv 32 0x0025c803). Proof. fw. Qed.
Lemma FF_34c : fetch_word segs (pcw e 0x34c) = Some (Z_to_bv 32 0x0035c883). Proof. fw. Qed.
Lemma FF_350 : fetch_word segs (pcw e 0x350) = Some (Z_to_bv 32 0x0045c283). Proof. fw. Qed.
Lemma FF_354 : fetch_word segs (pcw e 0x354) = Some (Z_to_bv 32 0x0055c303). Proof. fw. Qed.
Lemma FF_358 : fetch_word segs (pcw e 0x358) = Some (Z_to_bv 32 0x0065c383). Proof. fw. Qed.
Lemma FF_35c : fetch_word segs (pcw e 0x35c) = Some (Z_to_bv 32 0x0075ce03). Proof. fw. Qed.
Lemma FF_360 : fetch_word segs (pcw e 0x360) = Some (Z_to_bv 32 0x00858593). Proof. fw. Qed.
Lemma FF_364 : fetch_word segs (pcw e 0x364) = Some (Z_to_bv 32 0x00e68023). Proof. fw. Qed.
Lemma FF_368 : fetch_word segs (pcw e 0x368) = Some (Z_to_bv 32 0x00f680a3). Proof. fw. Qed.
Lemma FF_36c : fetch_word segs (pcw e 0x36c) = Some (Z_to_bv 32 0x01068123). Proof. fw. Qed.
Lemma FF_370 : fetch_word segs (pcw e 0x370) = Some (Z_to_bv 32 0x011681a3). Proof. fw. Qed.
Lemma FF_374 : fetch_word segs (pcw e 0x374) = Some (Z_to_bv 32 0x00868713). Proof. fw. Qed.
Lemma FF_378 : fetch_word segs (pcw e 0x378) = Some (Z_to_bv 32 0x00568223). Proof. fw. Qed.
Lemma FF_37c : fetch_word segs (pcw e 0x37c) = Some (Z_to_bv 32 0x006682a3). Proof. fw. Qed.
Lemma FF_380 : fetch_word segs (pcw e 0x380) = Some (Z_to_bv 32 0x00768323). Proof. fw. Qed.
Lemma FF_384 : fetch_word segs (pcw e 0x384) = Some (Z_to_bv 32 0x01c683a3). Proof. fw. Qed.
Lemma FF_388 : fetch_word segs (pcw e 0x388) = Some (Z_to_bv 32 0x00070693). Proof. fw. Qed.
Lemma FF_38c : fetch_word segs (pcw e 0x38c) = Some (Z_to_bv 32 0x00467713). Proof. fw. Qed.
Lemma FF_390 : fetch_word segs (pcw e 0x390) = Some (Z_to_bv 32 0x02070863). Proof. fw. Qed.
Lemma FF_394 : fetch_word segs (pcw e 0x394) = Some (Z_to_bv 32 0x0005c703). Proof. fw. Qed.
Lemma FF_398 : fetch_word segs (pcw e 0x398) = Some (Z_to_bv 32 0x0015c783). Proof. fw. Qed.
Lemma FF_39c : fetch_word segs (pcw e 0x39c) = Some (Z_to_bv 32 0x0025c803). Proof. fw. Qed.
Lemma FF_3a0 : fetch_word segs (pcw e 0x3a0) = Some (Z_to_bv 32 0x0035c883). Proof. fw. Qed.
Lemma FF_3a4 : fetch_word segs (pcw e 0x3a4) = Some (Z_to_bv 32 0x00458593). Proof. fw. Qed.
Lemma FF_3a8 : fetch_word segs (pcw e 0x3a8) = Some (Z_to_bv 32 0x00468293). Proof. fw. Qed.
Lemma FF_3ac : fetch_word segs (pcw e 0x3ac) = Some (Z_to_bv 32 0x00e68023). Proof. fw. Qed.
Lemma FF_3b0 : fetch_word segs (pcw e 0x3b0) = Some (Z_to_bv 32 0x00f680a3). Proof. fw. Qed.
Lemma FF_3b4 : fetch_word segs (pcw e 0x3b4) = Some (Z_to_bv 32 0x01068123). Proof. fw. Qed.
Lemma FF_3b8 : fetch_word segs (pcw e 0x3b8) = Some (Z_to_bv 32 0x011681a3). Proof. fw. Qed.
Lemma FF_3bc : fetch_word segs (pcw e 0x3bc) = Some (Z_to_bv 32 0x00028693). Proof. fw. Qed.

Section Loop.
Variable model : Model.
Variable J : machine_state -> Prop.
Hypothesis J_acc : forall ms ms' acc, ms_svc_pending ms = None ->
  step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) -> acc_ok model acc -> J ms' -> J ms.
Variable ms0 : machine_state.
Variables (dst src n : Z) (bs : list byte).
Hypothesis Hh : m_halted model = None.
Hypothesis Hd0 : (0 <= dst)%Z.
Hypothesis Hs0 : (0 <= src)%Z.
Hypothesis Hn : (0 <= n)%Z.
Hypothesis Hdn : (dst + n <= 2 ^ 47)%Z.
Hypothesis Hsn : (src + n <= 2 ^ 47)%Z.
Hypothesis Hdisj : (src + n <= dst \/ dst + n <= src)%Z.
Hypothesis Hbs : rdn segs (ms_mem ms0) (Z_to_bv 64 src) (Z.to_nat n) = Some bs.
Hypothesis Hsok : store_ok segs (ms_mem ms0) (Z_to_bv 64 dst) (Z.to_nat n) = true.
Hypothesis Hnls : no_lazy model src (src + n).
Hypothesis Hnld : no_lazy model dst (dst + n).
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms', MCRc MCF_CLOB ms0 ms' -> copied (ms_mem ms') (ms_mem ms0) dst n bs ->
  ms_pc_val ms' = rg ms0 1 -> J ms'.

Let HC : MCCode segs e := mcf_al segs e HF.
Let T2 := t2 segs e HC MCF_CLOB HCLF HCL1F model J J_acc ms0 dst src n bs Hh Hd0 Hs0 Hn Hdn Hsn Hdisj Hbs Hsok
             Hnls Hnld Hra HK.

Lemma LbsF : length bs = Z.to_nat n.
Proof. exact (rdn_length _ _ _ _ _ Hbs). Qed.

Lemma src_rdF : forall m k' (a : Z) (c : nat), copied m (ms_mem ms0) dst k' bs -> (0 <= k' <= n)%Z ->
  (0 <= a - src)%Z -> (a - src + Z.of_nat c <= n)%Z ->
  rdn segs m (Z_to_bv 64 a) c = Some (firstn c (skipn (Z.to_nat (a - src)) bs)).
Proof.
  intros m k' a c Hc Hk' Ha Hac.
  assert (E : rdn segs m (Z_to_bv 64 a) c = rdn segs (ms_mem ms0) (Z_to_bv 64 a) c).
  { apply rdn_ext; [rewrite bvu_z by lia; lia|].
    intros x Hx. rewrite bvu_z in Hx by lia. apply (proj2 (Hc x)). lia. }
  rewrite E.
  pose proof (SeqExec.rdn_skipn segs (ms_mem ms0) (Z.to_nat n) (Z_to_bv 64 src) bs (Z.to_nat (a - src)) Hbs ltac:(lia)) as Hs.
  unfold nat_to_word in Hs. rewrite zw_add, Z2Nat.id in Hs by lia. replace (src + (a - src))%Z with a in Hs by lia.
  apply (SeqExec.rdn_firstn segs (ms_mem ms0) (Z.to_nat n - Z.to_nat (a - src))); [exact Hs | lia].
Qed.

Lemma sok_subF : forall m k' (a : Z) (c : nat), copied m (ms_mem ms0) dst k' bs ->
  (0 <= a - dst)%Z -> (a - dst + Z.of_nat c <= n)%Z -> store_ok segs m (Z_to_bv 64 a) c = true.
Proof.
  intros m k' a c Hc Ha Hac.
  eapply store_ok_sub; [ | eapply store_ok_mono; [exact (copied_grows _ _ _ _ _ Hc) | exact Hsok] | | ];
    rewrite ?bvu_z by lia; rewrite ?Z2Nat.id by lia; lia.
Qed.

Lemma copied_st : forall m k' (a : Z) data (c : nat), copied m (ms_mem ms0) dst k' bs ->
  (0 <= k')%Z -> (k' + Z.of_nat c <= n)%Z -> a = (dst + k')%Z -> data = firstn c (skipn (Z.to_nat k') bs) ->
  copied (write_to_mem m (Z_to_bv 64 a) data) (ms_mem ms0) dst (k' + Z.of_nat c) bs.
Proof.
  intros m k' a data c Hc Hk Hkc -> ->. apply copied_step; [lia | lia | rewrite LbsF; lia | lia | exact Hc].
Qed.

Lemma len4F : forall (j : Z), (0 <= j)%Z -> (j + 4 <= n)%Z -> length (firstn 4 (skipn (Z.to_nat j) bs)) = 4%nat.
Proof. intros j Hj Hjn. rewrite length_firstn, length_skipn, LbsF. lia. Qed.

Lemma len1F : forall (j : Z), (0 <= j)%Z -> (j + 1 <= n)%Z -> length (firstn 1 (skipn (Z.to_nat j) bs)) = 1%nat.
Proof. intros j Hj Hjn. rewrite length_firstn, length_skipn, LbsF. lia. Qed.

Lemma fs_eq : forall (c : nat) (j j' : Z), j = j' -> firstn c (skipn (Z.to_nat j) bs) = firstn c (skipn (Z.to_nat j') bs).
Proof. intros c j j' ->. reflexivity. Qed.

Local Ltac rdS Hf := cbn [msz_n]; eapply src_rdF; [exact Hf | lia | lia | lia].
Local Ltac acS NL := cbn [msz_n]; apply acc_ok_one; rewrite bvu_z by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ];
                     [lia | eapply no_lazy_sub; [exact NL | lia | lia]].
Local Ltac okS Hf := cbn [msz_n]; eapply sok_subF; [exact Hf | lia | lia].

Local Ltac upd Hf c DT :=
  match goal with |- J (setx _ _ _ _ _ (write_to_mem ?m (Z_to_bv 64 ?a) ?data)) =>
    let Hf' := fresh "Hf" in
    pose proof (copied_st m _ a data c Hf ltac:(lia) ltac:(lia) ltac:(lia) ltac:(DT)) as Hf'; clear Hf; rename Hf' into Hf
  end.
Local Ltac ld F D Hf := jl F D ltac:(rdS Hf) ltac:(acS Hnls).
Local Ltac st F D Hf c DT := js F D regX ltac:(okS Hf) ltac:(acS Hnld); upd Hf c DT.
Local Ltac dt1 := rewrite store1_load1 by (apply len1F; lia); apply fs_eq; lia.
Local Ltac sb F D Hf := st F D Hf 1%nat dt1.
Local Ltac ai F D := jr wacc_OpImm F D valX.
Local Ltac regZ := rgn; rwregsX; first [ reflexivity | f_equal; lia ].

Lemma b4 : forall S k r, MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x394 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + 4 + r mod 4 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k r HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (Z.mod_pos_bound r 4 ltac:(lia)).
  ld FF_394 DW_0005c703 Hf. ld FF_398 DW_0015c783 Hf. ld FF_39c DW_0025c803 Hf. ld FF_3a0 DW_0035c883 Hf.
  ai FF_3a4 DW_00458593. ai FF_3a8 DW_00468293.
  sb FF_3ac DW_00e68023 Hf. sb FF_3b0 DW_00f680a3 Hf. sb FF_3b4 DW_01068123 Hf. sb FF_3b8 DW_011681a3 Hf.
  ai FF_3bc DW_00028693.
  apply (T2 _ (k + 4)%Z r); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
  - rewrite ?mem_setx. replace (k + 4)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
Qed.

Local Ltac snapregs S2 E rs :=
  lazymatch rs with
  | cons ?r ?rest => let R := fresh "R" in eassert (R : rg S2 r = _) by (rewrite E; regX); snapregs S2 E rest
  | nil => idtac
  end.
Local Ltac snap S HS Hf rs :=
  match goal with |- J ?S' =>
    let S2 := fresh "S" in let E := fresh "E" in
    remember S' as S2 eqn:E;
    let HS2 := fresh "HS" in assert (HS2 : MCRc MCF_CLOB ms0 S2) by (rewrite E; mcf_chain HS);
    let Hv := fresh "Hsvc" in assert (Hv : ms_svc_pending S2 = None) by (rewrite E; reflexivity);
    let Hp := fresh "Hpc" in eassert (Hp : ms_pc_val S2 = _) by (rewrite E; rewrite pc_setx; reflexivity);
    let Hf2 := fresh "Hf" in
    lazymatch type of Hf with copied _ _ _ ?k' _ =>
      assert (Hf2 : copied (ms_mem S2) (ms_mem ms0) dst k' bs) by (rewrite E, mem_setx; exact Hf) end;
    snapregs S2 E rs;
    clear E; clear dependent S; rename S2 into S; rename HS2 into HS; rename Hf2 into Hf
  end.

Local Ltac valA := rgn; rwregsX; rewrite alu_andi_z by (lits; lia); lits; reflexivity.
Local Ltac bnorm Hb := unfold w0 in Hb;
  rewrite ?branch_eq_z, ?branch_ne_z, ?branch_ltu_z, ?branch_geu_z in Hb by lia;
  rewrite ?negb_true_iff, ?negb_false_iff in Hb;
  first [ apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb | apply Z.ltb_lt in Hb | apply Z.ltb_ge in Hb | idtac ].

Lemma tl68 : forall S k r, MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x68 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + r mod 8 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k r HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (Z_land_range r 4 ltac:(lia) ltac:(lia)).
  jr wacc_OpImm FF_68 DW_00467713 valA.
  jb2 FF_6c DW_32071463; intros Hb; bnorm Hb.
  - destruct (c4_1 r Hr Hb) as [M1 M2].
    apply (b4 _ k r); [ mcf_chain HS | reflexivity | regX | regX | regX | lia | lia | lia | exact Hf ].
  - destruct (c4_0 r Hr Hb) as [M1 M2].
    jj FF_70 DW_3500006f.
    apply (T2 _ k r); [ mcf_chain HS | reflexivity | regX | regX | regX | lia | lia | lia | exact Hf ].
Qed.

Lemma b8 : forall S k r, MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x340 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + 8 + r mod 8 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k r HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (Z.mod_pos_bound r 8 ltac:(lia)). pose proof (Z_land_range r 4 ltac:(lia) ltac:(lia)).
  ld FF_340 DW_0005c703 Hf. ld FF_344 DW_0015c783 Hf. ld FF_348 DW_0025c803 Hf. ld FF_34c DW_0035c883 Hf.
  ld FF_350 DW_0045c283 Hf. ld FF_354 DW_0055c303 Hf. ld FF_358 DW_0065c383 Hf. ld FF_35c DW_0075ce03 Hf.
  ai FF_360 DW_00858593.
  snap S HS Hf ([11; 12; 13; 14; 15; 16; 17; 5; 6; 7; 28] : list reg).
  sb FF_364 DW_00e68023 Hf. sb FF_368 DW_00f680a3 Hf. sb FF_36c DW_01068123 Hf. sb FF_370 DW_011681a3 Hf.
  ai FF_374 DW_00868713.
  sb FF_378 DW_00568223 Hf. sb FF_37c DW_006682a3 Hf. sb FF_380 DW_00768323 Hf. sb FF_384 DW_01c683a3 Hf.
  ai FF_388 DW_00070693.
  snap S HS Hf ([11; 12; 13] : list reg).
  jr wacc_OpImm FF_38c DW_00467713 valA.
  jb2 FF_390 DW_02070863; intros Hb; bnorm Hb.
  - destruct (c4_0 r Hr Hb) as [M1 M2].
    apply (T2 _ (k + 8)%Z r); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
    rewrite ?mem_setx. replace (k + 8)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
                                                 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
  - destruct (c4_1 r Hr Hb) as [M1 M2].
    apply (b4 _ (k + 8)%Z r); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
    rewrite ?mem_setx. replace (k + 8)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
                                                 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
Qed.

Lemma tl60 : forall S k r, MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x60 ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (0 <= r < 32)%Z -> (0 <= k)%Z -> (k + r mod 16 = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k r HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (Z_land_range r 8 ltac:(lia) ltac:(lia)).
  jr wacc_OpImm FF_60 DW_00867713 valA.
  jb2 FF_64 DW_2c071e63; intros Hb; bnorm Hb.
  - destruct (c8_1 r Hr Hb) as [M1 M2].
    apply (b8 _ k r); [ mcf_chain HS | reflexivity | regX | regX | regX | lia | lia | lia | exact Hf ].
  - destruct (c8_0 r Hr Hb) as [M1 M2].
    apply (tl68 _ k r); [ mcf_chain HS | reflexivity | regX | regX | regX | lia | lia | lia | exact Hf ].
Qed.

Lemma b16 : forall S k r, MCRc MCF_CLOB ms0 S -> ms_pc_val S = pcw e 0x2ac ->
  rg S 11 = Z_to_bv 64 (src + k) -> rg S 13 = Z_to_bv 64 (dst + k) -> rg S 12 = Z_to_bv 64 r ->
  (16 <= r < 32)%Z -> (0 <= k)%Z -> (k + r = n)%Z ->
  copied (ms_mem S) (ms_mem ms0) dst k bs -> J S.
Proof.
  intros S k r HS Hpc H11 H13 H12 Hr Hk Hkn Hf. pose proof (mcr_svc _ _ _ HS) as Hsvc.
  pose proof (c16 r Hr). pose proof (Z_land_range r 8 ltac:(lia) ltac:(lia)).
  ld FF_2ac DW_0005c703 Hf. ld FF_2b0 DW_0015c783 Hf. ld FF_2b4 DW_0025c803 Hf. ld FF_2b8 DW_0035c883 Hf.
  ld FF_2bc DW_0045c283 Hf. ld FF_2c0 DW_0055c303 Hf. ld FF_2c4 DW_0065c383 Hf. ld FF_2c8 DW_0075ce03 Hf.
  sb FF_2cc DW_00e68023 Hf. sb FF_2d0 DW_00f680a3 Hf. sb FF_2d4 DW_01068123 Hf. sb FF_2d8 DW_011681a3 Hf.
  snap S HS Hf ([11; 12; 13; 5; 6; 7; 28] : list reg).
  ld FF_2dc DW_0085c703 Hf. ld FF_2e0 DW_0095c783 Hf. ld FF_2e4 DW_00a5c803 Hf. ld FF_2e8 DW_00b5c883 Hf.
  sb FF_2ec DW_00568223 Hf. sb FF_2f0 DW_006682a3 Hf. sb FF_2f4 DW_00768323 Hf. sb FF_2f8 DW_01c683a3 Hf.
  snap S HS Hf ([11; 12; 13; 14; 15; 16; 17] : list reg).
  ld FF_2fc DW_00c5c283 Hf. ld FF_300 DW_00d5c303 Hf. ld FF_304 DW_00e5c383 Hf. ld FF_308 DW_00f5ce03 Hf.
  ai FF_30c DW_01058593.
  snap S HS Hf ([11; 12; 13; 14; 15; 16; 17; 5; 6; 7; 28] : list reg).
  sb FF_310 DW_00e68423 Hf. sb FF_314 DW_00f684a3 Hf. sb FF_318 DW_01068523 Hf. sb FF_31c DW_011685a3 Hf.
  ai FF_320 DW_01068713.
  sb FF_324 DW_00568623 Hf. sb FF_328 DW_006686a3 Hf. sb FF_32c DW_00768723 Hf. sb FF_330 DW_01c687a3 Hf.
  ai FF_334 DW_00070693.
  snap S HS Hf ([11; 12; 13] : list reg).
  jr wacc_OpImm FF_338 DW_00867713 valA.
  jb2 FF_33c DW_d20706e3; intros Hb; bnorm Hb.
  - destruct (c8_0 r ltac:(lia) Hb) as [M1 M2].
    apply (tl68 _ (k + 16)%Z r); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
    rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
       + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
       + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
  - destruct (c8_1 r ltac:(lia) Hb) as [M1 M2].
    apply (b8 _ (k + 16)%Z r); [ mcf_chain HS | reflexivity | regZ | regZ | regZ | lia | lia | lia | ].
    rewrite ?mem_setx. replace (k + 16)%Z with (k + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
       + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1
       + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1 + Z.of_nat 1)%Z by lia. exact Hf.
Qed.
End Loop. End MCF.
