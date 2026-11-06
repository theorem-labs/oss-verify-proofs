(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec StepTac SeqExec CatExec StoreOk CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSWord AsanSLibc AsanSMat AsanSMiz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition pair_ok (segs : list Segment) (base o : Z) (rd rd2 : reg) (g : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 (base + o)), fetch_word segs (Z_to_bv 64 (base + (o + 4))) with
  | Some wa, Some wl =>
      match decode_any wa, decode_any wl with
      | Some (Auipc rd' ia, isa), Some (Load SZ8 true rd2' rs il, isl) =>
          Z.eqb isa 4 && Z.eqb isl 4 && bv_eqb rd' rd && bv_eqb rd2' rd2 && bv_eqb rs rd &&
          negb (is_ecall wa) && negb (is_ecall wl) &&
          Z.eqb (bv_unsigned (pcw base (o + bv_signed (bv_concat 32 ia (Z_to_bv 12 0))) + sext 64 il)) g
      | _, _ => false
      end
  | _, _ => false
  end.

Lemma bv_eqb_true : forall {n} (a c : bv n), bv_eqb a c = true -> a = c.
Proof. intros n a c H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma pair_ok_sound : forall segs base o rd rd2 g, pair_ok segs base o rd rd2 g = true ->
  (0 <= g < 2 ^ 64)%Z ->
  exists wa wl ia il,
    fetch_word segs (pcw base o) = Some wa /\ is_ecall wa = false /\ decode_any wa = Some (Auipc rd ia, 4%Z) /\
    fetch_word segs (pcw base (o + 4)) = Some wl /\ is_ecall wl = false /\ decode_any wl = Some (Load SZ8 true rd2 rd il, 4%Z) /\
    pcw base (o + bv_signed (bv_concat 32 ia (Z_to_bv 12 0))) + sext 64 il = Z_to_bv 64 g.
Proof.
  intros segs base o rd rd2 g H Hg. unfold pair_ok, pcw in *.
  destruct (fetch_word segs (Z_to_bv 64 (base + o))) as [wa|] eqn:Fa; [|discriminate].
  destruct (fetch_word segs (Z_to_bv 64 (base + (o + 4)))) as [wl|] eqn:Fl; [|discriminate].
  destruct (decode_any wa) as [[ia isa]|] eqn:Da; [|discriminate].
  destruct ia; try discriminate.
  destruct (decode_any wl) as [[il isl]|] eqn:Dl; [|discriminate].
  destruct il; try discriminate.
  match goal with H : match ?sz with SZ8 => _ | _ => _ end = true |- _ => destruct sz; try discriminate end.
  match goal with H : (if ?sg then _ else false) = true |- _ => destruct sg; try discriminate end.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [H ?] end.
  repeat match goal with H1 : Z.eqb _ 4 = true |- _ => apply Z.eqb_eq in H1; subst end.
  repeat match goal with H1 : bv_eqb _ _ = true |- _ => apply bv_eqb_true in H1; subst end.
  repeat match goal with H1 : negb _ = true |- _ => apply negb_true_iff in H1 end.
  match goal with Da : decode_any wa = Some (Auipc rd ?ia, _), Dl : decode_any wl = Some (Load SZ8 true rd2 rd ?il, _) |- _ =>
    exists wa, wl, ia, il end.
  repeat split; try reflexivity; try assumption.
  apply bv_eq. match goal with H1 : Z.eqb _ g = true |- _ => apply Z.eqb_eq in H1; rewrite H1 end.
  rewrite bvu_z by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition jal_ok (segs : list Segment) (base o : Z) (rd : reg) (tgt : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 (base + o)) with
  | Some w =>
      match decode_any w with
      | Some (Jal rd' imm, isz) => Z.eqb isz 4 && bv_eqb rd' rd && negb (is_ecall w) && Z.eqb (base + o + bv_signed imm) tgt
      | _ => false
      end
  | None => false
  end.

Lemma jal_ok_sound : forall segs base o rd tgt, jal_ok segs base o rd tgt = true ->
  exists (w : bv 32) (imm : bv 21),
    fetch_word segs (pcw base o) = Some w /\ is_ecall w = false /\ decode_any w = Some (Jal rd imm, 4%Z) /\
    (base + o + bv_signed imm = tgt)%Z.
Proof.
  intros segs base o rd tgt H. unfold jal_ok, pcw in *.
  destruct (fetch_word segs (Z_to_bv 64 (base + o))) as [w|] eqn:F; [|discriminate].
  destruct (decode_any w) as [[i isz]|] eqn:D; [|discriminate].
  destruct i; try discriminate.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply bv_eqb_true in H2. apply negb_true_iff in H3. apply Z.eqb_eq in H4. subst isz.
  match goal with D' : decode_any w = Some (Jal ?r ?im, _) |- _ => exists w, im; subst r end.
  split; [reflexivity|]. split; [exact H3|]. split; [exact D|]. exact H4.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HCLOB : list reg := [5; 10; 11; 12; 13; 14; 15; 16; 17].

(* [comment removed for export] *)
Definition rpg (size : Z) : Z := (size / 8 + 2)%Z.

Lemma rpg_f : forall size : Z, (8 * (rpg size - 2) <= size < 8 * (rpg size - 2) + 8)%Z.
Proof. intros size. unfold rpg. pose proof (Z.div_mod size 8 ltac:(lia)). pose proof (Z.mod_pos_bound size 8 ltac:(lia)). lia. Qed.

Definition RIP_WORDS : list (Z * Z) :=
  [(0x0, 0xfc010113); (0x4, 0x02113c23); (0x8, 0x02813823); (0xc, 0x02913423); (0x10, 0x03213023);
   (0x14, 0x01313c23); (0x18, 0x01413823); (0x1c, 0x01513423); (0x20, 0x14058c63); (0x24, 0x00058493);
   (0x28, 0x00050413); (0x34, 0x000ab583); (0x38, 0xfff58513); (0x3c, 0x00a5b633); (0x40, 0xfff60613);
   (0x44, 0x00a67633); (0x48, 0x04867263); (0x5c, 0x0006b803); (0x60, 0x00073683); (0x64, 0xfff80793);
   (0x68, 0x0087f463); (0x6c, 0x0286f063); (0x78, 0x00073283); (0x7c, 0x0032d713); (0x80, 0x00b708b3);
   (0x84, 0x1282e063); (0x88, 0x1088fe63); (0x8c, 0x00848933); (0x90, 0x05267263); (0xa4, 0x00063783);
   (0xa8, 0x0006b603); (0xac, 0xfff78713); (0xb0, 0x01277463); (0xb4, 0x03267063); (0xc0, 0x0006b883);
   (0xc4, 0x0038d693); (0xc8, 0x00b68833); (0xcc, 0x1328e463); (0xd0, 0x13287263); (0xd4, 0x23247863);
   (0xd8, 0x00740513); (0xdc, 0xff857513); (0xe0, 0xff897a13); (0xe4, 0xa91ff0ef); (0xe8, 0x00050993);
   (0xec, 0x000a0513); (0xf0, 0xa85ff0ef); (0xf4, 0x000ab583); (0xf8, 0x00345613); (0xfc, 0x00c58633);
   (0x100, 0x00060603); (0x104, 0x00060663); (0x108, 0x00747693); (0x10c, 0x02c6d063); (0x110, 0xfff90913);
   (0x114, 0x00395613); (0x118, 0x00c585b3); (0x11c, 0x00058583); (0x120, 0x04058263); (0x124, 0x00797613);
   (0x128, 0x02b64e63); (0x12c, 0x000ab503); (0x130, 0x00040593); (0x134, 0x0140006f); (0x138, 0x00140413);
   (0x13c, 0xfff48493); (0x140, 0x00158593); (0x144, 0x1e048063); (0x148, 0x00345613); (0x14c, 0x00c50633);
   (0x150, 0x00060603); (0x154, 0xfe0602e3); (0x158, 0x0075f693); (0x15c, 0xfcc6cee3); (0x160, 0x01c0006f);
   (0x164, 0x00a9fa63); (0x168, 0x413505b3); (0x16c, 0x00098513); (0x174, 0xfa050ce3);
   (0x178, 0x00000413); (0x17c, 0x00040513); (0x180, 0x03813083); (0x184, 0x03013403); (0x188, 0x02813483);
   (0x18c, 0x02013903); (0x190, 0x01813983); (0x194, 0x01013a03); (0x198, 0x00813a83); (0x19c, 0x04010113);
   (0x1a0, 0x00008067)]%Z.

Definition HLP_WORDS : list (Z * Z) :=
  [(0x8, 0x0005b583); (0xc, 0xfff58613); (0x10, 0x00c5b6b3); (0x14, 0xfff68693); (0x18, 0x00c6f6b3);
   (0x1c, 0x04a6f263); (0x30, 0x0006b803); (0x34, 0x00073683); (0x38, 0xfff80793); (0x3c, 0x00a7f463);
   (0x40, 0x02a6f063); (0x4c, 0x00073283); (0x50, 0x0032d713); (0x54, 0x00b708b3); (0x58, 0x00a2ea63);
   (0x5c, 0x00a8f863); (0x60, 0x00355513); (0x64, 0x00a58533); (0x68, 0x00008067)]%Z.

Lemma D_fc010113 : decode_any (Z_to_bv 32 0xfc010113) = Some (OpImm ALU_ADD 2 2 4032, 4%Z). Proof. wdec. Qed.
Lemma D_02113c23 : decode_any (Z_to_bv 32 0x02113c23) = Some (Store SZ8 2 1 56, 4%Z). Proof. wdec. Qed.
Lemma D_02813823 : decode_any (Z_to_bv 32 0x02813823) = Some (Store SZ8 2 8 48, 4%Z). Proof. wdec. Qed.
Lemma D_02913423 : decode_any (Z_to_bv 32 0x02913423) = Some (Store SZ8 2 9 40, 4%Z). Proof. wdec. Qed.
Lemma D_03213023 : decode_any (Z_to_bv 32 0x03213023) = Some (Store SZ8 2 18 32, 4%Z). Proof. wdec. Qed.
Lemma D_01313c23 : decode_any (Z_to_bv 32 0x01313c23) = Some (Store SZ8 2 19 24, 4%Z). Proof. wdec. Qed.
Lemma D_01413823 : decode_any (Z_to_bv 32 0x01413823) = Some (Store SZ8 2 20 16, 4%Z). Proof. wdec. Qed.
Lemma D_01513423 : decode_any (Z_to_bv 32 0x01513423) = Some (Store SZ8 2 21 8, 4%Z). Proof. wdec. Qed.
Lemma D_14058c63 : decode_any (Z_to_bv 32 0x14058c63) = Some (Branch BC_EQ 11 0 344, 4%Z). Proof. wdec. Qed.
Lemma D_00058493 : decode_any (Z_to_bv 32 0x00058493) = Some (OpImm ALU_ADD 9 11 0, 4%Z). Proof. wdec. Qed.
Lemma D_00050413 : decode_any (Z_to_bv 32 0x00050413) = Some (OpImm ALU_ADD 8 10 0, 4%Z). Proof. wdec. Qed.
Lemma D_000ab583 : decode_any (Z_to_bv 32 0x000ab583) = Some (Load SZ8 true 11 21 0, 4%Z). Proof. wdec. Qed.
Lemma D_fff58513 : decode_any (Z_to_bv 32 0xfff58513) = Some (OpImm ALU_ADD 10 11 4095, 4%Z). Proof. wdec. Qed.
Lemma D_00a5b633 : decode_any (Z_to_bv 32 0x00a5b633) = Some (Op ALU_SLTU 12 11 10, 4%Z). Proof. wdec. Qed.
Lemma D_fff60613 : decode_any (Z_to_bv 32 0xfff60613) = Some (OpImm ALU_ADD 12 12 4095, 4%Z). Proof. wdec. Qed.
Lemma D_00a67633 : decode_any (Z_to_bv 32 0x00a67633) = Some (Op ALU_AND 12 12 10, 4%Z). Proof. wdec. Qed.
Lemma D_04867263 : decode_any (Z_to_bv 32 0x04867263) = Some (Branch BC_GEU 12 8 68, 4%Z). Proof. wdec. Qed.
Lemma D_0006b803 : decode_any (Z_to_bv 32 0x0006b803) = Some (Load SZ8 true 16 13 0, 4%Z). Proof. wdec. Qed.
Lemma D_00073683 : decode_any (Z_to_bv 32 0x00073683) = Some (Load SZ8 true 13 14 0, 4%Z). Proof. wdec. Qed.
Lemma D_fff80793 : decode_any (Z_to_bv 32 0xfff80793) = Some (OpImm ALU_ADD 15 16 4095, 4%Z). Proof. wdec. Qed.
Lemma D_0087f463 : decode_any (Z_to_bv 32 0x0087f463) = Some (Branch BC_GEU 15 8 8, 4%Z). Proof. wdec. Qed.
Lemma D_0286f063 : decode_any (Z_to_bv 32 0x0286f063) = Some (Branch BC_GEU 13 8 32, 4%Z). Proof. wdec. Qed.
Lemma D_00073283 : decode_any (Z_to_bv 32 0x00073283) = Some (Load SZ8 true 5 14 0, 4%Z). Proof. wdec. Qed.
Lemma D_0032d713 : decode_any (Z_to_bv 32 0x0032d713) = Some (ShiftImm ALU_SRL 14 5 3, 4%Z). Proof. wdec. Qed.
Lemma D_00b708b3 : decode_any (Z_to_bv 32 0x00b708b3) = Some (Op ALU_ADD 17 14 11, 4%Z). Proof. wdec. Qed.
Lemma D_1282e063 : decode_any (Z_to_bv 32 0x1282e063) = Some (Branch BC_LTU 5 8 288, 4%Z). Proof. wdec. Qed.
Lemma D_1088fe63 : decode_any (Z_to_bv 32 0x1088fe63) = Some (Branch BC_GEU 17 8 284, 4%Z). Proof. wdec. Qed.
Lemma D_00848933 : decode_any (Z_to_bv 32 0x00848933) = Some (Op ALU_ADD 18 9 8, 4%Z). Proof. wdec. Qed.
Lemma D_05267263 : decode_any (Z_to_bv 32 0x05267263) = Some (Branch BC_GEU 12 18 68, 4%Z). Proof. wdec. Qed.
Lemma D_00063783 : decode_any (Z_to_bv 32 0x00063783) = Some (Load SZ8 true 15 12 0, 4%Z). Proof. wdec. Qed.
Lemma D_0006b603 : decode_any (Z_to_bv 32 0x0006b603) = Some (Load SZ8 true 12 13 0, 4%Z). Proof. wdec. Qed.
Lemma D_fff78713 : decode_any (Z_to_bv 32 0xfff78713) = Some (OpImm ALU_ADD 14 15 4095, 4%Z). Proof. wdec. Qed.
Lemma D_01277463 : decode_any (Z_to_bv 32 0x01277463) = Some (Branch BC_GEU 14 18 8, 4%Z). Proof. wdec. Qed.
Lemma D_03267063 : decode_any (Z_to_bv 32 0x03267063) = Some (Branch BC_GEU 12 18 32, 4%Z). Proof. wdec. Qed.
Lemma D_0006b883 : decode_any (Z_to_bv 32 0x0006b883) = Some (Load SZ8 true 17 13 0, 4%Z). Proof. wdec. Qed.
Lemma D_0038d693 : decode_any (Z_to_bv 32 0x0038d693) = Some (ShiftImm ALU_SRL 13 17 3, 4%Z). Proof. wdec. Qed.
Lemma D_00b68833 : decode_any (Z_to_bv 32 0x00b68833) = Some (Op ALU_ADD 16 13 11, 4%Z). Proof. wdec. Qed.
Lemma D_1328e463 : decode_any (Z_to_bv 32 0x1328e463) = Some (Branch BC_LTU 17 18 296, 4%Z). Proof. wdec. Qed.
Lemma D_13287263 : decode_any (Z_to_bv 32 0x13287263) = Some (Branch BC_GEU 16 18 292, 4%Z). Proof. wdec. Qed.
Lemma D_23247863 : decode_any (Z_to_bv 32 0x23247863) = Some (Branch BC_GEU 8 18 560, 4%Z). Proof. wdec. Qed.
Lemma D_00740513 : decode_any (Z_to_bv 32 0x00740513) = Some (OpImm ALU_ADD 10 8 7, 4%Z). Proof. wdec. Qed.
Lemma D_ff857513 : decode_any (Z_to_bv 32 0xff857513) = Some (OpImm ALU_AND 10 10 4088, 4%Z). Proof. wdec. Qed.
Lemma D_ff897a13 : decode_any (Z_to_bv 32 0xff897a13) = Some (OpImm ALU_AND 20 18 4088, 4%Z). Proof. wdec. Qed.
Lemma D_a91ff0ef : decode_any (Z_to_bv 32 0xa91ff0ef) = Some (Jal 1 2095760, 4%Z). Proof. wdec. Qed.
Lemma D_00050993 : decode_any (Z_to_bv 32 0x00050993) = Some (OpImm ALU_ADD 19 10 0, 4%Z). Proof. wdec. Qed.
Lemma D_000a0513 : decode_any (Z_to_bv 32 0x000a0513) = Some (OpImm ALU_ADD 10 20 0, 4%Z). Proof. wdec. Qed.
Lemma D_a85ff0ef : decode_any (Z_to_bv 32 0xa85ff0ef) = Some (Jal 1 2095748, 4%Z). Proof. wdec. Qed.
Lemma D_00345613 : decode_any (Z_to_bv 32 0x00345613) = Some (ShiftImm ALU_SRL 12 8 3, 4%Z). Proof. wdec. Qed.
Lemma D_00c58633 : decode_any (Z_to_bv 32 0x00c58633) = Some (Op ALU_ADD 12 11 12, 4%Z). Proof. wdec. Qed.
Lemma D_00060603 : decode_any (Z_to_bv 32 0x00060603) = Some (Load SZ1 true 12 12 0, 4%Z). Proof. wdec. Qed.
Lemma D_00060663 : decode_any (Z_to_bv 32 0x00060663) = Some (Branch BC_EQ 12 0 12, 4%Z). Proof. wdec. Qed.
Lemma D_00747693 : decode_any (Z_to_bv 32 0x00747693) = Some (OpImm ALU_AND 13 8 7, 4%Z). Proof. wdec. Qed.
Lemma D_02c6d063 : decode_any (Z_to_bv 32 0x02c6d063) = Some (Branch BC_GE 13 12 32, 4%Z). Proof. wdec. Qed.
Lemma D_fff90913 : decode_any (Z_to_bv 32 0xfff90913) = Some (OpImm ALU_ADD 18 18 4095, 4%Z). Proof. wdec. Qed.
Lemma D_00395613 : decode_any (Z_to_bv 32 0x00395613) = Some (ShiftImm ALU_SRL 12 18 3, 4%Z). Proof. wdec. Qed.
Lemma D_00c585b3 : decode_any (Z_to_bv 32 0x00c585b3) = Some (Op ALU_ADD 11 11 12, 4%Z). Proof. wdec. Qed.
Lemma D_00058583 : decode_any (Z_to_bv 32 0x00058583) = Some (Load SZ1 true 11 11 0, 4%Z). Proof. wdec. Qed.
Lemma D_04058263 : decode_any (Z_to_bv 32 0x04058263) = Some (Branch BC_EQ 11 0 68, 4%Z). Proof. wdec. Qed.
Lemma D_00797613 : decode_any (Z_to_bv 32 0x00797613) = Some (OpImm ALU_AND 12 18 7, 4%Z). Proof. wdec. Qed.
Lemma D_02b64e63 : decode_any (Z_to_bv 32 0x02b64e63) = Some (Branch BC_LT 12 11 60, 4%Z). Proof. wdec. Qed.
Lemma D_000ab503 : decode_any (Z_to_bv 32 0x000ab503) = Some (Load SZ8 true 10 21 0, 4%Z). Proof. wdec. Qed.
Lemma D_00040593 : decode_any (Z_to_bv 32 0x00040593) = Some (OpImm ALU_ADD 11 8 0, 4%Z). Proof. wdec. Qed.
Lemma D_0140006f : decode_any (Z_to_bv 32 0x0140006f) = Some (Jal 0 20, 4%Z). Proof. wdec. Qed.
Lemma D_00140413 : decode_any (Z_to_bv 32 0x00140413) = Some (OpImm ALU_ADD 8 8 1, 4%Z). Proof. wdec. Qed.
Lemma D_fff48493 : decode_any (Z_to_bv 32 0xfff48493) = Some (OpImm ALU_ADD 9 9 4095, 4%Z). Proof. wdec. Qed.
Lemma D_00158593 : decode_any (Z_to_bv 32 0x00158593) = Some (OpImm ALU_ADD 11 11 1, 4%Z). Proof. wdec. Qed.
Lemma D_1e048063 : decode_any (Z_to_bv 32 0x1e048063) = Some (Branch BC_EQ 9 0 480, 4%Z). Proof. wdec. Qed.
Lemma D_00c50633 : decode_any (Z_to_bv 32 0x00c50633) = Some (Op ALU_ADD 12 10 12, 4%Z). Proof. wdec. Qed.
Lemma D_fe0602e3 : decode_any (Z_to_bv 32 0xfe0602e3) = Some (Branch BC_EQ 12 0 8164, 4%Z). Proof. wdec. Qed.
Lemma D_0075f693 : decode_any (Z_to_bv 32 0x0075f693) = Some (OpImm ALU_AND 13 11 7, 4%Z). Proof. wdec. Qed.
Lemma D_fcc6cee3 : decode_any (Z_to_bv 32 0xfcc6cee3) = Some (Branch BC_LT 13 12 8156, 4%Z). Proof. wdec. Qed.
Lemma D_01c0006f : decode_any (Z_to_bv 32 0x01c0006f) = Some (Jal 0 28, 4%Z). Proof. wdec. Qed.
Lemma D_00a9fa63 : decode_any (Z_to_bv 32 0x00a9fa63) = Some (Branch BC_GEU 19 10 20, 4%Z). Proof. wdec. Qed.
Lemma D_413505b3 : decode_any (Z_to_bv 32 0x413505b3) = Some (Op ALU_SUB 11 10 19, 4%Z). Proof. wdec. Qed.
Lemma D_00098513 : decode_any (Z_to_bv 32 0x00098513) = Some (OpImm ALU_ADD 10 19 0, 4%Z). Proof. wdec. Qed.
Lemma D_fa050ce3 : decode_any (Z_to_bv 32 0xfa050ce3) = Some (Branch BC_EQ 10 0 8120, 4%Z). Proof. wdec. Qed.
Lemma D_00000413 : decode_any (Z_to_bv 32 0x00000413) = Some (OpImm ALU_ADD 8 0 0, 4%Z). Proof. wdec. Qed.
Lemma D_00040513 : decode_any (Z_to_bv 32 0x00040513) = Some (OpImm ALU_ADD 10 8 0, 4%Z). Proof. wdec. Qed.
Lemma D_03813083 : decode_any (Z_to_bv 32 0x03813083) = Some (Load SZ8 true 1 2 56, 4%Z). Proof. wdec. Qed.
Lemma D_03013403 : decode_any (Z_to_bv 32 0x03013403) = Some (Load SZ8 true 8 2 48, 4%Z). Proof. wdec. Qed.
Lemma D_02813483 : decode_any (Z_to_bv 32 0x02813483) = Some (Load SZ8 true 9 2 40, 4%Z). Proof. wdec. Qed.
Lemma D_02013903 : decode_any (Z_to_bv 32 0x02013903) = Some (Load SZ8 true 18 2 32, 4%Z). Proof. wdec. Qed.
Lemma D_01813983 : decode_any (Z_to_bv 32 0x01813983) = Some (Load SZ8 true 19 2 24, 4%Z). Proof. wdec. Qed.
Lemma D_01013a03 : decode_any (Z_to_bv 32 0x01013a03) = Some (Load SZ8 true 20 2 16, 4%Z). Proof. wdec. Qed.
Lemma D_00813a83 : decode_any (Z_to_bv 32 0x00813a83) = Some (Load SZ8 true 21 2 8, 4%Z). Proof. wdec. Qed.
Lemma D_04010113 : decode_any (Z_to_bv 32 0x04010113) = Some (OpImm ALU_ADD 2 2 64, 4%Z). Proof. wdec. Qed.
Lemma D_00008067 : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. wdec. Qed.
Lemma D_0005b583 : decode_any (Z_to_bv 32 0x0005b583) = Some (Load SZ8 true 11 11 0, 4%Z). Proof. wdec. Qed.
Lemma D_fff58613 : decode_any (Z_to_bv 32 0xfff58613) = Some (OpImm ALU_ADD 12 11 4095, 4%Z). Proof. wdec. Qed.
Lemma D_00c5b6b3 : decode_any (Z_to_bv 32 0x00c5b6b3) = Some (Op ALU_SLTU 13 11 12, 4%Z). Proof. wdec. Qed.
Lemma D_fff68693 : decode_any (Z_to_bv 32 0xfff68693) = Some (OpImm ALU_ADD 13 13 4095, 4%Z). Proof. wdec. Qed.
Lemma D_00c6f6b3 : decode_any (Z_to_bv 32 0x00c6f6b3) = Some (Op ALU_AND 13 13 12, 4%Z). Proof. wdec. Qed.
Lemma D_04a6f263 : decode_any (Z_to_bv 32 0x04a6f263) = Some (Branch BC_GEU 13 10 68, 4%Z). Proof. wdec. Qed.
Lemma D_00a7f463 : decode_any (Z_to_bv 32 0x00a7f463) = Some (Branch BC_GEU 15 10 8, 4%Z). Proof. wdec. Qed.
Lemma D_02a6f063 : decode_any (Z_to_bv 32 0x02a6f063) = Some (Branch BC_GEU 13 10 32, 4%Z). Proof. wdec. Qed.
Lemma D_00a2ea63 : decode_any (Z_to_bv 32 0x00a2ea63) = Some (Branch BC_LTU 5 10 20, 4%Z). Proof. wdec. Qed.
Lemma D_00a8f863 : decode_any (Z_to_bv 32 0x00a8f863) = Some (Branch BC_GEU 17 10 16, 4%Z). Proof. wdec. Qed.
Lemma D_00355513 : decode_any (Z_to_bv 32 0x00355513) = Some (ShiftImm ALU_SRL 10 10 3, 4%Z). Proof. wdec. Qed.
Lemma D_00a58533 : decode_any (Z_to_bv 32 0x00a58533) = Some (Op ALU_ADD 10 11 10, 4%Z). Proof. wdec. Qed.

Section Rip.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable b : Z.
Local Notation h := (b - 0x48c)%Z.
Variable z : Z.   (* [comment removed for export] *)
Variables gK gMB gME gHE aK aMB aME aHE : Z.
Hypothesis HW : words_ok segs b RIP_WORDS = true.
Hypothesis HWh : words_ok segs h HLP_WORDS = true.
Hypothesis HWz : words_ok segs z MIZ_WORDS = true.
Hypothesis HJz : jal_ok segs b 0x170 1 z = true.
Hypothesis HPh0 : pair_ok segs h 0x0 11 11 gK = true.
Hypothesis HPh20 : pair_ok segs h 0x20 13 13 gMB = true.
Hypothesis HPh28 : pair_ok segs h 0x28 14 14 gME = true.
Hypothesis HPh44 : pair_ok segs h 0x44 14 14 gHE = true.
Hypothesis HP2c : pair_ok segs b 0x2c 10 21 gK = true.
Hypothesis HP4c : pair_ok segs b 0x4c 13 13 gMB = true.
Hypothesis HP54 : pair_ok segs b 0x54 14 14 gME = true.
Hypothesis HP70 : pair_ok segs b 0x70 14 14 gHE = true.
Hypothesis HP94 : pair_ok segs b 0x94 12 12 gMB = true.
Hypothesis HP9c : pair_ok segs b 0x9c 13 13 gME = true.
Hypothesis HPb8 : pair_ok segs b 0xb8 13 13 gHE = true.
Hypothesis Hgb : (0 <= gK < 2 ^ 60 /\ 0 <= gMB < 2 ^ 60 /\ 0 <= gME < 2 ^ 60 /\ 0 <= gHE < 2 ^ 60 /\
                  0 <= aK < 2 ^ 60 /\ 0 <= aMB < 2 ^ 60 /\ 0 <= aME < 2 ^ 60 /\ 0 <= aHE < 2 ^ 60)%Z.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get_l segs b RIP_WORDS); [exact HW | reflexivity | reflexivity].
Local Ltac fwh := apply (words_get_l segs h HLP_WORDS); [exact HWh | reflexivity | reflexivity].

Lemma F_0 : fetch_word segs (pcw b 0x0) = Some (Z_to_bv 32 0xfc010113). Proof. fw. Qed.
Lemma F_4 : fetch_word segs (pcw b 0x4) = Some (Z_to_bv 32 0x02113c23). Proof. fw. Qed.
Lemma F_8 : fetch_word segs (pcw b 0x8) = Some (Z_to_bv 32 0x02813823). Proof. fw. Qed.
Lemma F_c : fetch_word segs (pcw b 0xc) = Some (Z_to_bv 32 0x02913423). Proof. fw. Qed.
Lemma F_10 : fetch_word segs (pcw b 0x10) = Some (Z_to_bv 32 0x03213023). Proof. fw. Qed.
Lemma F_14 : fetch_word segs (pcw b 0x14) = Some (Z_to_bv 32 0x01313c23). Proof. fw. Qed.
Lemma F_18 : fetch_word segs (pcw b 0x18) = Some (Z_to_bv 32 0x01413823). Proof. fw. Qed.
Lemma F_1c : fetch_word segs (pcw b 0x1c) = Some (Z_to_bv 32 0x01513423). Proof. fw. Qed.
Lemma F_20 : fetch_word segs (pcw b 0x20) = Some (Z_to_bv 32 0x14058c63). Proof. fw. Qed.
Lemma F_24 : fetch_word segs (pcw b 0x24) = Some (Z_to_bv 32 0x00058493). Proof. fw. Qed.
Lemma F_28 : fetch_word segs (pcw b 0x28) = Some (Z_to_bv 32 0x00050413). Proof. fw. Qed.
Lemma F_34 : fetch_word segs (pcw b 0x34) = Some (Z_to_bv 32 0x000ab583). Proof. fw. Qed.
Lemma F_38 : fetch_word segs (pcw b 0x38) = Some (Z_to_bv 32 0xfff58513). Proof. fw. Qed.
Lemma F_3c : fetch_word segs (pcw b 0x3c) = Some (Z_to_bv 32 0x00a5b633). Proof. fw. Qed.
Lemma F_40 : fetch_word segs (pcw b 0x40) = Some (Z_to_bv 32 0xfff60613). Proof. fw. Qed.
Lemma F_44 : fetch_word segs (pcw b 0x44) = Some (Z_to_bv 32 0x00a67633). Proof. fw. Qed.
Lemma F_48 : fetch_word segs (pcw b 0x48) = Some (Z_to_bv 32 0x04867263). Proof. fw. Qed.
Lemma F_5c : fetch_word segs (pcw b 0x5c) = Some (Z_to_bv 32 0x0006b803). Proof. fw. Qed.
Lemma F_60 : fetch_word segs (pcw b 0x60) = Some (Z_to_bv 32 0x00073683). Proof. fw. Qed.
Lemma F_64 : fetch_word segs (pcw b 0x64) = Some (Z_to_bv 32 0xfff80793). Proof. fw. Qed.
Lemma F_68 : fetch_word segs (pcw b 0x68) = Some (Z_to_bv 32 0x0087f463). Proof. fw. Qed.
Lemma F_6c : fetch_word segs (pcw b 0x6c) = Some (Z_to_bv 32 0x0286f063). Proof. fw. Qed.
Lemma F_78 : fetch_word segs (pcw b 0x78) = Some (Z_to_bv 32 0x00073283). Proof. fw. Qed.
Lemma F_7c : fetch_word segs (pcw b 0x7c) = Some (Z_to_bv 32 0x0032d713). Proof. fw. Qed.
Lemma F_80 : fetch_word segs (pcw b 0x80) = Some (Z_to_bv 32 0x00b708b3). Proof. fw. Qed.
Lemma F_84 : fetch_word segs (pcw b 0x84) = Some (Z_to_bv 32 0x1282e063). Proof. fw. Qed.
Lemma F_88 : fetch_word segs (pcw b 0x88) = Some (Z_to_bv 32 0x1088fe63). Proof. fw. Qed.
Lemma F_8c : fetch_word segs (pcw b 0x8c) = Some (Z_to_bv 32 0x00848933). Proof. fw. Qed.
Lemma F_90 : fetch_word segs (pcw b 0x90) = Some (Z_to_bv 32 0x05267263). Proof. fw. Qed.
Lemma F_a4 : fetch_word segs (pcw b 0xa4) = Some (Z_to_bv 32 0x00063783). Proof. fw. Qed.
Lemma F_a8 : fetch_word segs (pcw b 0xa8) = Some (Z_to_bv 32 0x0006b603). Proof. fw. Qed.
Lemma F_ac : fetch_word segs (pcw b 0xac) = Some (Z_to_bv 32 0xfff78713). Proof. fw. Qed.
Lemma F_b0 : fetch_word segs (pcw b 0xb0) = Some (Z_to_bv 32 0x01277463). Proof. fw. Qed.
Lemma F_b4 : fetch_word segs (pcw b 0xb4) = Some (Z_to_bv 32 0x03267063). Proof. fw. Qed.
Lemma F_c0 : fetch_word segs (pcw b 0xc0) = Some (Z_to_bv 32 0x0006b883). Proof. fw. Qed.
Lemma F_c4 : fetch_word segs (pcw b 0xc4) = Some (Z_to_bv 32 0x0038d693). Proof. fw. Qed.
Lemma F_c8 : fetch_word segs (pcw b 0xc8) = Some (Z_to_bv 32 0x00b68833). Proof. fw. Qed.
Lemma F_cc : fetch_word segs (pcw b 0xcc) = Some (Z_to_bv 32 0x1328e463). Proof. fw. Qed.
Lemma F_d0 : fetch_word segs (pcw b 0xd0) = Some (Z_to_bv 32 0x13287263). Proof. fw. Qed.
Lemma F_d4 : fetch_word segs (pcw b 0xd4) = Some (Z_to_bv 32 0x23247863). Proof. fw. Qed.
Lemma F_d8 : fetch_word segs (pcw b 0xd8) = Some (Z_to_bv 32 0x00740513). Proof. fw. Qed.
Lemma F_dc : fetch_word segs (pcw b 0xdc) = Some (Z_to_bv 32 0xff857513). Proof. fw. Qed.
Lemma F_e0 : fetch_word segs (pcw b 0xe0) = Some (Z_to_bv 32 0xff897a13). Proof. fw. Qed.
Lemma F_e4 : fetch_word segs (pcw b 0xe4) = Some (Z_to_bv 32 0xa91ff0ef). Proof. fw. Qed.
Lemma F_e8 : fetch_word segs (pcw b 0xe8) = Some (Z_to_bv 32 0x00050993). Proof. fw. Qed.
Lemma F_ec : fetch_word segs (pcw b 0xec) = Some (Z_to_bv 32 0x000a0513). Proof. fw. Qed.
Lemma F_f0 : fetch_word segs (pcw b 0xf0) = Some (Z_to_bv 32 0xa85ff0ef). Proof. fw. Qed.
Lemma F_f4 : fetch_word segs (pcw b 0xf4) = Some (Z_to_bv 32 0x000ab583). Proof. fw. Qed.
Lemma F_f8 : fetch_word segs (pcw b 0xf8) = Some (Z_to_bv 32 0x00345613). Proof. fw. Qed.
Lemma F_fc : fetch_word segs (pcw b 0xfc) = Some (Z_to_bv 32 0x00c58633). Proof. fw. Qed.
Lemma F_100 : fetch_word segs (pcw b 0x100) = Some (Z_to_bv 32 0x00060603). Proof. fw. Qed.
Lemma F_104 : fetch_word segs (pcw b 0x104) = Some (Z_to_bv 32 0x00060663). Proof. fw. Qed.
Lemma F_108 : fetch_word segs (pcw b 0x108) = Some (Z_to_bv 32 0x00747693). Proof. fw. Qed.
Lemma F_10c : fetch_word segs (pcw b 0x10c) = Some (Z_to_bv 32 0x02c6d063). Proof. fw. Qed.
Lemma F_110 : fetch_word segs (pcw b 0x110) = Some (Z_to_bv 32 0xfff90913). Proof. fw. Qed.
Lemma F_114 : fetch_word segs (pcw b 0x114) = Some (Z_to_bv 32 0x00395613). Proof. fw. Qed.
Lemma F_118 : fetch_word segs (pcw b 0x118) = Some (Z_to_bv 32 0x00c585b3). Proof. fw. Qed.
Lemma F_11c : fetch_word segs (pcw b 0x11c) = Some (Z_to_bv 32 0x00058583). Proof. fw. Qed.
Lemma F_120 : fetch_word segs (pcw b 0x120) = Some (Z_to_bv 32 0x04058263). Proof. fw. Qed.
Lemma F_124 : fetch_word segs (pcw b 0x124) = Some (Z_to_bv 32 0x00797613). Proof. fw. Qed.
Lemma F_128 : fetch_word segs (pcw b 0x128) = Some (Z_to_bv 32 0x02b64e63). Proof. fw. Qed.
Lemma F_12c : fetch_word segs (pcw b 0x12c) = Some (Z_to_bv 32 0x000ab503). Proof. fw. Qed.
Lemma F_130 : fetch_word segs (pcw b 0x130) = Some (Z_to_bv 32 0x00040593). Proof. fw. Qed.
Lemma F_134 : fetch_word segs (pcw b 0x134) = Some (Z_to_bv 32 0x0140006f). Proof. fw. Qed.
Lemma F_138 : fetch_word segs (pcw b 0x138) = Some (Z_to_bv 32 0x00140413). Proof. fw. Qed.
Lemma F_13c : fetch_word segs (pcw b 0x13c) = Some (Z_to_bv 32 0xfff48493). Proof. fw. Qed.
Lemma F_140 : fetch_word segs (pcw b 0x140) = Some (Z_to_bv 32 0x00158593). Proof. fw. Qed.
Lemma F_144 : fetch_word segs (pcw b 0x144) = Some (Z_to_bv 32 0x1e048063). Proof. fw. Qed.
Lemma F_148 : fetch_word segs (pcw b 0x148) = Some (Z_to_bv 32 0x00345613). Proof. fw. Qed.
Lemma F_14c : fetch_word segs (pcw b 0x14c) = Some (Z_to_bv 32 0x00c50633). Proof. fw. Qed.
Lemma F_150 : fetch_word segs (pcw b 0x150) = Some (Z_to_bv 32 0x00060603). Proof. fw. Qed.
Lemma F_154 : fetch_word segs (pcw b 0x154) = Some (Z_to_bv 32 0xfe0602e3). Proof. fw. Qed.
Lemma F_158 : fetch_word segs (pcw b 0x158) = Some (Z_to_bv 32 0x0075f693). Proof. fw. Qed.
Lemma F_15c : fetch_word segs (pcw b 0x15c) = Some (Z_to_bv 32 0xfcc6cee3). Proof. fw. Qed.
Lemma F_160 : fetch_word segs (pcw b 0x160) = Some (Z_to_bv 32 0x01c0006f). Proof. fw. Qed.
Lemma F_164 : fetch_word segs (pcw b 0x164) = Some (Z_to_bv 32 0x00a9fa63). Proof. fw. Qed.
Lemma F_168 : fetch_word segs (pcw b 0x168) = Some (Z_to_bv 32 0x413505b3). Proof. fw. Qed.
Lemma F_16c : fetch_word segs (pcw b 0x16c) = Some (Z_to_bv 32 0x00098513). Proof. fw. Qed.
Lemma F_174 : fetch_word segs (pcw b 0x174) = Some (Z_to_bv 32 0xfa050ce3). Proof. fw. Qed.
Lemma F_178 : fetch_word segs (pcw b 0x178) = Some (Z_to_bv 32 0x00000413). Proof. fw. Qed.
Lemma F_17c : fetch_word segs (pcw b 0x17c) = Some (Z_to_bv 32 0x00040513). Proof. fw. Qed.
Lemma F_180 : fetch_word segs (pcw b 0x180) = Some (Z_to_bv 32 0x03813083). Proof. fw. Qed.
Lemma F_184 : fetch_word segs (pcw b 0x184) = Some (Z_to_bv 32 0x03013403). Proof. fw. Qed.
Lemma F_188 : fetch_word segs (pcw b 0x188) = Some (Z_to_bv 32 0x02813483). Proof. fw. Qed.
Lemma F_18c : fetch_word segs (pcw b 0x18c) = Some (Z_to_bv 32 0x02013903). Proof. fw. Qed.
Lemma F_190 : fetch_word segs (pcw b 0x190) = Some (Z_to_bv 32 0x01813983). Proof. fw. Qed.
Lemma F_194 : fetch_word segs (pcw b 0x194) = Some (Z_to_bv 32 0x01013a03). Proof. fw. Qed.
Lemma F_198 : fetch_word segs (pcw b 0x198) = Some (Z_to_bv 32 0x00813a83). Proof. fw. Qed.
Lemma F_19c : fetch_word segs (pcw b 0x19c) = Some (Z_to_bv 32 0x04010113). Proof. fw. Qed.
Lemma F_1a0 : fetch_word segs (pcw b 0x1a0) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.
Lemma G_8 : fetch_word segs (pcw h 0x8) = Some (Z_to_bv 32 0x0005b583). Proof. fwh. Qed.
Lemma G_c : fetch_word segs (pcw h 0xc) = Some (Z_to_bv 32 0xfff58613). Proof. fwh. Qed.
Lemma G_10 : fetch_word segs (pcw h 0x10) = Some (Z_to_bv 32 0x00c5b6b3). Proof. fwh. Qed.
Lemma G_14 : fetch_word segs (pcw h 0x14) = Some (Z_to_bv 32 0xfff68693). Proof. fwh. Qed.
Lemma G_18 : fetch_word segs (pcw h 0x18) = Some (Z_to_bv 32 0x00c6f6b3). Proof. fwh. Qed.
Lemma G_1c : fetch_word segs (pcw h 0x1c) = Some (Z_to_bv 32 0x04a6f263). Proof. fwh. Qed.
Lemma G_30 : fetch_word segs (pcw h 0x30) = Some (Z_to_bv 32 0x0006b803). Proof. fwh. Qed.
Lemma G_34 : fetch_word segs (pcw h 0x34) = Some (Z_to_bv 32 0x00073683). Proof. fwh. Qed.
Lemma G_38 : fetch_word segs (pcw h 0x38) = Some (Z_to_bv 32 0xfff80793). Proof. fwh. Qed.
Lemma G_3c : fetch_word segs (pcw h 0x3c) = Some (Z_to_bv 32 0x00a7f463). Proof. fwh. Qed.
Lemma G_40 : fetch_word segs (pcw h 0x40) = Some (Z_to_bv 32 0x02a6f063). Proof. fwh. Qed.
Lemma G_4c : fetch_word segs (pcw h 0x4c) = Some (Z_to_bv 32 0x00073283). Proof. fwh. Qed.
Lemma G_50 : fetch_word segs (pcw h 0x50) = Some (Z_to_bv 32 0x0032d713). Proof. fwh. Qed.
Lemma G_54 : fetch_word segs (pcw h 0x54) = Some (Z_to_bv 32 0x00b708b3). Proof. fwh. Qed.
Lemma G_58 : fetch_word segs (pcw h 0x58) = Some (Z_to_bv 32 0x00a2ea63). Proof. fwh. Qed.
Lemma G_5c : fetch_word segs (pcw h 0x5c) = Some (Z_to_bv 32 0x00a8f863). Proof. fwh. Qed.
Lemma G_60 : fetch_word segs (pcw h 0x60) = Some (Z_to_bv 32 0x00355513). Proof. fwh. Qed.
Lemma G_64 : fetch_word segs (pcw h 0x64) = Some (Z_to_bv 32 0x00a58533). Proof. fwh. Qed.
Lemma G_68 : fetch_word segs (pcw h 0x68) = Some (Z_to_bv 32 0x00008067). Proof. fwh. Qed.

(* [comment removed for export] *)
Definition globals (mem : word -> option byte) : Prop :=
  cell8 segs mem gK aK /\ cell8 segs mem aK 0x7fff8000 /\ cell8 segs mem gMB aMB /\ cell8 segs mem aMB 0 /\
  cell8 segs mem gME aME /\ cell8 segs mem aME 0 /\ cell8 segs mem gHE aHE /\ cell8 segs mem aHE 0x7fffffffffff.
Definition globals_nl (model : Model) : Prop :=
  no_lazy model gK (gK + 8) /\ no_lazy model aK (aK + 8) /\ no_lazy model gMB (gMB + 8) /\ no_lazy model aMB (aMB + 8) /\
  no_lazy model gME (gME + 8) /\ no_lazy model aME (aME + 8) /\ no_lazy model gHE (gHE + 8) /\ no_lazy model aHE (aHE + 8).
Lemma srl3 : forall x : Z, (0 <= x < 2 ^ 64)%Z -> alu64 ALU_SRL (Z_to_bv 64 x) (zext 64 (@BV 6 3 I)) = Z_to_bv 64 (x / 8).
Proof.
  intros x Hx. apply bv_eq. cbn [alu64 alu].
  replace (bv_and (zext 64 (@BV 6 3 I)) (Z_to_bv 64 63)) with (Z_to_bv 64 3) by (apply bv_eq; vm_compute; reflexivity).
  rewrite bv_shiftr_unsigned. rewrite !bvu_z by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma cell_nl : forall model a, (0 <= a < 2 ^ 60)%Z -> no_lazy model a (a + 8) ->
  acc_ok model [(Z_to_bv 64 a, 8%nat)].
Proof. intros model a Ha Hn. apply acc_ok_one; rewrite bvu_z by lia; [lia | exact Hn]. Qed.
(* [comment removed for export] *)
Ltac wpair P Hl Hv Hnl :=
  let wa := fresh "wa" in let wl := fresh "wl" in let ia := fresh "ia" in let il := fresh "il" in
  let HFa := fresh "HFa" in let HEa := fresh "HEa" in let HDa := fresh "HDa" in
  let HFl := fresh "HFl" in let HEl := fresh "HEl" in let HDl := fresh "HDl" in let HA := fresh "HA" in
  destruct (pair_ok_sound _ _ _ _ _ _ P ltac:(lia)) as (wa & wl & ia & il & HFa & HEa & HDa & HFl & HEl & HDl & HA);
  eapply rzc_acc; [ assumption | first [ reflexivity | assumption ]
                  | eapply wacc_Auipc; [ fetch_tac HFa | exact HEa | exact HDa ] | apply acc_ok_nil | ];
  try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); pcn;
  eapply rzc_acc; [ assumption | reflexivity
                  | eapply wacc_Load; [ fetch_tac HFl | exact HEl | exact HDl | rgn; rewrite HA, ?mem_setx; exact Hl ]
                  | rgn; rewrite HA; apply cell_nl; [lia | exact Hnl]
                  | ];
  pcn; rewrite Hv.

(* [comment removed for export] *)
Ltac wvar F D Hl Hv Hnl :=
  eapply rzc_acc; [ assumption | reflexivity
                  | eapply wacc_Load; [ fetch_tac F | reflexivity | exact D | rgn; rewrite add_sext0, ?mem_setx; exact Hl ]
                  | rgn; rewrite add_sext0; apply cell_nl; [lia | exact Hnl]
                  | ];
  pcn; rewrite Hv.

Section Helper.
Variable model : Model.
Hypothesis Hh : m_halted model = None.

(* [comment removed for export] *)
Lemma h_sum : forall ms T (x : Z),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw h 0 -> rg ms 10 = Z_to_bv 64 x ->
  ((0 <= x <= 0x7fff7fff) \/ (0x10007fff8000 <= x <= 0x7fffffffffff))%Z ->
  globals (ms_mem ms) -> globals_nl model ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms', FR HCLOB ms ms' -> ms_pc_val ms' = rg ms 1 -> rg ms' 10 = Z_to_bv 64 (0x7fff8000 + x / 8) ->
     realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms T x Hsvc Hpc H10 Hx HG HN Hra HK.
  destruct HG as ((lgK & HlgK & HvgK) & (laK & HlaK & HvaK) & (lgMB & HlgMB & HvgMB) & (laMB & HlaMB & HvaMB) &
                  (lgME & HlgME & HvgME) & (laME & HlaME & HvaME) & (lgHE & HlgHE & HvgHE) & (laHE & HlaHE & HvaHE)).
  destruct HN as (NgK & NaK & NgMB & NaMB & NgME & NaME & NgHE & NaHE).
  wpair HPh0 HlgK HvgK NgK.
  wvar G_8 D_0005b583 HlaK HvaK NaK.
  wsx wacc_OpImm G_c D_fff58613. rgn. cnorm.
  wsx wacc_Op G_10 D_00c5b6b3. rgn. cnorm.
  wsx wacc_OpImm G_14 D_fff68693. rgn. cnorm.
  wsx wacc_Op G_18 D_00c6f6b3. rgn. cnorm.
  wsx wacc_Branch G_1c D_04a6f263. rgn. rewrite H10, branch_geu_z by lia.
  destruct Hx as [Hlo|Hx].
  { (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_ge _ x)) by lia. cbn [negb]. pcn.
    wsx wacc_ShiftImm G_60 D_00355513. rgn. rewrite H10, srl3 by lia.
    wsx wacc_Op G_64 D_00a58533. rgn. rewrite alu_add, zw_add.
    eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Jalr; [ fetch_tac G_68 | reflexivity | exact D_00008067 ] | apply acc_ok_nil | ].
    rgn. rewrite ?pc_setx, ret_even by exact Hra.
    apply HK; [ frs (FR_refl HCLOB ms Hsvc) | reflexivity | rgn; reflexivity ]. }
  rewrite (proj2 (Z.ltb_lt _ x)) by lia. cbn [negb]. pcn.
  wpair HPh20 HlgMB HvgMB NgMB.
  wpair HPh28 HlgME HvgME NgME.
  wvar G_30 D_0006b803 HlaMB HvaMB NaMB.
  wvar G_34 D_00073683 HlaME HvaME NaME.
  wsx wacc_OpImm G_38 D_fff80793. rgn. cnorm.
  wsx wacc_Branch G_3c D_00a7f463. rgn. rewrite H10, branch_geu_z by lia. rewrite (proj2 (Z.ltb_ge _ x)) by lia. cbn [negb]. pcn.
  wpair HPh44 HlgHE HvgHE NgHE.
  wvar G_4c D_00073283 HlaHE HvaHE NaHE.
  wsx wacc_ShiftImm G_50 D_0032d713. rgn. cnorm.
  wsx wacc_Op G_54 D_00b708b3. rgn. cnorm.
  wsx wacc_Branch G_58 D_00a2ea63. rgn. rewrite H10, branch_ltu_z by lia. rewrite (proj2 (Z.ltb_ge _ x)) by lia. pcn.
  wsx wacc_Branch G_5c D_00a8f863. rgn. rewrite H10, branch_geu_z by lia. rewrite (proj2 (Z.ltb_lt _ x)) by lia. cbn [negb]. pcn.
  wsx wacc_ShiftImm G_60 D_00355513. rgn. rewrite H10, srl3 by lia.
  wsx wacc_Op G_64 D_00a58533. rgn. rewrite alu_add, zw_add.
  eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Jalr; [ fetch_tac G_68 | reflexivity | exact D_00008067 ] | apply acc_ok_nil | ].
  rgn. rewrite ?pc_setx, ret_even by exact Hra.
  apply HK; [ frs (FR_refl HCLOB ms Hsvc) | reflexivity | rgn; reflexivity ].
Qed.
End Helper.
(* [comment removed for export] *)
Definition RPOST (S S' : machine_state) (lo hi : Z) : Prop :=
  ms_svc_pending S' = None /\ ms_rom S' = ms_rom S /\ ms_fregs S' = ms_fregs S /\ ms_fcsr S' = ms_fcsr S /\
  (ms_resv S' = ms_resv S \/ ms_resv S' = None) /\ (forall r, ~ In r HCLOB -> rg S' r = rg S r) /\
  (forall x : word, ~ (lo <= bv_unsigned x < hi)%Z -> ms_mem S' x = ms_mem S x) /\ mem_grows (ms_mem S) (ms_mem S').

(* [comment removed for export] *)
Definition BCLOB : list reg := [5; 10; 11; 12; 13; 14; 15; 16; 17; 1; 2; 8; 9; 18; 19; 20; 21].


End Rip.
