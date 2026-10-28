(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma huf_type_read : forall (dtb : list byte) ty, nth_error dtb 1 = Some ty ->
  extz false 1 (bytes_le_to_Z (firstn 1 (skipn (Z.to_nat 1) dtb))) = bv_unsigned ty.
Proof.
  intros dtb ty H. change (Z.to_nat 1) with 1%nat.
  destruct dtb as [|x0 [|x1 r]]; cbn in H; try discriminate. injection H as ->.
  cbn [skipn firstn]. unfold extz. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. reflexivity.
Qed.

Ltac huf_disp_tac T1 T2 U H1 H2 :=
  let PRE := fresh "PRE" in let DTP := fresh "DTP" in let TOK := fresh "TOK" in
  intros PRE DTP TOK;
  let DTB := fresh "DTB" in let DL := fresh "DL" in let TY := fresh "TY" in let TLB := fresh "TLB" in
  let TLR := fresh "TLR" in let X2 := fresh "X2" in let HDR := fresh "HDR" in let NB := fresh "NB" in
  let ty := fresh "ty" in let tl := fresh "tl" in
  pose proof PRE as (MI & _);
  pose proof DTP as (DTB & DL & ? & ? & ? & ? & ?);
  pose proof TOK as (HDR & ty & tl & TY & TLB & TLR & X2 & NB);
  unfold HUF_DTABLE_BYTES in *;
  lazymatch type of DTB with
  | bytes_at _ _ ?DT ?dtb =>
      kx_auto [T1; T2] 10%nat [KZRange DT 4096 (2^47); KZAlign DT 4] [(DT, 16388)];
      lazymatch goal with |- context [Z_to_bv 64 U] => kx_trap_fast | _ => idtac end;
      (let RD := fresh "RD" in
       kx_read_eq 31%nat RD;
       rewrite (rdval_bytes_at usegs _ DT dtb 1 1 false DTB ltac:(lia) ltac:(change (Z.to_nat 1) with 1%nat; lia)),
               (huf_type_read dtb ty TY) in RD;
       rewrite RD in *;
       rewrite Z_to_bv_unsigned, bv_wrap_small in *
         by (pose proof (bv_unsigned_in_range 8 ty) as RB; unfold bv_modulus in *; change (2 ^ Z.of_N 8) with 256 in RB;
             change (2 ^ Z.of_N 64) with (2^64); lia));
      [ (* [comment removed for export] *)
        eapply H1; [exact PRE | exact DTP | exact TLB | exact TLR | let X := fresh "X" in intro X; discriminate X |
                    match goal with K : bv_unsigned ty = 0 |- _ => rewrite K in NB end; exact NB]
      | (* [comment removed for export] *)
        eapply H2; [exact PRE | exact DTP | exact TLB | exact TLR | intros _; apply X2; assumption |
                    match goal with K : bv_unsigned ty <> 0 |- _ => apply Z.eqb_neq in K; rewrite K in NB end; exact NB] ]
  end.

Theorem huf_1x_proof : huf_1x1_stmt -> huf_1x2_stmt -> huf_1x_stmt.
Proof.
  intros H1 H2. unfold huf_1x_stmt, huf_using_stmt_at, PHUF_1X, HUF_1X_STACK.
  unfold huf_1x1_stmt, huf_1x2_stmt, huf_int_stmt_at, PHUF_1X1, PHUF_1X2 in *.
  intros until dtb. huf_disp_tac 0x20814 0x1fb64 0x20810 H1 H2.
Qed.

Theorem huf_4x_proof : huf_4x1_stmt -> huf_4x2_stmt -> huf_4x_stmt.
Proof.
  intros H1 H2. unfold huf_4x_stmt, huf_using_stmt_at, PHUF_4X.
  unfold huf_4x1_stmt, huf_4x2_stmt, huf_int_stmt_at, PHUF_4X1, PHUF_4X2 in *.
  intros until dtb. huf_disp_tac 0x22194 0x20d94 0x20d90 H1 H2.
Qed.
