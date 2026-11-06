(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the per-instruction STEP WRAPPERS the DUP segment of pj_set's image-B walk needs
   (fuzz_preset asan-ubsan, B 0x86e8c; the cuts of lib/B/Prog/pj_set_defs.v). lib/B/Prog/pj_set_seg_tail.v has the
   three the TAIL segment needed (addi / jal / j); the stretch +0xb0 .. +0x1a4 also loads, stores, shifts, compares
   and branches, so this file adds one wrapper per instruction class of that stretch, each in the same shape: the
   image word at the offset, its decoding, the value the instruction writes, the next pc, and the continuation.
   The store wrapper hands the continuation the new memory through its properties (the eight bytes written,
   every other byte kept, presence kept, writability kept, and the memnorm keep: a store under store_ok keeps
   YAkMemnorm.memnorm, YAkMemnorm.v memnorm_write / memnorm_munrestrict), so no caller ever names `munrestrict`.
   Also: the two READ helpers the stretch needs - a 64-bit field of a struct (`rd_u64`) read by `ld`, and a shadow
   byte of an 8-aligned 8-byte range read by `lbu`, which `range_addressable` forces to 0.
   proves no function (kind: reusable step lemmas).
   Numerals: 8 / 1 (LENGTH: access widths); 4 (DERIVED: the instruction length). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YN01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_set_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

Lemma pjsd_nth_of_error : forall (A : Type) (l : list A) (n : nat) (x d : A),
  nth_error l n = Some x -> nth n l d = x.
Proof.
intros A l; induction l as [|y l IH]; intros n x d H; destruct n as [|n]; cbn in H |- *;
  try discriminate H; [injection H as <-; reflexivity | apply IH; exact H].
Qed.

(* ---- the memory a store leaves, read off through mrestrict ---- *)
Lemma pjsd_unrestrict_mkst : forall `{fx : YK11.FPState} (H : word -> bool) (full : word -> option byte)
  (regs : bvmap 5 word) (pc : word) (m rom : word -> option byte),
  unrestrict H full (@YK11.mkst fx regs pc m rom) = @YK11.mkst fx regs pc (munrestrict H full m) rom.
Proof. intros. reflexivity. Qed.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).

(* ---- the ALU wrappers: one per instruction class of the stretch ---- *)
Lemma pjsd_addi : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_addi (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_andi : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_andi (getr regs rs) (bv_signed imm) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_andi (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_sltiu : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_sltiu (getr regs rs) (bv_signed imm) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_sltiu (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_slli : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (sh : bv 6) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_slli (getr regs rs) (bv_unsigned sh) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs sh rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_slli (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs sh (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_srli : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (sh : bv 6) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_srli (getr regs rs) (bv_unsigned sh) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs sh rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_srli (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs sh (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_srai : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (sh : bv 6) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_srai (getr regs rs) (bv_unsigned sh) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs sh rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_srai (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs sh (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_add : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs1 rs2 : bv 5) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_add (getr regs rs1) (getr regs rs2) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs1 rs2 rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_add (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs1 rs2 (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_sub : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs1 rs2 : bv 5) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_sub (getr regs rs1) (getr regs rs2) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs1 rs2 rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_sub (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs1 rs2 (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_sltu : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs1 rs2 : bv 5) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_sltu (getr regs rs1) (getr regs rs2) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs1 rs2 rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_sltu (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs1 rs2 (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_xor : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs1 rs2 : bv 5) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Op ALU_XOR rd rs1 rs2, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_xor (getr regs rs1) (getr regs rs2) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs1 rs2 rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_xor (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs1 rs2 (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_mulh : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs1 rs2 : bv 5) (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Mul M_MULH rd rs1 rs2, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_mulh (getr regs rs1) (getr regs rs2) = v ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs1 rs2 rd' v pc' Hl Hd Hrd Hrr Hv Hpc HK. subst rd' v pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_mulh (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs1 rs2 (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

(* ---- the loads ---- *)
Lemma pjsd_ld : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (imm : bv 12) bs (rd' : bv 5) (v pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) ->
  rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs) (bv_signed imm)) 8%nat = Some bs ->
  bytes_le_to_Z bs = bv_unsigned v ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' v) pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm bs rd' v pc' Hl Hd Hr Hv Hrd Hrr Hpc HK. subst rd' pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_ld (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm bs v (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hr Hv).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_lbu : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (b : byte) (pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4%Z) ->
  rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs) (bv_signed imm)) 1%nat = Some [b] ->
  bv_eqb rd (0%bv : bv 5) = false ->
  rd = rd' ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' (Z_to_bv 64 (bv_unsigned b))) pc' mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm rd' b pc' Hl Hd Hr Hrd Hrr Hpc HK. subst rd' pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_lbu (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm b (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hr).
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

(* ---- the branches ---- *)
Lemma pjsd_beq_ft : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rs1 rs2 : bv 5) (imm : bv 13) (pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = false ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx regs pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rs1 rs2 imm pc' Hl Hd Hc Hpc HK. subst pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_beq_ft (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_beq_tk : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rs1 rs2 : bv 5) (imm : bv 13) (pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx regs pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rs1 rs2 imm pc' Hl Hd Hc Hpc HK. subst pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_beq_tk (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_bne_ft : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rs1 rs2 : bv 5) (imm : bv 13) (pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs1 rs2 imm, 4%Z) ->
  c_eq (getr regs rs1) (getr regs rs2) = true ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx regs pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rs1 rs2 imm pc' Hl Hd Hc Hpc HK. subst pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_bne_ft (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

Lemma pjsd_bltu_ft : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rs1 rs2 : bv 5) (imm : bv 13) (pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Branch BC_LTU rs1 rs2 imm, 4%Z) ->
  c_ltu (getr regs rs1) (getr regs rs2) = false ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx regs pc' mem (YK11.seg_rom SEGS))
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rs1 rs2 imm pc' Hl Hd Hc Hpc HK. subst pc'.
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_bltu_ft (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rs1 rs2 imm (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Hc).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)). apply HK.
Qed.

(* ---- the store: the continuation gets the new memory through its properties and its memnorm keep ---- *)
Lemma pjsd_sd : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k : Z) w (rs1 rs2 : bv 5) (imm : bv 12) (a : Z) (pc' : word),
  clookup (@pa_tbl _ B_prog_listing PA) (BASE + k) = Some w ->
  decode_any (Z_to_bv 32 w) = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 a ->
  0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> w_H W (Z_to_bv 64 x) = false) ->
  (forall x, a <= x < a + 8 -> writable_at SEGS (mrestrict (w_H W) mem) x) ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = pc' ->
  (forall X (mem' : word -> option byte),
     val_mem SEGS (mrestrict (w_H W) mem') a 8 (bv_unsigned (getr regs rs2)) ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + 8) ->
        aview SEGS (w_H W) mem' x = aview SEGS (w_H W) mem x) ->
     (forall x : word, ~ (a <= bv_unsigned x < a + 8) ->
        mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
     mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
     (forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x) ->
     (forall x, a <= x < a + 8 -> apresent (w_H W) mem' x) ->
     (forall x, w_H W x = true -> mem' x = mem x) ->
     (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem') ->
     SRr SEGS W (mkCfg (@YK11.mkst fx regs pc' mem' (YK11.seg_rom SEGS))
       (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rs1 rs2 imm a pc' Hl Hd Ha Ha0 Ha8 HH HWR Hpc HK. subst pc'.
set (bs := word_to_le_bytes 8 (getr regs rs2)).
assert (Hlen : length bs = 8%nat) by (unfold bs, word_to_le_bytes; apply length_Z_to_le_bytes).
assert (Hau : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
assert (HOK : RiscvSemantics.store_ok SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 a) 8%nat = true)
  by (apply writable_store_ok; [lia | lia | exact HWR]).
eapply (SRr_step SEGS (@pa_wx _ B_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  exact (step_sd_at (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rs1 rs2 imm (Z_to_bv 64 a) (getr regs rs2) (pa_fetch_ok (PI := PA) _ _ Hl)
    (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd Ha eq_refl HOK).
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (pjsd_unrestrict_mkst (fx := fx)).
  set (mw := wbytes (mrestrict (w_H W) mem) (Z_to_bv 64 a) bs).
  set (mem' := munrestrict (w_H W) mem mw).
  assert (Emr : mrestrict (w_H W) mem' = mrestrict (w_H W) mw)
    by (unfold mem'; apply mrestrict_munrestrict).
  (* the written bytes *)
  assert (HIN : forall j, (j < 8)%nat -> mrestrict (w_H W) mem' (Z_to_bv 64 (a + Z.of_nat j))
                  = Some (nth j bs (Z_to_bv 8 0))).
  { intros j Hj. rewrite Emr. unfold mrestrict at 1.
    rewrite (HH (a + Z.of_nat j) ltac:(lia)).
    unfold mw.
    replace (a + Z.of_nat j) with (bv_unsigned (Z_to_bv 64 a) + Z.of_nat j) by (rewrite Hau; reflexivity).
    apply AX2S.wbytes_nth; [rewrite Hau, Hlen; cbn [Z.of_nat]; lia | lia]. }
  (* every other byte is kept *)
  assert (HOUT : forall x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + 8) ->
                   mrestrict (w_H W) mem' (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
  { intros x Hx Hn.
    assert (Hmw : mw (Z_to_bv 64 x) = mrestrict (w_H W) mem (Z_to_bv 64 x)).
    { unfold mw. destruct (Z_lt_le_dec x a) as [Hlt | Hge].
      - apply wbytes_below; rewrite ?Hau, ?Hlen; cbn [Z.of_nat];
        [lia | rewrite unsigned_lit_small by lia; lia].
      - apply wbytes_above. rewrite Hau, Hlen. cbn [Z.of_nat].
        rewrite unsigned_lit_small by lia. lia. }
    rewrite Emr. unfold mrestrict at 1 2.
    destruct (w_H W (Z_to_bv 64 x)) eqn:Eh; [reflexivity|].
    rewrite Hmw. unfold mrestrict. rewrite Eh. reflexivity. }
  assert (HPRES : forall x, apresent (w_H W) mem x -> apresent (w_H W) mem' x).
  { intros x (Hh & b & Hb). split; [exact Hh|].
    unfold mem', munrestrict. rewrite Hh. unfold mw.
    destruct (Z_le_dec a (bv_unsigned (Z_to_bv 64 x))) as [H1|H1];
    [destruct (Z_lt_dec (bv_unsigned (Z_to_bv 64 x)) (a + 8)) as [H2|H2]|].
    - set (j := Z.to_nat (bv_unsigned (Z_to_bv 64 x) - a)).
      assert (Hj : (j < 8)%nat) by (unfold j; lia).
      replace (Z_to_bv 64 x) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a) + Z.of_nat j))
        by (apply bv_eq; rewrite !unsigned_lit_small by (unfold j; lia); unfold j; lia).
      rewrite (AX2S.wbytes_nth bs (mrestrict (w_H W) mem) (Z_to_bv 64 a) j
        ltac:(rewrite Hau, Hlen; cbn [Z.of_nat]; lia) ltac:(lia)).
      eexists. reflexivity.
    - rewrite wbytes_above by (rewrite Hau, Hlen; cbn [Z.of_nat]; lia).
      unfold mrestrict. rewrite Hh. exists b. exact Hb.
    - rewrite wbytes_below by (rewrite ?Hau, ?Hlen; cbn [Z.of_nat]; lia).
      unfold mrestrict. rewrite Hh. exists b. exact Hb. }
  apply (HK _ mem').
  + intros j Hj. unfold val_mem, mbyte. rewrite (HIN j Hj). f_equal.
    pose proof (nth_error_Z_to_le_bytes 8 (bv_unsigned (getr regs rs2)) j Hj) as Hne.
    assert (Hnn : nth j (Z_to_le_bytes 8 (bv_unsigned (getr regs rs2))) (Z_to_bv 8 0)
      = Z_to_bv 8 (Z.shiftr (bv_unsigned (getr regs rs2)) (8 * Z.of_nat j)))
      by (apply (pjsd_nth_of_error _ _ _ _ _ Hne)).
    unfold bs, word_to_le_bytes. rewrite Hnn.
    rewrite (le_byte_bv (bv_unsigned (getr regs rs2)) 8 j Hj).
    f_equal. f_equal. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
    pose proof (u64_range (getr regs rs2)). rewrite Z.mod_small by lia. reflexivity.
  + intros x Hx Hn. unfold aview, mbyte. rewrite (HOUT x Hx Hn). reflexivity.
  + intros x Hn. pose proof (HOUT (bv_unsigned x) (u64_range x) Hn) as HE.
    rewrite Z_to_bv_bv_unsigned in HE. exact HE.
  + intros x Hx. unfold mrestrict in Hx |- *. destruct (w_H W x) eqn:Eh; [exact Hx|].
    destruct (mem x) as [b|] eqn:Em; [|exfalso; apply Hx; reflexivity].
    assert (Hp : apresent (w_H W) mem (bv_unsigned x))
      by (split; rewrite Z_to_bv_bv_unsigned; [exact Eh | exists b; exact Em]).
    destruct (HPRES _ Hp) as (_ & b' & Hb'). rewrite Z_to_bv_bv_unsigned in Hb'.
    rewrite Hb'. discriminate.
  + exact HPRES.
  + intros x Hx. split; [exact (HH x Hx)|].
    assert (Hj : (Z.to_nat (x - a) < 8)%nat) by lia.
    pose proof (HIN (Z.to_nat (x - a)) Hj) as HI.
    replace (a + Z.of_nat (Z.to_nat (x - a))) with x in HI by lia.
    unfold mrestrict in HI. rewrite (HH x Hx) in HI.
    rewrite HI. eexists. reflexivity.
  + intros x Hh. unfold mem', munrestrict. rewrite Hh. reflexivity.
  + (* the memnorm keep: the merged memory of a store under store_ok *)
    intros HMN. unfold mem'. apply (YAkMemnorm.memnorm_munrestrict SEGS); [exact HMN|].
    unfold mw. rewrite <- write_to_mem_wbytes.
    apply (YAkMemnorm.memnorm_write SEGS); [apply (YAkMemnorm.memnorm_mrestrict SEGS); exact HMN|].
    rewrite Hlen. exact HOK.
Qed.

(* ---- the two reads ---- *)
(* an 8-byte field whose value the caller already knows *)
Lemma pjsd_rd8 : forall (W : world SEGS) (mem : word -> option byte) (p v : Z),
  rd_u64 SEGS (mrestrict (w_H W) mem) p v -> 0 <= p -> p + 8 <= 2 ^ 64 ->
  exists bs, rdn SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 p) 8%nat = Some bs /\
    bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 v).
Proof.
intros W mem p v (Hv & Hm) Hp0 Hp8.
apply (word_mem_ld SEGS (mrestrict (w_H W) mem) p v); [|lia|lia].
apply (proj1 (val_mem_word_mem SEGS (mrestrict (w_H W) mem) p v)). exact Hm.
Qed.

(* the shadow byte of an 8-aligned, 8-byte addressable range is 0 *)
Lemma pjsd_sh0 : forall (W : world SEGS) (mem : word -> option byte) (p : Z),
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p 8 -> p mod 8 = 0 ->
  exists b : byte, rdn SEGS (mrestrict (w_H W) mem) (Z_to_bv 64 (shadow_addr p)) 1%nat = Some [b] /\
    bv_unsigned b = 0.
Proof.
intros W mem p HR Hal.
destruct (range_addressable_present (aview SEGS (w_H W) mem) SHADOW_OFF p 8 p HR ltac:(lia)) as (s & Hs).
assert (Hz : s = 0).
{ apply (check_passes_whole (aview SEGS (w_H W) mem) SHADOW_OFF p 8 p 8 s HR ltac:(lia) ltac:(lia));
  [pose proof (Z.div_mod p 8 ltac:(lia)); lia | exact Hs]. }
subst s. unfold aview in Hs.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (shadow_of_addr SHADOW_OFF p)) as [b|] eqn:Eb;
  [|cbn in Hs; discriminate Hs].
cbn in Hs. injection Hs as Hs.
exists b. split; [|exact Hs].
apply byte1_rdn. unfold shadow_addr. exact Eb.
Qed.

End h.
