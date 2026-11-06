(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module names changed; 299 of its 346 lines of code are new or changed and 731 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Rtt102FR1KitA.v; 35 of its 346 lines of code are new or changed and 35 lines of the source are left out. *)
(* B' TWIN (asan-ubsan d663f82d7f488d30, unstripped twin c90d4fa54d43160b) of lib/A/Prog/Rtt102FR1KitA.v, by a name map:
   round_trip_text's body on image B is image A's instruction sequence with only pc-relative immediates changed
   (capstone over both twins' symtab bodies; every call site at the same offset), so the twin is the A' file with
   image A's listing / image / PrhImg / CfImg names replaced by image B's (A_prog_* -> B_prog_*, PI_prog_A /
   PL_prog_A -> _B, prh_img_A -> prh_img_B, CfImg_A -> CfImg_B, S1ImgA -> S1ImgB, IMG_LO / IMG_TOP -> IMG_LO_B /
   IMG_TOP_B, the A' stretch modules Rtt102*A -> Rtt102*B, the file's own *_A names -> *_B) and image B's own value
   for each image numeral the file states (a load offset, the function's listing offset, a witness address); every
   closed image check is re-run at B' by the build. The comments below are the A' file's: their addresses and slot
   numbers are image A's. *)
(* fuzz_preset, image A' (asan, sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the A'-ONLY part of lane RttFR1's
   kit (WalkRtt102 for the text owner): the concrete steps of register-only code, whose premises compute on A''s listing, and
   the image facts the generic kit Rtt102FR1Kit.v takes as Section hypotheses, discharged at A'.
   rule 24: proves no function (kind: segment lemma helpers); the function-level lookup is the brief's.
   1. fr_addi / fr_jal / fr_beqz_tk / fr_beqz_ft: H5RttS4.v s4_addi / s4_jal / s4_beqz_tk / s4_beqz_ft
      (the H2H5 walk head 1934271f1f40), this lane's copy over YC4aP's classes. A stretch that writes no byte
      needs neither the symbolic runner's write premise nor its shadow tokens.
      fr_bnez_tk / fr_bnez_ft / fr_auipc / fr_ld / fr_lw / fr_lbu: the same over YK11.v's step_bne_* / step_auipc /
      step_ld / step_lw / step_lbu, a load's bytes read off a value cell by YN2e.v rdn_cell / bytes_le_to_Z_le_list.
   2. rtt_fp_B / rtt_stkr_B: Rtt102FR1Kit.v's RTT_FP / STKR_frame at A' (by computation); its pst_in_img / pst_not_ro are
      S1ImgB.v's pst_in_img_B / pst_not_ro_B.
   Numerals: 4 (LENGTH: instruction), 2 ^ 40 (LENGTH), 192 (LENGTH: Rtt102FR1Kit.v STKR_frame). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YN2e YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Rtt102Cut Rtt102FR1Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- 1. concrete steps (H5RttS4.v :118-255, this lane's copy) ---- *)
Section stp. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
#[local] Notation BASE := (@pa_val _ L PI A_TEXT).

Lemma fr_addi : forall (W : world SEGS) regs mem md Q w k (rd rs : bv 5) (imm : bv 12) (rd0 rs0 : bv 5) (i0 : Z),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
rd = rd0 -> rs = rs0 -> bv_signed imm = i0 ->
bv_eqb rd0 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx (regupd regs rd0 (v_addi (getr regs rs0) i0))
             (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rd rs imm rd0 rs0 i0 Hpl Hdec Erd Ers Ei Hrd Hk0 Hk4 HK. subst rd rs i0.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_addi SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd0 rs0 imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

(* a call slot is a PCall entry of the listing, not a PW word: the step reads the image's own code table *)
Lemma fr_jal : forall (W : world SEGS) regs mem md Q w k tgt (rd : bv 5) (imm : bv 21),
clookup pa_tbl (BASE + k) = Some w ->
decode_any (Z_to_bv 32 w) = Some (Jal rd imm, 4%Z) -> rd = 1%bv ->
0 <= k -> k + 4 < 2 ^ 40 ->
btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = Z_to_bv 64 tgt ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx (regupd regs 1%bv (Z_to_bv 64 (BASE + (k + 4))))
             (Z_to_bv 64 tgt) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k tgt rd imm Hl Hdec Hrd1 Hk0 Hk4 Htgt HK. subst rd.
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (H10 : bv_eqb (1%bv : bv 5) 0 = false) by (vm_compute; reflexivity).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_jal_link SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) 1%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite H10. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Htgt.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

(* `beqz rs, off`: beq rs, x0 - the taken and the fall-through step *)
Lemma fr_beqz_tk : forall (W : world SEGS) regs mem md Q w k tgt (rs r0 : bv 5) (imm : bv 13),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs r0 imm, 4%Z) -> r0 = 0%bv ->
0 <= k -> k + 4 < 2 ^ 40 ->
btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = Z_to_bv 64 tgt ->
c_eq (getr regs rs) (getr regs 0%bv) = true ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 tgt) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k tgt rs r0 imm Hpl Hdec Hr0 Hk0 Hk4 Htgt Hc HK. subst r0.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_beq_tk SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs 0%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Htgt. apply HK.
Qed.

Lemma fr_beqz_ft : forall (W : world SEGS) regs mem md Q w k (rs r0 : bv 5) (imm : bv 13),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_EQ rs r0 imm, 4%Z) -> r0 = 0%bv ->
0 <= k -> k + 4 < 2 ^ 40 ->
c_eq (getr regs rs) (getr regs 0%bv) = false ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rs r0 imm Hpl Hdec Hr0 Hk0 Hk4 Hc HK. subst r0.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_beq_ft SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs 0%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

(* `bnez rs, off`: bne rs, x0 - the taken and the fall-through step *)
Lemma fr_bnez_tk : forall (W : world SEGS) regs mem md Q w k tgt (rs r0 : bv 5) (imm : bv 13),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs r0 imm, 4%Z) -> r0 = 0%bv ->
0 <= k -> k + 4 < 2 ^ 40 ->
btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm) = Z_to_bv 64 tgt ->
c_eq (getr regs rs) (getr regs 0%bv) = false ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 tgt) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k tgt rs r0 imm Hpl Hdec Hr0 Hk0 Hk4 Htgt Hc HK. subst r0.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_bne_tk SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs 0%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict. rewrite Htgt. apply HK.
Qed.

Lemma fr_bnez_ft : forall (W : world SEGS) regs mem md Q w k (rs r0 : bv 5) (imm : bv 13),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Branch BC_NE rs r0 imm, 4%Z) -> r0 = 0%bv ->
0 <= k -> k + 4 < 2 ^ 40 ->
c_eq (getr regs rs) (getr regs 0%bv) = true ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rs r0 imm Hpl Hdec Hr0 Hk0 Hk4 Hc HK. subst r0.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_bne_ft SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rs 0%bv imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hc).
  reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

(* `auipc rd, imm`: rd := pc + (imm << 12); a relocated slot (the listing's PHi), so the step reads the image's code table *)
Lemma fr_auipc : forall (W : world SEGS) regs mem md Q w k (rd : bv 5) (imm : bv 20) (rd0 : bv 5),
clookup pa_tbl (BASE + k) = Some w ->
decode_any (Z_to_bv 32 w) = Some (Auipc rd imm, 4%Z) -> rd = rd0 ->
bv_eqb rd0 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx (regupd regs rd0 (v_auipc (Z_to_bv 64 (BASE + k)) (Z.shiftl (bv_signed imm) 12)))
             (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rd imm rd0 Hl Hdec Erd Hrd Hk0 Hk4 HK. subst rd.
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_auipc SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd0 imm (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

(* the loads read the world's view of memory (fr_lbu reads the code table: its slot is the listing's PLdHi) (the step runs on mrestrict (w_H W) mem); a value cell's bytes are
   YN2e.le_list of its value (YN2e.rdn_cell) and they decode back to it modulo the width (bytes_le_to_Z_le_list) *)
Lemma fr_ld : forall (W : world SEGS) regs mem md Q w k (rd rs : bv 5) (imm : bv 12) (rd0 rs0 : bv 5) (a v : Z),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) ->
rd = rd0 -> rs = rs0 -> v_addi (getr regs rs0) (bv_signed imm) = Z_to_bv 64 a ->
val_mem SEGS (mrestrict (w_H W) mem) a 8 v ->
bv_eqb rd0 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx (regupd regs rd0 (Z_to_bv 64 v))
             (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rd rs imm rd0 rs0 a v Hpl Hdec Erd Ers Ea Hv Hrd Hk0 Hk4 HK. subst rd rs.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (Hr : rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs0) (bv_signed imm)) 8 = Some (YN2e.le_list v 8)).
{ rewrite Ea. exact (YN2e.rdn_cell SEGS _ a v 8 Hv). }
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_ld SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd0 rs0 imm (YN2e.le_list v 8) (Z_to_bv 64 v) (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hr (YN2e.word_mem_value_mod v)).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma fr_lw : forall (W : world SEGS) regs mem md Q w k (rd rs : bv 5) (imm : bv 12) (rd0 rs0 : bv 5) (a v : Z),
plookup pl_tpi k = Some (PW w) ->
decode_any (Z_to_bv 32 w) = Some (Load SZ4 true rd rs imm, 4%Z) ->
rd = rd0 -> rs = rs0 -> v_addi (getr regs rs0) (bv_signed imm) = Z_to_bv 64 a ->
val_mem SEGS (mrestrict (w_H W) mem) a 4 v ->
bv_eqb rd0 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx (regupd regs rd0 (v_lw (Z_to_bv 64 (v mod 2 ^ 32))))
             (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rd rs imm rd0 rs0 a v Hpl Hdec Erd Ers Ea Hv Hrd Hk0 Hk4 HK. subst rd rs.
pose proof (pa_lookup_pw k w Hpl) as (Hl & _ & _).
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
assert (Hr : rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs0) (bv_signed imm)) 4 = Some (YN2e.le_list v 4)).
{ rewrite Ea. exact (YN2e.rdn_cell SEGS _ a v 4 Hv). }
assert (Hb : bytes_le_to_Z (YN2e.le_list v 4) = bv_unsigned (Z_to_bv 64 (v mod 2 ^ 32))).
{ rewrite YN2e.bytes_le_to_Z_le_list. change (8 * Z.of_nat 4) with 32. rewrite unsigned_lit_small; [reflexivity|].
  pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)). lia. }
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_lw SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd0 rs0 imm (YN2e.le_list v 4) (Z_to_bv 64 (v mod 2 ^ 32)) (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hr Hb).
  rewrite Hrd. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.

Lemma fr_lbu : forall (W : world SEGS) regs mem md Q w k (rd rs : bv 5) (imm : bv 12) (rd0 rs0 : bv 5) (a v : Z),
clookup pa_tbl (BASE + k) = Some w ->
decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4%Z) ->
rd = rd0 -> rs = rs0 -> v_addi (getr regs rs0) (bv_signed imm) = Z_to_bv 64 a ->
val_mem SEGS (mrestrict (w_H W) mem) a 1 v ->
bv_eqb rd0 0 = false -> 0 <= k -> k + 4 < 2 ^ 40 ->
(forall mat', YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W
   (mkCfg (@YK11.mkst fx (regupd regs rd0 (Z_to_bv 64 (v mod 2 ^ 8)))
             (Z_to_bv 64 (BASE + (k + 4))) mem (YK11.seg_rom SEGS))
          (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q w k rd rs imm rd0 rs0 a v Hl Hdec Erd Ers Ea Hv Hrd Hk0 Hk4 HK. subst rd rs.
pose proof (pa_B_ok (L := L)) as (HB0 & HB1 & _).
set (b := Z_to_bv 8 (le_byte v 1 0)).
assert (Hr : rdn SEGS (mrestrict (w_H W) mem) (v_addi (getr regs rs0) (bv_signed imm)) 1 = Some [b]).
{ rewrite Ea. exact (YN2e.rdn_cell SEGS _ a v 1 Hv). }
assert (Hb : Z_to_bv 64 (bv_unsigned b) = Z_to_bv 64 (v mod 2 ^ 8)).
{ f_equal. pose proof (YN2e.bytes_le_to_Z_le_list v 1) as E. unfold YN2e.le_list in E. cbn [seq map] in E.
  rewrite YK1e.bytes_le_to_Z_1 in E. exact E. }
eapply (YSRrG.SRrG_step SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) pa_wx W); [reflexivity | |].
- rewrite restrict_mkst_fx.
  rewrite (step_lbu SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
             (Z_to_bv 32 w) rd0 rs0 imm b (pa_fetch_ok _ _ Hl)
             (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec Hr).
  rewrite Hrd, Hb. reflexivity.
- intros model' Hsame. rewrite (same_but_materialized_wvb md model' Hsame).
  cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  replace (v_addi (Z_to_bv 64 (BASE + k)) 4) with (Z_to_bv 64 (BASE + (k + 4))); [apply HK|].
  unfold v_addi. rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.
End stp.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation BASE := (@pa_val _ B_prog_listing PI_prog_B A_TEXT).
(* ---- 2. the generic kit's image facts at A' ---- *)
Lemma rtt_fp_B : @pi_fp prh_img_B F_round_trip_text = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rtt_stkr_B : 192 <= @STK_round_trip_text prh_img_B.
Proof. vm_compute. discriminate. Qed.

(* ---- 3. the generic kit's two image facts at PI_prog_B's FIELDS (the form Rtt102FR1Kit.v's pst_in_img / pst_not_ro
   take at A'): the instance's projections are reduced here once, by cbn over PI_prog_B only, so a consumer never asks
   the elaborator to unify S1ImgA's rsegs with @pa_segs _ B_prog_listing PI_prog_B (Time: measured cost of that step) *)
Lemma pst_in_img_K : forall a, Exists (in_zr a) (@prh_pst prh_img_B) -> in_img (@pa_segs _ B_prog_listing PI_prog_B) a.
Proof. Time cbn [pa_segs PI_prog_B]. Time exact pst_in_img_B. Time Qed.
Lemma pst_not_ro_K : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  ~ in_roP (@pa_segs _ B_prog_listing PI_prog_B) (@pa_relro_lo _ B_prog_listing PI_prog_B)
    (@pa_relro_hi _ B_prog_listing PI_prog_B) a.
Proof. Time cbn [pa_segs pa_relro_lo pa_relro_hi PI_prog_B]. Time exact pst_not_ro_B. Time Qed.

(* ---- 4. THE SLOT'S WORD AND ITS DECODED FIELDS AS CLOSED PROJECTIONS (the B' R5 porter's finding, B' row R5: a
   `vm_compute; reflexivity` over a goal that still carries EVARS for the word / the decoded fields cannot run on the
   bytecode VM - at B' it times out, at A' it was this lane's whole build cost). For a PW slot the closed form is
   Rtt102StepKit.v's boolean checks, image-generic. The two RELOCATED slots F reads (the `auipc s11` at +440, a PHi
   slot, and the `lbu a0, off(s11)` at +444, a PLdHi slot) have no boolean twin yet, so here they are read off A''s
   own code table by TOTAL PROJECTIONS: every premise a step asks is then a CLOSED equation. The image-generic twin
   is the listing's own certificate (YP0b.v pi_slot_check's PHi / PLdHi rows through YC1fP.v cert_slot), which gives
   the decoding and `auipc_val pc imm = pa_val (A_HI j)` / `pa_val (A_HI j) + bv_signed imm = pa_val a + off` at every
   image; it needs one bridge lemma (v_auipc against auipc_val, through YK11.v:782 b_auipc) that this lane has not
   written. B' has no row that reads these two slots. *)
#[local] Definition RTT_K_B : Z := 4 * Z.of_nat (B_prog_slot AS_round_trip_text).
Definition rtt_w_B (k : Z) : Z := match clookup pa_tbl (BASE + k) with Some w => w | None => 0 end.
Lemma rtt_w_B_ok : forall k, clookup pa_tbl (BASE + k) <> None -> clookup pa_tbl (BASE + k) = Some (rtt_w_B k).
Proof. intros k H. unfold rtt_w_B. destruct (clookup pa_tbl (BASE + k)); [reflexivity | contradiction]. Qed.
(* the decoded immediate of an auipc / of a load at a slot, as a total function (0 off a matching slot) *)
Definition rtt_auipc_imm_B (k : Z) : bv 20 :=
  match decode_any (Z_to_bv 32 (rtt_w_B k)) with Some (Auipc _ imm, _) => imm | _ => Z_to_bv 20 0 end.
Definition rtt_load_imm_B (k : Z) : bv 12 :=
  match decode_any (Z_to_bv 32 (rtt_w_B k)) with Some (Load _ _ _ _ imm, _) => imm | _ => Z_to_bv 12 0 end.

(* the decoding of those two slots as a BOOLEAN check too: an equation between two decode results is an equation
   between bv RECORDS, and vm_compute normalises their proof components differently ("Unable to unify
   Some (Auipc 27 1369, 4) with Some (Auipc 27 1369, 4)"). The boolean has no such component. *)
Definition rtt_auipc_ok_B (k : Z) (rd0 : bv 5) : bool :=
  match decode_any (Z_to_bv 32 (rtt_w_B k)) with
  | Some (Auipc rd _, sz) => bv_eqb rd rd0 && (sz =? 4) | _ => false end.
Definition rtt_load_ok_B (k : Z) (sz0 : msize) (sg0 : bool) (rd0 rs0 : bv 5) : bool :=
  match decode_any (Z_to_bv 32 (rtt_w_B k)) with
  | Some (Load sz sg rd rs _, isz) =>
      msize_eqb sz sz0 && Bool.eqb sg sg0 && bv_eqb rd rd0 && bv_eqb rs rs0 && (isz =? 4)
  | _ => false end.
Lemma rtt_auipc_dec_B : forall k rd0, rtt_auipc_ok_B k rd0 = true ->
  decode_any (Z_to_bv 32 (rtt_w_B k)) = Some (Auipc rd0 (rtt_auipc_imm_B k), 4%Z).
Proof.
intros k rd0 H. unfold rtt_auipc_ok_B, rtt_auipc_imm_B in *.
destruct (decode_any (Z_to_bv 32 (rtt_w_B k))) as [[i sz]|] eqn:E; try discriminate H.
destruct i; try discriminate H.
apply andb_prop in H as [Hr Hsz]. unfold bv_eqb in Hr. apply Z.eqb_eq in Hr. apply bv_eq in Hr.
apply Z.eqb_eq in Hsz. subst. reflexivity.
Qed.
Lemma rtt_load_dec_B : forall k sz0 sg0 rd0 rs0, rtt_load_ok_B k sz0 sg0 rd0 rs0 = true ->
  decode_any (Z_to_bv 32 (rtt_w_B k)) = Some (Load sz0 sg0 rd0 rs0 (rtt_load_imm_B k), 4%Z).
Proof.
intros k sz0 sg0 rd0 rs0 H. unfold rtt_load_ok_B, rtt_load_imm_B in *.
destruct (decode_any (Z_to_bv 32 (rtt_w_B k))) as [[i isz]|] eqn:E; try discriminate H.
destruct i; try discriminate H.
apply andb_prop in H as [H Hsz]. apply andb_prop in H as [H Hrs]. apply andb_prop in H as [H Hrd].
apply andb_prop in H as [Hm Hsg].
apply msize_eqb_eq in Hm. apply Bool.eqb_prop in Hsg.
unfold bv_eqb in Hrd, Hrs. apply Z.eqb_eq in Hrd, Hrs, Hsz. apply bv_eq in Hrd. apply bv_eq in Hrs.
subst. reflexivity.
Qed.
End a.
