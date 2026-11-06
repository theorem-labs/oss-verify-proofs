(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44): SEGMENT S6 of the walk of parse_noting (row
   N10-PNA; cut table lib/A/Prog/PN102Cuts.v): from the join pn_cut_S6 (+0x58) to the post of the batch kit's text pn_post.
   The slots, read on the listing (lib/A/Listing_prog.v, parse_noting's slots 611 .. 618): +0x58 mv a0,s2;
   +0x5c .. +0x6c ld ra,40(sp) / s0,32 / s1,24 / s2,16 / s3,8; +0x70 addi sp,sp,48; +0x74 ret.
   rule 24: proves function parse_noting (reuse search: `proof-index parse_noting` exit 4 at 2026-10-30 07:2xZ,
   index v5 06:36:24Z: 0 named / 0 by address / 0 related / 0 released; the unreleased hits are this lane's own N10-PNA
   files and the plain / UBSan / B' twins; R24Pna CONFIRM 2026-10-29 18:2xZ; own signed walk preset-tree-at-2026-10-29T20-00-00Z.tsv (sha256 84c0bfddb1f3; internal record), its one
   announced re-bind). This file: segment S6 of that walk.
   THE BATCH KIT'S RE-BIND: a Theorem Labs lane's signed A' file of the same role (a working branch 13970867e0c9),
   re-fit to the batch kit's cut (commit 7cdbb61b5fa0) as the B' twin was re-fit
   (a working branch c7276d935095 lib/B/Prog/PN102B<same role>.v, read back at PI_prog_A / prh_img_A).
   FORM: eight CONCRETE steps (PN102Help.v pn_step_addi / pn_step_ret, and pn6_step_ld here: pn_step_addi's form over
   YK11.v step_ld, the eight bytes read by PN102Help.v pn_rd64_val and YN01.v word_mem_ld). The steps leave memory and
   the world alone and only materialize the model, so the cut's journal (at the budget pn_cw X and at the relation
   YA0nH.wle' SEGS RZ_cf, since pj_parse frees before the cut; PN102Keep.v pn_ajw_materialize), its hull use pn_hull,
   its reading pn_R, its memnorm keep and its float state carry to the `ret`; the five loads give
   back the entry ra, s0 .. s3 from the cut's saved words, the addi the entry sp, and the `ret` jumps to the entry ra
   (its ret_ok from pp_fpre). The batch kit's post is budgeted (fpostFbm (wbudget [] (prh_wk F_parse_noting))): its budget is
   pn_cw X, two traces (PN102Keep.v pn_cw_budget).
   SHAPES TAKEN: pn6_aregs is lib/A/Prog/Ent102L6A.v l6_aregs (a working branch b1bc025047ea), renamed;
   pn6_fd is lib/A/Prog/Ent102L3ASteps.v l3_fd (same branch) at PL_prog_A.
   NUMERALS: 4 (an instruction), 8 (a word), 48 (the frame), 8 .. 40 (the save slots), 2 ^ 40 / 2 ^ 64 (the engine's
   code-span and word ranges), the instruction offsets 0x58 .. 0x74 (LENGTH). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YN01 YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PN102Cuts PN102Help PN102Keep.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Tactics and pure facts: the listing slot at an offset with its instruction checked by vm_refl_bv; a register
      read through a chain of register updates; aregs_preserved from the fifteen callee-saved registers. *)
Ltac pn6_fd k ins Hpl Hd :=
  let r := eval vm_compute in (plookup (@pl_tpi _ PL_prog_A) k) in
  lazymatch r with
  | Some (PW ?w) =>
    assert (Hpl : plookup (@pl_tpi _ PL_prog_A) k = Some (PW w)) by (vm_compute; reflexivity);
    assert (Hd : decode_any (Z_to_bv 32 w) = Some (ins, 4%Z)) by vm_refl_bv
  | _ => fail "pn6_fd: no plain word at offset" k
  end.
Ltac pn6_gr := repeat first [rewrite getr_same by pn_regne | rewrite getr_other by pn_regne].

Lemma pn6_aregs : forall regs0 regs' : bvmap 5 word,
  getr regs' 2 = getr regs0 2 -> getr regs' 3 = getr regs0 3 -> getr regs' 4 = getr regs0 4 ->
  getr regs' 8 = getr regs0 8 -> getr regs' 9 = getr regs0 9 ->
  getr regs' 18 = getr regs0 18 -> getr regs' 19 = getr regs0 19 -> getr regs' 20 = getr regs0 20 ->
  getr regs' 21 = getr regs0 21 -> getr regs' 22 = getr regs0 22 -> getr regs' 23 = getr regs0 23 ->
  getr regs' 24 = getr regs0 24 -> getr regs' 25 = getr regs0 25 -> getr regs' 26 = getr regs0 26 ->
  getr regs' 27 = getr regs0 27 ->
  aregs_preserved regs0 regs'.
Proof.
intros regs0 regs' H2 H3 H4 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 r Hr.
unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; [exact H2 | exact H3 | exact H4 | exact H8 | exact H9 |].
assert (Hc : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; assumption.
Qed.

(* the address sp + o of a load or an addi *)
Lemma pn6_vaddi_sp : forall (regs : bvmap 5 word) (o a : Z), spZ regs + o = a -> v_addi (getr regs 2) o = Z_to_bv 64 a.
Proof. intros regs o a H. unfold v_addi. f_equal. exact H. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The `ld` step at the A' instance: the eight bytes at the address are a reader word of the view, the register
      gets that word (pn_step_addi's form over YK11.v step_ld). *)
Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).

Lemma pn6_step_ld : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (Q : world SEGS -> config -> Prop) (k w : Z) (rd rs : bv 5) (imm : bv 12) (rd' : bv 5) (a v : Z),
  0 <= k < 2 ^ 40 ->
  plookup (@pl_tpi _ PL_prog_A) k = Some (PW w) ->
  decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs imm, 4%Z) ->
  bv_eqb rd (0%bv : bv 5) = false -> rd = rd' ->
  v_addi (getr regs rs) (bv_signed imm) = Z_to_bv 64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rd64 (aview SEGS (w_H W) mem) a v ->
  (forall X, SRr SEGS W (mkCfg (@YK11.mkst fx (regupd regs rd' (Z_to_bv 64 v)) (Z_to_bv 64 (BASE + (k + 4))) mem
     (YK11.seg_rom SEGS)) (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + k)) mem (YK11.seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md Q k w rd rs imm rd' a v Hk Hpl Hd Hrd Erd Ha Ha0 Ha8 Hr HK. subst rd'.
pose proof (pa_fetch_pw (PL := PL_prog_A) (PI := PA) k w Hpl) as Hf.
pose proof (pn_rd64_val (w_H W) mem a v Hr) as Hvm.
apply (proj1 (val_mem_word_mem SEGS _ _ _)) in Hvm.
destruct (YN01.word_mem_ld SEGS _ a v Hvm Ha0 Ha8) as (bs & Hbs & Hle).
eapply (SRr_step SEGS (@pa_wx rc A_prog_listing PA) W); [reflexivity | |].
- rewrite (restrict_mkst_fx (fx := fx)).
  rewrite (step_ld (fx := fx) SEGS regs (Z_to_bv 64 (BASE + k)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)
    (Z_to_bv 32 w) rd rs imm bs (Z_to_bv 64 v) Hf (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd);
    [| rewrite Ha; exact Hbs | exact Hle].
  rewrite Hrd. cbv beta iota. reflexivity.
- intros model' Hs. rewrite (same_but_materialized_wvb md model' Hs).
  cbn [ms_regs ms_mem YK11.mkst]. rewrite (unrestrict_mkst_mrestrict (fx := fx)).
  rewrite (pn_pc4 k Hk). apply HK.
Qed.
End S.

(* ---------------------------------------------------------------------- *)
(* 3. THE SEGMENT at the A' instance. *)
Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {SK : YI16.sink_head}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PA := (@PI_prog_A rc).
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PA).
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp (W : world SEGS) mem md =>
  ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).

Theorem pn_seg_S6 : forall CTX0,
  pn_seg_S6_stmt (fx := fx) (cp := CP) (PI := prh_img_A) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) B ARc SK CTX0.
Proof.
intros CTX0. unfold pn_seg_S6_stmt.
intros X W c Hpre Hcut.
(* the entry ra returns to itself (afn_pre_x's ret_ok) *)
pose proof (pp_fpre _ _ _ _ Hpre) as ((_ & Hraok & _) & _).
unfold YK0s.ret_ok in Hraok.
unfold pn_cut_S6 in Hcut.
destruct Hcut as (fy & regs & mem & md & ly & S & Hp & k & Lam & peak & cnt & fail & ran & ok & res & tr
  & -> & Hfr & Hhull & Hroom & HR).
unfold pn_frameR in Hfr.
destruct Hfr as (HJ & Hsp & Mra & Ms0 & Ms1 & Ms2 & Ms3 & Hcs & Hfz & Hfk & Hmn & Hro).
assert (LAWS : AR_laws_x SEGS B ARc (@cf_head CP))
  by exact (AR_laws_x_xs (cp := CP) SEGS B (AR_laws_ok_cf (cp := CP) SEGS B)).
(* ranges: the code span, the two sps *)
pose proof pn_slot0_range as (R0 & R1). unfold PN_RET in R1.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rsp.
pose proof (bv_unsigned_in_range 64 (getr (px_regs X) 2)) as Rsp0.
change (bv_modulus 64) with (2 ^ 64) in Rsp, Rsp0.
change (bv_unsigned (getr regs 2)) with (spZ regs) in Rsp.
change (bv_unsigned (getr (px_regs X) 2)) with (spZ (px_regs X)) in Rsp0.
unfold PN_FRAME in Hsp.
rewrite (pn_cfg_eq fy PN_S6 regs mem md).
(* +0x58 mv a0,s2 *)
pn6_fd (PN_SLOT0 + PN_S6) (OpImm ALU_ADD 10 18 (Z_to_bv 12 0)) Hpl1 Hd1.
assert (Hv1 : v_addi (getr regs 18) (bv_signed (Z_to_bv 12 0)) = getr regs 18)
  by (change (bv_signed (Z_to_bv 12 0)) with 0; apply YK11.v_addi_0).
apply (pn_step_addi (fx := fy) W regs mem md _ (PN_SLOT0 + PN_S6) _ 10 18 (Z_to_bv 12 0) 10 (getr regs 18)
  ltac:(unfold PN_S6; lia) Hpl1 Hd1 eq_refl eq_refl Hv1).
intros mt1.
(* +0x5c ld ra,40(sp) *)
pn6_fd (PN_SLOT0 + PN_S6 + 4) (Load SZ8 true 1 2 (Z_to_bv 12 40)) Hpl2 Hd2.
apply (pn6_step_ld (fx := fy) W _ mem _ _ (PN_SLOT0 + PN_S6 + 4) _ 1 2 (Z_to_bv 12 40) 1
  (spZ (px_regs X) - 8) (raZ (px_regs X)) ltac:(unfold PN_S6; lia) Hpl2 Hd2 eq_refl eq_refl);
  [pn6_gr; apply pn6_vaddi_sp; change (bv_signed (Z_to_bv 12 40)) with 40; lia | lia | lia | exact Mra |].
intros mt2.
(* +0x60 ld s0,32(sp) *)
pn6_fd (PN_SLOT0 + PN_S6 + 4 + 4) (Load SZ8 true 8 2 (Z_to_bv 12 32)) Hpl3 Hd3.
apply (pn6_step_ld (fx := fy) W _ mem _ _ (PN_SLOT0 + PN_S6 + 4 + 4) _ 8 2 (Z_to_bv 12 32) 8
  (spZ (px_regs X) - 16) (bv_unsigned (getr (px_regs X) 8)) ltac:(unfold PN_S6; lia) Hpl3 Hd3 eq_refl eq_refl);
  [pn6_gr; apply pn6_vaddi_sp; change (bv_signed (Z_to_bv 12 32)) with 32; lia | lia | lia | exact Ms0 |].
intros mt3.
(* +0x64 ld s1,24(sp) *)
pn6_fd (PN_SLOT0 + PN_S6 + 4 + 4 + 4) (Load SZ8 true 9 2 (Z_to_bv 12 24)) Hpl4 Hd4.
apply (pn6_step_ld (fx := fy) W _ mem _ _ (PN_SLOT0 + PN_S6 + 4 + 4 + 4) _ 9 2 (Z_to_bv 12 24) 9
  (spZ (px_regs X) - 24) (bv_unsigned (getr (px_regs X) 9)) ltac:(unfold PN_S6; lia) Hpl4 Hd4 eq_refl eq_refl);
  [pn6_gr; apply pn6_vaddi_sp; change (bv_signed (Z_to_bv 12 24)) with 24; lia | lia | lia | exact Ms1 |].
intros mt4.
(* +0x68 ld s2,16(sp) *)
pn6_fd (PN_SLOT0 + PN_S6 + 4 + 4 + 4 + 4) (Load SZ8 true 18 2 (Z_to_bv 12 16)) Hpl5 Hd5.
apply (pn6_step_ld (fx := fy) W _ mem _ _ (PN_SLOT0 + PN_S6 + 4 + 4 + 4 + 4) _ 18 2 (Z_to_bv 12 16) 18
  (spZ (px_regs X) - 32) (bv_unsigned (getr (px_regs X) 18)) ltac:(unfold PN_S6; lia) Hpl5 Hd5 eq_refl eq_refl);
  [pn6_gr; apply pn6_vaddi_sp; change (bv_signed (Z_to_bv 12 16)) with 16; lia | lia | lia | exact Ms2 |].
intros mt5.
(* +0x6c ld s3,8(sp) *)
pn6_fd (PN_SLOT0 + PN_S6 + 4 + 4 + 4 + 4 + 4) (Load SZ8 true 19 2 (Z_to_bv 12 8)) Hpl6 Hd6.
apply (pn6_step_ld (fx := fy) W _ mem _ _ (PN_SLOT0 + PN_S6 + 4 + 4 + 4 + 4 + 4) _ 19 2 (Z_to_bv 12 8) 19
  (spZ (px_regs X) - 40) (bv_unsigned (getr (px_regs X) 19)) ltac:(unfold PN_S6; lia) Hpl6 Hd6 eq_refl eq_refl);
  [pn6_gr; apply pn6_vaddi_sp; change (bv_signed (Z_to_bv 12 8)) with 8; lia | lia | lia | exact Ms3 |].
intros mt6.
(* +0x70 addi sp,sp,48: the entry sp *)
pn6_fd (PN_SLOT0 + PN_S6 + 4 + 4 + 4 + 4 + 4 + 4) (OpImm ALU_ADD 2 2 (Z_to_bv 12 48)) Hpl7 Hd7.
apply (pn_step_addi (fx := fy) W _ mem _ _ (PN_SLOT0 + PN_S6 + 4 + 4 + 4 + 4 + 4 + 4) _ 2 2 (Z_to_bv 12 48) 2
  (getr (px_regs X) 2) ltac:(unfold PN_S6; lia) Hpl7 Hd7 eq_refl eq_refl);
  [pn6_gr; change (bv_signed (Z_to_bv 12 48)) with 48; rewrite (pn6_vaddi_sp regs 48 (spZ (px_regs X))) by lia;
   unfold spZ; apply Z_to_bv_bv_unsigned |].
intros mt7.
(* +0x74 ret *)
assert (Hpl8 : plookup (@pl_tpi _ PL_prog_A) (PN_SLOT0 + PN_S6 + 4 + 4 + 4 + 4 + 4 + 4 + 4) = Some (PW RET_WORD_r))
  by (vm_compute; reflexivity).
apply (pn_step_ret (fx := fy) W _ mem _ _ _ Hpl8).
intros mt8.
(* THE CLOSE: the final registers *)
lazymatch goal with |- context [mkCfg (@YK11.mkst _ ?r _ _ _) _] => remember r as RF eqn:ERF end.
assert (Q1 : getr RF 1 = getr (px_regs X) 1) by (subst RF; pn6_gr; unfold raZ; apply Z_to_bv_bv_unsigned).
assert (Q2 : getr RF 2 = getr (px_regs X) 2) by (subst RF; pn6_gr; reflexivity).
assert (Q8 : getr RF 8 = getr (px_regs X) 8) by (subst RF; pn6_gr; apply Z_to_bv_bv_unsigned).
assert (Q9 : getr RF 9 = getr (px_regs X) 9) by (subst RF; pn6_gr; apply Z_to_bv_bv_unsigned).
assert (Q18 : getr RF 18 = getr (px_regs X) 18) by (subst RF; pn6_gr; apply Z_to_bv_bv_unsigned).
assert (Q19 : getr RF 19 = getr (px_regs X) 19) by (subst RF; pn6_gr; apply Z_to_bv_bv_unsigned).
assert (Q10 : getr RF 10 = getr regs 18) by (subst RF; pn6_gr; reflexivity).
assert (QP : aregs_preserved (px_regs X) RF).
{ apply pn6_aregs; [exact Q2 | | | exact Q8 | exact Q9 | exact Q18 | exact Q19 | | | | | | | |];
  subst RF; pn6_gr;
  lazymatch goal with |- getr _ ?q = _ =>
    let n := eval vm_compute in (bv_unsigned q) in
    exact (Hcs n ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  end. }
rewrite Q1, Hraok.
unfold pn_post, fpostFbm, fpostFb, YCbqGwild.apost_base_xbFR.
exists fy, ly, S, Hp, RF, mem. eexists. exists k, (pn_cw (PI := prh_img_A) (PA := PA) B X).
split; [reflexivity|].
split; [exact Hfz|]. split; [exact Hfk|].
split; [exact (pn_cw_budget B X)|].
split.
{ repeat apply (pn_ajw_materialize B LAWS (wle' SEGS YGcfRehidePost.RZ_cf)). exact HJ. }
split; [exact QP|].
unfold fQmn. split; [|exact Hmn].
unfold pn_Q. split; [exact Hhull|]. split; [exact Hroom|].
exists Lam, peak, cnt, fail, ran, ok, res, tr. rewrite Q10. exact HR.
Qed.
End I.
