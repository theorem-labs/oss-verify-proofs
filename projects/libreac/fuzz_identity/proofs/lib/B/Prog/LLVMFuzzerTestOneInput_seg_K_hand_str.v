(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-278
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1570-1572, 1593-1598, 1605-1613 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The
   same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:106-109. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_base.v; 70 of its 146 lines of code are new or changed and 567 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81 IdentBlkTail.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
check_str reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_seg_K_hand_stmt LLVMFuzzerTestOneInput_seg_K_base.

Lemma ks_bytes_nth : forall (bs : list byte) i,
  (i < length (bs ++ [RcIdentModel.zb 0]))%nat ->
  nth i (map (fun b : byte => bv_unsigned b) (bs ++ [RcIdentModel.zb 0])) 0 =
  RcIdentModel.bz (RcIdentModel.nthb (bs ++ [RcIdentModel.zb 0]) i).
Proof.
intros bs i Hi. unfold RcIdentModel.nthb, RcIdentModel.bz.
rewrite (nth_indep _ 0 (bv_unsigned (RcIdentModel.zb 0))) by (rewrite length_map; exact Hi).
rewrite (map_nth (fun b : byte => bv_unsigned b)). reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
#[local] Notation KPREn := (KPRE B RLO RHI LLVMF_STK arodata_okS G).
#[local] Notation KHn := (KH B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Hypothesis HPRE : KPREn.
Section run.
Variables (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model).
Hypothesis HKH : KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2.

Lemma ks_laws : AR_laws SEGS B.
Proof. eapply k_laws. exact HPRE. Qed.

Lemma ks_geom :
  alloc_ceiling + 8192 <= mf - 8208 /\ mf + 320 <= e_sp0 g /\ e_sp0 g <= 2 ^ 47 /\
  e_sp0 g mod 16 = 0 /\ e_sp0 g - 336 <= mf /\ mf mod 32 = 0 /\ e_sp0 g - LLVMF_STK <= mf - 8208 /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  frame_addr ly2 4 pos = SFa g pos /\
  shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8 /\ 0 <= shadow_addr (SFa g pos) /\
  shadow_addr (SFa g pos) + 128 <= alloc_ceiling /\ In (4, pos) (frames S2).
Proof. eapply k_geom; [exact HPRE | exact HKH]. Qed.

(* The facts the strlen wrapper and check_str ask of a NUL-terminated string held by a heap block of the
   journal's state, whose bytes the start state holds. *)
Lemma ks_str : forall mem md p n (bs : list byte),
  AR SEGS B ly2 S2 W2 mem md -> kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  In (p, n) (ablocks B ly2 S2) ->
  bytes_at8 W2 mem2 p (bs ++ [RcIdentModel.zb 0]) -> KModel.nzb bs = true ->
  Z.of_nat (length bs) + 1 <= req_size n ->
  let r := Z.of_nat (length bs) in
  0 < p /\ p + r + 1 <= alloc_ceiling /\
  first_byte SEGS W2 mem p (r + 1) 0 r /\
  (forall a, p <= a < p + (r + 1) -> aview SEGS (w_H W2) mem a <> None) /\
  amem_range p (r + 1) /\
  range_addressable (aview SEGS (w_H W2) mem) SHADOW_OFF p (r + 1) /\
  shadow_hull_vis (aview SEGS (w_H W2) mem) p (r + 1) /\
  (forall a, p + r < a < p + r - (p + r) mod 8 + 8 -> aview SEGS (w_H W2) mem a <> None) /\
  (p + r + 1 <= IMG_LO \/ IMG_TOP <= p).
Proof.
intros mem md p n bs HAR HKP Hb Hby Hnz Hlen r.
pose proof ks_laws as LAWS.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem md p n HAR Hb) as (_ & Hp4096 & Hpceil & _ & _ & _).
destruct HKP as (_ & HKB & _).
assert (Er : r = Z.of_nat (length bs)) by reflexivity. clearbody r.
assert (Hr0 : 0 <= r) by (rewrite Er; clear; lia).
assert (Hrl : r + 1 <= req_size n) by (rewrite Er; clear - Hlen; lia).
assert (HB : forall i, (i < length (bs ++ [RcIdentModel.zb 0]))%nat ->
  aview SEGS (w_H W2) mem (p + Z.of_nat i) =
  Some (RcIdentModel.bz (RcIdentModel.nthb (bs ++ [RcIdentModel.zb 0]) i))).
{ intros i Hi.
  assert (Hi' : (i <= length bs)%nat) by (rewrite length_app in Hi; cbn [length] in Hi; clear - Hi; lia).
  rewrite (HKB p n (Z.of_nat i) Hb ltac:(clear - Hi' Hlen; lia)).
  destruct (Hby i ltac:(rewrite length_map; exact Hi)) as [Hv Hrg].
  rewrite (ks_bytes_nth bs i Hi) in Hv, Hrg.
  exact (aview_of_val_mem1 SEGS (w_H W2) mem2 _ _ Hv Hrg). }
clear HKB Hby.
assert (Hlast : aview SEGS (w_H W2) mem (p + r) = Some 0).
{ pose proof (HB (length bs) ltac:(rewrite length_app; cbn [length]; clear; lia)) as H.
  unfold RcIdentModel.nthb in H. rewrite app_nth2, Nat.sub_diag in H by (clear; lia). cbn [nth] in H.
  rewrite Er. exact H. }
assert (Hmid : forall i, 0 <= i < r -> exists b, aview SEGS (w_H W2) mem (p + i) = Some b /\ b <> 0).
{ intros i Hi.
  assert (Hi' : (Z.to_nat i < length bs)%nat) by (clear - Hi Er; lia).
  pose proof (HB (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; clear - Hi'; lia)) as H.
  rewrite Z2Nat.id in H by (clear - Hi; lia).
  exists (RcIdentModel.bz (RcIdentModel.nthb (bs ++ [RcIdentModel.zb 0]) (Z.to_nat i))). split; [exact H|].
  unfold RcIdentModel.nthb. rewrite app_nth1 by exact Hi'.
  exact (KModel.nzb_nth bs (Z.to_nat i) Hnz Hi'). }
clear HB.
split; [clear - Hp4096; lia|].
split; [clear - Hpceil Hrl; lia|].
split.
{ split; [clear - Hr0; lia|]. split; [exact Hmid|]. intros _. exact Hlast. }
split.
{ intros a Ha. destruct (Z.eq_dec a (p + r)) as [-> | Hne]; [rewrite Hlast; discriminate|].
  destruct (Hmid (a - p) ltac:(clear - Ha Hne; lia)) as (b & Hb' & _).
  replace a with (p + (a - p)) by (clear; lia). rewrite Hb'. discriminate. }
split; [exact (amem_range_of_block SEGS B LAWS ly2 S2 W2 mem md p n p (r + 1) HAR Hb ltac:(clear; lia) ltac:(clear - Hrl; lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem md p n p (r + 1) HAR Hb ltac:(clear; lia) ltac:(clear - Hrl; lia))|].
split; [exact (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem md p n p (r + 1) HAR Hb ltac:(clear; lia) ltac:(clear - Hrl; lia) ltac:(clear - Hr0; lia))|].
split.
{ intros a Ha. exact (blk_tail_present SEGS B LAWS ly2 S2 W2 mem md p n r a HAR Hb ltac:(clear - Hr0 Hrl; lia) Ha). }
destruct (blk_off_imgP B ly2 S2 W2 mem md p n HAR Hb) as [Hi | Hi]; [left; clear - Hi Hrl; lia | right; exact Hi].
Qed.

End run.
End c.
End b.
End a.
