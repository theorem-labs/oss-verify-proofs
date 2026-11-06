(* Modified by a Theorem Labs lane (ReallocPrimary.CfW.ReplyEnqReloc), 2026-10-30: carried BY PATH from commit d3183c6ef2d0 (CfF1's lane F1 head; blobs hold on layer ae2fa80b0325), proofs/cgif/cgif_file_fuzzer/lib/YGcfInstErrno.v, sha256 bea965f8b8143337. The only change is the module paths: OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib M -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable M, except lib.A for: ImgBase ImgBaseAG ImgBaseDG YGcfMallocCompose ErrnoG ErrnoGcf YGcfDIface ErrnoApart. No numeral and no statement changed. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstErrno.v at commit f303438be5b, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10 (lane F1 of the generic cf instance layer; integrator ReallocPrimary).
   The cf twin of proofs/cgif/cgif_file_fuzzer/lib/ErrnoApartcgif.v at c5 30a1993588f (with AGif1m.v's
   errno_not_owned_cgif and CLenqcgifE.v's errno_kept_view / enq_errno_kept, the errno facts the cgif arms read
   beside it), feeding ErrnoGcf.v.
   rule 24: no function proved (kind: interface-instance discharge: errno's image facts and errno kept at the cf
   relation).

   ErrnoApartcgif.v proves ErrnoApart.v's image facts with cgif's numerals (TFIB_ERRNO = 0x5d916c against cgif's
   zones).  A generic file cannot: the facts compare errno's address with the zones of the unit's image classes
   (ImgBase.AImg, ImgBaseAG.AGImg, ImgBaseDG.DImg).  So each fact is a FIELD of [ErrnoImgCf], which a unit fills at its
   image (preset: A/ErrnoApartA.v, the same nine lemmas at AImg_A / AGImg_A / DImg_A; cgif: ErrnoApartcgif.v).
   The secondary path's three facts (ErrnoApartS.v) are in YGcfInstErrnoS.v: ErrnoApartS's Require closure reaches
   AGif4 / YA08 / YA09 / YA0e, whose Zify flag setting escapes Require (ErrnoApartS.v's header), and this file keeps
   out of that closure, as ErrnoApartcgif.v does.

   What this file proves, over the fields and the cf relation ARcf (YG0ncf.v), with no image constant:
   - [errno_not_owned_cf]: errno is no byte of the allocator's owned set at ARcf (AGif1m.errno_not_owned_cgif's
     script over YG0scf.AR_owned_image_law_ok_cf), from two UNIT IMAGE premises named over the symbol table only:
     [errno_seg_t] (errno's 4 bytes are segment bytes, in the segment-byte form `seg_rom im_segs _ <> None`: cgif
     YB13.tfib_rw_rom) and [errno_nstatic_t] (they lie in no owned static range: cgif Tfib_owned_static); cgif
     discharges both in YGcfInstErrnocgif.v.  [errno_in_segs_cf] is the in_img corollary the owned-image law reads;
   - [errno_not_xs_cf]: errno is not in the errbuf slot (the cf owned set's extra extent, YGcfMallocCompose.AOXm_cf):
     the slot is disjoint from the layout's image window (YG0ncf.xs_placed_cf), errno is inside it (errno_in_img);
   - [errno_not_aox_cf]: both, for AOXm_cf;
   - [errno_kept_of_frame_cf]: errno kept on the raw memory by any frame that keeps every byte outside the
     pre-state's owned set and one stack window (CLenqcgifE.enq_errno_kept's script, for every such callee);
   - [errno_kept_view_cf]: errno kept on the raw memory is errno kept on the view (ErrnoApart.errno_kept_v_of_raw);
   - [errno_kept_g_gcf] / [errno_kept_gcf_g] / [errno_kept_cf_g] / [errno_kept_g_cf]: ErrnoG.errno_kept,
     ErrnoGcf.errno_kept and YGcfMallocCompose.errno_kept_cf are one text (conversion).
   The image window comes from the ledger through the kit's image premise YGcfDIface.IMG_COVER (ALedger_cf ->
   im_img_cover; preset's Reusable/YGcfDIface.v:266, carried by path in the layer): one name for that fact.
   EVENT-FREE: no event count, event ceiling, regime or cgif meter term appears here (CF-LAYER-LANES.md (sha256 f291131825b7; internal record)'s gate). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG ImgBaseDG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG ErrnoGcf YGcfDIface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ErrnoApart.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {IM : AImg} {AG : AGImg} {DI : DImg}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. ErrnoApart.v's image facts, one field each (ErrnoApartcgif.v's nine lemmas, at the unit's image classes).    *)
Record ErrnoImgCf : Prop := {
  ei_in_img : errno_in_img;
  ei_unhidden : errno_unhidden;
  ei_dzone_ag : errno_apart_dzone_ag;
  ei_shadow_ag : errno_apart_shadow_ag;
  ei_inst_ag : errno_apart_inst_ag;
  ei_dzone_d : errno_apart_dzone_d;
  ei_izone : errno_apart_izone;
  ei_zone3_d : errno_apart_zone3_d;
  ei_inst_d : errno_apart_inst_d
}.

Section b.
Variable B : asyms.
Hypothesis TS : im_syms B.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. errno is no allocator byte at the cf relation.                                                               *)

(* UNIT IMAGE premise: errno's 4 bytes are bytes of a loaded segment, in the segment-byte form (cgif:
   YB13.tfib_rw_rom; YGcfInstErrnocgif.errno_seg_cgif). *)
Definition errno_seg_t : Prop :=
forall a, as_errno B <= a < as_errno B + 4 -> seg_rom im_segs (Z_to_bv 64 a) <> None.
(* UNIT IMAGE premise: errno's 4 bytes lie in no owned static range (cgif: Tfib_owned_static, AGif1m.v:113-115;
   YGcfInstErrnocgif.errno_nstatic_cgif). *)
Definition errno_nstatic_t : Prop :=
forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).

(* The in_img corollary of [errno_seg_t] (YG0s.seg_rom_in_img), at any layout the relation places. *)
Lemma errno_in_segs_cf : errno_in_img -> YGcfDIface.IMG_COVER -> errno_seg_t ->
forall ly S Hp (W : world im_segs) mem md a, ARcf im_segs B ly S Hp W mem md ->
as_errno B <= a < as_errno B + 4 -> YG0d.in_img im_segs a.
Proof.
intros HI HC HSEG ly S Hp W mem md a HAR Ha.
pose proof HAR as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LY.
pose proof (HC ly S md L) as IMG.
destruct (HI B ly TS IMG) as [E1 E2].
pose proof (lo_img ly LY) as (L1 & L2 & L3 & _).
apply (seg_rom_in_img im_segs a); [unfold kImgLo, kImgEnd in *; lia | exact (HSEG a Ha)].
Qed.

(* AGif1m.errno_not_owned_cgif at ARcf: an owned byte of the image is an owned static byte (the cf owned-image law). *)
Lemma errno_not_owned_cf : errno_in_img -> YGcfDIface.IMG_COVER -> errno_seg_t -> errno_nstatic_t ->
forall ly S Hp (W : world im_segs) mem md a, ARcf im_segs B ly S Hp W mem md ->
as_errno B <= a < as_errno B + 4 -> ~ aowned B ly S a.
Proof.
intros HI HC HSEG HNS ly S Hp W mem md a HAR Ha O.
apply (HNS a Ha).
exact (proj1 (AR_owned_image_law_ok_cf im_segs B ly S Hp W mem md a HAR
  (errno_in_segs_cf HI HC HSEG ly S Hp W mem md a HAR Ha)) O).
Qed.

(* errno is not in the errbuf slot: the slot is disjoint from the static extents, the image window among them. *)
Lemma errno_not_xs_cf : errno_in_img -> YGcfDIface.IMG_COVER ->
forall ly S Hp (W : world im_segs) mem md a, ARcf im_segs B ly S Hp W mem md ->
as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (xs_cf ly S).
Proof.
intros HI HC ly S Hp W mem md a HAR Ha HX.
destruct HAR as (M & L & _).
pose proof (HC ly S md L) as IMG.
destruct (HI B ly TS IMG) as [E1 E2].
pose proof (amc_xs_placed _ _ _ _ _ M) as XP. unfold xs_placed_cf in XP.
apply Exists_exists in HX as (e & He & Hin).
destruct (proj1 (Forall_forall _ _) XP e He) as (_ & _ & _ & D).
assert (HIM : In (ly_img ly) (sec_extents ly S ++ static_extents ly ++ ly_extra ly)).
{ apply in_or_app. right. apply in_or_app. left. unfold static_extents. apply in_or_app. right. right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) D _ HIM) as DJ.
unfold zdisjoint, in_zr in *. lia.
Qed.

(* errno is outside the cf owned set AOXm_cf (the blocks and the errbuf slot). *)
Lemma errno_not_aox_cf : ErrnoImgCf -> errno_seg_t -> errno_nstatic_t -> YGcfDIface.IMG_COVER ->
forall ly S Hp (W : world im_segs) mem md a, ARcf im_segs B ly S Hp W mem md ->
as_errno B <= a < as_errno B + 4 -> ~ AOXm_cf B ly S a.
Proof.
intros EI HSEG HNS HC ly S Hp W mem md a HAR Ha [O|O].
- exact (errno_not_owned_cf (ei_in_img EI) HC HSEG HNS ly S Hp W mem md a HAR Ha O).
- exact (errno_not_xs_cf (ei_in_img EI) HC ly S Hp W mem md a HAR Ha O).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. errno kept by a raw frame (CLenqcgifE.enq_errno_kept's script): a callee that keeps every byte outside the    *)
(*    pre-state's owned set and one stack window [lo, hi) above the stack's base keeps errno's 4 bytes.             *)
Lemma errno_kept_of_frame_cf : ErrnoImgCf -> errno_seg_t -> errno_nstatic_t -> YGcfDIface.IMG_COVER ->
forall ly S Hp (W : world im_segs) mem md (lo hi : Z) (mem' : word -> option byte),
ARcf im_segs B ly S Hp W mem md -> ly_stk_lo ly <= lo ->
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ (lo <= bv_unsigned x < hi) -> mem' x = mem x) ->
ErrnoG.errno_kept B mem mem'.
Proof.
intros EI HSEG HNS HC ly S Hp W mem md lo hi mem' HAR HLO FR i Hi.
pose proof HAR as (M & L & _).
pose proof (amc_layout _ _ _ _ _ M) as LY.
pose proof (HC ly S md L) as IMG.
destruct (ei_in_img EI B ly TS IMG) as [E1 E2].
pose proof (lo_img ly LY) as (L1 & L2 & L3 & _).
assert (EB : bv_unsigned (w64 (as_errno B + i)) = as_errno B + i)
  by (apply w64_unsigned; unfold kImgLo, kImgEnd in *; lia).
apply FR.
- rewrite EB. exact (errno_not_owned_cf (ei_in_img EI) HC HSEG HNS ly S Hp W mem md (as_errno B + i) HAR ltac:(lia)).
- rewrite EB. intros HW.
  exact (errno_apart_stack (ei_in_img EI) B ly lo hi (as_errno B + i) TS LY IMG HLO HW ltac:(lia)).
Qed.

(* errno kept on the raw memory is errno kept on the view, in any two worlds (ErrnoApart.errno_kept_v_of_raw). *)
Lemma errno_kept_view_cf : ErrnoImgCf -> forall (W W' : world im_segs) (mem mem' : word -> option byte),
ErrnoG.errno_kept B mem mem' -> ErrnoG.errno_kept_v im_segs B W W' mem mem'.
Proof.
intros EI W W' mem mem' E.
exact (errno_kept_v_of_raw (ei_unhidden EI) B W W' mem mem' TS E).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. ErrnoG's, ErrnoGcf's and the compose's errno texts are one text.                                             *)
Lemma errno_kept_g_gcf : forall mem mem', ErrnoG.errno_kept B mem mem' -> ErrnoGcf.errno_kept B mem mem'.
Proof. intros mem mem' H. exact H. Qed.
Lemma errno_kept_gcf_g : forall mem mem', ErrnoGcf.errno_kept B mem mem' -> ErrnoG.errno_kept B mem mem'.
Proof. intros mem mem' H. exact H. Qed.
Lemma errno_kept_g_cf : forall mem mem', ErrnoG.errno_kept B mem mem' -> errno_kept_cf B mem mem'.
Proof. intros mem mem' H. exact H. Qed.
Lemma errno_kept_cf_g : forall mem mem', errno_kept_cf B mem mem' -> ErrnoG.errno_kept B mem mem'.
Proof. intros mem mem' H. exact H. Qed.
Lemma errno_kept_v_g_gcf : forall (W W' : world im_segs) mem mem',
ErrnoG.errno_kept_v im_segs B W W' mem mem' -> ErrnoGcf.errno_kept_v im_segs B W W' mem mem'.
Proof. intros W W' mem mem' H. exact H. Qed.

End b.
End a.
