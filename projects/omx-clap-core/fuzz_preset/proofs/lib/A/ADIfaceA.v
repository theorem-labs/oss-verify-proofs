(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the event-free allocator instance of c-asan's Deallocate interface DIface (Reusable/
   YGcfDIface.v, image-free) AT IMAGE A, preset's ASan binary (suffix _A).
   - DImg_A: the Deallocate image class of a Theorem Labs lane's image-free interface files (ImgBaseDG.DImg, a copy of
     cgif/cgif_file_fuzzer lib/ImgBaseDG.v (file sha256 9ec73d89c58a; donor not released) in lib/Reusable, changed in its module prefix and in one abort label, 209280 -> 4 at :88, as its line 1 says) at image A, every field by lib/A's name: the zones of lib/A's relocated walk (A/AFgi.v
     DZONE, A/AFgn.v IZONE and IAL_POST over AF0m's TFIB_IAL_*, A/AF0x.v zone3) and its entry pcs (A/AFl0.v, A/AFew.v,
     A/AFeu.v); the instance window and the constant cells' zone are A/AGImgA.v's inst_ok and CZONE, as cgif's
     DImg_cgif takes AGif0cgif's (Main 10:4xZ). The image class AImg_A (segments, cells, TfibSyms, Tfib_const,
     img_cover) is in A/AImgA.v, re-exported here, so the chain is cgif's three files: AImgA (cgif: AGif2cgif) <-
     AGImgA (cgif: AGif0cgif) <- this file (cgif: DGif0cgif). The reflexivity bridges below name each field's value.
   - The image premises of YGcfDIface at A: IMG_COVER from img_lo_seg_A / img_hi_seg_A (the segments found by value,
     an existsb decision over the whole list); DZONE_OWNED and IZONE_OWNED from the owned static table found by value
     (ADIfaceImgA.covers_b) and the symbol bounds: IAL_AREA_B HOLDS at A (ial_area_B_A: the zone's bounds are AF0m's
     TFIB_IAL_LO / HI, which TfibSyms equates to as_ialloc_lo / hi).
  - Each DIface model field at the instance, with every premise discharged: di_inst_A, di_view_n_img_A, di_shape_n_A,
    di_lpost_d_A, di_post_n_inst_A (from A/ADIfacePostNA.v's di_post_n_A, whose dmem_n_A is DGif0's dmem_n at DImg_A
    up to conversion), di_frame_A, di_stack_A, di_owned_A, di_owned_b_A, di_owned_i_A, di_owned_x_A. EXCEPT di_shape_A:
    it is the enqueue side only (it takes the OPEN premise req_size n <= kQuarantineMax, free_cf's size test), so it no
    longer has DGif0.v:279's di_shape type; the big blocks take the big Deallocate arm (DGbigIF.DIfaceBig, lib/Reusable/DGbigIF.v:146).
   No address of preset's image is typed here. Nothing here is a function's proof (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG02cf YG0ncf YG0dcf YG0qcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AFgi AFgn AFix AFl0 AFew AFeu ADIfaceImgA ADIfacePostNA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG DMspec DMiface DGif0 YGcfDIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Export AImgA.
(* AGImgA is used qualified (AGImgA.inst_ok, AGImgA.CZONE): importing it would bring the walk's geometry names. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AGImgA.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================================================================================================ *)
(* The Deallocate image class at image A (AImg_A: A/AImgA.v).                                                       *)

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[export] Instance DImg_A : DImg (IM := AImg_A) := {|
  dg_czone := AGImgA.CZONE; dg_inst_ok := AGImgA.inst_ok;
  dg_dzone := AFgi.DZONE; dg_izone := AFgn.IZONE; dg_ial_post := AFgn.IAL_POST;
  dg_zone3 := AF0x.zone3;
  dg_depot := AFl0.A_StackDepotPut; dg_enqueue := AFew.A_Enqueue;
  dg_drain := AFeu.A_Drain; dg_rchunk := AFeu.A_RChunk; dg_cdealloc := AFeu.A_CDealloc
|}.
End D.
Canonical Structure DImg_A.

(* The reflexivity bridges: each field of the two instances is lib/A's named value; TFIB_INST lies in the window. *)
Section BR. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma im_segs_A : im_segs = tfibsegs. Proof. reflexivity. Qed.
Lemma im_img_cover_A : forall ly, im_img_cover ly = AF0x.img_cover ly. Proof. reflexivity. Qed.
Lemma dg_dzone_A : forall ly a, dg_dzone ly a = AFgi.DZONE ly a. Proof. reflexivity. Qed.
Lemma dg_izone_A : forall a, dg_izone a = AFgn.IZONE a. Proof. reflexivity. Qed.
Lemma dg_ial_post_A : forall W m, dg_ial_post W m = AFgn.IAL_POST W m. Proof. reflexivity. Qed.
Lemma dg_inst_ok_A : forall inst, dg_inst_ok inst = AGImgA.inst_ok inst. Proof. reflexivity. Qed.
Lemma dg_czone_A : forall ly a, dg_czone ly a = AGImgA.CZONE ly a. Proof. reflexivity. Qed.
Lemma inst_ok_TFIB_INST_A : AGImgA.inst_ok TFIB_INST.
Proof. unfold AGImgA.inst_ok, TFIB_INST. split; [lia | split; [lia | reflexivity]]. Qed.
End BR.

(* ================================================================================================================ *)
(* The image premises at A.                                                                                         *)
Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

(* Some segment of A starts at or below IMG_LO, and some ends at or above IMG_TOP: each found by value. *)
Lemma img_lo_seg_A : IMG_LO_SEG tfibsegs YImgTop.IMG_LO.
Proof.
assert (E : existsb (fun sg => Z.of_N (seg_base sg) <=? YImgTop.IMG_LO) tfibsegs = true) by (clear; vm_compute; reflexivity).
apply existsb_exists in E as (sg & Hs & Hb). exists sg. split; [exact Hs | apply Z.leb_le; exact Hb].
Qed.
Lemma img_hi_seg_A : IMG_HI_SEG tfibsegs YImgTop.IMG_TOP.
Proof.
assert (E : existsb (fun sg => YImgTop.IMG_TOP <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) tfibsegs = true)
by (clear; vm_compute; reflexivity).
apply existsb_exists in E as (sg & Hs & Hb). exists sg. split; [exact Hs | apply Z.leb_le; exact Hb].
Qed.
Lemma img_cover_A : IMG_COVER.
Proof.
intros ly S md L. rewrite im_img_cover_A. unfold AF0x.img_cover. rewrite TFIB_IMG_LO_lo, TFIB_IMG_END_top.
exact (img_cover_of_ledger_cf tfibsegs YImgTop.IMG_LO YImgTop.IMG_TOP ly S md img_lo_seg_A img_hi_seg_A L).
Qed.

(* The depot zone's static part lies in one owned static area (found by value over the whole table); the rest is
   the nodes and store blocks. *)
Lemma dzone_owned_A : forall B, TfibSyms B -> DZONE_OWNED B.
Proof.
intros B TB ly a Ha. rewrite dg_dzone_A in Ha. unfold AFgi.DZONE in Ha. destruct Ha as [Ha|[Ha|Ha]].
- left. rewrite (ts_owned _ TB). refine (ADIfaceImgA.covers_b_Exists _ _ _ _ a Ha). clear. vm_compute. reflexivity.
- right. left. exact Ha.
- right. right. exact Ha.
Qed.

(* IAL_AREA_B at A: the internal allocator zone's bounds (AF0m's TFIB_IAL_LO / HI, A/AFgn.v IZONE) are B's. *)
Lemma ial_area_B_A : forall B, TfibSyms B -> as_ialloc_lo B <= TFIB_IAL_LO /\ TFIB_IAL_HI <= as_ialloc_hi B.
Proof. intros B TB. rewrite (ts_ial_lo _ TB), (ts_ial_hi _ TB). lia. Qed.
(* The flag bytes lie in one owned static area (found by value over the whole table). *)
Lemma ial_flag_static_A : forall B, TfibSyms B ->
forall a, TFIB_IAL_FLAG <= a < TFIB_IAL_FLAG + 4 -> Exists (in_zr a) (as_owned_static B).
Proof.
intros B TB a Ha. rewrite (ts_owned _ TB). refine (ADIfaceImgA.covers_b_Exists _ _ _ _ a Ha). clear. vm_compute. reflexivity.
Qed.
Lemma izone_owned_A : forall B, TfibSyms B -> IZONE_OWNED B.
Proof.
intros B TB a Ha. rewrite dg_izone_A in Ha. unfold AFgn.IZONE in Ha. destruct Ha as [Ha|Ha].
- left. pose proof (ial_area_B_A B TB) as [L H]. lia.
- right. exact (ial_flag_static_A B TB a Ha).
Qed.

(* ================================================================================================================ *)
(* The DIface model fields at the instance, for every ghost set Hp (ARX := ARXs_cf B im_segs Hp, AOX := aowned B,   *)
(* rpre := rpre_dealloc_cf B, fpre := fpre_cf B Hp, lpost := qtight, ft := free_cf, dbody := drain_body_cf,           *)
(* U := admits (as_universe B); di_lpost_d_A / di_post_n_inst_A below, YGcfDIface.v:9).                              *)
Theorem di_inst_A : forall B, TfibSyms B ->
forall Hp inst ly S W mem md, ARXs_cf B im_segs Hp inst ly S W mem md -> dg_inst_ok inst.
Proof. intros B TB Hp inst ly S W mem md (Hi & _). rewrite dg_inst_ok_A, Hi, (ts_inst _ TB). exact inst_ok_TFIB_INST_A. Qed.

Theorem di_view_n_img_A : forall B Hp inst ly S W mem md n,
ARXs_cf B im_segs Hp inst ly S W mem md -> rpre_dealloc_cf B S n -> im_img_cover ly.
Proof. intros B. exact (di_view_n_img_cf B img_cover_A). Qed.

Theorem di_shape_n_A : forall B n tr S, rpre_dealloc_cf B S n -> free_cf PNull tr S = ret tt (dtick S).
Proof. exact di_shape_n_cf. Qed.

(* Modified by a Theorem Labs lane (DeallocNmaxA), 2026-10-30: the enqueue side of free_cf's size test only
   (`req_size n <= kQuarantineMax`, as YGcfDIface.di_shape_cf); the larger blocks take the big Deallocate arm
   (DGbigIF.DIfaceBig, lib/Reusable/DGbigIF.v:146). *)
Theorem di_shape_A : forall B p n tr S k, p <> PNull -> rpre_dealloc_cf B S n -> req_size n <= kQuarantineMax ->
In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
free_cf p tr S = (depot_put tr ;; modify (fun s => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; enqueue (qk k) ;; dmd drain_body_cf) (dtick S).
Proof. exact di_shape_cf. Qed.

Theorem di_lpost_d_A : forall B Hp inst ly S W mem md p n tr k z nb X' (W' : world im_segs) (mem' : word -> option byte) (md' : Model) trc r,
ARXs_cf B im_segs Hp inst ly S W mem md -> rpre_dealloc_cf B S n -> In (p, n) (blocks S) -> admits (as_universe B) tr S ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
st_qthread X' = qc_push (st_qthread (qx S k z tr)) (qk k) nb ->
match nb with None => need_new_batch (st_qthread (qx S k z tr)) = false | Some _ => need_new_batch (st_qthread (qx S k z tr)) = true end ->
st_chunks X' = st_chunks (qx S k z tr) -> st_qglobal X' = st_qglobal (qx S k z tr) ->
ARXs_cf B im_segs Hp inst ly X' W' mem' md' ->
kQuarantineCacheMax < qc_bytes (st_qthread X') ->
apath (drain_body_cf X' X') trc r -> gflag trc = true -> qtight (snd r).
Proof. exact di_lpost_d_cf. Qed.

(* di_post_n with no premise left: A/ADIfacePostNA.v's di_post_n_A, whose dmem_n_A and ARXs_cf B tfibsegs Hp are
   DGif0's dmem_n and ARXs_cf B im_segs Hp at AImg_A / DImg_A by conversion. The fpre premise is not used. *)
Theorem di_post_n_inst_A : forall B, TfibSyms B ->
forall Hp inst ly S W mem0 md0 n tr sp0 mem' mat,
ARXs_cf B im_segs Hp inst ly S W mem0 md0 -> rpre_dealloc_cf B S n -> fpre_cf B Hp ly S W mem0 PNull n -> admits (as_universe B) tr S ->
ly_stk_lo ly + DGbaseC.DFSTACK <= sp0 -> sp0 <= ly_stk_hi ly -> ly_bot ly < sp0 -> sp0 mod 16 = 0 ->
dmem_n W ly sp0 mem0 mem' ->
(exists trc, apath (free_cf PNull tr S) trc (tt, dtick S) /\ gflag trc = true) ->
ARXs_cf B im_segs Hp inst ly (dtick S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\ qtight (dtick S).
Proof.
intros B TB Hp inst ly S W mem0 md0 n tr sp0 mem' mat HA HR _ HU H1 H2 H3 H4 HM HP.
exact (ADIfacePostNA.di_post_n_A B TB Hp inst ly S W mem0 md0 n tr sp0 mem' mat HA HR HU H1 H2 H3 H4 HM HP).
Qed.

Theorem di_frame_A : forall B Hp, di_frame_t (ARXs_cf B im_segs Hp) (aowned B).
Proof. exact di_frame_cf. Qed.

Theorem di_stack_A : forall B Hp, di_stack_t (ARXs_cf B im_segs Hp) (aowned B).
Proof. exact di_stack_cf. Qed.

Theorem di_owned_A : forall B, TfibSyms B ->
forall Hp inst ly S W mem md p n k a,
ARXs_cf B im_segs Hp inst ly S W mem md -> rpre_dealloc_cf B S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
0 <= a < 2 ^ 64 -> dwrites ly (sptr_addr B ly p) (req_size n) a ->
aowned B ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof. intros B TB. exact (di_owned_cf B (dzone_owned_A B TB)). Qed.

Theorem di_owned_b_A : forall B Hp inst ly S W mem md lastb initr a,
ARXs_cf B im_segs Hp inst ly S W mem md -> rev (qc_list (st_qthread S)) = lastb :: initr -> 0 <= a < 2 ^ 64 -> bwrites ly lastb a ->
aowned B ly S a.
Proof. exact di_owned_b_cf. Qed.

Theorem di_owned_i_A : forall B, TfibSyms B ->
forall Hp inst ly S W mem md a, ARXs_cf B im_segs Hp inst ly S W mem md -> dg_izone a -> aowned B ly S a.
Proof. intros B TB. exact (di_owned_i_cf B (izone_owned_A B TB)). Qed.

Theorem di_owned_x_A : forall B Hp inst ly S W mem md p n k z tr a,
ARXs_cf B im_segs Hp inst ly S W mem md -> rpre_dealloc_cf B S n -> In (p, n) (blocks S) -> find_user (st_chunks S) p = Some k ->
aowned B ly (qx S k z tr) a -> aowned B ly S a \/ (sptr_addr B ly p <= a < sptr_addr B ly p + req_size n).
Proof. exact di_owned_x_cf. Qed.

End P.
