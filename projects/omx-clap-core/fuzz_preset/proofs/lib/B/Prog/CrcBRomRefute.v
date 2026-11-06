(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin c90d4fa54d43), lane
   BCrs of h-rw-pre-5 (relocated to B' by lane CrcBp): the IMAGE-PREMISE REPAIR of lib/B/Prog/CrcB.v
   (check_reject_clean_holds_B) and its instance witnesses, after the template of lib/A/Prog/S6PalLitRefute.v
   (cold/h-hpreset-7-walk-S6 9b261c2b0c8). Every fact is a vm_compute of a CLOSED goal at the B' instance of this tree:
   segments B/Img0.v rsegs (blob d17de1e3b380; = pa_segs PI_prog_B, PAImg_prog.v:405 `pa_segs := rsegs`) and asyms
   YD2l.TfibB (lib/Reusable/YD2l.v 95803a8b9493, whose as_owned_static is YF0m.Tfib_owned_static and as_errno
   YF0m.TFIB_ERRNO, YD2l.v:34 / :23; YF0m.v f82202ebccdf).
   (a) THE REFUTATION of the old premise in its own words at the B' instance: CrcB.v's stand-in pal_rom_ok (`forall a,
       in_rom SEGS a -> ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)`, CrcB.v:251 at
       the old-pin blob 10dc5869c48c) is FALSE: an owned-static range of positive size starts inside a read-only
       segment (the ASan redzones of .rodata globals). cr_pal_rom_ok_false_B.
       AGREEMENT with g-ph-relay's #102 refutation pal_rom_ok_false_B102 (origin/cold/g-ph-relay-p102-N9-ROMVIEW-102Bp
       0d0f7930f0a3, lib/ZZRomviewProbe102Bp.v:46-49, over the same blobs Img0 d17de1e3b380 / YF0m f82202ebccdf):
       cr_pal_rom_ok_txt_B102 shows the old text at TfibB IS relay's proposition (by conversion), and
       cr_pal_rom_ok_false_B102 restates relay's lemma verbatim from cr_pal_rom_ok_false_B. The Evals below print the
       same counts as relay's probe (:51-53).
   (b) THE RESTATED premise is CrcB.v's cr_empty_ro: only the 56 bytes of `empty` the walk reads itself are not
       owned-static and not errno (arodata_okP's guard, so fpre's arodata_okP gives their image bytes).
   (c) ITS INSTANCE WITNESS cr_empty_ro_B: cr_empty_ro YD2l.TfibB.
   (d) THE INSTANCE WITNESS of CrcB.v's EMPTY_ZS: cr_empty_zs_B (a granule-aligned zero-shadow range of TfibB covers
       `empty`'s 56 bytes).
   (e) check_reject_clean_holds_B_inst: the walk at B := TfibB, ARx := ARcf rsegs TfibB, LAWS by PALibB.exvi_eh_laws
       (5baa19c890f7), EMPTY_RO / EMPTY_ZS by (c) / (d); the callee texts and the image-shadow fact stay premises.
   rule 24: proves no function (kind: image-premise refutation and witness). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrcB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m YG0ncf YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
Import ListNotations.
Local Open Scope Z_scope.
(* image B's segments, FULLY QUALIFIED: the closure also loads the PLAIN image's lib/Img0.v, and in this file the short
   name `Img0.rsegs` resolves to THAT one (Locate, measured 19:2xZ), not to lib/B/Img0.v's *)
#[local] Notation SEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.

(* CrcB.v's OLD pal_rom_ok (:251, blob 10dc5869c48c), verbatim over its Section's SEGS (= pa_segs PI_prog_B = rsegs,
   PAImg_prog.v:405) and B *)
Definition cr_pal_rom_ok_txt (B : asyms) : Prop :=
  forall a, in_rom SEGS_B a ->
    ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

(* (a) the old premise is false at the B' instance *)
Lemma cr_pal_rom_ok_false_B : ~ cr_pal_rom_ok_txt YD2l.TfibB.
Proof.
intros Hall.
assert (H : existsb (fun r => existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? fst r) &&
    (fst r <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS_B && (0 <? snd r))
  (as_owned_static YD2l.TfibB) = true) by (vm_compute; reflexivity).
apply existsb_exists in H as (r & Hr & Hb). apply andb_prop in Hb as [Hs Hpos]. apply Z.ltb_lt in Hpos.
apply existsb_exists in Hs as (s & Hs & Hb). apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct (Hall (fst r) ltac:(exists s; split; [exact Hs|]; split; [exact H0|]; lia)) as [Hn _].
apply Hn. apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. lia.
Qed.

(* (a') the old text at TfibB is g-ph-relay's proposition (ZZRomviewProbe102Bp.v:46-48), by conversion *)
Lemma cr_pal_rom_ok_txt_B102 : cr_pal_rom_ok_txt YD2l.TfibB <->
  (forall a, in_rom SEGS_B a -> ~ Exists (in_zr a) YF0m.Tfib_owned_static
                                  /\ ~ (YF0m.TFIB_ERRNO <= a < YF0m.TFIB_ERRNO + 4)).
Proof. split; intros H; exact H. Qed.

(* g-ph-relay's pal_rom_ok_false_B102, its statement verbatim, from (a) *)
Lemma cr_pal_rom_ok_false_B102 :
  ~ (forall a, in_rom SEGS_B a -> ~ Exists (in_zr a) YF0m.Tfib_owned_static
                                       /\ ~ (YF0m.TFIB_ERRNO <= a < YF0m.TFIB_ERRNO + 4)).
Proof. intros H. apply cr_pal_rom_ok_false_B. apply cr_pal_rom_ok_txt_B102. exact H. Qed.

(* (c) the INSTANCE WITNESS of the restated premise *)
Lemma cr_empty_ro_B : cr_empty_ro YD2l.TfibB.
Proof.
unfold cr_empty_ro.
assert (Hb : forallb (fun j =>
    forallb (fun r => negb ((fst r <=? CR_EMPTY + Z.of_nat j) && (CR_EMPTY + Z.of_nat j <? fst r + snd r)))
      (as_owned_static YD2l.TfibB) &&
    negb ((as_errno YD2l.TfibB <=? CR_EMPTY + Z.of_nat j) && (CR_EMPTY + Z.of_nat j <? as_errno YD2l.TfibB + 4)))
  (seq 0 56) = true) by (vm_compute; reflexivity).
intros a Ha. rewrite forallb_forall in Hb.
specialize (Hb (Z.to_nat (a - CR_EMPTY)) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in Hb by lia. replace (CR_EMPTY + (a - CR_EMPTY)) with a in Hb by lia.
apply andb_prop in Hb as [Ho He]. split.
- intros HE. apply Exists_exists in HE as (r & Hr & Hin). rewrite forallb_forall in Ho. specialize (Ho r Hr).
  unfold in_zr in Hin. apply negb_true_iff, andb_false_iff in Ho.
  destruct Ho as [Ho | Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; lia.
- apply negb_true_iff, andb_false_iff in He.
  destruct He as [He | He]; [apply Z.leb_gt in He | apply Z.ltb_ge in He]; lia.
Qed.

(* (d) the INSTANCE WITNESS of CrcB.v's EMPTY_ZS *)
Lemma cr_empty_zs_B : exists q m, In (q, m) (as_zero_shadow YD2l.TfibB) /\ q mod 8 = 0 /\ q <= CR_EMPTY /\
  CR_EMPTY + 56 <= q + m / 8 * 8.
Proof.
assert (H : existsb (fun r => (fst r mod 8 =? 0) && (fst r <=? CR_EMPTY) && (CR_EMPTY + 56 <=? fst r + snd r / 8 * 8))
  (as_zero_shadow YD2l.TfibB) = true) by (vm_compute; reflexivity).
apply existsb_exists in H as ([q m] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
exists q, m. split; [exact Hin|]. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(* (e) THE WALK AT THE B' INSTANCE: check_reject_clean_holds_B at B := TfibB and ARx := h-mani-a8's ARcf rsegs TfibB
   (PALibB.v's ARI), with its static image premises DISCHARGED: LAWS by PALibB.exvi_eh_laws (blob 5baa19c890f7),
   EMPTY_RO by cr_empty_ro_B, EMPTY_ZS by cr_empty_zs_B. What stays a premise is what this walk does not own: the
   callee texts (fuzz_alloc_live's text, owner the accessor lane; the bcmp row in the keep form, owner
   a Theorem Labs lane) and the image-shadow fact at ARcf (owner a Theorem Labs lane: tfib_img_shadow_vis_cf_B, AImgShadowVisCfB.v:48). *)
Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
(* the guard: CrcB.v's SEGS (pa_segs PI_prog_B) IS image B's segments, so every fact above is about the walk's image *)
Lemma cr_segs_B : @pa_segs _ B_prog_listing PI_prog_B = SEGS_B.
Proof. reflexivity. Qed.
Lemma check_reject_clean_holds_B_inst : forall SK : YI16.sink_head,
  tfuzz_alloc_live_specX (cp := CfParams_preset) (PI := prh_img_B) (PA := PI_prog_B) YD2l.TfibB
    (YG0ncf.ARcf (cp := CfParams_preset) SEGS_B YD2l.TfibB) SK ->
  YGcallMxmn.abcmp_realizes_xm SEGS_B YD2l.TfibB (YG0ncf.ARcf (cp := CfParams_preset) SEGS_B YD2l.TfibB)
    (@pa_sigma _ B_prog_listing PI_prog_B AS___wrap_bcmp) ->
  cr_img_shadow_vis_B (YG0ncf.ARcf (cp := CfParams_preset) SEGS_B YD2l.TfibB) ->
  tcheck_reject_clean_specX (cp := CfParams_preset) (PI := prh_img_B) (PA := PI_prog_B) YD2l.TfibB
    (YG0ncf.ARcf (cp := CfParams_preset) SEGS_B YD2l.TfibB) SK.
Proof.
intros SK FL BC IV.
eapply check_reject_clean_holds_B;
  [exact PALibB.exvi_eh_laws | exact FL | exact BC | exact cr_empty_ro_B | exact IV | exact cr_empty_zs_B].
Qed.
End inst.

(* `empty`'s address at B' (to compare with the twin's symtab: check_reject_clean.empty) *)
Eval vm_compute in CR_EMPTY.
(* the witnesses of (a): every owned-static range of positive size that starts inside a read-only segment *)
Eval vm_compute in (filter (fun r => existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? fst r) &&
    (fst r <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS_B && (0 <? snd r))
  (as_owned_static YD2l.TfibB)).
(* relay's two counts (ZZRomviewProbe102Bp.v:51-52), over the same lists *)
Eval vm_compute in (length (filter (fun r => existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? fst r) &&
    (fst r <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) SEGS_B && (0 <? snd r)) YF0m.Tfib_owned_static),
  length YF0m.Tfib_owned_static).
(* the zero-shadow range of (d) *)
Eval vm_compute in (filter (fun r => (fst r mod 8 =? 0) && (fst r <=? CR_EMPTY) && (CR_EMPTY + 56 <=? fst r + snd r / 8 * 8))
  (as_zero_shadow YD2l.TfibB)).
Print Assumptions cr_pal_rom_ok_false_B.
Print Assumptions cr_pal_rom_ok_false_B102.
Print Assumptions cr_empty_ro_B.
Print Assumptions cr_empty_zs_B.
Print Implicit check_reject_clean_holds_B.
Check check_reject_clean_holds_B.
Print Assumptions check_reject_clean_holds_B.
Print Assumptions check_reject_clean_holds_B_inst.
