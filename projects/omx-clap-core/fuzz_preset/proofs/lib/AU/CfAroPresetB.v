(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (rows A19b + A19 of omx-clap-core/fuzz_preset's cf instance, image B' = #102 pin
   fuzz_preset.asan-ubsan d663f82d7f48; field round 3 part 3c re-fit 2026-10-31).  The two unit IMAGE rows field
   round 3 asks of each image (lib/Reusable/YG0ncf.v relro_seg_t / errno_relro_t) at CfImg_B, the bridge's
   non-writable row, and the arodata corollary at image B'; the twin of lib/A/CfAroPresetA.v.
   - [relro_seg_preset_AU]: the RELRO range [cf_relro_lo, cf_relro_hi) of CfImg_B (AU/CfImgB.v, generated from the
     unstripped twin; equal to the twin's PT_GNU_RELRO, read with pyelftools) and each range of CfImg_B's cf_ro_reads
     lie in one segment of YB1v.tfibsegs: decided by computation over the segment list;
   - [errno_relro_preset_AU]: errno's four bytes (YF0m.TFIB_ERRNO through TfibSyms' ts_errno) are apart from the RELRO
     range and from each cf_ro_reads range;
   - [relro_top_preset_AU]: the RELRO range ends inside the 64-bit address space;
   - [ro_reads_nw_preset_AU]: each cf_ro_reads range lies in a NON-WRITABLE segment, inside 2^64 (the bridge's RONW);
   - [arodata_ok_cf_preset_AU]: lib/Reusable/YCeg.v's reader form arodata_ok at a world's view gives the layer's value
     form YG0dcf.arodata_ok_cf at CfImg_B (the bridge lib/Reusable/YGcfAroBridge.v with the four rows).
   Every bound is a named value (CfImg_B's fields, YF0m.TFIB_ERRNO, the segment list); no numeral is typed here.
   rule 24: no function proved (kind: image facts by computation and one corollary of a generic bridge). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0n YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCeg.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.

(* A19b, row 1 (part 3c: both conjuncts): the RELRO range and each range of cf_ro_reads lie in one segment of the
   image, by computation over the segment list. *)
Theorem relro_seg_preset_AU : relro_seg_t (ci := CfImg_B) tfibsegs.
Proof.
assert (Hb : existsb (fun sg => ((Z.of_N (seg_base sg) <=? @cf_relro_lo CfImg_B) &&
                                (@cf_relro_hi CfImg_B <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool)
               tfibsegs = true) by (vm_compute; reflexivity).
assert (Hr : forallb (fun r => existsb (fun sg => ((Z.of_N (seg_base sg) <=? fst r) &&
                                (fst r + snd r <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool) tfibsegs)
               (@cf_ro_reads CfImg_B) = true) by (vm_compute; reflexivity).
split.
- apply existsb_exists in Hb as (sg & Hin & Hs). apply andb_true_iff in Hs as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin | split; assumption].
- apply Forall_forall. intros r Hin. rewrite forallb_forall in Hr. specialize (Hr r Hin).
  apply existsb_exists in Hr as (sg & Hs & Hb2). apply andb_true_iff in Hb2 as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hs | split; assumption].
Qed.

(* A19b, row 2 (part 3c: both conjuncts): errno's four bytes are apart from the RELRO range and from each range of
   cf_ro_reads. *)
Theorem errno_relro_preset_AU : forall B, TfibSyms B -> errno_relro_t (ci := CfImg_B) B.
Proof.
intros B TS. unfold errno_relro_t. rewrite (ts_errno B TS). unfold TFIB_ERRNO.
split; [cbv [cf_relro_lo cf_relro_hi CfImg_B]; lia|].
assert (Hr : forallb (fun r => ((TFIB_ERRNO + 4 <=? fst r) || (fst r + snd r <=? TFIB_ERRNO))%bool)
               (@cf_ro_reads CfImg_B) = true) by (vm_compute; reflexivity).
apply Forall_forall. intros r Hin. rewrite forallb_forall in Hr. specialize (Hr r Hin).
apply orb_true_iff in Hr as [H1 | H1]; [left | right]; apply Z.leb_le in H1; exact H1.
Qed.

(* The RELRO range ends inside the 64-bit address space (the bridge's HTOP). *)
Theorem relro_top_preset_AU : @cf_relro_hi CfImg_B <= 2 ^ 64.
Proof. cbv [cf_relro_hi CfImg_B]. lia. Qed.

(* Part 3c, the bridge's RONW: each range of cf_ro_reads lies in a NON-WRITABLE segment of the image, inside 2^64, by
   computation over the segment list. *)
Theorem ro_reads_nw_preset_AU : YGcfAroBridge.ro_reads_nw_t (ci := CfImg_B) tfibsegs.
Proof.
assert (Hr : forallb (fun r => (fst r + snd r <=? 2 ^ 64) && existsb (fun sg => (negb (seg_writable sg) &&
                                (Z.of_N (seg_base sg) <=? fst r) &&
                                (fst r + snd r <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool) tfibsegs)%bool
               (@cf_ro_reads CfImg_B) = true) by (vm_compute; reflexivity).
unfold YGcfAroBridge.ro_reads_nw_t. apply Forall_forall. intros r Hin. rewrite forallb_forall in Hr.
specialize (Hr r Hin). apply andb_true_iff in Hr as [HT Hr]. apply Z.leb_le in HT.
apply existsb_exists in Hr as (sg & Hs & Hb). apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [NW H1].
apply negb_true_iff in NW. apply Z.leb_le in H1. apply Z.leb_le in H2.
split; [exact HT|]. exists sg. split; [exact Hs | split; [exact NW | split; assumption]].
Qed.

(* A19, the corollary at image B': the reader form of YCeg.v at a world's view gives arodata_ok_cf at CfImg_B. *)
Theorem arodata_ok_cf_preset_AU : forall B (W : world tfibsegs) (mem : word -> option byte), TfibSyms B ->
  YCeg.arodata_ok B (aview tfibsegs (w_H W) mem) -> arodata_ok_cf (ci := CfImg_B) tfibsegs B mem.
Proof.
intros B W mem TS H.
apply (YGcfAroBridge.arodata_ok_cf_of_P (ci := CfImg_B) tfibsegs B W mem relro_seg_preset_AU
  (errno_relro_preset_AU B TS) relro_top_preset_AU ro_reads_nw_preset_AU).
exact H.
Qed.

End a.
