(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan). ONE TEXT FOR EVERY PIN: it holds no image numeral, so the same
   blob builds on the old pin (f8f98a95bc52, twin 3b5e1a099b53) and on the #102 pin B' (d663f82d7f48, twin c90d4fa54d43); each
   tree's own record files (YD2l, the B listing, YF0m, YCej) decide the values, and every field closes by vm_compute there.
   The ONE HOME of the image-instance facts every image-B program walk takes as Section stand-ins: YC1fP.PALib at
   the whole-program listing PI_prog_B and B := TfibB (lib/Reusable/YD2l.v), the head length and the laws of
   h-mani-a8's second allocator instance ARcf rsegs TfibB at CfParams_preset. Proves nothing about the program.
   MOVED from h-rw-pre-7's lib/B/Prog/ExvB_ImgFacts.v at origin/cold/h-rw-pre-7-b-ex_value 96eea692f6cd (blob
   da1be778494f): exvi_eh_errno :186, exvi_eh_palib :196, exvi_eh_head :211, exvi_eh_laws :214 (h-rw-pre-7 agreed
   2026-10-29 12:15Z). Changes, none to a statement: the errno cell fact (strtod_row.strtod_cells_B's third conjunct)
   moved here as palib_errno_cells_B at as_errno TB; the errno bound and the GOT / uar disjointness are computed from
   the record instead of citing a typed address (0x5de0ec, old pin only) or a listing lemma (B_prog_got_uar_disj, v4 only).
   Numerals: 4 (LENGTH: errno). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Section i. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).

(* the errno cells lie in the image (moved from strtod_row.strtod_cells_B's third conjunct) *)
Lemma palib_errno_cells_B : YStrtodRowX.srx_cells_b rsegs (as_errno TB) 4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma exvi_eh_errno : api_env rsegs TB.
Proof.
split; [|split].
- (* the errno address is computed from the record (no typed numeral, so the same text holds on every pin) *)
  let v := eval vm_compute in (as_errno TB) in assert (E : as_errno TB = v) by (vm_compute; reflexivity).
  rewrite E. unfold kLowMemEnd. lia.
- intros a Ha.
  exact (YStrtodRowX.srx_cell_img rsegs a
    (YStrtodRowX.srx_cells_b_sound rsegs (as_errno TB) 4 a palib_errno_cells_B Ha)).
- split; apply YCej.memZL_In; vm_compute; reflexivity.
Qed.

Lemma exvi_eh_palib : YC1fP.PALib (PI := PI_prog_B) TB.
Proof.
constructor.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- left. apply Z.leb_le. vm_compute. reflexivity.
- exact exvi_eh_errno.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- split; apply Z.ltb_lt; vm_compute; reflexivity.
- vm_compute. reflexivity.
- (* the GOT / uar disjointness, closed here by computation so this file needs no listing lemma (the core's B PAImg_prog
     3b5bc0a640ec has none; v4 5abade432081 names it B_prog_got_uar_disj) *)
  assert (D : forall a b : Z, (a + 8 <=? b) || (b + 8 <=? a) = true -> a + 8 <= b \/ b + 8 <= a)
    by (intros a b Hab; apply Bool.orb_true_iff in Hab as [Hab|Hab]; [left|right]; apply Z.leb_le; exact Hab).
  split; apply D; vm_compute; reflexivity.
Qed.

(* ---- the instance's head length and laws ---- *)
Lemma exvi_eh_head : 8 <= @cf_head CP.
Proof. exact CfParamsPreset.preset_head_wide. Qed.

Lemma exvi_eh_laws : AR_laws_x rsegs TB ARI (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_cf (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB)). Qed.
End i.
