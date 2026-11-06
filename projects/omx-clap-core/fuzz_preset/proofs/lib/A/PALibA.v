(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 pin asan 1be0f53d96cb, unstripped twin bff8519bbe3e; facts 8f3e7e1a07f1):
   the A' twin of the old-pin PALibA (9191751aea39, pin d83eb25dbf0d), the same proof text, built against the A' record files
   (AD2l eb321db7a357, AF0m 97f423adf6eb, listing 7ed1529926bd / PAImg_prog 505a51ff7d08, YImgTop d2a97d3111ce): the
   image-A twin of lib/B/PALibB.v, the ONE HOME of the image-instance facts every image-A program walk takes as Section
   stand-ins: YC1fP.PALib at the whole-program listing PI_prog_A and B := TfibB of lib/A/AD2l.v (image A's generated
   record), the head length and the laws of h-mani-a8's second allocator instance ARcf rsegs TfibB at CfParams_preset.
   Proves nothing about the program. Shaped on h-rw-pre-7's image-B proof (lib/B/Prog/ExvB_ImgFacts.v :186 / :196 /
   :211 / :214 at origin/cold/h-rw-pre-7-b-ex_value 96eea692f6cd, moved to lib/B/PALibB.v): same tactics, image A's
   record, listing and image. Closed facts by vm_compute on closed terms only.
   Numerals: none typed except 4 (LENGTH: errno) and the errno address, which is read from the record (as_errno TfibB =
   AD2l's TFIB_ERRNO) and checked against kLowMemEnd by computation. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Img Img0 Listing_prog PAImg_prog.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_A.

Section i. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TA).

(* the errno cells lie in image A *)
Lemma palib_errno_cells_A : YStrtodRowX.srx_cells_b rsegs (as_errno TA) 4 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma palib_errno_A : api_env rsegs TA.
Proof.
split; [|split].
- split; apply Z.leb_le; vm_compute; reflexivity.
- intros a Ha.
  exact (YStrtodRowX.srx_cell_img rsegs a
    (YStrtodRowX.srx_cells_b_sound rsegs (as_errno TA) 4 a palib_errno_cells_A Ha)).
- split; apply YCej.memZL_In; vm_compute; reflexivity.
Qed.

Lemma palib_A : YC1fP.PALib (PI := PI_prog_A) TA.
Proof.
constructor.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- left. apply Z.leb_le. vm_compute. reflexivity.
- exact palib_errno_A.
- vm_compute. reflexivity.
- vm_compute. reflexivity.
- split; apply Z.ltb_lt; vm_compute; reflexivity.
- vm_compute. reflexivity.
- exact A_prog_got_uar_disj.
Qed.

(* ---- the instance's head length and laws ---- *)
Lemma palib_head_A : 8 <= @cf_head CP.
Proof. exact CfParamsPreset.preset_head_wide. Qed.

Lemma palib_laws_A : AR_laws_x rsegs TA ARI (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_cf (cp := CP) rsegs TA (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TA)). Qed.
End i.
