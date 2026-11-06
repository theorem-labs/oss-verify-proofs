(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file for libreac/fuzz_scene's asan walk (lib.A).  The PRESENCE of
   reac_scene_placeholder, [0x20e80, 0x20e80 + 8904) (lib/A/P_LLVMFuzzerTestOneInput.v's A_reac_scene_placeholder
   and LLVMF_SCENE_BYTES, written here as literals because this file does not Require the statement file; they are
   convertible): every byte of it is a byte of the image's loaded segments, so `seg_rom` gives it.  This is the
   placeholder-presence premise of the S1 segment in the form lib/AU/P_LLVMFuzzerTestOneInput_S1.v states it as
   HIMG_PL.  Only presence: the byte values are not stated here.  Decided on the image by one closed `vm_compute`
   over the 8904 offsets (the route of a Theorem Labs lane's asan S1 file, lemma s1_pl_rom). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A.Prog Require Import SceneList SceneCode ScenePa SceneImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The closed form, on the image's segment list itself: the goal vm_compute sees has no section variable. *)
Lemma scene_pl_rom_segs : forall i, 0 <= i < 8904 -> seg_rom scene_segs (Z_to_bv 64 (0x20e80 + i)) <> None.
Proof.
assert (Hb : forallb (fun k => match seg_rom scene_segs (Z_to_bv 64 (0x20e80 + Z.of_nat k)) with
Some _ => true | None => false end) (seq 0 8904) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. intros i Hi.
assert (Hin : In (Z.to_nat i) (seq 0 8904)).
{ apply in_seq. split; [apply Nat.le_0_l|]. rewrite Nat.add_0_l.
change 8904%nat with (Z.to_nat 8904). apply Z2Nat.inj_lt; lia. }
specialize (Hb _ Hin). rewrite Z2Nat.id in Hb by lia.
destruct (seg_rom scene_segs (Z_to_bv 64 (0x20e80 + i))); [discriminate | discriminate Hb].
Qed.

(* The form the S1 segment takes as its placeholder-presence premise, with SEGS spelled out (its Section's context). *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma scene_pl_rom : forall i, 0 <= i < 8904 -> seg_rom (@pa_segs _ scene_listing PI_scene) (Z_to_bv 64 (0x20e80 + i)) <> None.
Proof. exact scene_pl_rom_segs. Qed.
End r.
