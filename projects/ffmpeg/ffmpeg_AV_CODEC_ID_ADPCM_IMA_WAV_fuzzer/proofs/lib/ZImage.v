(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: written for zlib/checksum_fuzzer on the frame of the cgif proof's library; 18 of its 48 lines of code, among them its imports, match lines of proofs/cgif/cgif_rgb_fuzzer/lib/YH05.v up to addresses and numbers, and the rest is new. *)
(* Modified by Trevor Hansen, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/ZImage.v for ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer, with its module paths changed, and its addresses and numbers named by Reusable/YAddr.v, which holds this fuzz target's plain binary's values; its comments restated for this fuzz target. *)
(** Symbolic initial memory for the fixed ADPCM_IMA_WAV plain image. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import
  YK11 YP0m YP09 YP0l YP08 YP02.
From OSSVerify.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.images Require Plain.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import YAddr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.

Definition zsegs : list Segment := Plain.M.loaded_segments.
(* .text: 0x493c4, 0xe338c bytes = 232675 instructions *)
Definition ztext_start : Z := (AX_text_start).
Definition ztext_count : nat := NX_text_insns.
Definition ztbl : ctable := Eval vm_compute in
  (build_table zsegs ztext_start ztext_count TEmpty).
Lemma ztbl_eq : ztbl = build_table zsegs ztext_start ztext_count TEmpty.
Proof. vm_compute. reflexivity. Qed.
Lemma ztbl_ok : table_ok zsegs ztbl.
Proof. rewrite ztbl_eq. apply build_table_ok0. unfold ztext_start. lia. Qed.

(* the four LOAD segments, page-aligned: read-only data, code, relro, data + bss *)
Definition zimg : smem :=
  [mkRegion None (AX_page_ro) (AX_page_text) 0 0 [mkChunk (AX_page_ro) (CImg LX_ro)];
   mkRegion None (AX_page_text) (AX_page_relro) 0 0 [mkChunk (AX_page_text) (CImg LX_text)];
   mkRegion None (AX_page_relro) (AX_page_data) (AX_page_relro) (AX_page_data) [mkChunk (AX_page_relro) (CImg LX_relro)];
   mkRegion None (AX_page_data) (AX_page_end) (AX_page_data) (AX_page_end) [mkChunk (AX_page_data) (CImg LX_data)]].
Lemma zimg_ok : img_check zsegs zimg = true.
Proof. vm_compute. reflexivity. Qed.
Definition zpc0 : Z := (AX_text_start).
Definition zW : Z := 65536.
Definition zss0 (two : bool) : sstate := ss0 zpc0 Plain.M.phdrs zW two zimg.
Lemma z_init_pc_eq : Z.of_N Plain.M.init_pc = zpc0.
Proof. reflexivity. Qed.

Theorem z_init_st_ok : forall
  (sp : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw)
  (xw : nat -> word) (xd : nat -> list byte) (two : bool),
  valid_sp sp -> valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp ->
  xd UID_DATOM = uid_bytes uid -> xd HWCAP_DATOM = hwcap_bytes hw ->
  xd RAND_DATOM = rand_bytes rnd ->
  (if two then 2 <= length argv else True)%nat ->
  st_ok zsegs (E0 sp argv envp xw xd) (zss0 two)
    (init_machine_state zsegs Plain.M.init_pc Plain.M.phdrs sp rnd argv envp uid hw).
Proof.
  intros sp argv envp uid hw rnd xw xd two Hsp Hva Hve Hfits Hxd Hxh Hxr Htwo.
  unfold zss0. rewrite <- z_init_pc_eq.
  apply (init_st_ok zsegs Plain.M.phdrs sp argv envp Hsp Hva Hve Hfits uid hw rnd
    zW ltac:(unfold zW; lia) xw xd Hxd Hxh Hxr Plain.M.init_pc two zimg Htwo zimg_ok).
Qed.
