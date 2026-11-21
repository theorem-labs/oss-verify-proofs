(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: written for zlib/checksum_fuzzer on the frame of the cgif proof's library; 18 of its 48 lines of code, among them its imports, match lines of proofs/cgif/cgif_rgb_fuzzer/lib/YH05.v up to addresses and numbers, and the rest is new. *)
(* Modified by Trevor Hansen, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/ZImage.v for ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer, with its module paths changed, and its addresses and numbers named by Reusable/YAddr.v, which holds this fuzz target's plain binary's values; its comments restated for this fuzz target. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (z_init_st_ok over the launch's ProcInput, the vDSO base and the CONFIG_RSEQ start-up state); launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
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
Definition zss0 (rs two : bool) : sstate := ss0 rs zpc0 Plain.M.phdrs zW two zimg.
Lemma z_init_pc_eq : Z.of_N Plain.M.init_pc = zpc0.
Proof. reflexivity. Qed.

Theorem z_init_st_ok : forall
  (inp : ProcInput) (mbase sp brk : word) (rnd : EntryDraw)
  (xw : nat -> word) (xd : nat -> list byte) (two : bool),
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
  xd UID_DATOM = uid_bytes (in_uid inp) -> xd HWCAP_DATOM = hwcap_bytes (in_hwcap inp) ->
  xd RAND_DATOM = rand_bytes rnd -> xd GID_DATOM = gid_bytes (in_gid inp) ->
  xd EHDR_DATOM = ehdr_bytes inp sp mbase ->
  xd EXECFN_DATOM = execfn_ptr_bytes (ed_top rnd) (in_execfn inp) ->
  (if two then 2 <= length (in_argv inp) else True)%nat ->
  st_ok zsegs (E0 sp (ed_top rnd) (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp) (in_execfn inp) xw xd)
    (zss0 (kb_rseq (in_kernel inp)) two)
    (init_machine_state zsegs Plain.M.init_pc Plain.M.phdrs sp mbase rnd inp).
Proof.
  intros inp mbase sp brk rnd xw xd two Hsp Hva Hve Hvl Hlau Hxd Hxh Hxr Hxg Hxe Hxf Htwo.
  unfold zss0. rewrite <- z_init_pc_eq.
  eapply init_st_ok;
    first [ exact Hsp | exact Hva | exact Hve | exact Hvl | exact Hlau
          | exact Hxd | exact Hxh | exact Hxr | exact Hxg | exact Hxe | exact Hxf
          | exact Htwo | exact zimg_ok | (unfold zW; lia) ].
Qed.
