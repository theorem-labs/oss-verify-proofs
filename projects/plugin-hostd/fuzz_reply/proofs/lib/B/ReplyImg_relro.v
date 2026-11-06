(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file. Row img-relro-B of a Theorem Labs lane's reply image rows (its CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) :158,
   Table 1 note "RELRO byte 0x9edd0 = 1" at cgif): the same fact at reply image B (fuzz_reply.asan-ubsan, pin sha256
   10ffb5f9202ae2bd...; unstripped twin 3389287e1d610784...). The image-A twin, lib/A/ReplyImg_relro.v (row img-relro-A,
   written on its own branch), states the same names and statements with suffix _A.

   What the word is (measured on the pin and its twin; scripts' output kept with the lane, not cited by path here): the .got
   slot that holds the address of the absolute symbol __sanitizer_silent_reports (st_value 1, SHN_ABS). Two readers load it,
   each by an auipc / ld pair: __sanitizer::CatastrophicErrorWrite (auipc 0x620f0, ld 0x620f4) and
   __sanitizer::ReportFile::Write (auipc 0x67ce0, ld 0x67ce4, then `beqz a3, 8; ret`), so the word being 1 makes both report
   writes return at once. At cgif the same slot is 0x9edd0, loaded at 0x6082c and 0x6641c. The slot lies in .got
   [0x9def0, 0x9ec48), inside PT_GNU_RELRO [0x9d9b8, 0x9f000) (lib/B/W_img.v fr_relro_img).

   Consumer form: the report walk's rif_silent (cgif lib/RepIFcf.v:170 on the report-f1 lane,
   `val_mem tfibsegs (mrestrict (w_H W) mem) C_SILENT 8 1`, C_SILENT at :70); silent_val_B gives it for any memory that
   holds nothing at the slot, and silent_img_B for the empty memory.
   The slot address is read from the twin's code and .got; the byte values come from the image bytes through
   YB13.tfib_rom2 by vm_compute. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YO0f YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB13.
Local Open Scope Z_scope.

(* the .got slot of __sanitizer_silent_reports at image B (the cf report walk's C_SILENT) *)
Definition C_SILENT_B : Z := 0x9eb18.

Lemma silent_in_relro_B : 0x9d9b8 <= C_SILENT_B /\ C_SILENT_B + 8 <= 0x9f000.
Proof. unfold C_SILENT_B. lia. Qed.

(* the 8 image bytes of the slot are the little-endian word 1 *)
Lemma silent_rom_B : forall k, (k < 8)%nat ->
  seg_rom tfibsegs (Z_to_bv 64 (C_SILENT_B + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte 1 8 k)).
Proof.
  intros k Hk. unfold C_SILENT_B.
  do 8 (destruct k as [|k]; [rewrite tfib_rom2 by lia; vm_compute; reflexivity|]). lia.
Qed.

(* the consumer form: a memory that holds nothing at the slot reads the word 1 there *)
Lemma silent_val_B : forall mem : word -> option byte,
  (forall k, (k < 8)%nat -> mem (Z_to_bv 64 (C_SILENT_B + Z.of_nat k)) = None) ->
  val_mem tfibsegs mem C_SILENT_B 8 1.
Proof.
  intros mem H k Hk. unfold mbyte. rewrite (H k Hk). exact (silent_rom_B k Hk).
Qed.

Lemma silent_img_B : val_mem tfibsegs (fun _ => None) C_SILENT_B 8 1.
Proof. apply silent_val_B. intros k _. reflexivity. Qed.
