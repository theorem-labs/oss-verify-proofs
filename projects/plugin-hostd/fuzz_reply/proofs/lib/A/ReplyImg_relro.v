(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply; row img-relro-A of
   REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record), CF-UNIT-HYPS.md:158 (sha256 77b3f94c95d2; internal record) "RELRO byte 0x9edd0 = 1 at cgif").
   rule 24: no function proved (kind: image row; a closed computation over reply's image A, fuzz_reply.asan, pin
   42c58610e125).  Reuse search: proof-index silent_rom silent_img C_SILENT rif_silent __sanitizer_silent_reports
   (2026-10-30 04:5xZ): no lemma at any unit; C_SILENT is only the cf report walk's Definition (RepIFcf.v:70, cgif).

   The fact.  cgif's 0x9edd0 (asan-ubsan image) is the .got word that __sanitizer::ReportFile::Write and
   CatastrophicErrorWrite load and test (`ld; beqz; ret`): the address of the absolute symbol
   __sanitizer_silent_reports, which this toolchain links as 1, so both return at once and no report is written.  The
   cf report walk names it C_SILENT (RepIFcf.v:70) and takes it as the field
   `rif_silent : val_mem tfibsegs (mrestrict (w_H W) mem) C_SILENT 8 1` of rep_img_facts (RepIFcf.v:170).
   At reply A (fuzz_reply.asan, read from the pin and its unstripped twin): __sanitizer_silent_reports = 1 (SHN_ABS);
   the .got word 0x9e598 holds it ([0x9d970, 0x9e6c8) is .got, inside PT_GNU_RELRO [0x9d438, 0x9f000)).  Readers, by a
   linear decode of .text (every auipc + ld resolving to the word): TWO, CatastrophicErrorWrite+0x8 0x6209c
   (`auipc a1, 0x3c; ld a3, 1280(a1)`) and ReportFile::Write+0x4 0x67c8c (`auipc a3, 0x37; ld a3, -0x6f0(a3)`), each
   followed by `beqz a3, 8; ret`.  Same two at reply B
   (0x620f4, 0x67ce4, word 0x9eb18) and at cgif (0x60830, 0x66420, word 0x9edd0).  The names below are the ones of
   lib/B/ReplyImg_relro.v (agreed with a Theorem Labs lane, 2026-10-30 05:00Z), so the A -> B relocation maps one to the other.
   The reply tree does not carry RepIFcf.v, so this file states the IMAGE part UNFOLDED: the eight bytes at C_SILENT_A
   are the little-endian word 1 in the image's segments (seg_rom), by AB13.tfib_rom2 and vm_compute over the proof
   image's bytes; and the val_mem form of rif_silent for every memory that leaves those bytes to the image. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YK1b YK07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP09 YO0f YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB13.
Open Scope Z_scope.

(* The cf report walk's C_SILENT (RepIFcf.v:70) at reply image A. *)
Definition C_SILENT_A : Z := 0x9e598.

(* The word's 8 bytes lie in the numeric RELRO range [0x9d438, 0x9f000) that A/W_img.v:52 fr_relro_img states. *)
Lemma silent_in_relro_A : 0x9d438 <= C_SILENT_A /\ C_SILENT_A + 8 <= 0x9f000.
Proof. unfold C_SILENT_A. lia. Qed.

(* The image bytes: byte k of the word at C_SILENT_A is byte k of 1 (little-endian). *)
Lemma silent_rom_A : forall k, (k < 8)%nat ->
  seg_rom tfibsegs (Z_to_bv 64 (C_SILENT_A + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte 1 8 k)).
Proof.
intros k Hk. unfold C_SILENT_A.
rewrite tfib_rom2 by lia.
do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

(* rif_silent's body (val_mem tfibsegs _ C_SILENT 8 1) at reply A, for any memory that holds no byte of its own at
   the eight addresses (there mbyte reads the image, YP09.v:18-22); at the empty memory in particular. *)
Lemma silent_val_A : forall mem : word -> option byte,
  (forall k, (k < 8)%nat -> mem (Z_to_bv 64 (C_SILENT_A + Z.of_nat k)) = None) ->
  val_mem tfibsegs mem C_SILENT_A 8 1.
Proof.
intros mem Hn k Hk. unfold mbyte. rewrite (Hn k Hk). apply silent_rom_A. exact Hk.
Qed.

Lemma silent_img_A : val_mem tfibsegs (fun _ => None) C_SILENT_A 8 1.
Proof. apply silent_val_A. intros k _. reflexivity. Qed.

Print Assumptions silent_rom_A.
Print Assumptions silent_val_A.
Print Assumptions silent_img_A.
Print Assumptions silent_in_relro_A.
