(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8n.v:1199-1201
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-202, 358-363, 390-392 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:207-209 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC59.v:27-30 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8k.v:388-389. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_identity_reac_ver_str.v, with its module paths and module names changed; 48 of its 69 lines of code are new or changed and 1053 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: taken from a working branch d2efa2b83ff without its uncommitted DRAFT_fopen.v (sha256 c5819f1f77c8; internal record): the image facts (segments, read-only image) and the strcmp wrapper's contract are named Section hypotheses; the strcmp window is FO_WIN's ESTACK. *)
(* Modified by Theorem Labs, 2026-10: moved here unchanged from lib/A/Prog/PcapFuzzFopen.v (a working branch aa9ae568171): roimg_low, roimg_kept_aview, astrcmp_path_at and the Record FopenImg (fields fi_sep / fi_head / fi_kimg, their Arguments lines, and FopenImg's clear-implicits line with its guard), in their Sections, so that both images' walks Require one text: lib/B/Prog/PcapFuzzFopen.v (a working branch a629513d834) restates them and will Require this file instead. *)
(* The image-generic Definitions of libreac_fuzz_fopen's walk (fuzz_pcap v1.9.0: lib/A/Prog/PcapFuzzFopen.v walks the
   ASan image, lib/B/Prog/PcapFuzzFopen.v the asan-ubsan image): the read-only-image fact's dependence on the bytes
   below alloc_ceiling (roimg_low) and its keeping (roimg_kept_aview), the strcmp wrapper's contract at the walk's one
   call (astrcmp_path_at), and the image facts the walk takes (FopenImg). This file Requires lib/Reusable, lib/A/Prog's
   PcapBase.v and PcapFuzzFopenDefs.v (FO_WIN, mbyte_kept_lo) and lib/A/Stdio only: no listing, no PAImg, no image
   instance. The comments below name the ASan image's instances, as in the walk they came from. The fields' Arguments
   lines act only inside Section d: a file that Requires this one gives FopenImg its SK and reads the fields as
   fi_sep _ _ _ FI. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI0s YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0s YC5d PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFmemopenISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapFuzzFopenDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section p.
Variable segs : list Segment.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* The read-only-image fact roimg (lib/A's ro_img, a Theorem Labs lane's lib/A/AE3i.v) depends only on the image bytes below
   alloc_ceiling; so the writes of this function and of its strcmp call, all inside FO_WIN, keep it. *)
Definition roimg_low (roimg : (word -> option byte) -> Prop) : Prop :=
forall m m' : word -> option byte,
(forall a, 0 <= a < alloc_ceiling -> mbyte segs m' a = mbyte segs m a) -> roimg m -> roimg m'.

Lemma roimg_kept_aview : forall (roimg : (word -> option byte) -> Prop), roimg_low roimg ->
forall (W : world segs) (m m' : word -> option byte) sp0,
(forall x, 0 <= x < 2 ^ 64 -> ~ FO_WIN sp0 x -> aview segs (w_H W) m' x = aview segs (w_H W) m x) ->
alloc_ceiling <= sp0 - 32 - ESTACK ->
roimg (rdW W m) -> roimg (rdW W m').
Proof.
intros roimg HLOW W m m' sp0 HK Hlo. apply HLOW. intros a Ha. exact (mbyte_kept_lo segs W m m' sp0 a HK Hlo Ha).
Qed.

(* The strcmp wrapper's contract at this function's one call: entered at pc with a0 = a1 = x, the address of the
   "<fuzz-input>" literal (12 bytes and the NUL: 13), with the read-only-image fact and the literal addressable in
   ASan's shadow, it returns 0, keeps memory outside [sp - ESTACK, sp), the ASan state AR, the callee-saved
   registers, and makes no event. It is a Theorem Labs lane's astrcmp_lit_realizes B (lib/A/Rt/StrcmpDef.v) at its instance
   (A_FUZZ_PATH, A_FUZZ_PATH, 0), with segs := tfibsegs, roimg := ro_img, pc := SM_ENTRY, x := A_FUZZ_PATH (that
   contract's window is the same [sp - ESTACK, sp); a strcmp text that keeps memory only outside
   [sp - 2 * ESTACK, sp) does not imply this post). *)
Definition astrcmp_path_at (B : asyms) (roimg : (word -> option byte) -> Prop) (pc x : Z) : Prop :=
forall ly S (W : world segs) regs mem md,
ecall_pre segs B ly S W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 x ->
roimg (rdW W mem) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x 13 ->
shadow_hull_vis (aview segs (w_H W) mem) x 13 ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
  c' = cfg_at segs (raZ regs) regs' mem' md' /\
  AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
  getr regs' 10 = w64 0 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End p.

(* The image facts the walk uses, each fixed by fuzz_pcap.asan and discharged by the image instance: the two
   globals do not overlap, the source's open-file head is the one ajournal spares, and the stdio cells
   asource_none names lie in the image. None of them names the segments. *)
Record FopenImg (A_GLEN A_GFILE : Z) (K : asource_syms) : Prop := {
fi_sep : A_GLEN + 8 <= A_GFILE \/ A_GFILE + 8 <= A_GLEN;
fi_head : as_ofl_head K = @AOFL_HEAD SK;
fi_kimg : Forall (fun a => 0 <= a /\ a + 16 <= pcap_img_end)
  [as_threaded K; as_need_locks K; as_ofl_lock K; as_mode K; as_rwa K; as_canary K]
}.
(* The record's parameters are inferable from the record argument, so the fields read as  fi_sep FI. *)
Arguments fi_sep {A_GLEN A_GFILE K} _.
Arguments fi_head {A_GLEN A_GFILE K} _.
Arguments fi_kimg {A_GLEN A_GFILE K} _.
End d.
(* The sink-head instance is the caller's to give: the only global instance loaded with the unit is the plain
   build's (Reusable/YI5b.v src0_sink_head), whose open-file head is not the ASan image's. *)
Arguments FopenImg SK A_GLEN A_GFILE K : clear implicits.
Check (fun (SK : YI16.sink_head) (A_GLEN A_GFILE : Z)
           (K : asource_syms) => FopenImg SK A_GLEN A_GFILE K).
