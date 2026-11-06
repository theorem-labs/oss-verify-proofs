(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset literal, image B' (#102 asan-ubsan pin d663f82d7f48, unstripped twin c90d4fa54d43;
   facts 8f3e7e1a07f1): literal_bridge.literal_holds (lib/B/Prog/literal_bridge.v) at the image instance. No new walk.
   #102: relocated from the old-pin instance (origin/cold/h-verbs-1-lit-bridgeb 34b0f96319c6, pin f8f98a95bc52) by the
   alreloc of record c4338d099cfb8025 (moved: one comment numeral below, by a resolve line; the row is in the commit).
   The instance: B := YD2l.TfibB (image B's generated record, lib/Reusable/YD2l.v 95803a8b9493, the B' record of
   origin/cold/h-rw-man-5-palib102bj ed438196d17c, at this tree's base origin/cold/h-verbs-1-leaves102 6240a87c3eb7),
   ARx := YG0ncf.ARcf (cp := CfParams_preset) rsegs TfibB (h-mani-a8's second allocator instance), HL := cf_head
   CfParams_preset. The instance facts are h-rw-man-5's lib/B/PALibB.v (blob 5baa19c890f7, = ed438196d17c's; one text
   for every pin): LAWS := PALibB.exvi_eh_laws, PAL := PALibB.exvi_eh_palib, each closed there (exvi_eh_palib field by
   field by vm_compute at the B' record and the #102 listing PI_prog_B; exvi_eh_laws by YG0lawscf.AR_laws_ok_cf). These
   are the INSTANCE WITNESSES of the two image-fact premises of literal_holds (LAWS, PAL); no other image fact is a
   premise.
   READ-ONLY MEMORY (2026-10-29): no instance premise. literal_holds no longer takes pal_rom_ok (in_rom a -> a in no
   as_owned_static range and not an errno byte), which 68059ec877b proved FALSE on the old pin; at B' too as_owned_static
   TfibB (lib/Reusable/YF0m.v Tfib_owned_static) has rows inside the read-only segment [65536, 200704), e.g. (66280, 8)
   and (118379, 21). The leaf takes the fpre conjunct arodata_okP (owned-static and errno bytes excluded) as it is
   (lib/Prog/literal_xs.v).
   REMAINING PREMISES, both call rows: ASTRLEN : YGcallMxmn.astrlen_realizes_xrom at PI_prog_B's __wrap_strlen and relro
   range (the strlen row, arodata_okP form with the memnorm keep); ABCMP : YGcallMxmn.abcmp_realizes_xm at PI_prog_B's
   __wrap_bcmp (the bcmp row; no read-only premise). Both at this B and ARx; the row owners give them.
   Numerals: none in code. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YG0ncf YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require literal_bridge.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

#[local] Notation PA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.PI_prog_B.
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation TB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YD2l.TfibB.
#[local] Notation ARI := (YG0ncf.ARcf (cp := CP) SEGS TB).

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Variable SK : YI16.sink_head.
Hypothesis ASTRLEN : YGcallMxmn.astrlen_realizes_xrom SEGS TB ARI (@pa_relro_lo _ B_prog_listing PA) (@pa_relro_hi _ B_prog_listing PA)
  (@pa_sigma _ B_prog_listing PA AS___wrap_strlen).
Hypothesis ABCMP : YGcallMxmn.abcmp_realizes_xm SEGS TB ARI (@pa_sigma _ B_prog_listing PA AS___wrap_bcmp).

Theorem literal_holds_inst : tliteral_specX (cp := CP) (PI := prh_img_B) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) TB ARI SK.
Proof.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.literal_bridge.literal_holds (fx := fx) (rc := rc)
  (HL := @cf_head CP) SK TB ARI (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PALibB.exvi_eh_laws (rc := rc))
  (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PALibB.exvi_eh_palib (rc := rc)) ASTRLEN ABCMP).
Qed.
End i.
Check literal_holds_inst.
Print Assumptions literal_holds_inst.
(* the delivered statements with every implicit (instance / state) argument shown *)
Set Printing Implicit. Unset Printing Notations.
Check @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.literal_x4.literal_x_holds4.
Check @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.literal_mn4.literal_x_holds_mnI4.
Check @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.literal_bridge.literal_holds.
Check @literal_holds_inst.
Unset Printing Implicit. Set Printing Notations.
