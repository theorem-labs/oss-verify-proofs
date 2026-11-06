(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset literal, image A' (#102 asan pin 1be0f53d96cb, unstripped twin bff8519bbe3e; facts
   8f3e7e1a07f1): literal_bridge.literal_holds (lib/A/Prog/literal_bridge.v) at the image instance. No new walk.
   #102: relocated from the old-pin instance (origin/cold/h-verbs-1-lit-bridgeb 34b0f96319c6, pin d83eb25dbf0d) by the
   alreloc of record c4338d099cfb8025 (moved: one comment numeral below, by a resolve line; the row is in the commit).
   The instance: B := AD2l.TfibB (image A's generated record, lib/A/AD2l.v eb321db7a357 at this tree's base
   origin/cold/h-verbs-1-leaves102 6240a87c3eb7), ARx := YG0ncf.ARcf (cp := CfParams_preset) rsegs TfibB (h-mani-a8's
   second allocator instance), HL := cf_head CfParams_preset. The instance facts are h-rw-man-5's lib/A/PALibA.v (blob
   88c72c8175cf, = origin/cold/h-rw-man-5-palib102i d00dd1234426's, the A' twin; at the base): LAWS :=
   PALibA.palib_laws_A, PAL := PALibA.palib_A, each closed there (palib_A field by field by vm_compute at the A' record
   and the #102 listing PI_prog_A; palib_laws_A by YG0lawscf.AR_laws_ok_cf). These are the INSTANCE WITNESSES of the two
   image-fact premises of literal_holds (LAWS, PAL); no other image fact is a premise.
   READ-ONLY MEMORY (2026-10-29): no instance premise. literal_holds no longer takes pal_rom_ok (in_rom a -> a in no
   as_owned_static range and not an errno byte), which 68059ec877b proved FALSE on the old pin; at A' too as_owned_static
   TfibB (lib/A/AF0m.v Tfib_owned_static) has rows inside the read-only segment [65536, 200704), e.g. (66280, 8) and
   (118373, 21). The leaf takes the fpre conjunct arodata_okP (owned-static and errno bytes excluded) as it is
   (lib/Prog/literal_xs.v).
   REMAINING PREMISES, both call rows: ASTRLEN : YGcallMxmn.astrlen_realizes_xrom at PI_prog_A's __wrap_strlen and relro
   range (the strlen row, arodata_okP form with the memnorm keep); ABCMP : YGcallMxmn.abcmp_realizes_xm at PI_prog_A's
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnReader CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l PALibA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require literal_bridge.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

#[local] Notation PA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PAImg_prog.PI_prog_A.
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation TA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.AD2l.TfibB.
#[local] Notation ARI := (YG0ncf.ARcf (cp := CP) SEGS TA).

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Variable SK : YI16.sink_head.
Hypothesis ASTRLEN : YGcallMxmn.astrlen_realizes_xrom SEGS TA ARI (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA)
  (@pa_sigma _ A_prog_listing PA AS___wrap_strlen).
Hypothesis ABCMP : YGcallMxmn.abcmp_realizes_xm SEGS TA ARI (@pa_sigma _ A_prog_listing PA AS___wrap_bcmp).

Theorem literal_holds_inst : tliteral_specX (cp := CP) (PI := prh_img_A) (RL := prh_room_live_a8 (cp := CP)) (PA := PA) TA ARI SK.
Proof.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.literal_bridge.literal_holds (fx := fx) (rc := rc)
  (HL := @cf_head CP) SK TA ARI (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PALibA.palib_laws_A (rc := rc))
  (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PALibA.palib_A (rc := rc)) ASTRLEN ABCMP).
Qed.
End i.
Check literal_holds_inst.
Print Assumptions literal_holds_inst.
(* the delivered statements with every implicit (instance / state) argument shown *)
Set Printing Implicit. Unset Printing Notations.
Check @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.literal_x.literal_x_holds.
Check @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.literal_mn.literal_x_holds_mnI.
Check @OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog.literal_bridge.literal_holds.
Check @literal_holds_inst.
Unset Printing Implicit. Set Printing Notations.
