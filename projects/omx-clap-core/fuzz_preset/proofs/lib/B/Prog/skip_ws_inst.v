(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset skip_ws, image B' (asan-ubsan, the #102 pin d663f82d7f48, unstripped twin c90d4fa54d43):
   skip_ws_mn.skip_ws_holds (lib/B/Prog/skip_ws_mn.v) at the image instance. No new walk. RELOCATED from
   origin/cold/h-verbs-1-skip-union ad1c5072e3e7 (blob 2bba6542fdb6); the text holds no image numeral, so the proof is
   unchanged: every value comes from the #102 tree's record files. Added: the Check / Print / Print Assumptions block.
   B := YD2l.TfibB (the generated record of image B', lib/Reusable/YD2l.v blob 95803a8b9493 on this tree), ARx := YG0ncf.ARcf
   (cp := CfParams_preset) rsegs TfibB (h-mani-a8's second allocator instance), HL := cf_head CfParams_preset. The
   instance facts are lib/B/PALibB.v's (blob 5baa19c890f7, h-rw-man-5's PALib for B'): LAWS := PALibB.exvi_eh_laws,
   PALibCore := YC1fP.palib_core TfibB PALibB.exvi_eh_palib (every PALib field closed by vm_compute at TfibB).
   ci / cp / RL stay the section variables skip_ws_holds has (any value; the image-B texts take cp := CfParams_preset,
   RL := prh_room_live_a8). REMAINING PREMISES: none. No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16 YK06 YK04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require skip_ws_x skip_ws_mn skip_ws_witness.
Import ListNotations.
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.

#[local] Notation CP := CfParams_preset.
#[local] Notation TB := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YD2l.TfibB.
#[local] Notation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.

Theorem skip_ws_holds_inst : tskip_ws_specX (PI := prh_img_B) (PA := PI_prog_B) TB ARI SK.
Proof.
exact (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.skip_ws_holds (HL := @cf_head CP)
  SK TB ARI OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PALibB.exvi_eh_laws
  (YC1fP.palib_core TB OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PALibB.exvi_eh_palib)).
Qed.
End i.
Set Printing Implicit. Unset Printing Notations.
Check skip_ws_holds_inst.
Check OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.skip_ws_holds.
Check OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.skip_ws_x_holds_mnI.
Check OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.skip_ws_x_holds_mn.
Check OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_x.skip_ws_x_holds.
Check OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_witness.skip_ws_palib_core_B.
Print OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_x.tskip_ws_leafX.
Print OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.tskip_ws_leafXmn.
Print OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.tskip_ws_leafXmnI.
Print OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.tskip_ws_leafXP.
Print OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.msteps_keeps.
Print OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_mn.run_post_tok_AJxP.
Print Assumptions skip_ws_holds_inst.
Print Assumptions OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog.skip_ws_witness.skip_ws_palib_core_B.
