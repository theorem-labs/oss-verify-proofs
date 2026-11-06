(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-29: omx-clap-core/fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin
   c90d4fa54d43): THE B' INSTANCE of CheckBoundedAllocB.v's check_bounded_alloc_holds_B (the f97c text
   tcheck_bounded_alloc_specX, lib/A/PRH_FnCheck.v:523-532 blob 9ecd8eb167c6, proved verbatim with the ONE premise
   LAWS : AR_laws_x SEGS B ARx HL). Lane CbaBp of h-rw-pre-5.
   check_bounded_alloc_holds_B_inst: B := YD2l.TfibB (lib/Reusable/YD2l.v 95803a8b9493), ARx := h-mani-a8's allocator
   ARcf over image B's segments at CfParams_preset (PALibB.v's ARI), LAWS := PALibB.exvi_eh_laws (lib/B/PALibB.v
   5baa19c890f7). No other static image premise exists: the walk closes its image facts (the entry pa_sigma, the
   frame size, prh_pst's cells at prh_img_B) by vm_compute inside its own proof.
   NAMES: image B's segments are written FULLY QUALIFIED (SEGS_B below): this file's closure also loads the PLAIN
   image's lib/Img0.v, so the short name `Img0.rsegs` may resolve to the plain image (the Locate lines at the end print
   what each short name resolves to here). cba_segs_B checks by reflexivity that the walk's segments (pa_segs
   PI_prog_B, PAImg_prog.v:405 `pa_segs := rsegs`) ARE image B's.
   check_bounded_alloc_holds_B_inst_xs (h-pre-b1's request through h-rw-pre-5, 19:5xZ, so that its driver composes over
   ONE relation): the same walk at the relation of CrcBInstLive.v's check_reject_clean_holds_B_inst_live
   (origin/cold/h-rw-pre-5-r102-crcB 8f5bab31e565, lib/B/Prog/CrcBInstLive.v e49be3adb151), word for word:
   RL := prh_room_live_a8 at CfParams_preset, ARx := ARcf /\ xs_placed_cf over PI_prog_B's segments (its ARcfx), LAWS
   by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (CrcBInstLive.v's discharge). No premise.
   A separate file so that the walk's own closure (CheckBoundedAllocB.v) stays the one it was proved in: PALibB brings
   YF0v, which re-sets the zify flag. No numeral. rule 24: proves no function (kind: instance of an existing walk). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CheckBoundedAllocB.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
Import ListNotations.
Local Open Scope Z_scope.

(* image B's segments and the instance's names, FULLY QUALIFIED *)
#[local] Abbreviation SEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
#[local] Abbreviation PI_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.PI_prog_B.
#[local] Abbreviation L_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Listing_prog.B_prog_listing.
#[local] Abbreviation IMG_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PRH_ImgB.prh_img_B.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.

Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
(* the guard: the walk's SEGS (pa_segs PI_prog_B) IS image B's segments *)
Lemma cba_segs_B : @pa_segs _ L_B PI_B = SEGS_B.
Proof. reflexivity. Qed.
(* THE WALK AT THE B' INSTANCE, LAWS discharged by PALibB 5baa19c890f7 *)
Lemma check_bounded_alloc_holds_B_inst : forall SK : YI16.sink_head,
  tcheck_bounded_alloc_specX (cp := CP) (PI := IMG_B) (L := L_B) (PA := PI_B) YD2l.TfibB
    (YG0ncf.ARcf (cp := CP) SEGS_B YD2l.TfibB) SK.
Proof.
intros SK. exact (check_bounded_alloc_holds_B (cp := CP) YD2l.TfibB _ SK PALibB.exvi_eh_laws).
Qed.
End inst.

(* THE WALK AT CrcBInstLive.v's RELATION: ARx := ARcf /\ xs_placed_cf (its ARcfx, the same lambda over pa_segs
   PI_prog_B), RL := prh_room_live_a8; LAWS by YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf *)
Section L. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation SEGS := (@pa_segs _ L_B PI_B).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md =>
  YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).
Theorem check_bounded_alloc_holds_B_inst_xs : forall SK : YI16.sink_head,
  tcheck_bounded_alloc_specX (cp := CP) (PI := IMG_B) (RL := prh_room_live_a8 (cp := CP)) (L := L_B) (PA := PI_B)
    TB ARcfx SK.
Proof.
intros SK.
exact (check_bounded_alloc_holds_B (cp := CP) (RL := prh_room_live_a8 (cp := CP)) TB ARcfx SK
  (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB))).
Qed.
End L.

Locate Img0.rsegs.
Locate rsegs.
Locate PI_prog_B.
Locate B_prog_listing.
Locate prh_img_B.
Print Implicit check_bounded_alloc_holds_B.
Check @check_bounded_alloc_holds_B.
Check @check_bounded_alloc_holds_B_inst.
Print Assumptions check_bounded_alloc_holds_B.
Print Assumptions check_bounded_alloc_holds_B_inst.
Check @check_bounded_alloc_holds_B_inst_xs.
Print Assumptions check_bounded_alloc_holds_B_inst_xs.
(* the elaborated statement of the xs corollary, every implicit shown *)
Set Printing Implicit.
Unset Printing Notations.
Print check_bounded_alloc_holds_B_inst_xs.
(* the wrong-image check (rebind rule 7): every PA / L / PI argument of the three tops names image B' *)
About check_bounded_alloc_holds_B.
About check_bounded_alloc_holds_B_inst.
About check_bounded_alloc_holds_B_inst_xs.
Unset Printing Implicit.
Set Printing Notations.
