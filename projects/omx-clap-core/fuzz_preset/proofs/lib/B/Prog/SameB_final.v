(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B' (asan-ubsan #102 pin d663f82d7f48, unstripped twin c90d4fa54d43), same:
   THE WALK AT THE INSTANCE OF RECORD. lib/B/Prog/SameB_walk.v's same_holds_B, the batch kit's text tsame_specX itself
   (lib/A/PRH_FnEx.v :353 at the cut 7cdbb61b5fa0, with its GUARDED live-stack premise
   `spZ regs <= pa -> YGcallStackUp.astack_up_x segs ly W (spZ regs) mem` after fpre), at B := YD2l.TfibB,
   RL := prh_room_live_a8. PAL := PALibB.exvi_eh_palib; SMB_CF (ARx refines ARcf) the identity / proj1. Two tops:
   - same_holds_B_TfibBx at the relation of record ARxs = ARcf /\ xs_placed_cf (YGcallcf.ARxs; LAWS :=
     YGcallcf.AR_laws_x_xs);
   - same_holds_B_TfibB at plain ARcf (LAWS := PALibB.exvi_eh_laws).
   CONSUMER CHECK (fresh reviewer subagent SameCallSites, 2026-10-29 21:5xZ, read-only): every B' application of the
   same text discharges the GUARDED premise with no caller change, because each root is in a fake frame or a Lam
   block, below YM05.alloc_ceiling <= the callee's sp, so the guard is false: Cno102B_R7.v:736 (cno102b-r
   1db3315ff552 = dec-2-p102-R7-7 4526688622a1; check_no_overread's class-3 fake frame), Rtt102CKB.v:2046
   (h-aag-10-p102-R7; doc a caller's fake frame, back round_trip_text's class-1 fake frame), the SameB recursion
   (kids in Lam). No B' call site passes a root on the caller's own stack.
   What stays open, by name: the two runtime rows, MARKED TEXTS (strcmp: YGcallMxmn.astrcmp_realizes_xrom, OWNER
   c-libc-stdio; bcmp: YGcallMxmn.abcmp_realizes_xm, OWNER c-asan), as ExvB_Stmt.v's EXV_HYP eh_strcmp / eh_bcmp take
   them. No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import SameB_defs SameB_walk.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).

Theorem same_holds_B_TfibB : forall (SK : YI16.sink_head),
  astrcmp_realizes_xrom rsegs TB ARI B_prog_relro_lo B_prog_relro_hi SMB_STRCMP ->
  abcmp_realizes_xm rsegs TB ARI SMB_BCMP ->
  forall n, tsame_specX (cp := CP) (RL := @prh_room_live_a8 CP) (PA := PI_prog_B) TB ARI SK n.
Proof.
intros SK HSTR HBCMP n.
exact (@same_holds_B fx rc ci CP (@prh_room_live_a8 CP) TB ARI SK PALibB.exvi_eh_laws PALibB.exvi_eh_palib HSTR HBCMP
  (fun _ _ _ _ _ _ H => H) n).
Qed.

(* ---- AT THE RELATION OF RECORD for the image-B TFIB closure: ARx := ARcfx = (ARcf rsegs TfibB /\ xs_placed_cf), the
   relation consumers cite (as PItems_compose.v's pi_step_PI_TfibBx, cold/h-rw-pre-7-bp-parse_items 73f5e5156205).
   LAWS by YGcallcf.AR_laws_x_xs rsegs TfibB (YG0lawscf.AR_laws_ok_cf rsegs TfibB), unconditional; PAL by
   PALibB.exvi_eh_palib (PALib does not mention ARx); SMB_CF by proj1. The two runtime rows stay MARKED TEXTS, now at
   ARcfx. ---- *)
#[local] Abbreviation ARX := (fun ly S Hp W mem md =>
  YG0ncf.ARcf (cp := CP) rsegs TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

Theorem same_holds_B_TfibBx : forall (SK : YI16.sink_head),
  astrcmp_realizes_xrom rsegs TB ARX B_prog_relro_lo B_prog_relro_hi SMB_STRCMP ->
  abcmp_realizes_xm rsegs TB ARX SMB_BCMP ->
  forall n, tsame_specX (cp := CP) (RL := @prh_room_live_a8 CP) (PA := PI_prog_B) TB ARX SK n.
Proof.
intros SK HSTR HBCMP n.
exact (@same_holds_B fx rc ci CP (@prh_room_live_a8 CP) TB ARX SK
  (YGcallcf.AR_laws_x_xs (cp := CP) rsegs TB (YG0lawscf.AR_laws_ok_cf (cp := CP) rsegs TB))
  PALibB.exvi_eh_palib HSTR HBCMP (fun _ _ _ _ _ _ H => proj1 H) n).
Qed.
End f.

Set Printing Implicit.
Check same_holds_B_TfibBx.
Check same_holds_B_TfibB.
Unset Printing Implicit.
Print Assumptions same_holds_B_TfibB.
Print Assumptions same_holds_B_TfibBx.
