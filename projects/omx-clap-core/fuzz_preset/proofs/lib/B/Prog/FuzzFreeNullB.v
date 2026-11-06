(* fuzz_preset, image B (asan-ubsan): the kit's NULL-only text tfuzz_free_null_specX (lib/A/PRH_FnAlloc.v, image-parametric;
   the internal file PRIMED-SHAPES.md sec. 4.1) PROVED at image B's instance (prh_img_B, PI_prog_B) and the walk's allocator
   relation ARcfx, by a Theorem Labs lane's walk of the NULL arm of fuzz_free, lib/B/Prog/FuzzFreeB.v ff_p0 (the frame, beqz a0
   taken, the epilogue, ret: no call is made). The B' taker crs_free0_B (lib/B/Prog/CrsFree0Bp.v) takes this same
   text at prh_img_B. The kit's file: it Requires the walk and does not edit it.
   THE ONE EXTRA STEP, as lib/A/Prog/FuzzFreeNull.v: ff_p0 states the memnorm keep as the LAST conjunct of its Q, the
   text's fpostm puts it outside Q (PRH_Base.fQmn), so one SRr_mono re-associates the post. Unprimed: no SRr', no wle'.
   rule 24: reuses the walk of fuzz_free (lib/B/Prog/FuzzFreeB.v ff_p0, a Theorem Labs lane); no new walk.
   Inputs: lib/A/PRH_FnAlloc.v at a working branch 199ce1959e69 (blob 9bdccdc2648e); lib/B/Prog/FuzzFreeB.v
   at a working branch 0a79ffff7ef4. No numeral in this file. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre FCiface YGcallx YGcallcf YGcfHp YGcallPx YGcallPcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzFreeB.
Import ListNotations.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance prh_room_live_a8.
#[local] Abbreviation PA := PI_prog_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).

Section f.
Variable B : asyms.
(* the walk's allocator relation, as FuzzFreeB.v Section f spells it *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* FuzzFreeB.v Section f's hypotheses, in its spelling; the theorem below keeps only those ff_p0 uses (About below) *)
Hypothesis AFREE : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep SEGS B.
Hypothesis AUNPOISON : aunpoison_realizes_cf SEGS B.
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.
Hypothesis pal_pst_ok : forall a, Exists (in_zr a) prh_pst ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis pal_unpoison : SIGMA AS___asan_unpoison_memory_region = cf_pc_unpoison.
Hypothesis TS : YF0m.TfibSyms B.

Theorem fuzz_free_null_holds_B :
  tfuzz_free_null_specX (PI := prh_img_B) (PA := PI_prog_B) B ARcfx SK.
Proof.
unfold tfuzz_free_null_specX, fpostm, fQmn.
intros most own ly S Hp W regs mem md ch Lam peak cnt fail ran HPRE H10 HL.
destruct HPRE as [HPRE0 _].
eapply SRr_mono; [eapply (FuzzFreeB.ff_p0 (fx := fx) (rc := rc) (SK := SK) B); eassumption |].
(* the keep moves from the last conjunct of Q to fQmn's place outside Q *)
intros W' c' _ H. unfold fpost, apost_base_x in H |- *.
destruct H as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HP & ES & EHp & Eab & HL' & Hmn).
exists ly', S', Hp', regs', mem', md', k.
split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|]. cbv beta.
split; [|exact Hmn]. split; [exact ES|]. split; [exact EHp|]. split; [exact Eab | exact HL'].
Qed.

End f.
End d.

About fuzz_free_null_holds_B.
Print Assumptions fuzz_free_null_holds_B.
