(* fuzz_preset, image A (asan): the kit's NULL-only text tfuzz_free_null_specX (lib/A/PRH_FnAlloc.v, the internal file PRIMED-SHAPES.md
   sec. 4.1, route (i) of the unit owner's 18:51Z item (2)) PROVED at the walk's allocator relation ARcfx, by
   a Theorem Labs lane's walk of the NULL arm of fuzz_free, lib/A/Prog/FuzzFree.v ff_p0 (the frame, beqz a0 taken, the
   epilogue, ret: no call is made). The kit's file: it Requires the walk and does not edit it.
   THE ONE EXTRA STEP: ff_p0 states the memnorm keep as the LAST conjunct of its Q, while the text's fpostm puts it
   outside Q (PRH_Base.fQmn: Q /\ keep). So the proof takes ff_p0 and re-associates the post by one SRr_mono; the
   journal, the return and the register conjuncts pass through unchanged. No SRr' and no wle': the text is unprimed on
   purpose (no free is called on this path, so nothing is re-hidden).
   rule 24: reuses the walk of fuzz_free (lib/A/Prog/FuzzFree.v ff_p0, a Theorem Labs lane); no new walk.
   Inputs: lib/A/PRH_FnAlloc.v at a working branch 199ce1959e69 (blob 9bdccdc2648e); lib/A/Prog/FuzzFree.v
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomPre YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcallcf YGcallPx YGcallPcf YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require FuzzFree.
Import ListNotations.
Open Scope Z_scope.

#[local] Abbreviation PA := (PI_prog_A).
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Abbreviation PST := (prh_pst (PI := prh_img_A)).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
#[local] Existing Instance prh_room_live_a8.
Context {SK : YI16.sink_head}.

Section f.
Variable B : asyms.
(* the walk's allocator relation, as FuzzFree.v Section f spells it *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* FuzzFree.v Section f's hypotheses, in its spelling; the theorem below keeps only those ff_p0 uses (About below) *)
Hypothesis AFREE : YGcfMallocComposeKeep.afree_realizes_cf_rh_keep SEGS B.
Hypothesis AUNPOISON : aunpoison_realizes_cf SEGS B.
Hypothesis PAL : PALib (rc := rc) (L := A_prog_listing) (PI := PA) B.
Hypothesis pal_pst_ok : forall a, Exists (in_zr a) PST ->
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis TB : AF0m.TfibSyms B.

Theorem fuzz_free_null_holds :
  tfuzz_free_null_specX (PI := prh_img_A) (PA := PI_prog_A) B ARcfx SK.
Proof.
unfold tfuzz_free_null_specX, fpostm, fQmn.
intros most own ly S Hp W regs mem md ch Lam peak cnt fail ran HPRE H10 HL.
destruct HPRE as [HPRE0 _].
eapply SRr_mono; [eapply (FuzzFree.ff_p0 (fx := fx) (rc := rc) (SK := SK) B); eassumption |].
(* the keep moves from the last conjunct of Q to fQmn's place outside Q *)
intros W' c' _ H. unfold fpost, apost_base_x in H |- *.
destruct H as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & HJ & HP & ES & EHp & Eab & HL' & Hmn).
exists ly', S', Hp', regs', mem', md', k.
split; [exact Hc|]. split; [exact HJ|]. split; [exact HP|]. cbv beta.
split; [|exact Hmn]. split; [exact ES|]. split; [exact EHp|]. split; [exact Eab | exact HL'].
Qed.

End f.
End d.

About fuzz_free_null_holds.
Print Assumptions fuzz_free_null_holds.
