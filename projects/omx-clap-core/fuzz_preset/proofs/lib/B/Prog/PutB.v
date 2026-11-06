(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (asan-ubsan #102 pin d663f82d7f48, unstripped twin c90d4fa54d43), THE
   THEOREM of the walk of put (lane PutB, a Theorem Labs lane), against the kit's text tput_specX of the batch kit's cut
   (lib/A/PRH_FnWriter.v (sha256 bc9a9128f55a; internal record) :410-499), at the B' instance
   (the internal file bprime-pivot.md item 6): PA := PI_prog_B, B := YD2l.TfibB, ARx := ARcfx (ARcf /\ xs_placed_cf =
   YGcallcf.ARxs), cp := CfParams_preset, ci := CfImg_B, RL := prh_room_live_a8.
   rule 24: no function proved (the batch kit's rebind of put B'): the walk is int102's (e3d81b897ee, from a Theorem Labs lane bp-put
   0ea1325e9b81), rebound to the batch kit's texts.
   WHAT IS PROVED: THE TEXT ITSELF. The earlier walk proved a _FIX twin that added a refusal premise
   (REFUSED-RET) and weakened the grow-NULL conjunct to `exists hist'` (NULL-HIST). The kit's text resolves both:
   it takes the consumer window prh_cons_from and states the refusal arm DEAD (`exists ok, prhWriter_ret_ok .. /\
   prh_granted ..`, DEAD-PUT), and its grow-NULL conjunct is the twin's `exists hist'` form. So the twin, its
   premise and the kernel check tput_specX_FIX_of_text are deleted, and put_holds_B is tput_specX at the instance.
   FRM0-ENTRY: fpre carries `frm_zero (fp_csr fx)`; put's post is fpostWmR at wle' (no exit frm_zero), so the entry
   conjunct is only threaded to fuzz_realloc's fpre (PutB_Base.put_realloc_call).
   THE RE-HIDING MOVE AND THE HULL (the texts' current form): tput_specX concludes SRr' segs RZ_cf with its post
   fpostWmR at wle' segs RZ_cf and takes `(length rp_os <= 4)%nat`. Arm 0 (PutB_Arms.putb_arm0) is proved in that form;
   arm 1 makes no call, so its plain SRr is lifted here (YA0nH.SRr_SRr', its journal by YCbqG.ajournal_xwR_mono).
   fuzz_realloc's hull budget is the env's pe_hull, witnessed at the instance in PutB_Wit.v from put's run position
   (PresetHullPay.hull_budget_of_room_pos): fuzz_realloc's text takes a hull_budget, not the entry headroom
   cf_hull_adm that drv_cf_headroom_at_call_B gives.
   SECTION HYPOTHESES of the instance theorem (each a callee or runtime row, with its owner):
     H_real : tfuzz_realloc_specX at the instance (the kit's text at the batch kit's cut, PRH_FnAlloc.v 4d8aeba047e :412-509; owner
              the fuzz_realloc B' walk);
     H_amc  : YGcallMxmn.aintrin_realizes_xm for __asan_memcpy at the instance (owner the runtime rows).
   Every image premise of the walk (PutB_Base.putb_env) is witnessed at the instance in PutB_Wit.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC81.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YGcallMx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YG0dcf YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetLiveBounds PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterSpecFacts WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutB_Kit PutB_Base PutB_Arms PutB_Wit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
Import ListNotations.
Open Scope Z_scope.

(* ---- the walk's theorem, generic in the instance PA of the B' listing, B, ARx and the premise bundle ---- *)
Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).

Theorem putb_holds_gen : forall (B : asyms)
    (ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop),
  putb_env (SK := SK) B ARx ->
  forall CTX0, tput_specX (PI := prh_img_B) (L := B_prog_listing) (PA := PA) B ARx SK CTX0.
Proof.
intros B ARx PE CTX0 rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S Hp W regs mem md ch o s n d buf st bs Lam
  peak ran HPRE HROOM HPOS HLEN HCONS HUNIV H10 H11 H12 HCASE HREC HWIN Hol Hoh HOUT HLED HSRC Hn HHOME HEV HWMAX HMAX
  HLIVE.
pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & Hf01 & _).
pose proof (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) as PL.
pose proof (srr_inv_call_imp SEGS mem) as PC.
destruct Hf01 as [Hf0 | Hf1].
- refine (SRr'_mono SEGS YGcfRehidePost.RZ_cf _ _ _ _ (putb_arm0 B ARx PE CTX0 rp_sm rp_x rp_os rp_H0
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PL PC
    ly S Hp W regs mem md ch o s n d buf st bs Lam peak ran most own rp_i rp_hist HPRE HROOM HPOS HLEN HCONS HUNIV
    H10 H11 H12 HCASE HREC HWIN Hol Hoh HOUT HLED HSRC Hn HHOME HEV HWMAX HMAX HLIVE Hf0 (fun H => H)) _).
  intros W' c' _ HQ. unfold fpostWmR. exact HQ.
- (* arm 1 runs no call: its plain SRr and its journal are lifted into the text's form *)
  apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  refine (SRr_mono SEGS _ _ _ _ (putb_arm1 B ARx PE rp_sm rp_x rp_os rp_H0
    (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) PL
    ly S Hp W regs mem md ch o d buf st bs Lam peak ran most own rp_i rp_hist HPRE HROOM HPOS H10 HWIN Hol Hoh HOUT
    HLED Hf1 (fun H => H)) _).
  intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Ec & HJ & HK & HP & HQ).
  unfold fpostWmR, fpostWR. exists ly', S', Hp', regs', mem', md', k.
  split; [exact Ec|].
  split; [exact (ajournal_xwR_mono (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (@wle SEGS)
    (wle' SEGS YGcfRehidePost.RZ_cf) (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJ)|].
  split; [exact HK|]. split; [exact HP | exact HQ].
Qed.
End W.

(* ---- THE INSTANCE THEOREM ---- *)
Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {ci : CfImg}.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance PRH_Base.prh_room_live_a8.
#[local] Abbreviation PA := (@PI_prog_B rc).
#[local] Abbreviation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation ARcfx :=
  (fun ly S Hp (W : world SEGS) mem md => YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* CALLEE TEXT, owner the fuzz_realloc B' lane: the kit's tfuzz_realloc_specX at the batch kit's cut (PRH_FnAlloc.v 4d8aeba047e
   :412-509) *)
Hypothesis H_real :
  tfuzz_realloc_specX (ci := CfImgB.CfImg_B) (cp := CP) (RL := @PRH_Base.prh_room_live_a8 CP) (PI := prh_img_B)
    (L := B_prog_listing) (PA := PA) TB ARcfx SK.
(* RUNTIME ROW, owner the runtime rows: __asan_memcpy realizes OCpy with its memnorm keep *)
Hypothesis H_amc : YGcallMxmn.aintrin_realizes_xm SEGS TB ARcfx OCpy (SIGMA AS___asan_memcpy).

(* The kit's text tput_specX (PRH_FnWriter.v d89d3c67b78 :410-499) at the instance, VERBATIM *)
Theorem put_holds_B : forall CTX0,
  tput_specX (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CP) (PI := prh_img_B)
    (RL := @PRH_Base.prh_room_live_a8 CP) (L := B_prog_listing) (PA := PA) TB ARcfx SK CTX0.
Proof.
exact (putb_holds_gen (fx := fx) (rc := rc) (ci := CfImgB.CfImg_B) (cp := CP)
  (RL := @PRH_Base.prh_room_live_a8 CP) (SK := SK) (PA := PA) TB ARcfx (putb_wit_env H_real H_amc)).
Qed.
End inst.

Set Printing Implicit. Unset Printing Notations.
Check put_holds_B.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions put_holds_B.
