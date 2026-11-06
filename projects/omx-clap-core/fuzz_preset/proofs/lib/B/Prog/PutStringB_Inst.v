(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f488d30, twin c90d4fa54d43160b), this
   PutStringB (a Theorem Labs lane): the batch kit's tput_string_specX (the cut 7cdbb61b5fa0,
   lib/A/PRH_FnWriter.v (sha256 bc9a9128f55a; internal record), PRH_Base.v (sha256 2ca8a3d631bd; internal record); the walk proved the earlier PRH_FnWriter.v (sha256 1b338cb8e926; internal record) and was
   and was re-fitted to the batch kit with no new walk) for put_string AT THE INSTANCE OF RECORD (the internal file bprime-pivot.md item 6):
   PA := PAImg_prog.PI_prog_B, B := YD2l.TfibB, ARx := ARcfx = YG0ncf.ARcf SEGS TfibB /\ YG0ncf.xs_placed_cf
   (YGcallcf.v's ARxs), ci := CfImgB.CfImg_B, cp := CfParamsPreset.CfParams_preset, RL := PRH_Base.prh_room_live_a8,
   PI := prh_img_B; rc and SK stay Section Context, the float state is the theorem's binder.
   rule 24: proves function put_string (proof-index 17:58Z: `proof-index: end; put_string: 14 named, 15 by
   address, 4 related, 8 released lemma(s), delivery: 2 named and 21 name(s) holding it, 6 UNRELEASED file(s) in the
   lemma index, 0 UNRELEASED hit(s) on live working heads`; census-1 sweep 18:01Z: 0 hits; second-agent check: CONFIRM).
   Every image fact of the walk is discharged by PutStringB_Wit.v's witnesses (cited by name below); the premises
   left are the CALLEE TEXTS, each at every float state, each with its owner:
   - put: the batch kit's tput_specX (lane PutB's walk);
   - __asan_stack_malloc_0: YGcallMxmn.astack_malloc_realizes_xm .. 0 (owner R4);
   - __asan_memcpy: YGcallMxmn.aintrin_realizes_xm .. OCpy (owner R2);
   - __wrap_snprintf: the row's TEXT YGcallSnp.asnprintf_realizes_xrom at the escape family YGcallSnpCk.FF_esc, at
     SOME instance parameters (K, the window Kp, the format band lo / hi, the canary cells, the image range, the
     read-only ranges) with K <= Kp and the ONE condition the walk reads of them, PutStringB_E.ps_snp_inst (owner:
     the row's instance owner). ps_snp_inst is SATISFIED at the owner's B' values
     (PutStringB_SnpWit.ps_snp_inst_B), and PutStringB_SnpWit.put_string_holds_B_owner states this theorem with the
     snprintf premise reduced to the owner's row text at those values.
   __wrap_strlen is NOT a premise: its row is PROVED at ARcfx (lib/AU/PSstrRo.v ps_strlen_xrom_xs_B,
   PutStringB_Wit.psw_strlen). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn YGcallSnp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallSnpCk.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PutStringB_E PutStringB PutStringB_Wit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
Import ListNotations.
Local Open Scope Z_scope.

Section i. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {ci : CfImg}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance PRH_Base.prh_room_live_a8.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Abbreviation RLO := (@pa_relro_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation RHI := (@pa_relro_hi _ B_prog_listing PI_prog_B).
#[local] Abbreviation ARcfx := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

Theorem put_string_holds_B : forall (CTX0 : list (list Z)),
  (* put: the #102 tput_specX at the instance (PutB.v's walk) *)
  (forall fz : YK11.FPState, tput_specX (fx := fz) (ci := CfImgB.CfImg_B) (cp := CP) (PI := prh_img_B)
     (RL := PRH_Base.prh_room_live_a8) (L := B_prog_listing) (PA := PI_prog_B) TB ARcfx SK CTX0) ->
  (* __asan_stack_malloc_0 (owner R4) *)
  (forall fz : YK11.FPState, astack_malloc_realizes_xm (fx := fz) SEGS TB ARcfx 0) ->
  (* __asan_memcpy (owner R2) *)
  (forall fz : YK11.FPState, aintrin_realizes_xm (fx := fz) SEGS TB ARcfx OCpy (SIGMA AS___asan_memcpy)) ->
  (* __wrap_snprintf's row text at its instance parameters *)
  (exists (K Kp lo hi gcan can img_lo img_hi : Z) (cr : list (Z * Z)),
     K <= Kp /\ PutStringB_E.ps_snp_inst (PA := PI_prog_B) TB ARcfx Kp lo hi gcan can img_lo img_hi cr /\
     forall fz : YK11.FPState, asnprintf_realizes_xrom (fx := fz) SEGS TB ARcfx RLO RHI (YGcallSnpCk.FF_esc lo hi) K
       gcan can img_lo img_hi cr (SIGMA AS___wrap_snprintf)) ->
  forall fe : YK11.FPState,
  tput_string_specX (fx := fe) (ci := CfImgB.CfImg_B) (cp := CP) (PI := prh_img_B) (RL := PRH_Base.prh_room_live_a8)
    (L := B_prog_listing) (PA := PI_prog_B) TB ARcfx SK CTX0.
Proof.
intros CTX0 PUT ASM0 AMCPY (K & Kp & lo & hi & gcan & can & img_lo & img_hi & cr & HKK & HSNPI & ASNP) fe.
exact (@PutStringB.put_string_holds rc CfImgB.CfImg_B CP SK PRH_Base.prh_room_live_a8 PI_prog_B TB ARcfx
  PutStringB_Wit.psw_laws PutStringB_Wit.psw_tl PutStringB_Wit.psw_hent PutStringB_Wit.psw_huar
  PutStringB_Wit.psw_hobj PutStringB_Wit.psw_hobjd PutStringB_Wit.psw_huarc PutStringB_Wit.psw_segs_low
  PutStringB_Wit.psw_errno_low PutStringB_Wit.psw_ownlow PutStringB_Wit.psw_smx PutStringB_Wit.psw_hsm0
  PutStringB_Wit.psw_hw PutStringB_Wit.psw_aso PutStringB_Wit.psw_himgsh PutStringB_Wit.psw_fhull
  PutStringB_Wit.psw_hpab PutStringB_Wit.psw_pst_ok PutStringB_Wit.psw_hpstro
  PutStringB_Wit.psw_hlit18 PutStringB_Wit.psw_hlit85 PutStringB_Wit.psw_hlit87 PutStringB_Wit.psw_hlit91
  PutStringB_Wit.psw_hlit93 PutStringB_Wit.psw_hlit89
  PutStringB_Wit.psw_asfx PutStringB_Wit.psw_fflx PutStringB_Wit.psw_sfx PutStringB_Wit.psw_fprx
  CTX0 PUT ASM0 AMCPY (fun fz => @PutStringB_Wit.psw_strlen fz rc)
  K Kp lo hi gcan can img_lo img_hi cr HKK HSNPI ASNP fe).
Qed.
End i.

(* the statement as the kernel holds it, implicit arguments shown (the brief's check: the class position of
   tput_string_specX holds the theorem's float binder fe, and each callee text its own binder fz) *)
Set Printing Implicit.
Unset Printing Notations.
Set Printing Width 200.
Check put_string_holds_B.
Print tput_string_specX.
Print PutStringB_Base.ps_pre.
Print PutStringB_Base.ps_common.
Print PutStringB_Base.ps_commonR.
Print PutStringB_Base.ps_head.
Print PutStringB_Base.ps_next.
Print PutStringB_Base.ps_esc.
Print PutStringB_Base.ps_tail.
Print PutStringB_Base.ps_Qfin.
Print PutStringB_Base.ps_Qin.
Print PutStringB_Base.psK_head.
Print PutStringB_Base.psK_next.
Print PutStringB_Base.psK_esc.
Print PutStringB_Base.psK_tail.
Print PutStringB_Base.psK_headR.
Print PutStringB_Base.psK_nextR.
Print PutStringB_Base.psK_escR.
Print PutStringB_Base.psK_tailR.
Print PutStringB_E.pe_wrt.
Print PutStringB_E.ps_snp_inst.
Unset Printing Implicit.
Set Printing Notations.
Print Assumptions put_string_holds_B.
Print Assumptions PutStringB.put_string_holds.
