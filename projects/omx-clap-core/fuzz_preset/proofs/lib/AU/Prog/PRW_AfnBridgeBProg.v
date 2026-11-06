(* fuzz_preset, program part, image B' (asan-ubsan, #102 pin d663f82d7f488d30, twin c90d4fa54d43160b): the one
   program-callee entry of LLVMFuzzerTestOneInput that is not the kit's text alone on B': check_reject_clean, from
   its SIGNED B' walk lib/B/Prog/CrcB.v at the interface's ARx, and the image-shadow fact that walk takes, proved at TfibB'.
   rule 24: no function proved (kind: interface adapter).
   AT THE KIT CUT (kit tree preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record)): taken by path
   from lib/AU/Prog/PRW_AfnBridgeBProg.v (sha256 5f0e7a018715; internal record); the proof text is unchanged. The cut's interface is
   lib/AU/PresetCfnB.v da6e0dfbe282 (no-DW) and its texts lib/A/PRH_FnCheck.v c40cf3fdcd2a; tcheck_reject_clean_specX
   takes no data word and no context list, and the cut carries the walk's three files at the blobs below.
   The paragraphs below were written on an earlier kit; their file names hold at the cut.
   WHY THE REST OF THE OLD-PIN BRIDGE IS GONE. The donor (this path, PRW_AfnBridgeBProg.v (sha256 27948a9847d4; internal record),
   image B f8f98a95) adapted each callee's kit text to the old interface's afn_spec_cf over a fn_iface record. On B'
   the interface is lib/AU/PresetCfnB.v (sha256 01db9c743820; internal record) (decision D1 of
   17:34Z): each field of preset_callee_contracts IS the kit's text t<f>_specX, at
   iface_ARx (ARcf /\ xs_placed_cf), prh_room_live_a8, preset_sink_head, iface_ctx0, DOC_D and A_MOD_AT / A_STAMP.
   fn_iface and afn_spec_cf left the slot, so a text-to-afn_spec_cf adapter has no consumer on B' and none is carried.
   A signed walk of a text is cited by the top directly (lib/AU/HaltsClosedB.v).
   WHAT STAYS: check_reject_clean. Its B' walk (its blobs as walked, the same
   in the kit cut: lib/B/Prog/CrcB.v db333f7f606a, CrcBRomRefute.v 4aa5b7e9c24d, CrcBInstLive.v e49be3adb151) is
   cited through its instance check_reject_clean_holds_B_inst_live: the walk at B := TfibB', RL := prh_room_live_a8 and
   ARx := ARcf /\ xs_placed_cf (the interface's iface_ARx, by conversion), with LAWS, FLIVE (FuzzAllocAccInstB102.v's
   fuzz_alloc_live_holds_B_inst), EMPTY_RO (cr_empty_ro: only `empty`'s 56 bytes; the false pal_rom_ok is gone) and
   EMPTY_ZS discharged inside it. Its two premises left: BCMP (the bcmp row in the keep form abcmp_realizes_xm; owner
   Theorem Labs) stays a premise; IMGV (cr_img_shadow_vis_B at ARcf, CfImg_B's bounds) is YGcfAmx2.v's
   img_shadow_vis_cf (ci := CfImg_B) by conversion, PROVED at TfibB' here (img_shadow_vis_cf_TfibB: the cover check of
   YF0m's generated lists, as A's AImgShadowVisCf.v; the B' instance lib/AU/AImgShadowVisCfB.v
   tfib_img_shadow_vis_cf_B states the same at every B with TfibSyms B).
   RELOCATION: the donor's numerals moved by alreloc c4338d099cfb8025: none. This file writes no image numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetCfnB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YD2l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfAmx2 YImgShadowCover YImgShadowCoverCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require CrcB CrcBInstLive.
Import ListNotations.
Local Open Scope Z_scope.

(* ==== 1. the image's shadow at B''s CfImg bounds, at TfibB' (img_shadow_vis_cf, YGcfAmx2.v :47) ==== *)
(* the cover check of YF0m's generated lists at CfImg_B's [cf_img_lo, cf_img_top) (A's AImgShadowVis.v twin) *)
Lemma crB_img_shadow_cover :
  img_shadow_cover YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow (@cf_img_lo CfImg_B) (@cf_img_top CfImg_B) = true.
Proof. vm_compute. reflexivity. Qed.
Section shw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma img_shadow_vis_cf_TfibB : forall segs,
  img_shadow_vis_cf (ci := CfImg_B) (cp := CfParams_preset) segs YD2l.TfibB.
Proof.
intros segs. pose proof YD2l.TfibB_syms as HB.
apply (img_shadow_vis_cf_of_cover (ci := CfImg_B) (cp := CfParams_preset) segs YD2l.TfibB
  YF0m.Tfib_zero_shadow YF0m.Tfib_const_shadow crB_img_shadow_cover).
- rewrite (YF0m.ts_zsh _ HB). apply incl_refl.
- intros ly. rewrite (YF0m.ts_const _ HB ly). unfold YF0m.Tfib_const. apply incl_appr, incl_appr, incl_refl.
Qed.
End shw.

(* ==== 2. the entry ==== *)
Section crw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* image B''s CfImg record (lib/AU/CfImgB.v): ARcf reads ci, and the image-shadow fact above is proved at CfImg_B's
   bounds, so the entry is stated at ci := CfImg_B (the record the halts top takes) *)
#[local] Existing Instance CfImg_B.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PIA := prh_img_B.
#[local] Abbreviation RLX := (@prh_room_live_a8 CfParams_preset).
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Abbreviation SKA := PresetCfnB.preset_sink_head.
(* the interface's ARx (PresetCfnB.v iface_ARx: ARcf /\ xs_placed_cf) at the B' listing and TfibB' *)
#[local] Abbreviation ARi := (PresetCfnB.iface_ARx (L := B_prog_listing) (PA := PI_prog_B) YD2l.TfibB).

(* THE ENTRY: the interface's field pcc_check_reject_clean (PresetCfnB.v preset_callee_contracts) at this float state
   and run ceiling: the B' walk's instance (the header) with its image-shadow premise discharged *)
Theorem pcc_check_reject_clean_of_walk :
  YGcallMxmn.abcmp_realizes_xm SEGS YD2l.TfibB ARi (SIGMA AS___wrap_bcmp) ->
  tcheck_reject_clean_specX (cp := CP) (PI := PIA) (RL := RLX) (PA := PI_prog_B) YD2l.TfibB ARi SKA.
Proof.
intros BCMP.
exact (CrcBInstLive.check_reject_clean_holds_B_inst_live SKA BCMP (img_shadow_vis_cf_TfibB SEGS)).
Qed.
End crw.

Set Printing Implicit. Unset Printing Notations.
About img_shadow_vis_cf_TfibB.
About pcc_check_reject_clean_of_walk.
Print Assumptions img_shadow_vis_cf_TfibB.
Print Assumptions pcc_check_reject_clean_of_walk.
