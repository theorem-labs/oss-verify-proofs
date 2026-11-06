(* Theorem Labs, 2026-10-30: omx-clap-core/fuzz_preset, image B' (asan-ubsan, #102 pin B' d663f82d7f48, unstripped twin
   c90d4fa54d43): pj_free's B' result AT THE INTERFACE INSTANCE, for the B' halts top, whose slot field
   PresetCfnB.pcc_pj_free states the kit's tpj_free_specX at ARx := PresetCfnB.iface_ARx (lib/AU/PresetCfnB.v:965:
   ARcf at CfParams_preset /\ xs_placed_cf, over the listing's segments).
   tpj_free_specX_B_preset_iface: the kit's tpj_free_specX (lib/A/PRH_FnPj.v) at CfParams_preset, prh_img_B,
   B_prog_listing, PI_prog_B, YD2l.TfibB and ARx := iface_ARx, for every CTX0 and depth n; the callee premises are
   the kit's fuzz_free text and __asan_memset's m-form, at the same ARx (the form the B' fuzz_free walk proves:
   FuzzFreeB.fuzz_free_holds_B at its ARcfx, the same relation). DERIVED from the same walk theorem the ARcf top
   tpj_free_specX_B_preset instantiates (pj_free_top.v tpj_free_specX_B, generic in ARx), so no transfer between
   relations is needed: its three Section hypotheses at iface_ARx are
   - LAWS: YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (the conjunction keeps the cf laws; the discharge
     CheckBoundedAllocBInst.v's check_bounded_alloc_holds_B_inst_xs uses at the same relation);
   - VISF: YGcfFsVis.ARx_frame_hull_vis_cf_ok at ARcf, through the first conjunct (ARx_frame_hull_vis reads ARx
     only as a premise);
   - PAL: pj_free_top.v's pf_wit_pal (independent of ARx).
   A separate leaf so that the walk's own files and closure stay as landed; this file alone Requires the interface.
   Both of the kit's texts here are the restated ones (the re-hiding move: each concludes SRr' SEGS RZ_cf, YA0nH.v, with its post
   at wle' SEGS RZ_cf; the kit's hull budget at entry and hull use in the post): the premise and the conclusion keep the kit's
   names, so this pass-through proof is unchanged, and the hull is threaded inside the walk by PjFreeCommon.v.
   No numeral. rule 24: proves no function (kind: instance of an existing walk at another allocator relation). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0dcf YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YD2l YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import pj_free_top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetCfnB.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

Section iface. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
(* the interface's relation (lib/AU/PresetCfnB.v iface_ARx) at the B' listing *)
#[local] Abbreviation ARi := (PresetCfnB.iface_ARx (L := B_prog_listing) (PA := PI_prog_B) TB).

(* LAWS at iface_ARx: the cf laws, kept by the conjunction with xs_placed_cf (YGcallcf.AR_laws_x_xs) *)
Lemma pf_wit_laws_iface : AR_laws_x SEGS TB ARi (@cf_head CP).
Proof.
unfold PresetCfnB.iface_ARx.
exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)).
Qed.

(* VISF at iface_ARx: the cf instance's frame-hull visibility through the first conjunct *)
Lemma pf_wit_visf_iface : ARx_frame_hull_vis SEGS TB ARi.
Proof.
intros ly S Hp W mem md cid pos [HA _] Hin.
exact (ARx_frame_hull_vis_cf_ok SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB) ly S Hp W mem md cid pos HA Hin).
Qed.

(* The kit's tpj_free_specX at the interface instance, every depth *)
Theorem tpj_free_specX_B_preset_iface :
  PRH_FnAlloc.tfuzz_free_specX (cp := CP) (PA := PI_prog_B) TB ARi SK ->
  YGcallMxmn.aintrin_realizes_xm SEGS TB ARi OSet (@pa_sigma _ B_prog_listing PI_prog_B AS___asan_memset) ->
  forall CTX0 n, tpj_free_specX (cp := CP) (PA := PI_prog_B) TB ARi SK CTX0 n.
Proof.
intros XFF XMS.
exact (tpj_free_specX_B (cp := CP) TB ARi pf_wit_laws_iface pf_wit_visf_iface pf_wit_pal XFF XMS).
Qed.
End iface.
