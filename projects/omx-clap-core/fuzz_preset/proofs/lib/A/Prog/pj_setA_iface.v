(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset, image A' (asan, pin 1be0f53d96cb, unstripped twin
   bff8519bbe3e): pj_set's A' result AT THE INTERFACE INSTANCE, the relation the A' composition uses
   (PresetCfnA.iface_ARx, lib/A/PresetCfnA.v: ARcf at CfParams_preset /\ xs_placed_cf, over the listing's segments).
   tpj_set_specX_A_preset_iface: tpj_set_specX (lib/A/PRH_FnPj.v) at CfParams_preset, prh_img_A, A_prog_listing,
   PI_prog_A, AD2l.TfibB and ARx := iface_ARx, for every CTX0 and dd; the callee premises pjsA_texts (the six callee
   texts, pj_setA_defs.v) at the same ARx. DERIVED from the ARx-generic walk theorem the ARcf top
   tpj_set_specX_A_preset instantiates (pj_setA_top.v tpj_set_specX_A_holds), so no transfer between relations is
   needed; its Section hypotheses at iface_ARx:
   - LAWS: YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf;
   - VIS: pj_setA_vis_inst.v pjsA_g_vis_preset (at ARcf) through the first conjunct, in each of its three clauses (each
     reads ARx only as a premise);
   - PAL: PALibA.palib_A (independent of ARx);
   - HULL: pj_setA_top.v pjsA_g_hull_preset (a fact of CfParams_preset only, independent of ARx).
   A separate leaf so that the walk's own files and closure do not Require the interface.
   pjsA_texts_of_callees assembles pjsA_texts at iface_ARx for every float state from the four callee texts (get, free,
   grow, strdup) in the shapes of lib/A/Prog/Crt102TopInstA.v's Section hypotheses; its two intrinsic rows are cited
   here (__asan_memset: Cno102A_Mset.cn_memset_A; __asan_memcpy: PRowCpy.prow_asan_memcpy_xm_A).
   tpj_set_specX_A_of_callees composes the two, so the composition's PJSET is one application.
   No numeral. proves no function (kind: instance of the walk at another allocator relation). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0dcf YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj PRH_FnReader PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PALibA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import pj_setA_defs pj_setA_vis_inst pj_setA_top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetCfnA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AB1v PRowCpy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Cno102A_Mset.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_A.

Section iface. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := AD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
(* the interface's relation (lib/A/PresetCfnA.v iface_ARx) at the A' listing *)
#[local] Abbreviation ARi := (PresetCfnA.iface_ARx (L := A_prog_listing) (PA := PI_prog_A) TB).

(* LAWS at iface_ARx: the cf laws, kept by the conjunction with xs_placed_cf (YGcallcf.AR_laws_x_xs) *)
Lemma pjsA_set_wit_laws_iface : AR_laws_x SEGS TB ARi (@cf_head CP).
Proof.
unfold PresetCfnA.iface_ARx.
exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)).
Qed.

(* VIS at iface_ARx: pjsA_g_vis_preset's three clauses through the first conjunct *)
Lemma pjsA_g_vis_iface : pjsA_g_vis (rc := rc) TB ARi.
Proof.
pose proof (pjsA_g_vis_preset (rc := rc)) as V. unfold pjsA_g_vis in V |- *. destruct V as (V1 & V2 & V3).
split; [|split].
- intros ly S Hp W mem md cid pos [HA _] Hin. exact (V1 ly S Hp W mem md cid pos HA Hin).
- intros ly S Hp W mem md a n [HA _] Hz Hn. exact (V2 ly S Hp W mem md a n HA Hz Hn).
- intros ly S Hp W mem md a [HA _] Ha. exact (V3 ly S Hp W mem md a HA Ha).
Qed.

(* tpj_set_specX at the interface instance *)
Theorem tpj_set_specX_A_preset_iface : forall CTX0 dd,
  pjsA_texts (fx := fx) (cp := CP) (SK := SK) TB ARi CTX0 dd ->
  tpj_set_specX (fx := fx) (cp := CP) (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) TB ARi SK CTX0 dd.
Proof.
intros CTX0 dd TXT.
exact (tpj_set_specX_A_holds (fx := fx) (cp := CP) TB ARi pjsA_set_wit_laws_iface pjsA_g_vis_iface PALibA.palib_A
  pjsA_g_hull_preset CTX0 dd TXT).
Qed.

(* the __asan_memset row at iface_ARx, every float state: PRowSet's row by Cno102A_Mset.cn_memset_A *)
Lemma pjsA_memset_iface : forall fxk : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fxk) SEGS TB ARi OSet (pa_sigma AS___asan_memset).
Proof.
exact (Cno102A_Mset.cn_memset_A (cp := CP) TB ARi pjsA_set_wit_laws_iface (proj2 AD2l.TfibB_pair)).
Qed.

(* the __asan_memcpy row at iface_ARx, every float state: PRowCpy.prow_asan_memcpy_xm_A, its entry read through
   TfibSyms (as Cno102A_TopA.v's cn_memcpy_A_inst) *)
Lemma pjsA_memcpy_iface : forall fxk : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fxk) SEGS TB ARi OCpy (pa_sigma AS___asan_memcpy).
Proof.
intros fxk.
change (@pa_sigma _ A_prog_listing PI_prog_A AS___asan_memcpy) with (pc_asan_memcpy (as_code TB)).
change SEGS with AB1v.tfibsegs.
exact (PRowCpy.prow_asan_memcpy_xm_A (fx := fxk) TB ARi (@cf_head CP) pjsA_set_wit_laws_iface (proj2 AD2l.TfibB_pair)).
Qed.

(* the callee texts below take CfParams_preset and prh_img_A by instance, as pjsA_texts does *)
#[local] Existing Instance CfParamsPreset.CfParams_preset.

(* pjsA_texts at iface_ARx from the four callee texts at every float state, in the shapes of the composition's Section
   hypotheses (lib/A/Prog/Crt102TopInstA.v: PJFREE is the free text; get, grow and strdup are the callees' tops); the two
   intrinsic rows are discharged above *)
Lemma pjsA_texts_of_callees : forall CTX0 dd,
  (forall fxk : YK11.FPState, tpj_get_specX (fx := fxk) (PA := PI_prog_A) TB ARi SK) ->
  (forall fxk : YK11.FPState,
     tpj_free_specX (fx := fxk) (PA := PI_prog_A) TB ARi SK CTX0 dd) ->
  (forall fxk : YK11.FPState,
     tgrow_specX (fx := fxk) (PA := PI_prog_A) TB ARi SK CTX0) ->
  (forall fxk : YK11.FPState,
     tfuzz_strdup_specX (fx := fxk) (PA := PI_prog_A) TB ARi SK) ->
  forall fxk : YK11.FPState, pjsA_texts (fx := fxk) (cp := CP) (SK := SK) TB ARi CTX0 dd.
Proof.
intros CTX0 dd GET FREE GROW STRDUP fxk.
unfold pjsA_texts.
exact (conj (GET fxk) (conj (FREE fxk) (conj (GROW fxk) (conj (STRDUP fxk)
  (conj (pjsA_memcpy_iface fxk) (pjsA_memset_iface fxk)))))).
Qed.

(* tpj_set_specX at iface_ARx, every float state, from the four callee texts: the composition's PJSET in one step *)
Corollary tpj_set_specX_A_of_callees : forall CTX0 dd,
  (forall fxk : YK11.FPState, tpj_get_specX (fx := fxk) (PA := PI_prog_A) TB ARi SK) ->
  (forall fxk : YK11.FPState,
     tpj_free_specX (fx := fxk) (PA := PI_prog_A) TB ARi SK CTX0 dd) ->
  (forall fxk : YK11.FPState,
     tgrow_specX (fx := fxk) (PA := PI_prog_A) TB ARi SK CTX0) ->
  (forall fxk : YK11.FPState,
     tfuzz_strdup_specX (fx := fxk) (PA := PI_prog_A) TB ARi SK) ->
  forall fxk : YK11.FPState,
  tpj_set_specX (fx := fxk) (cp := CP) (PI := prh_img_A) (L := A_prog_listing) (PA := PI_prog_A) TB ARi SK CTX0 dd.
Proof.
intros CTX0 dd GET FREE GROW STRDUP fxk.
exact (tpj_set_specX_A_holds (fx := fxk) (cp := CP) TB ARi pjsA_set_wit_laws_iface pjsA_g_vis_iface PALibA.palib_A
  pjsA_g_hull_preset CTX0 dd (pjsA_texts_of_callees CTX0 dd GET FREE GROW STRDUP fxk)).
Qed.
End iface.
