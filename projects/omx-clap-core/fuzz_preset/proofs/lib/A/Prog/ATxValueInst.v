(* fuzz_preset, image A' (asan, #102 pin 1be0f53d96cb): tx_value's text AT THE CRT INSTANCE. rule 24: proves no
   function (kind: instance corollary of ATxValue.tx_value_A_holds, the walk of tx_value at image A').
   THE STATEMENT of tx_value_A_inst is the body of the crt corollary's carried premise H_txt_tx_value_A
   (lib/A/Prog/Crt102TopInstA.v, Section i, Context {rc}), verbatim: ttx_value_specX at every float state fxk, at
   ci := CfImg_A, cp := CfParams_preset, PI := PresetCfnA.preset_prh_img, RL := prh_room_live_a8, PA := PI_prog_A rc,
   B := AD2l.TfibB, ARx := PresetCfnA.iface_ARx at CfImg_A, SK := PresetCfnA.preset_sink_head,
   CTX0 := PresetCfnA.iface_ctx0, depth bound n := PRH_Base.DOC_D. So the driver (Ent102DrvTopA3.v) can cite it as
   `fun fxk => @tx_value_A_inst rc fxk` in that premise's place.
   DISCHARGED (the Section hypotheses of tx_value_A_holds), each by a cited Qed lemma at the instance:
     LAWS YGcallcf.AR_laws_x_xs over YG0lawscf.AR_laws_ok_cf; PAL PALibA.palib_A; tv_jt_own ATxValue.tv_jt_own_TfibB;
     ASx PSstrRo.ps_strlen_xrom_xs_A (its pc is the listing's __wrap_strlen: txvi_strlen_pc, by computation);
     zs_aligned ATxLine.tl_zs_aligned_TfibB; img_shadow_vis_x AImgShadowVisCf.img_shadow_vis_xs_A; tv_img_cf_box
     ATxLine.tl_img_cf_box_A; tl_lit_img ATxLine.tl_lit_img_TfibB; tv_lit_img ATxValue.tv_lit_img_TfibB;
     TXPUT TxPut102A_Inst.tx_put_holds_A, with TB AD2l.TfibB_syms, AI PRowCpy.prow_asan_memcpy_xm_A at ARcf (laws
     YGcallcf.AR_laws_x_cf; its pc is the listing's __asan_memcpy by computation), AREAL
     AllocAssembleA.arealloc_realizes_cf_A and AREALN AllocAssembleA.arealloc_null_realizes_cf_A (premise-free).
     These are the crt corollary's own discharges of the same rows (its cti_laws, cti_strlen, cti_amcpy_cf,
     cti_areal, cti_arealn, cti_txput), restated here so this file does not Require the corollary.
     TXSTR ATxString.tx_string_A_inst (lib/A/Prog/ATxString.v, the image-A' walk of tx_string at this instance), at
     its one premise, tx_put's text at the instance, which is txvi_txput below.
   Nothing is carried: tx_value_A_inst has no premise.
   Numerals: none of its own. No ADDRESS: every address is pa_sigma of PAImg_prog.v or a CfImg / asyms field. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcallcf YG0lawscf YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep YGcfReallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnTx PresetCfnA AB1v AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PALibA PSstrRo PRowCpy AImgShadowVisCf AllocAssembleA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require ATxLine ATxValue TxPut102A_Inst ATxString.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.

(* the strlen trampoline and the memcpy interceptor of the instance are the listing's __wrap_strlen and __asan_memcpy
   (closed computations) *)
Lemma txvi_strlen_pc : A_prog_sigma AS___wrap_strlen = @cf_pc_strlen CfImg_A.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {rc : YM05.RunCeil}.
#[local] Existing Instance CfImg_A.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_A.
#[local] Existing Instance PRH_Base.prh_room_live_a8.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation SEGS := (@pa_segs rc A_prog_listing (@PI_prog_A rc)).
#[local] Notation SIGMA := (@pa_sigma rc A_prog_listing (@PI_prog_A rc)).
#[local] Notation RLO := (@pa_relro_lo rc A_prog_listing (@PI_prog_A rc)).
#[local] Notation RHI := (@pa_relro_hi rc A_prog_listing (@PI_prog_A rc)).
#[local] Notation TA := AD2l.TfibB.
#[local] Notation CP := CfParams_preset.
#[local] Notation RLA := (@PRH_Base.prh_room_live_a8 CfParams_preset).
#[local] Notation ARI := (@PresetCfnA.iface_ARx rc A_prog_listing (@PI_prog_A rc) CfImg_A AD2l.TfibB).
#[local] Notation SKA := PresetCfnA.preset_sink_head.
#[local] Notation PIA := PresetCfnA.preset_prh_img.
#[local] Notation CTXA := PresetCfnA.iface_ctx0.

(* ---- the discharges, each at the instance ---- *)
Lemma txvi_laws : AR_laws_x SEGS TA ARI cf_head.
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TA (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TA)). Qed.

Lemma txvi_strlen : forall fxq : YK11.FPState,
  @YGcallMxmn.astrlen_realizes_xrom fxq SEGS TA ARI RLO RHI (SIGMA AS___wrap_strlen).
Proof.
intros fxq.
change (SIGMA AS___wrap_strlen) with (A_prog_sigma AS___wrap_strlen). rewrite txvi_strlen_pc.
change SEGS with AB1v.tfibsegs.
exact (PSstrRo.ps_strlen_xrom_xs_A (fx := fxq) (rc := rc) (cp := CP) TA AD2l.TfibB_syms RLO RHI).
Qed.

Lemma txvi_amcpy_cf : forall fy : YK11.FPState,
  YGcallMxmn.aintrin_realizes_xm (fx := fy) SEGS TA
    (fun ly S Hp W mem md => YG0ncf.ARcf (cp := CP) SEGS TA ly S Hp W mem md) OCpy (SIGMA AS___asan_memcpy).
Proof.
intros fy. assert (E : SIGMA AS___asan_memcpy = pc_asan_memcpy (as_code TA)) by (vm_compute; reflexivity).
rewrite E.
exact (PRowCpy.prow_asan_memcpy_xm_A (fx := fy) TA _ _
  (YGcallcf.AR_laws_x_cf (cp := CP) SEGS TA (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TA)) AD2l.TfibB_syms).
Qed.

Lemma txvi_txput : forall fxk : YK11.FPState,
  @PRH_FnTx.ttx_put_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA.
Proof.
intros fxk.
exact (TxPut102A_Inst.tx_put_holds_A (fx := fxk) (rc := rc) TA SKA CTXA AD2l.TfibB_syms (txvi_amcpy_cf fxk)
  (AllocAssembleA.arealloc_realizes_cf_A rc fxk) (AllocAssembleA.arealloc_null_realizes_cf_A rc fxk)).
Qed.

(* tx_string's text at the instance, every float state: ATxString.tx_string_A_inst at tx_put's text txvi_txput *)
Lemma txvi_txstr : forall fxk : YK11.FPState,
  @PRH_FnTx.ttx_string_specX fxk rc CfImg_A CP PIA RLA A_prog_listing PA TA ARI SKA CTXA.
Proof. exact (@ATxString.tx_string_A_inst rc txvi_txput). Qed.

Lemma txvi_isv : forall ly S Hp W mem md a, ARI ly S Hp W mem md -> @cf_img_lo CfImg_A <= a < @cf_img_top CfImg_A ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
Proof. exact (AImgShadowVisCf.img_shadow_vis_xs_A (rc := rc) (cp := CP) SEGS TA AD2l.TfibB_syms). Qed.

(* ---- THE TEXT AT THE INSTANCE (Crt102TopInstA.v's H_txt_tx_value_A, verbatim) ---- *)
Theorem tx_value_A_inst : forall fxk : YK11.FPState,
  @PRH_FnTx.ttx_value_specX fxk rc CfImg_A CfParams_preset PresetCfnA.preset_prh_img
    (@PRH_Base.prh_room_live_a8 CfParams_preset)
    A_prog_listing (@PAImg_prog.PI_prog_A rc) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImg_A AD2l.TfibB)
    PresetCfnA.preset_sink_head PresetCfnA.iface_ctx0 PRH_Base.DOC_D.
Proof.
intros fxk.
eapply (ATxValue.tx_value_A_holds (fx := fxk) (rc := rc) (ci := CfImg_A) (RL := RLA) (SK := SKA) TA ARI).
all: first
  [ exact txvi_laws
  | exact (PALibA.palib_A (rc := rc))
  | exact PALibA.palib_A
  | exact (ATxValue.tv_jt_own_TfibB (rc := rc))
  | exact ATxValue.tv_jt_own_TfibB
  | exact (txvi_strlen fxk)
  | exact (txvi_txput fxk)
  | exact (txvi_txstr fxk)
  | exact ATxLine.tl_zs_aligned_TfibB
  | exact txvi_isv
  | exact (ATxLine.tl_img_cf_box_A (rc := rc))
  | exact ATxLine.tl_img_cf_box_A
  | exact (ATxLine.tl_lit_img_TfibB (rc := rc))
  | exact ATxLine.tl_lit_img_TfibB
  | exact (ATxValue.tv_lit_img_TfibB (rc := rc))
  | exact ATxValue.tv_lit_img_TfibB ].
Qed.
End i.

Print Assumptions tx_value_A_inst.
Set Printing Implicit.
About tx_value_A_inst.
Unset Printing Implicit.
