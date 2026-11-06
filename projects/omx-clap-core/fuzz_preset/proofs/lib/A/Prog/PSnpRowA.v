(* Theorem Labs, 2026-10: fuzz_preset image A' (#102 asan pin 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4), the
   __wrap_snprintf ROW AT THE A' DRIVER'S INSTANCE: the engine's text
   YGcallSnp.asnprintf_realizes_xrom, stated verbatim as the A' driver's third composed top's own lemma
   drv3_snprintf_A (lib/A/Prog/Ent102DrvTopA3.v, under its put_string_holds' SNP header comment):
   segs := pa_segs of PI_prog_A,
   B := AD2l.TfibB, ARx := PresetCfnA.iface_ARx (ARcf /\ xs_placed_cf at CfParams_preset), the
   relro range [pa_relro_lo, pa_relro_hi), the format family FF_esc IMG_LO A_GOT_STACK_CHK_GUARD, the window
   PRH_Base.STK_RT_PRINTF, the canary chain AImgCells.A_GOT_STACK_CHK_GUARD -> AImgCells.A_STACK_CHK_GUARD, the image
   range [IMG_LO, IMG_TOP), cr := PRW_put_string_e.ps_snp_cr (Required, so the statement is drv3_snprintf_A's text),
   pc := pa_sigma AS___wrap_snprintf; rc and fx are bound.
   rule 24: no function proved (kind: instantiation of an existing Qed root, PSnpSnpRoot.snprintf_xrom_A
   (lib/A/PSnpSnpRoot.v), at a concrete instance; no new walk).
   The root's Section items, each supplied at the instance (none is left a premise):
   - LAWS := YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (YG0lawscf.v:22), at cf_head;
   - TB := AD2l.TfibB_syms (lib/A/AD2l.v:73);
   - alx_band_pres := YCbqG.alx_band_pres (AR_laws_x's field 20) of LAWS;
   - W_H8 := the world's field YA0n.w_H8 (YA0n.v:25).
   The root's five side conditions are closed comparisons of the instance's bounds, decided by vm_compute. Its
   conclusion is the row by conversion only: pa_segs of PI_prog_A is Img0.rsegs (PAImg_prog.v:406, Img0.v:3), the
   loaded segments AB1v.tfibsegs is (AB1v.v:12); FF_preset_x and FF_esc have the same body (PSnpPfFam.v:75-76 and
   :95-99, YGcallSnpCk.v:112-118); AE2p's canary cells are AImgCells' computed (AE2p.v:33-34); PSnpPcom.PCM_CR
   (PSnpPcom.v:83-84) is ps_snp_cr's map / filter (PRW_put_string_e.ps_snp_cr) over the same segments; and
   PSnpI.PC_snprintf (PSnpI.v:71) is pa_sigma AS___wrap_snprintf (PAImg_prog.v:81).
   Numerals: none typed. No image ADDRESS is typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require
YK11 YM05 YA0n YCbqG YC4aP YPsym YImgTop YGcallSnp YGcallSnpCk YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require
CfImgA CfParamsPreset AD2l AImgCells Listing_prog PAImg_prog PresetCfnA PRH_Base PSnpSnpRoot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_put_string_e.
Local Open Scope Z_scope.

#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation SEGS rc := (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc)).
#[local] Abbreviation RLO rc := (@YC4aP.pa_relro_lo rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc)).
#[local] Abbreviation RHI rc := (@YC4aP.pa_relro_hi rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc)).
#[local] Abbreviation ARi rc :=
  (@PresetCfnA.iface_ARx rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB).
(* the driver's image instance (lib/A/PresetD2pAPf.v: ci := CfImg_A), as Ent102DrvTopA3.v declares it, so the
   callee texts below elaborate at it *)
#[local] Existing Instance CfImgA.CfImg_A.

(* THE ROW AT THE INSTANCE (Ent102DrvTopA3.v's drv3_snprintf_A, verbatim) *)
Theorem snprintf_row_A_inst : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  @YGcallSnp.asnprintf_realizes_xrom fx (@YC4aP.pa_segs rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc)) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB) (@YC4aP.pa_relro_lo rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc))
    (@YC4aP.pa_relro_hi rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc)) (YGcallSnpCk.FF_esc YImgTop.IMG_LO AImgCells.A_GOT_STACK_CHK_GUARD) PRH_Base.STK_RT_PRINTF
    AImgCells.A_GOT_STACK_CHK_GUARD AImgCells.A_STACK_CHK_GUARD YImgTop.IMG_LO YImgTop.IMG_TOP (@PRW_put_string_e.ps_snp_cr rc (@PAImg_prog.PI_prog_A rc))
    (@YC4aP.pa_sigma rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) YPsym.AS___wrap_snprintf).
Proof.
intros rc fx.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) (SEGS rc) TA (YG0lawscf.AR_laws_ok_cf (cp := CP) (SEGS rc) TA)) as LAWS.
(* the root takes W_H8 (closed by the world's w_H8 field) on trees before its discharge, and does not after it: one
   file for both *)
first
[ pose proof (PSnpSnpRoot.snprintf_xrom_A (fx := fx) TA (ARi rc) LAWS AD2l.TfibB_syms (YCbqG.alx_band_pres _ _ _ LAWS)
    (fun W a H => YA0n.w_H8 W a H) (RLO rc) (RHI rc) YImgTop.IMG_LO AImgCells.A_GOT_STACK_CHK_GUARD
    PRH_Base.STK_RT_PRINTF YImgTop.IMG_LO YImgTop.IMG_TOP) as R
| pose proof (PSnpSnpRoot.snprintf_xrom_A (fx := fx) TA (ARi rc) LAWS AD2l.TfibB_syms (YCbqG.alx_band_pres _ _ _ LAWS)
    (RLO rc) (RHI rc) YImgTop.IMG_LO AImgCells.A_GOT_STACK_CHK_GUARD
    PRH_Base.STK_RT_PRINTF YImgTop.IMG_LO YImgTop.IMG_TOP) as R ].
refine (R _ _ _ _ _); apply Z.leb_le; vm_compute; reflexivity.
Qed.
