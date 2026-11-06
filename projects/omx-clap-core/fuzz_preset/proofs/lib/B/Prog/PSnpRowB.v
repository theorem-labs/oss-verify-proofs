(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (#102 asan-ubsan pin d663f82d7f488d30, twin c90d4fa54d43160b), the
   __wrap_snprintf ROW AT PUT_STRING B''s INSTANCE: the engine's text
   YGcallSnp.asnprintf_realizes_xrom at the values PutStringB_SnpWit.put_string_holds_B_owner's snprintf premise
   names (PutStringB_SnpWit.v:194-197): segs := the instance's segments, B := YD2l.TfibB, ARx := ARcfx = ARcf /\
   xs_placed_cf (cp := CfParamsPreset.CfParams_preset), the relro range [pa_relro_lo, pa_relro_hi), the format band
   [pa_lo, the stack guard's GOT cell YE22.A_GOT_CANARY), the canary chain YE22.A_GOT_CANARY -> YE22.V_GOT_CANARY, the
   image range [pa_lo, pa_hi), cr := every non-writable segment (snr_cr below: PutStringB_SnpWit.psn_cr's body, :74-75,
   restated because this file Requires no PutStringB file), pc := pa_sigma AS___wrap_snprintf, any K at or above the
   root's window.
   rule 24: no function proved (kind: instantiation of an existing Qed root, PSnpSnpRoot.snprintf_xrom_B, at a
   concrete instance; no new walk).
   The root's Section items, each supplied at the instance (none is left a premise):
   - LAWS := YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (YG0lawscf.v:22), at cf_head (the
     term PutStringB_Wit.psw_laws, PutStringB_Wit.v:313-314, is);
   - TB := YD2l.TfibB_syms (YD2l.v:71);
   - alx_band_pres := YCbqG.alx_band_pres (AR_laws_x's field 20, its law ARx_band_pres_law) of LAWS;
   - W_H8 := the world's field YA0n.w_H8 (YA0n.v:25).
   The root's five side conditions are closed comparisons of the instance's bounds, decided by vm_compute. Its
   conclusion is the row by conversion only: the segments are YB1v.tfibsegs (PutStringB_SnpWit.psn_segs), FF_preset_x
   and FF_esc have the same body (PSnpPfFam.v:95-99, YGcallSnpCk.v:112-118), YE2p's canary cells are YE22's (both
   generated constants), PSnpPcom.PCM_CR is snr_cr's map / filter over the same segments, and PSnpI.PC_snprintf is
   pa_sigma AS___wrap_snprintf (PAImg_prog.v:81).
   Numerals: 8160 (LENGTH: the root's window, PSnpSnpRoot.snprintf_xrom_B's 8160 <= K). No image ADDRESS is typed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK04 YA0n YM05 YG0f YCbqG YC4aP YPsym YGcallSnp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require
YB1v YE22 YE2p YD2l YF0m YG0ncf YGcallcf YG0lawscf YGcallSnpCk PSnpPfFam.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSnpI PSnpPcom PSnpSnpRoot.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From Stdlib Require Import List Bool.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {rc : YM05.RunCeil}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Abbreviation RLO := (@pa_relro_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation RHI := (@pa_relro_hi _ B_prog_listing PI_prog_B).
#[local] Abbreviation PLO := (@pa_lo _ B_prog_listing PI_prog_B).
#[local] Abbreviation PHI := (@pa_hi _ B_prog_listing PI_prog_B).
(* image B's CfImg: YG0ncf's cf section now takes {ci : CfImg}, so ARcf below elaborates at the image's own instance,
   as the other B' files declare it (Cno102B_TopInst.v, Caw102B_Img.v) *)
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Abbreviation ARcfx := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) SEGS TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* the owner's cr: every non-writable segment of the image, as (base, size) (PutStringB_SnpWit.psn_cr's body) *)
Definition snr_cr : list (Z * Z) :=
  map (fun sg => (Z.of_N (seg_base sg), Z.of_N (seg_size sg))) (filter (fun sg => negb (seg_writable sg)) SEGS).

(* THE ROW AT THE INSTANCE *)
Theorem snprintf_row_B_inst : forall K, 8160 <= K -> forall fz : YK11.FPState,
  asnprintf_realizes_xrom (fx := fz) SEGS TB ARcfx RLO RHI (YGcallSnpCk.FF_esc PLO YE22.A_GOT_CANARY) K
    YE22.A_GOT_CANARY YE22.V_GOT_CANARY PLO PHI snr_cr (SIGMA AS___wrap_snprintf).
Proof.
intros K HK fz.
pose proof (YGcallcf.AR_laws_x_xs (cp := CP) SEGS TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGS TB)) as LAWS.
(* the root takes W_H8 (closed by the world's w_H8 field) on trees before its discharge, and does not
   after it: one file for both *)
first
[ pose proof (PSnpSnpRoot.snprintf_xrom_B (fx := fz) TB ARcfx LAWS YD2l.TfibB_syms (YCbqG.alx_band_pres _ _ _ LAWS)
    (fun W a H => YA0n.w_H8 W a H) RLO RHI PLO YE22.A_GOT_CANARY K PLO PHI) as R
| pose proof (PSnpSnpRoot.snprintf_xrom_B (fx := fz) TB ARcfx LAWS YD2l.TfibB_syms (YCbqG.alx_band_pres _ _ _ LAWS)
    RLO RHI PLO YE22.A_GOT_CANARY K PLO PHI) as R ].
refine (R _ _ HK _ _); apply Z.leb_le; vm_compute; reflexivity.
Qed.
End c.
