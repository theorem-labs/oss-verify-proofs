(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aTopClosed.v, with its module paths changed. *)
(* ex_value on image A', CLOSED at the driver's instance: S8aTop.ex_value_A with every one of its Section premises
   discharged by a closed lemma, no hypothesis left.
   rule 24: no function proved here (kind: instance discharge; the walk is S8aTop.ex_value_A).
   The instance (lib/A/Prog/Ent102DrvTopA3.v's driver names, written out): ci := CfImgA.CfImg_A,
   cp := CfParamsPreset.CfParams_preset, RL := PRH_Base.prh_room_live_a8, PI := PresetCfnA.preset_prh_img
   (= PRH_Img.prh_img_A), PA := PI_prog_A, B := AD2l.TfibB, ARx := PresetCfnA.iface_ARx (= ARcf /\ xs_placed_cf,
   S8aTopInst.v's ARx, by unfolding), SK := PresetCfnA.preset_sink_head, at nesting PRH_Base.DOC_D (the driver's) and
   every float state fx.
   The premises, in ex_value_A's binder order, each with the lemma that closes it (S8aTop.v's PREMISE comments, or its
   S8aTopInst.v wrapper where that comment says OPEN or no wrapper yet):
   LAWS YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf; errno_low PALibA.palib_errno_A; OWNLOW
   YGcallcf.ARx_owned_low_law_xs; ASM1 S8aTopInst.s8i_ASM1; SMX YGcallScf.stack_malloc_x_any; TS AD2l.TfibB_syms;
   GOT_SHADOW / GOT_UAR / CELL_SHADOW YC1fP.pal_got_shadow / pal_got_uar / pal_cell of PALibA.palib_A; UAR_CELL
   S8aTopInst.s8i_UAR_CELL; HW CfParamsPreset.preset_head_wide; HIMG / HPST / Htp / Herrno / Hown S8aNumberW.w_himg /
   w_hpst / w_htp / w_herrno / w_hown; HOFFB FuzzFree.ff_blk_off_img; HOFFF S8aTopInst.s8i_HOFFF; HGOTC
   S8aNumberW.w_hgotc; CPY PRowCpy.prow_asan_memcpy_xm_A; CMP PSstrRo.ps_strcmp_xrom_xs_A; BCMP PRowCmp.pr_bcmp_xm_A;
   HBLK32 / HAMEM8 S8aTopInst.s8i_HBLK32 / s8i_HAMEM8; HSHD YG0sshcf.AR_shadow_law_ok_cf; HAM8 S8aTopInst.s8i_HAM8;
   PAL PALibA.palib_A; STRLENm PSstrRo.ps_strlen_xrom_xs_A; ASFX YGcallScf.astack_free_x_xs.
   ex_value_A_inst_drv is the statement again at the driver's local instances, so the driver's hypothesis
   H_txt_ex_value_A is its exact type. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0ncf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallcf YGcallScf YC1fP YG0sshcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx PRH_Img Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l CfImgA CfParamsPreset PresetCfnA PALibA PRowCpy
  PSstrRo PRowCmp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aTop S8aTopInst S8aNumberW FuzzFree.
Import ListNotations.
Local Open Scope Z_scope.

Theorem ex_value_A_inst : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnEx.tex_value_specX (fx := fx) (rc := rc) (cp := CfParamsPreset.CfParams_preset)
    (PI := PresetCfnA.preset_prh_img) (RL := @PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset)
    (L := Listing_prog.A_prog_listing) (PA := @PAImg_prog.PI_prog_A rc) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB)
    PresetCfnA.preset_sink_head PRH_Base.DOC_D.
Proof.
intros rc fx.
pose proof (@PALibA.palib_A rc) as PALA.
refine (@S8aTop.ex_value_A rc (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset) AD2l.TfibB
  (@PresetCfnA.iface_ARx rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB)
  PresetCfnA.preset_sink_head
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRH_Base.DOC_D fx).
(* LAWS *) - eapply YGcallcf.AR_laws_x_xs; eapply YG0lawscf.AR_laws_ok_cf.
(* errno_low *) - exact PALibA.palib_errno_A.
(* OWNLOW *) - eapply YGcallcf.ARx_owned_low_law_xs; eapply YG0lawscf.AR_laws_ok_cf.
(* ASM1 *) - exact S8aTopInst.s8i_ASM1.
(* SMX *) - intros; eapply YGcallScf.stack_malloc_x_any; eassumption.
(* TS *) - exact AD2l.TfibB_syms.
(* GOT_SHADOW *) - exact (YC1fP.pal_got_shadow _ PALA).
(* GOT_UAR *) - exact (YC1fP.pal_got_uar _ PALA).
(* CELL_SHADOW *) - exact (YC1fP.pal_cell _ PALA).
(* UAR_CELL *) - exact S8aTopInst.s8i_UAR_CELL.
(* HW *) - exact CfParamsPreset.preset_head_wide.
(* HIMG *) - exact S8aNumberW.w_himg.
(* HPST *) - exact (S8aNumberW.w_hpst AD2l.TfibB AD2l.TfibB_syms).
(* Htp *) - exact (S8aNumberW.w_htp AD2l.TfibB AD2l.TfibB_syms).
(* Herrno *) - exact (S8aNumberW.w_herrno AD2l.TfibB AD2l.TfibB_syms).
(* Hown *) - exact (S8aNumberW.w_hown AD2l.TfibB AD2l.TfibB_syms).
(* HOFFB: FuzzFree's IMG_LO / IMG_TOP are strtod_img_A's bounds, by conversion *)
- intros ly S Hp W mem md p n HA Hin. exact (@FuzzFree.ff_blk_off_img rc AD2l.TfibB ly S Hp W mem md p n HA Hin).
(* HOFFF *) - exact S8aTopInst.s8i_HOFFF.
(* HGOTC *) - exact (S8aNumberW.w_hgotc AD2l.TfibB AD2l.TfibB_syms).
(* CPY *) - intros; eapply PRowCpy.prow_asan_memcpy_xm_A; [eapply YGcallcf.AR_laws_x_xs; eapply YG0lawscf.AR_laws_ok_cf | exact AD2l.TfibB_syms].
(* CMP *) - intros; eapply PSstrRo.ps_strcmp_xrom_xs_A; exact AD2l.TfibB_syms.
(* BCMP *) - intros; eapply PRowCmp.pr_bcmp_xm_A; [eapply YGcallcf.AR_laws_x_xs; eapply YG0lawscf.AR_laws_ok_cf | exact AD2l.TfibB_syms].
(* HBLK32 *) - exact S8aTopInst.s8i_HBLK32.
(* HAMEM8 *) - exact S8aTopInst.s8i_HAMEM8.
(* HSHD: the allocator's shadow law on ARcf, the left conjunct of iface_ARx *)
- intros ly S Hp W mem md p n HA Hin.
  exact (@YG0sshcf.AR_shadow_law_ok_cf rc CfImgA.CfImg_A CfParamsPreset.CfParams_preset _ AD2l.TfibB ly S Hp W mem md p n
    (proj1 HA) Hin).
(* HAM8 *) - exact S8aTopInst.s8i_HAM8.
(* PAL *) - exact PALA.
(* STRLENm *) - intros; eapply PSstrRo.ps_strlen_xrom_xs_A; exact AD2l.TfibB_syms.
(* ASFX *) - intros; eapply YGcallScf.astack_free_x_xs; eassumption.
Qed.

(* the same statement, with the driver's names (lib/A/Prog/Ent102DrvTopA3.v's abbreviations and local instances) *)
Section drv.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Existing Instance PRH_Base.prh_room_live_a8.
Lemma ex_value_A_inst_drv : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  PRH_FnEx.tex_value_specX (fx := fx) (rc := rc) (cp := CfParamsPreset.CfParams_preset)
    (PI := PresetCfnA.preset_prh_img) (PA := @PAImg_prog.PI_prog_A rc) AD2l.TfibB
    (@PresetCfnA.iface_ARx rc Listing_prog.A_prog_listing (@PAImg_prog.PI_prog_A rc) CfImgA.CfImg_A AD2l.TfibB)
    PresetCfnA.preset_sink_head PRH_Base.DOC_D.
Proof. exact ex_value_A_inst. Qed.
End drv.
