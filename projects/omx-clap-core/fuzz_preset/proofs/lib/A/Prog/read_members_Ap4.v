(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102): read_members at the A' instance, NO premise, at the
   allocator relation the driver uses: ARcf /\ xs_placed_cf at CfParams_preset (a Theorem Labs lane's ec_ARx, PresetCfnA.v's
   iface_ARx; the relation of FuzzFree.v / CheckBoundedAllocAInst.v / Crc102InstA.v). The ARcf-only top
   read_members_holds_Ap3 (lib/A/Prog/read_members_Ap3.v) is kept as it is.
   The walk read_members_holds (lib/A/Prog/read_members.v) and the pj_get / pj_get_str walks (lib/A/Prog/S6PjGet.v,
   S6PjGetStr.v) are generic in the allocator relation; here they are taken at that relation:
     LAWS  YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf (the laws at ARcf /\ xs_placed_cf, the discharge the other
           tops at this relation use)
     ASC   a Theorem Labs lane's strcmp row at the same relation, PSstrRo.ps_strcmp_xrom_xs_A, carried to the wrapper pc by
           read_members_Ap3.rmA3_pc
     the image facts: read_members_inst.v's lemmas and S6ImgWit.v's, which do not depend on the relation.
   REMAINING PREMISES: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l CfImgA PSstrRo PALibA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require read_members read_members_inst read_members_Ap3.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S6PjGet S6PjGetStr S6ImgWit.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Variable SK : YI16.sink_head.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation PIA := (PI_prog_A (rc := rc)).
#[local] Abbreviation SEGSA := (@pa_segs _ A_prog_listing PIA).
(* the driver's allocator relation: ARcf with the error buffer placed *)
#[local] Abbreviation ARX := (fun ly S Hp W mem md =>
  YG0ncf.ARcf (rc := rc) (cp := CP) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs TA
    ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

Lemma rmA4_laws : AR_laws_x SEGSA TA ARX (@cf_head CP).
Proof.
exact (YGcallcf.AR_laws_x_xs (cp := CP) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs TA
  (YG0lawscf.AR_laws_ok_cf (cp := CP) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs TA)).
Qed.

Lemma rmA4_asc : YGcallMxmn.astrcmp_realizes_xrom (fx := fx) SEGSA TA ARX (@pa_relro_lo _ _ PIA) (@pa_relro_hi _ _ PIA)
  (@pa_sigma _ A_prog_listing PIA AS___wrap_strcmp).
Proof.
pose proof (PSstrRo.ps_strcmp_xrom_xs_A (fx := fx) (rc := rc) (cp := CP) TA AD2l.TfibB_syms
  (@pa_relro_lo _ _ PIA) (@pa_relro_hi _ _ PIA)) as ASC.
rewrite read_members_Ap3.rmA3_pc in ASC. exact ASC.
Qed.

Theorem read_members_holds_Ap4 :
  tread_members_specX (fx := fx) (rc := rc) (cp := CP) (PI := prh_img_A) (RL := RL) (PA := PIA) TA ARX SK.
Proof.
pose proof (PALibA.palib_A (rc := rc)) as TL.
pose proof (S6PjGet.pj_get_holds (fx := fx) (rc := rc) (RL := RL) (PA := PIA) SK TA ARX rmA4_laws TL
  (S6ImgWit.s6w_ent_pj_get (rc := rc)) (S6ImgWit.s6w_obj (rc := rc)) rmA4_asc) as PJ.
pose proof (S6PjGetStr.pj_get_str_holds (fx := fx) (rc := rc) (RL := RL) (PA := PIA) SK TA ARX rmA4_laws TL
  (S6ImgWit.s6w_ent_pj_get_str (rc := rc)) (S6ImgWit.s6w_obj (rc := rc)) (S6ImgWit.s6w_pab (rc := rc)) PJ) as PJS.
eapply (read_members.read_members_holds (fx := fx) (rc := rc) (cp := CP) (RL := RL) (PA := PIA) TA ARX SK).
all: first [ exact rmA4_laws | exact TL | exact PJ | exact PJS
           | exact read_members_inst.RM_IMG_at_Ap | exact read_members_inst.rmA_ent | exact read_members_inst.rmA_obj
           | exact read_members_inst.rmA_lo | exact read_members_inst.rmA_hi | exact read_members_inst.rmA_lits
           | exact read_members_inst.rmA_top | exact read_members_inst.rmA_pst | exact CfParamsPreset.preset_head_wide ].
Qed.
End c.

Set Printing Implicit.
Check read_members_holds_Ap4.
Unset Printing Implicit.
Print Assumptions read_members_holds_Ap4.
