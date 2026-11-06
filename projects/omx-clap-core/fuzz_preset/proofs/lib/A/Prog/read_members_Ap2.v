(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102): THE COMPOSITION of the read_members instance
   (lib/A/Prog/read_members_inst.v, read_members_holds_inst) with a Theorem Labs lane's pj_get / pj_get_str A' walks
   (lib/A/Prog/S6PjGet.v caa17d88daea pj_get_holds, lib/A/Prog/S6PjGetStr.v 846c46d9b454 pj_get_str_holds: the
   tpj_get_specX / tpj_get_str_specX), at PA := PI_prog_A, B := AD2l.TfibB, ARx := ARcf at CfParams_preset, on
   a Theorem Labs lane's P'' set (a working branch 19a067d0b7eb, which carries every file used here; nothing
   taken by path). The A' mirror of the B' corollary lib/B/Prog/read_members_Bp2.v.
   DISCHARGED HERE, the walks' Section hypotheses at the instance:
     LAWS  PALibA.palib_laws_A (lib/A/PALibA.v 88c72c8175cf)
     TL    PALibA.palib_A
     Hent  S6ImgWit.s6w_ent_pj_get / S6ImgWit.s6w_ent_pj_get_str (lib/A/Prog/S6ImgWit.v 1a301f811bfc, vm_compute)
     Hobj  S6ImgWit.s6w_obj (vm_compute)
     PAB   S6ImgWit.s6w_pab (pj_get_str only; reflexivity)
     GET   pj_get_str's callee text: pj_get_holds above.
   REMAINING PREMISE, exactly one: ASC, the walks' one call row - a Theorem Labs lane's strcmp row astrcmp_realizes_xrom at
   the wrapper AS___wrap_strcmp (lib/Reusable/YGcallMxmn.v b47cf7942c3d), which read_members does not supply. (The
   former gap premise RM_G3 is gone: read_members takes both its halves from LAWS at cf_head, fields 14 alx_hshadow and
   22 alx_hhead.) *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l PALibA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require read_members_inst S6PjGet S6PjGetStr S6ImgWit.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Variable SK : YI16.sink_head.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation PIA := (PI_prog_A (rc := rc)).
#[local] Abbreviation SEGSA := (@pa_segs _ A_prog_listing PIA).
(* the allocator instance, as read_members_inst.v states it (the A' segments, written fully qualified) *)
#[local] Abbreviation ARI :=
  (YG0ncf.ARcf (rc := rc) (cp := CP) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs TA).
(* the walks' one call row: the strcmp row at the wrapper (owner c-libc-stdio), as S6PjGet.v states it (ASCR) *)
Hypothesis ASC : YGcallMxmn.astrcmp_realizes_xrom (fx := fx) SEGSA TA ARI (@pa_relro_lo _ _ PIA) (@pa_relro_hi _ _ PIA)
  (@pa_sigma _ A_prog_listing PIA AS___wrap_strcmp).
Theorem read_members_holds_Ap_c :
  tread_members_specX (fx := fx) (rc := rc) (cp := CP) (PI := prh_img_A) (RL := RL) (PA := PIA) TA ARI SK.
Proof.
pose proof (PALibA.palib_laws_A (rc := rc)) as LAWS.
pose proof (PALibA.palib_A (rc := rc)) as TL.
pose proof (S6PjGet.pj_get_holds (fx := fx) (rc := rc) (RL := RL) (PA := PIA) SK TA ARI LAWS TL
  (S6ImgWit.s6w_ent_pj_get (rc := rc)) (S6ImgWit.s6w_obj (rc := rc)) ASC) as PJ.
pose proof (S6PjGetStr.pj_get_str_holds (fx := fx) (rc := rc) (RL := RL) (PA := PIA) SK TA ARI LAWS TL
  (S6ImgWit.s6w_ent_pj_get_str (rc := rc)) (S6ImgWit.s6w_obj (rc := rc)) (S6ImgWit.s6w_pab (rc := rc)) PJ) as PJS.
exact (read_members_inst.read_members_holds_inst (fx := fx) (rc := rc) (RL := RL) SK PJ PJS).
Qed.
End c.

Set Printing Implicit.
Check read_members_holds_Ap_c.
Unset Printing Implicit.
Print Assumptions read_members_holds_Ap_c.
