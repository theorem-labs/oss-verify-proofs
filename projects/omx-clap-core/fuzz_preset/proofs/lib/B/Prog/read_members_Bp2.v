(* omx-clap-core/fuzz_preset, image B' (#102 pin d663f82d7f488d30): THE COMPOSITION of the read_members instance
   (lib/B/Prog/read_members_Bp.v, read_members_holds_Bp) with a Theorem Labs lane's pj_get / pj_get_str B' tops
   (lib/B/Prog/PjGetB.v 7946e6065cb8: pj_get_holds_B_top / pj_get_str_holds_B_top, K0's tpj_get_specX /
   tpj_get_str_specX at PI_prog_B, TfibB, ARcf at CfParams_preset), on a Theorem Labs lane's P'' set
   (a working branch 19a067d0b7eb, which carries all three files; nothing taken by path).
   REMAINING PREMISE, exactly one: ASC, the tops' one hypothesis - a Theorem Labs lane's strcmp row astrcmp_realizes_xrom at
   the wrapper AS___wrap_strcmp (YGcallMxmn.v), which read_members does not supply. (The former gap premise RM_G3 is
   gone: read_members takes both its halves from LAWS at cf_head, fields 14 alx_hshadow and 22 alx_hhead.) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YM05 YI16 YG00 YG0f YG0n YG0d YA0n YCbqG YPsym YC4aP YGcfNames YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require read_members_Bp PjGetB.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation PIB := (PI_prog_B (rc := rc)).
#[local] Abbreviation SEGSB := (@pa_segs _ B_prog_listing PIB).
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) SEGSB TB).
(* the tops' one hypothesis: the strcmp row at the wrapper (owner c-libc-stdio), as PjGetB.v states it *)
Hypothesis ASC : astrcmp_realizes_xrom SEGSB TB ARI (@pa_relro_lo _ _ PIB) (@pa_relro_hi _ _ PIB)
  (@pa_sigma _ B_prog_listing PIB AS___wrap_strcmp).
Theorem read_members_holds_Bp_c :
  tread_members_specX (cp := CP) (PI := prh_img_B) (PA := PIB) TB ARI SK.
Proof.
exact (read_members_Bp.read_members_holds_Bp (fx := fx) (rc := rc) (RL := RL) SK
  (PjGetB.pj_get_holds_B_top (fx := fx) (rc := rc) (RL := RL) SK ASC)
  (PjGetB.pj_get_str_holds_B_top (fx := fx) (rc := rc) (RL := RL) SK ASC)).
Qed.
End c.
