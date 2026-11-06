(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f488d30): read_members at the B' instance, NO
   premise, at the allocator relation the driver uses: ARcf /\ xs_placed_cf at CfParams_preset (the relation of
   PresetCfnA.v's iface_ARx at image B). The ARcf-only top read_members_holds_Bp3 (lib/B/Prog/read_members_Bp3.v) is
   kept as it is.
   The walk read_members_holds (lib/B/Prog/read_members.v) and a Theorem Labs lane's pj_get / pj_get_str B' walks
   (lib/B/Prog/PjGetB.v pj_get_holds_B_K0 / pj_get_str_holds_B_K0) are generic in the allocator relation; here they are
   taken at that relation:
     LAWS  YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf
     TL    PALibB.exvi_eh_palib
     ASC   a Theorem Labs lane's strcmp row at the same relation, PSstrRo.ps_strcmp_xrom_xs_B (lib/AU/PSstrRo.v), carried to the
           wrapper pc by read_members_Bp3.rmB3_pc
     the image facts: read_members_Bp.v's lemmas, which do not depend on the relation.
   REMAINING PREMISES: none. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YM05 YI16 YG00 YG0f YG0n YG0d YA0n YCbqG YPsym YC4aP YC1fP YGcfNames YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require read_members read_members_Bp read_members_Bp3 PjGetB.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Variable SK : YI16.sink_head.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation PIB := (PI_prog_B (rc := rc)).
#[local] Abbreviation SEGSB := (@pa_segs _ B_prog_listing PIB).
(* the driver's allocator relation: ARcf with the error buffer placed *)
#[local] Abbreviation ARX := (fun ly S Hp W mem md =>
  YG0ncf.ARcf (rc := rc) (cp := CP) SEGSB TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

Lemma rmB4_laws : AR_laws_x SEGSB TB ARX (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs (cp := CP) SEGSB TB (YG0lawscf.AR_laws_ok_cf (cp := CP) SEGSB TB)). Qed.

Lemma rmB4_asc : astrcmp_realizes_xrom (fx := fx) SEGSB TB ARX (@pa_relro_lo _ _ PIB) (@pa_relro_hi _ _ PIB)
  (@pa_sigma _ B_prog_listing PIB AS___wrap_strcmp).
Proof.
pose proof (PSstrRo.ps_strcmp_xrom_xs_B (fx := fx) (rc := rc) (cp := CP) TB YD2l.TfibB_syms
  (@pa_relro_lo _ _ PIB) (@pa_relro_hi _ _ PIB)) as ASC.
rewrite read_members_Bp3.rmB3_pc in ASC. exact ASC.
Qed.

Theorem read_members_holds_Bp4 :
  tread_members_specX (fx := fx) (rc := rc) (cp := CP) (PI := prh_img_B) (RL := RL) (PA := PIB) TB ARX SK.
Proof.
exact (@read_members.read_members_holds fx rc RL SK PIB TB ARX
  rmB4_laws (palib_core (PI := PIB) TB (PALibB.exvi_eh_palib (rc := rc)))
  (PjGetB.pj_get_holds_B_K0 (fx := fx) (rc := rc) (RL := RL) SK TB ARX rmB4_laws PALibB.exvi_eh_palib rmB4_asc)
  (PjGetB.pj_get_str_holds_B_K0 (fx := fx) (rc := rc) (RL := RL) SK TB ARX rmB4_laws PALibB.exvi_eh_palib rmB4_asc)
  read_members_Bp.RM_IMG_at_Bp read_members_Bp.rmB_ent read_members_Bp.rmB_obj read_members_Bp.rmB_lo
  read_members_Bp.rmB_o2 read_members_Bp.rmB_keys read_members_Bp.rmB_top read_members_Bp.rmB_top_al
  read_members_Bp.rmB_pst).
Qed.
End c.

Set Printing Implicit.
Check read_members_holds_Bp4.
Unset Printing Implicit.
Print Assumptions read_members_holds_Bp4.
