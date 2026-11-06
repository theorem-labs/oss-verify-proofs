(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, #102 pin d663f82d7f488d30): read_members at the B' instance with
   the strcmp row CLOSED, so it has no premise. read_members_holds_Bp_c (lib/B/Prog/read_members_Bp2.v) applied to
   a Theorem Labs lane's B' strcmp row PSstrRo.ps_strcmp_xrom_B (lib/AU/PSstrRo.v:67, blob 45e63604063e:
   astrcmp_realizes_xrom at YB1v.tfibsegs, ARcf, any rlo / rhi, pc CfImgB's cf_pc_strcmp), at B := YD2l.TfibB with
   TS := YD2l.TfibB_syms (lib/Reusable/YD2l.v:71), rlo / rhi := PI_prog_B's relro bounds.
   THE TWO FACTS that carry the row to read_members_holds_Bp_c's premise ASC:
     the pc     CfImgB's cf_pc_strcmp (lib/AU/CfImgB.v:46) and PI_prog_B's pa_sigma AS___wrap_strcmp (lib/B/PAImg_prog.v:82)
                are the same entry (__wrap_strcmp = __interceptor_trampoline_strcmp): rmB3_pc, by vm_compute;
     the segs   YB1v.tfibsegs (lib/Reusable/YB1v.v:14) and PI_prog_B's pa_segs = lib/B/Img0.v rsegs are both
                AsanUbsan.M.loaded_segments: by conversion (delta), at the final `exact`.
   The row's implicit arguments are {fx rc cp} (About below): no CfImg instance is asked.
   REMAINING PREMISES: none. (The former gap premise RM_G3 is gone: read_members takes both its halves from the laws at
   cf_head, fields 14 alx_hshadow and 22 alx_hhead of PALibB.exvi_eh_laws.) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YM05 YI16 YG00 YG0f YG0n YG0d YA0n YCbqG YPsym YC4aP YGcfNames YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require read_members_Bp2.
Local Open Scope Z_scope.

(* the supplier's arguments, implicit ones included, printed for the record *)
About PSstrRo.ps_strcmp_xrom_B.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Variable SK : YI16.sink_head.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation PIB := (PI_prog_B (rc := rc)).
#[local] Abbreviation SEGSB := (@pa_segs _ B_prog_listing PIB).
#[local] Abbreviation ARI := (YG0ncf.ARcf (rc := rc) (cp := CP) SEGSB TB).

(* the pc: the row's trampoline entry is the listing's __wrap_strcmp (both 0x42e0c on B') *)
Lemma rmB3_pc : @cf_pc_strcmp CfImgB.CfImg_B = @pa_sigma _ B_prog_listing PIB AS___wrap_strcmp.
Proof. cbn [pa_sigma PI_prog_B]. vm_compute. reflexivity. Qed.

Theorem read_members_holds_Bp3 :
  tread_members_specX (fx := fx) (rc := rc) (cp := CP) (PI := prh_img_B) (RL := RL) (PA := PIB) TB ARI SK.
Proof.
pose proof (PSstrRo.ps_strcmp_xrom_B (fx := fx) (rc := rc) (cp := CP) TB YD2l.TfibB_syms
  (@pa_relro_lo _ _ PIB) (@pa_relro_hi _ _ PIB)) as ASC.
rewrite rmB3_pc in ASC.
exact (read_members_Bp2.read_members_holds_Bp_c (fx := fx) (rc := rc) (RL := RL) SK ASC).
Qed.
End c.

Set Printing Implicit.
Check rmB3_pc.
Check read_members_holds_Bp3.
Unset Printing Implicit.
Print Assumptions read_members_holds_Bp3.
