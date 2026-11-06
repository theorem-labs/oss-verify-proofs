(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102): read_members at the A' instance with the strcmp row
   CLOSED, so it has no premise. read_members_holds_Ap_c (lib/A/Prog/read_members_Ap2.v) applied to
   c-libc-stdio's A' strcmp row PSstrRo.ps_strcmp_xrom_A (lib/A/PSstrRo.v:66, blob 4de202368a14: astrcmp_realizes_xrom at
   AB1v.tfibsegs, ARcf, any rlo / rhi, pc CfImgA's cf_pc_strcmp), at B := AD2l.TfibB with TS := AD2l.TfibB_syms
   (lib/A/AD2l.v:73), rlo / rhi := PI_prog_A's relro bounds.
   THE TWO FACTS that carry the row to read_members_holds_Ap_c's premise ASC:
     the pc     CfImgA's cf_pc_strcmp (lib/A/CfImgA.v:46) and PI_prog_A's pa_sigma AS___wrap_strcmp (lib/A/PAImg_prog.v:82)
                are the same entry (__wrap_strcmp = __interceptor_trampoline_strcmp): rmA3_pc, by vm_compute;
     the segs   AB1v.tfibsegs (lib/A/AB1v.v:12) and PI_prog_A's pa_segs = lib/A/Img0.v rsegs are both
                Asan.M.loaded_segments: by conversion (delta), at the final `exact`.
   The row's implicit arguments are {fx rc cp} (About below): no CfImg instance is asked.
   REMAINING PREMISES: none. (The former gap premise RM_G3 is gone: read_members takes both its halves from the laws at
   cf_head, fields 14 alx_hshadow and 22 alx_hhead of PALibA.palib_laws_A.) *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD2l CfImgA PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnPj PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require read_members_Ap2.
Local Open Scope Z_scope.

(* the supplier's arguments, implicit ones included, printed for the record *)
About PSstrRo.ps_strcmp_xrom_A.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive} {ci : CfImg}.
Variable SK : YI16.sink_head.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Abbreviation PIA := (PI_prog_A (rc := rc)).
#[local] Abbreviation SEGSA := (@pa_segs _ A_prog_listing PIA).
#[local] Abbreviation ARI :=
  (YG0ncf.ARcf (rc := rc) (cp := CP) OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs TA).

(* the pc: the row's trampoline entry is the listing's __wrap_strcmp (both 0x42d20 on A') *)
Lemma rmA3_pc : @cf_pc_strcmp CfImgA.CfImg_A = @pa_sigma _ A_prog_listing PIA AS___wrap_strcmp.
Proof. cbn [pa_sigma PI_prog_A]. vm_compute. reflexivity. Qed.

Theorem read_members_holds_Ap3 :
  tread_members_specX (fx := fx) (rc := rc) (cp := CP) (PI := prh_img_A) (RL := RL) (PA := PIA) TA ARI SK.
Proof.
pose proof (PSstrRo.ps_strcmp_xrom_A (fx := fx) (rc := rc) (cp := CP) TA AD2l.TfibB_syms
  (@pa_relro_lo _ _ PIA) (@pa_relro_hi _ _ PIA)) as ASC.
rewrite rmA3_pc in ASC.
exact (read_members_Ap2.read_members_holds_Ap_c (fx := fx) (rc := rc) (RL := RL) SK ASC).
Qed.
End c.

Set Printing Implicit.
Check rmA3_pc.
Check read_members_holds_Ap3.
Unset Printing Implicit.
Print Assumptions read_members_holds_Ap3.
