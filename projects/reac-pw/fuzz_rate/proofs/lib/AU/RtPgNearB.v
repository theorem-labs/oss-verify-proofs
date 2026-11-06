(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgNearA.v at 92636bfca57b; the module paths name reac-pw/fuzz_rate, rl_pod_nearest_A becomes rt_pod_nearest_A against lib/A/RtPgCSpec.v's rt_pod_nearest_specX, and the image is reac-pw/fuzz_rate's image A (fuzz_rate.asan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgNearA.v at b089f28d962e; rt_pod_nearest_A becomes rt_pod_nearest_B at reac-pw/fuzz_rate's image B (fuzz_rate.asan-ubsan): the walk lib/AU/RtPgNearWB.v, the lift lib/AU/RtPgNearLB.v, the image lib/AU/Img0.v and the addresses of lib/AU/RtPgNearImgB.v, and the five soft-float callee contracts at image B's symbol map are Section hypotheses (image A's were the instances of lib/CJ/RL/I/InstA.v). *)
(* pod_nearest(f, out) of reac-pw/fuzz_rate's ASan image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14), entry RtPgNearImgB.B_POD_NEAREST, proved
   against lib/A/RtPgCSpec.v's rt_pod_nearest_specX: the walk (lib/AU/RtPgNearWB.v pod_nearest_B_holds, the
   machine-level contract lib/AU/RtPgNearCB.v pod_nearest_B_contract from the binary128 value facts, closed by
   lib/Prog/NearSFClose.v near_sf_facts_ok, and the soft-float callees' CJ contracts at image B's symbol map
   RtPgNearImgB.N_img) composed with the lift (lib/AU/RtPgNearLB.v rt_pod_nearest_B_of). Its Section hypotheses:
   those of the lift, the meter's laws MTL, the runtime's AR laws LAWS, and the two cells of the runtime's symbol
   record the code reads, the .got slot (HGOT) and the shadow-offset cell (HSC); and the five soft-float callee
   contracts at RtPgNearImgB.N_img (HEX, HLE, HFD, HSB, HGE), of the types image A's lib/CJ/RL/I/InstA.v instances
   have at image A's map. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YK11 YK14 YK0s YK15 YK18 YK0i YK1b YP09 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require C_extendsftf2 C_floatditf G_letf2 G_getf2 G_subtf3.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgNearImgB RtPgNearWB RtPgNearLB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require NearSFClose.
Local Open Scope Z_scope.

Module NI := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU.RtPgNearImgB.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Hypothesis HGOT : as_got_shadow B = NI.B_GOT_SHADOW.
Hypothesis HSC : as_shadow_cell B = NI.B_SHADOW_CELL.
Hypothesis HEX : @C_extendsftf2.extendsftf2_contract NI.N_img.
Hypothesis HLE : @G_letf2.letf2_contract NI.N_img.
Hypothesis HFD : @C_floatditf.floatditf_contract NI.N_img.
Hypothesis HSB : @G_subtf3.subtf3_contract NI.N_img.
Hypothesis HGE : @G_getf2.getf2_contract NI.N_img.

Theorem rt_pod_nearest_B : rt_pod_nearest_specX rsegs B MT NI.B_POD_NEAREST.
Proof using MTL LAWS HGOT HSC HEX HLE HFD HSB HGE.
exact (RtPgNearLB.rt_pod_nearest_B_of B MT MTL LAWS HGOT HSC
  (RtPgNearWB.pod_nearest_B_holds NearSFClose.near_sf_facts_ok HEX HLE HFD HSB HGE)).
Qed.
End d.
End b.

Check rt_pod_nearest_B.
Print Assumptions rt_pod_nearest_B.
About rt_pod_nearest_B.
