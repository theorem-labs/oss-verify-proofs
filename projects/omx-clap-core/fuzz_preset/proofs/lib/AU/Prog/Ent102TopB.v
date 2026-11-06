(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, image B' (asan-ubsan, harness fix #102 pin sha256
   d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin c90d4fa54d43): THE B' TOP of
   the walk of LLVMFuzzerTestOneInput (entry 0x816cc) - ONE statement, from cut_start to cut_ret, at the unit's
   CfParams (CfParams_preset):
     forall E, ec_hyps -> ec_laneR WLE' (cut_start E) (cut_ret E)    (WLE' := wle' segs RZ_cf: the walk frees)
   (the statements of lib/AU/Ent102CutsB.v, on the kit's cut 7cdbb61b5fa0). It is entry_B_of_segs (lib/AU/Prog/Ent102L7B.v, the
   composition) applied to the thirteen segment theorems, each merged by sha into the record line a working branch:
     seg_L0a_B, seg_L0b_B   lib/AU/Prog/Ent102L0B.v                  (a Theorem Labs lane, c2ea314d0fb0)
     seg_L1_B               lib/AU/Prog/Ent102L1B.v                  (a Theorem Labs lane, ca1c591014b4)
     seg_L2_B               lib/AU/Prog/Ent102L2B.v                  (a Theorem Labs lane, 9b9694ae4896)
     seg_L3_B               lib/AU/Prog/Ent102L3B.v                  (a Theorem Labs lane, d9247d9c057d)
     seg_L4_B               lib/AU/Prog/Ent102L4B.v                  (a Theorem Labs lane, d2760ca3af40)
     seg_L4j_B              lib/AU/Prog/Ent102L4jB.v                 (a Theorem Labs lane, 1e48ffd42f76)
     seg_L5a_B              lib/AU/Prog/Ent102L5aB.v                 (this lane, e6241d139dd8)
     seg_L5b_B, seg_L5c_B   lib/AU/Prog/Ent102L5bB.v / Ent102L5cB.v  (a Theorem Labs lane, 1a3b4412c781)
     seg_L5d_B              lib/AU/Prog/Ent102L5dB.v                 (a Theorem Labs lane, bfc3e902e3f2)
     seg_L6f_B              lib/AU/Prog/Ent102L6Bf.v                 (a Theorem Labs lane, 038e7ecbcbeb)
     seg_L6x_B              lib/AU/Prog/Ent102L6B.v                  (a Theorem Labs lane, 0ff0afabbfa0)
   The only premise of any segment is seg_L5b's per-request ceiling sat_rq_crt (generic in cp), discharged here at
   CfParams_preset by lib/A/Ent102ReqA.v sat_rq_crt_preset (a Theorem Labs lane's rq_crt_cf_bound); the granted callee texts
   the rows cite are derived from the batch kit's in lib/A/Prog/Ent102OfPost.v. So this theorem carries NO premise beyond its
   statement: what remains is the instance of ec_hyps itself, which the seam lib/AU/Prog/Ent102SeamB.v supplies (ec_img by lib/AU/Ent102InstB.v,
   ec_pay by lib/AU/Ent102PaySatB.v ec_pay_sat_preset, ec_texts / ec_univ / ec_frame_area / ec_noref from the slot's callee record and
   pre).
   rule 24: proves function LLVMFuzzerTestOneInput (the B' composition of its thirteen segments; reuse search
   the lane's index output, the internal file idx-llvm-newpin.txt exit=0, checker R24CheckLLVMF CONFIRM; NEW walk on the #102
   pins). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YI16 YG0f YC4aP YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import Ent102CutsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset Ent102ReqA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Import
  Ent102L0B Ent102L1B Ent102L2B Ent102L3B Ent102L4B Ent102L4jB Ent102L5aB Ent102L5bB Ent102L5cB Ent102L5dB
  Ent102L6Bf Ent102L6B Ent102L7B.

Section TopB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {PI : PrhImg} {RL : PrhRoomLive}.
Context {PA : @PAImg rc B_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variables ec_ccut ec_lcut : @ecx rc B_prog_listing PA -> nat -> Z.

(* NO PROVISIONAL PREMISE: all three granted texts the rows cite (lib/A/Prog/Ent102GrantA.v) are DERIVED from the batch kit's
   texts in lib/A/Prog/Ent102OfPost.v (Qed, zero hypotheses), and no row carries a Section hypothesis. The only premise
   of any segment is LL5b's per-request ceiling, discharged here by lib/A/Ent102ReqA.v sat_rq_crt_preset. *)
Local Ltac seg_prem := exact Ent102ReqA.sat_rq_crt_preset.

Definition entry_B_walk_term :=
  @entry_B_of_segs fx rc ci CfParamsPreset.CfParams_preset PI RL B_prog_listing PA B SK
    EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut
    ltac:(apply seg_L0a_B; repeat seg_prem) ltac:(apply seg_L0b_B; repeat seg_prem)
    ltac:(apply seg_L1_B; repeat seg_prem) ltac:(apply seg_L2_B; repeat seg_prem)
    ltac:(apply seg_L3_B; repeat seg_prem) ltac:(apply seg_L4_B; repeat seg_prem)
    ltac:(apply seg_L4j_B; repeat seg_prem) ltac:(apply seg_L5a_B; repeat seg_prem)
    ltac:(apply seg_L5b_B; repeat seg_prem) ltac:(apply seg_L5c_B; repeat seg_prem)
    ltac:(apply seg_L5d_B; repeat seg_prem) ltac:(apply seg_L6f_B; repeat seg_prem)
    ltac:(apply seg_L6x_B; repeat seg_prem).

(* THE B' TOP: its type is exactly `forall E, ec_hyps -> ec_laneR WLE' (cut_start E) (cut_ret E)` at CfParams_preset *)
Theorem entry_B_walk : ltac:(let T := type of entry_B_walk_term in exact T).
Proof. exact entry_B_walk_term. Qed.

End TopB.

Check entry_B_walk.
About entry_B_walk.
Print Assumptions entry_B_walk.
