(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102TopA.v, with its module paths changed; 8 of its 34 lines of code are new or changed and 4 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102 pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): THE A' TOP of
   the walk of LLVMFuzzerTestOneInput (entry 0x815e0) - ONE statement, from cut_start to cut_ret, at the unit's
   CfParams (CfParams_preset):
     forall E, ec_hyps -> ec_laneR WLE' (cut_start E) (cut_ret E)    (WLE' := wle' segs RZ_cf: the walk frees)
   (the statements of lib/A/Ent102CutsA.v, on the kit's cut 7cdbb61b5fa0). It is entry_A_of_segs (lib/A/Prog/Ent102L7A.v, the
   composition) applied to the thirteen segment theorems, each merged by sha into the record line a working branch:
     seg_L0a_A, seg_L0b_A   lib/A/Prog/Ent102L0A.v                  (this lane)
     seg_L1_A               lib/A/Prog/Ent102L1A.v                  (a Theorem Labs lane, 90bcaf49278f)
     seg_L2_A               lib/A/Prog/Ent102L2A.v                  (a Theorem Labs lane, 5a6cb823b4e2)
     seg_L3_A               lib/A/Prog/Ent102L3A.v                  (a Theorem Labs lane, d0197f4426a5)
     seg_L4_A               lib/A/Prog/Ent102L4A.v                  (this lane, 1c9e4170e608)
     seg_L4j_A              lib/A/Prog/Ent102L4jA.v                 (this lane, e1eae03c16c6)
     seg_L5a_A              lib/A/Prog/Ent102L5aA.v                 (this lane, 55388e259692)
     seg_L5b_A              lib/A/Prog/Ent102L5bA.v                 (a Theorem Labs lane, 8770d577d8aa)
     seg_L5c_A              lib/A/Prog/Ent102L5cA.v                 (a Theorem Labs lane, 9bdfc14e422a)
     seg_L5d_A              lib/A/Prog/Ent102L5dA.v                 (this lane, 85dacbe4891a)
     seg_L6f_A              lib/A/Prog/Ent102L6Af.v                 (this lane, bb86a26820dd)
     seg_L6x_A              lib/A/Prog/Ent102L6A.v                  (this lane, f89e08f2c51b)
   The only premise of any segment is seg_L5b's per-request ceiling sat_rq_crt (generic in cp), discharged here at
   CfParams_preset by lib/A/Ent102ReqA.v sat_rq_crt_preset (a Theorem Labs lane's rq_crt_cf_bound); the granted callee texts
   the rows cite are derived from the batch kit's in lib/A/Prog/Ent102OfPost.v. So this theorem carries NO premise beyond its
   statement: what remains is the instance of ec_hyps itself, which the seam lib/A/Prog/Ent102SeamA.v supplies (ec_img by lib/A/Ent102InstA.v,
   ec_pay by lib/A/Ent102PaySat.v ec_pay_sat_preset, ec_texts / ec_univ / ec_frame_area / ec_noref from the slot's callee record and
   pre).
   rule 24: proves function LLVMFuzzerTestOneInput (the A' composition of its thirteen segments; reuse search
   the lane's index output, the internal file idx-llvm-newpin.txt exit=0, checker R24CheckLLVMF CONFIRM; NEW walk on the #102
   pins). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YM05 YI16 YG0f YC4aP YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base Listing_prog Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset Ent102ReqA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import
  Ent102L0A Ent102L1A Ent102L2A Ent102L3A Ent102L4A Ent102L4jA Ent102L5aA Ent102L5bA Ent102L5cA Ent102L5dA
  Ent102L6Af Ent102L6A Ent102L7A.

Section TopA.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {PI : PrhImg} {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variables ec_ccut ec_lcut : @ecx rc A_prog_listing PA -> nat -> Z.

(* NO PROVISIONAL PREMISE: all three granted texts the rows cite (lib/A/Prog/Ent102GrantA.v) are DERIVED from the batch kit's
   texts in lib/A/Prog/Ent102OfPost.v (Qed, zero hypotheses), and no row carries a Section hypothesis. The only premise
   of any segment is LL5b's per-request ceiling, discharged here by lib/A/Ent102ReqA.v sat_rq_crt_preset. *)
Local Ltac seg_prem := exact Ent102ReqA.sat_rq_crt_preset.

Definition entry_A_walk_term :=
  @entry_A_of_segs fx rc ci CfParamsPreset.CfParams_preset PI RL A_prog_listing PA B SK
    EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG ec_ccut ec_lcut
    ltac:(apply seg_L0a_A; repeat seg_prem) ltac:(apply seg_L0b_A; repeat seg_prem)
    ltac:(apply seg_L1_A; repeat seg_prem) ltac:(apply seg_L2_A; repeat seg_prem)
    ltac:(apply seg_L3_A; repeat seg_prem) ltac:(apply seg_L4_A; repeat seg_prem)
    ltac:(apply seg_L4j_A; repeat seg_prem) ltac:(apply seg_L5a_A; repeat seg_prem)
    ltac:(apply seg_L5b_A; repeat seg_prem) ltac:(apply seg_L5c_A; repeat seg_prem)
    ltac:(apply seg_L5d_A; repeat seg_prem) ltac:(apply seg_L6f_A; repeat seg_prem)
    ltac:(apply seg_L6x_A; repeat seg_prem).

(* THE A' TOP: its type is exactly `forall E, ec_hyps -> ec_laneR WLE' (cut_start E) (cut_ret E)` at CfParams_preset *)
Theorem entry_A_walk : ltac:(let T := type of entry_A_walk_term in exact T).
Proof. exact entry_A_walk_term. Qed.

End TopA.

Check entry_A_walk.
About entry_A_walk.
Print Assumptions entry_A_walk.
