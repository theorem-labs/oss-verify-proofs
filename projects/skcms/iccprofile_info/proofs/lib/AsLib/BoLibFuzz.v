(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec Hoare LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibDefs BoBase AsRtSpec BoRtSetShadow BoRtStackFree5 BoRtStackMalloc BoRtStackMalloc5 BoRtMemset BoRtMemcpy BoLibRte BoLibEvalCurve BoLibClassify BoLibGetTag BoLibGetIdx BoLibToXyz BoLibMftcA2B BoLibMftcB2A BoLibItabA2B BoLibItabB2A BoLibReadCurve BoLibReadCurves BoLibFitLinear BoLibCanon BoLibReadA2Bh BoLibReadB2Ah BoLibUsable BoLibCicp BoLibParse BoLibFuzzA BoLibSpec.

Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma read_curve_closed : forall ceil, AsLibCurveSpec.read_curve_contract_as SEGS as_both ceil.
Proof. intros ceil. exact (read_curve_bo_ok ceil (imemset20_both ceil) (classify_bo_ok ceil)). Qed.

Lemma canonicalize_closed : forall ceil, AsLibFPSpec.canonicalize_contract_as SEGS as_both ceil.
Proof.
  intros ceil.
  exact (canonicalize_both ceil (fit_linear_both ceil (eval_curve_bo_ok ceil) (stkmalloc0_both ceil)) (stkmalloc0_both ceil) (imemset20_both ceil)).
Qed.

Lemma read_a2b_closed : forall ceil, BoLibSpec.read_a2b_contract_bo SEGS as_both ceil.
Proof.
  intros ceil.
  exact (read_a2b_bo_ok ceil (read_mft_common_a2b_bo_ok ceil) (init_tables_a2b_bo_ok ceil) (read_curves_bo_ok ceil (read_curve_closed ceil))
           (canonicalize_closed ceil)).
Qed.

Lemma read_b2a_closed : forall ceil, BoLibSpec.read_b2a_contract_bo SEGS as_both ceil.
Proof.
  intros ceil.
  exact (read_b2a_bo_ok ceil (read_mft_common_b2a_bo_ok ceil) (init_tables_b2a_bo_ok ceil) (read_curves_bo_ok ceil (read_curve_closed ceil))
           (canonicalize_closed ceil)).
Qed.

Lemma parse_closed : forall ceil, BoLibSpec.parse_contract_bo SEGS as_both ceil.
Proof.
  intros ceil.
  exact (parse_bo_ok ceil (imemset976_both ceil) (gettag_bo_ok ceil) (read_curve_closed ceil) (imemcpy32_both ceil) (xyzd50_bo_ok ceil)
           (read_a2b_closed ceil) (read_b2a_closed ceil) (cicp_bo_ok ceil) (usable_bo_ok ceil)).
Qed.

Lemma parse0_closed : forall ceil, BoLibFuzzA.parse0_contract ceil.
Proof.
  intros ceil sp prio P fs ch FPI regs mem rom ret Hra Hret PRE.
  exact (parse0_ok ceil (imemset976_both ceil) (gettag_bo_ok ceil) (read_curve_closed ceil) (imemcpy32_both ceil) (xyzd50_bo_ok ceil)
           (read_a2b_closed ceil) (read_b2a_closed ceil) (cicp_bo_ok ceil) (usable_bo_ok ceil) sp prio P fs ch FPI regs mem rom ret Hra Hret PRE).
Qed.

Theorem as_fuzz_closed : as_fuzz_contract SEGS both_abi.
Proof.
  exact (as_fuzz_ok parse_closed parse0_closed getidx_bo_ok rte_bo_ok stkmalloc5_both stkfree5_both setsh00_both setshf8_both).
Qed.
