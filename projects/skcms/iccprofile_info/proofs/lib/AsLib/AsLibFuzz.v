(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec Hoare LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsFuzzContract AsLibDefs AsRtSpec AsRtSetShadow AsRtStackFree5 AsRtStackMalloc AsRtStackMalloc5 AsRtMemset AsRtMemcpy AsLibRte AsLibEvalCurve AsLibClassify AsLibGetTag AsLibGetIdx AsLibToXyz AsLibMftcA2B AsLibMftcB2A AsLibItabA2B AsLibItabB2A AsLibReadCurve AsLibReadCurves AsLibFitLinear AsLibCanon AsLibReadA2Bh AsLibReadB2Ah AsLibParse AsLibFuzzA.

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
#[local] Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Lemma read_curve_closed : forall ceil, AsLibCurveSpec.read_curve_contract_as SEGS as_asan ceil.
Proof. intros ceil. exact (read_curve_as_ok ceil (imemset20_asan ceil) (classify_as_ok ceil)). Qed.

Lemma canonicalize_closed : forall ceil, AsLibFPSpec.canonicalize_contract_as SEGS as_asan ceil.
Proof.
  intros ceil.
  exact (canonicalize_asan ceil (fit_linear_asan ceil (eval_curve_as_ok ceil) (stkmalloc0_asan ceil)) (stkmalloc0_asan ceil) (imemset20_asan ceil)).
Qed.

Lemma read_a2b_closed : forall ceil, AsLibWP2Spec.read_a2b_contract_as SEGS as_asan ceil.
Proof.
  intros ceil.
  exact (read_a2b_as_ok ceil (read_mft_common_a2b_as_ok ceil) (init_tables_a2b_as_ok ceil) (read_curves_as_ok ceil (read_curve_closed ceil))
           (canonicalize_closed ceil)).
Qed.

Lemma read_b2a_closed : forall ceil, AsLibWP2Spec.read_b2a_contract_as SEGS as_asan ceil.
Proof.
  intros ceil.
  exact (read_b2a_as_ok ceil (read_mft_common_b2a_as_ok ceil) (init_tables_b2a_as_ok ceil) (read_curves_as_ok ceil (read_curve_closed ceil))
           (canonicalize_closed ceil)).
Qed.

Lemma parse_closed : forall ceil, AsLibParseSpec.parse_contract_as SEGS as_asan ceil.
Proof.
  intros ceil.
  exact (parse_as_ok ceil (imemset976_asan ceil) (gettag_as_ok ceil) (read_curve_closed ceil) (imemcpy32_asan ceil) (xyzd50_as_ok ceil)
           (read_a2b_closed ceil) (read_b2a_closed ceil)).
Qed.

Lemma parse0_closed : forall ceil, AsLibFuzzA.parse0_contract ceil.
Proof.
  intros ceil sp prio P fs ch FPI regs mem rom ret Hra Hret PRE.
  exact (parse0_ok ceil (imemset976_asan ceil) (gettag_as_ok ceil) (read_curve_closed ceil) (imemcpy32_asan ceil) (xyzd50_as_ok ceil)
           (read_a2b_closed ceil) (read_b2a_closed ceil) sp prio P fs ch FPI regs mem rom ret Hra Hret PRE).
Qed.

Theorem as_fuzz_closed : as_fuzz_contract SEGS asan_abi.
Proof.
  exact (as_fuzz_ok parse_closed parse0_closed getidx_as_ok rte_as_ok stkmalloc5_asan stkfree5_asan setsh00_asan setshf8_asan).
Qed.
