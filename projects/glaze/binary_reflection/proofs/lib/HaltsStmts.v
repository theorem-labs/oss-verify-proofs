(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by gabelogan195, 2026-11: made from TopHalts.v of this proof library: its exit-code lemmas are restated for the statuses 0 and 2 instead of AnyExit.codes, and its root-fact definitions and four halts_*_of theorems are replaced by the four halting statements of Statements.v (forced_only_cfg, with the budget premise), proved from the root facts of DrvRootP, UbDrvRootP, AsBaseA and BoBaseB; ec_* is renamed hc_* and spec_of_exit_codes spec_of_halt_codes, the Zify setting at line 15 of TopHalts.v is left out, and Classical_Prop is imported; lines 29-51 of projects/skcms/iccprofile_info/proofs/lib/Halts/HaltsBridge.v at commit f92feaf8b7 (refusal_decided_classic, decided_from_classic, must_exit_in_at_cfg_mono_classic) are taken unchanged. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(** The four halting statements of this harness, in the form [Statements.v]
    states them.

    Each build's root fact ([P_root_f], [U_root_f], [A_root_f], [B_root_f] of
    [TopHalts]) is a realization of the spec [spec_of] at 16 GiB under the
    configuration [CfgStep.kit_cfg], in which a memory request is refused
    only when forced and any other call may fail.
    [ShapeHalts.must_exit_in_of_root_f] turns it
    into a must-exit fact for any set of statuses the spec's exits lie in;
    the spec exits only with 0 or 2, and never dies by a signal.  The
    statement's own configuration, [forced_only_cfg], refuses less, so every
    execution under it is one under [kit_cfg] and the fact carries over
    ([must_exit_in_at_cfg_mono]).  The budget the root facts are proved at is
    the statement's own, so its budget premise is not used. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
Require OSSVerify.glaze.binary_reflection.images.Plain OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Require OSSVerify.glaze.binary_reflection.Statements.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.TopHalts OSSVerify.Proofs.glaze.binary_reflection.lib.DrvRootP OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvRootP OSSVerify.Proofs.glaze.binary_reflection.lib.AsBaseA OSSVerify.Proofs.glaze.binary_reflection.lib.BoBaseB. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRoot OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ShapeHalts OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.Spec4KF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(** ** The spec exits only with status 0 or 2 *)

(** The statuses [Statements.plain_halts] and its siblings allow, as
    [Core.Shapes.Exits.ok_or_refused] spells them. *)
Definition HALT_CODES : list word := [Z_to_bv 64 0; Z_to_bv 64 2].

Lemma halt_code_0 : In (exit_code 0) HALT_CODES.
Proof. left. reflexivity. Qed.

Lemma halt_code_2 : In (exit_code 2) HALT_CODES.
Proof. right. left. reflexivity. Qed.

Lemma hc_die : forall msg fs, exit_codes_in HALT_CODES (t_die msg fs).
Proof.
  intros. unfold t_die, W. apply exit_codes_in_t_emit; [intros c f H; exfalso; exact (writes_no_exit _ _ _ _ H) |].
  apply exit_codes_in_t_exit. exact halt_code_2.
Qed.

Lemma hc_success : forall calls fs, exit_codes_in HALT_CODES (t_success calls fs).
Proof.
  intros. unfold t_success, W. apply exit_codes_in_t_emit; [intros c f H; exfalso; exact (writes_no_exit _ _ _ _ H) |].
  apply exit_codes_in_t_exit. exact halt_code_0.
Qed.

Lemma hc_payload : forall cm pl calls fs, exit_codes_in HALT_CODES (t_payload cm pl calls fs).
Proof. intros. unfold t_payload. apply hc_success. Qed.

Lemma hc_body : forall data fs, exit_codes_in HALT_CODES (t_body data fs).
Proof.
  intros. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length data))%Z; [apply hc_die|].
  destruct (Z.of_nat (length data) <? 6)%Z; [apply hc_die|].
  destruct (Z.of_nat (length data) <? 6 + hdr_cfglen data)%Z; [apply hc_die|].
  apply hc_payload.
Qed.

Lemma hc_opened : forall data fs, exit_codes_in HALT_CODES (t_opened data fs).
Proof. intros. unfold t_opened. apply hc_body. Qed.

Lemma hc_opened_dir : forall path fs, exit_codes_in HALT_CODES (t_opened_dir path fs).
Proof. intros. unfold t_opened_dir. apply hc_die. Qed.

Lemma hc_spec : forall argv fs0, exit_codes_in HALT_CODES (spec argv fs0).
Proof.
  intros argv fs0. unfold spec.
  destruct argv as [|a0 [|path [|x l]]]; try apply hc_die.
  destruct (4096 <=? length path)%nat; [apply hc_die|].
  destruct (path_eqb path []); [apply hc_die|].
  destruct (path_is_dirref path); [apply exit_codes_in_t_alt2; [apply hc_die | apply hc_opened_dir]|].
  destruct (fs_lookup fs0 path); [apply exit_codes_in_t_alt2; [apply hc_die | apply hc_opened] | apply hc_die].
Qed.

Theorem spec_of_halt_codes : exit_codes_allowed HALT_CODES spec_of.
Proof. intros inp tr code fs _ H. exact (hc_spec _ _ _ _ _ H). Qed.

(** ** The refusal question, answered classically *)

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
  intros cfg i m _.
  destruct (classic (exists eff' m' evs',
              syscall_spec i m (Ok eff' m' evs')
              /\ refusal_b i m (eff_ret eff') = false)) as [H | H];
    [left; exact H | right].
  intros eff' m' evs' Hs.
  destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity | exfalso].
  apply H. exists eff', m', evs'. split; [exact Hs | exact E].
Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof. intros cfg segs c tr c' x8 _ _. apply refusal_decided_classic. Qed.

Lemma must_exit_in_at_cfg_mono_classic : forall cfg1 cfg2 segs S c,
  cfg_le cfg1 cfg2 ->
  must_exit_in_at_cfg cfg2 segs S c ->
  must_exit_in_at_cfg cfg1 segs S c.
Proof.
  intros cfg1 cfg2 segs S c Hle H.
  exact (must_exit_in_at_cfg_mono cfg1 cfg2 segs S c Hle (decided_from_classic cfg1 segs c) H).
Qed.

(** ** From a root fact to the statement's configuration *)

Lemma must_exit_forced_of_root_f : forall segs pc ph,
  root_obligation_core_f (mkImage segs pc ph) source_alloc_limit spec_of ->
  forall en inp,
    valid_entry (mkImage segs pc ph) en inp ->
    valid_input inp ->
    must_exit_in_scfg forced_only_cfg HALT_CODES (mkImage segs pc ph) source_alloc_limit en inp.
Proof.
  intros segs pc ph Hroot en inp Hen Hinp.
  pose proof (must_exit_in_of_root_f HALT_CODES (mkImage segs pc ph) source_alloc_limit spec_of en inp
                Hroot spec_of_kill_free spec_of_halt_codes Hen Hinp) as H.
  destruct en as [sp brk0 mb rnd].
  cbn [must_exit_in_scfg] in H |- *.
  exact (must_exit_in_at_cfg_mono_classic forced_only_cfg _ segs HALT_CODES _ (forced_only_cfg_least _) H).
Qed.

(** ** The four halting statements *)

Theorem plain_halts : OSSVerify.glaze.binary_reflection.Statements.plain_halts.
Proof.
  intros en inp Hen Hinp _.
  exact (must_exit_forced_of_root_f
           OSSVerify.glaze.binary_reflection.images.Plain.M.loaded_segments
           OSSVerify.glaze.binary_reflection.images.Plain.M.init_pc
           OSSVerify.glaze.binary_reflection.images.Plain.M.phdrs
           OSSVerify.Proofs.glaze.binary_reflection.lib.DrvRootP.P_root_f_holds en inp Hen Hinp).
Qed.

Theorem ubsan_halts : OSSVerify.glaze.binary_reflection.Statements.ubsan_halts.
Proof.
  intros en inp Hen Hinp _.
  exact (must_exit_forced_of_root_f
           OSSVerify.glaze.binary_reflection.images.Ubsan.M.loaded_segments
           OSSVerify.glaze.binary_reflection.images.Ubsan.M.init_pc
           OSSVerify.glaze.binary_reflection.images.Ubsan.M.phdrs
           OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvRootP.U_root_f_holds en inp Hen Hinp).
Qed.

Theorem asan_halts : OSSVerify.glaze.binary_reflection.Statements.asan_halts.
Proof.
  intros en inp Hen Hinp _.
  exact (must_exit_forced_of_root_f
           OSSVerify.glaze.binary_reflection.images.Asan.M.loaded_segments
           OSSVerify.glaze.binary_reflection.images.Asan.M.init_pc
           OSSVerify.glaze.binary_reflection.images.Asan.M.phdrs
           OSSVerify.Proofs.glaze.binary_reflection.lib.AsBaseA.A_root_f_closed en inp Hen Hinp).
Qed.

Theorem asan_ubsan_halts : OSSVerify.glaze.binary_reflection.Statements.asan_ubsan_halts.
Proof.
  intros en inp Hen Hinp _.
  exact (must_exit_forced_of_root_f
           OSSVerify.glaze.binary_reflection.images.AsanUbsan.M.loaded_segments
           OSSVerify.glaze.binary_reflection.images.AsanUbsan.M.init_pc
           OSSVerify.glaze.binary_reflection.images.AsanUbsan.M.phdrs
           OSSVerify.Proofs.glaze.binary_reflection.lib.BoBaseB.B_root_f_closed en inp Hen Hinp).
Qed.
