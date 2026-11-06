(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec FP.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.A17 Require Import FrmExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition frm_word (w : bv 32) : bool :=
  is_ecall w || match decode_any w with Some (i, _) => frm_safe i | None => true end.

Lemma decode_exec_frm : forall segs st w r, frm_word w = true ->
  decode_exec_accesses segs st w = MachineOk r -> frm0 (ms_fcsr st) -> frm0 (ms_fcsr (access_value _ r)).
Proof.
  intros segs st w r Hw H H0. unfold decode_exec_accesses in H. unfold frm_word in Hw.
  destruct (is_ecall w); [injection H as <-; exact H0|]. cbn [orb] in Hw.
  destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
  destruct (interp_eff_accesses segs _ _) as [rep| |] eqn:E; try discriminate.
  assert (HF : frm0 (c_fcsr (fst (access_value _ rep)))).
  { apply (interp_eff_all (fun c' => frm0 (c_fcsr c')) segs _ _ rep E). apply exec_frm; [exact Hw | exact H0]. }
  destruct (access_value _ rep) as [c m'] eqn:AV. injection H as <-. cbn [access_value ms_fcsr].
  exact HF.
Qed.

(* [comment removed for export] *)
Lemma find_segment_in : forall segs a n seg, find_segment segs a n = Some seg ->
  In seg segs /\ Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction segs as [|s rest IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|]. cbv zeta in H.
  match type of H with context [if ?b then _ else _] => destruct b eqn:E end.
  - injection H as <-. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2. split; [left; reflexivity | lia].
  - destruct (IH a n seg H) as (H1 & H2 & H3). split; [right; exact H1 | lia].
Qed.

Definition no_wx (segs : list Segment) : bool := forallb (fun s => negb (seg_executable s && seg_writable s)) segs.

Lemma code_read_ov_no_wx : forall segs m a n, no_wx segs = true -> code_read_ov segs m a n = None.
Proof.
  intros segs m a n Hn. unfold code_read_ov. destruct (find_segment _ _ _) as [seg|] eqn:F; [|reflexivity].
  destruct (find_segment_in _ _ _ _ F) as [Hin _]. unfold no_wx in Hn. rewrite forallb_forall in Hn.
  pose proof (Hn seg Hin) as Hs. apply negb_true_iff in Hs. rewrite Hs. reflexivity.
Qed.

Lemma fetch_word_ov_no_wx : forall segs m a, no_wx segs = true -> fetch_word_ov segs m a = None.
Proof.
  intros segs m a Hn. unfold fetch_word_ov. rewrite code_read_ov_no_wx by exact Hn.
  destruct (negb _); reflexivity.
Qed.

Lemma fetch_tail_any_no_wx : forall segs m a, no_wx segs = true -> fetch_tail_any segs m a = fetch_tail segs a.
Proof.
  intros segs m a Hn.
  assert (HH : forall b, fetch_half_any segs m b = fetch_half segs b).
  { intros b. unfold fetch_half_any, fetch_half_ov. rewrite code_read_ov_no_wx by exact Hn.
    destruct (fetch_half segs b); reflexivity. }
  unfold fetch_tail_any, fetch_tail. rewrite !HH. reflexivity.
Qed.

Lemma fetch_failure_not_ok : forall segs m a st, fetch_failure segs m a <> MachineOk st.
Proof.
  intros segs m a st. unfold fetch_failure. destruct (negb _); [discriminate|].
  destruct (_ || _)%bool; discriminate.
Qed.

(* [comment removed for export] *)
Definition fetch_frm_at (segs : list Segment) (a : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 a) with
  | Some w => frm_word w
  | None => match fetch_tail segs (Z_to_bv 64 a) with Some w => frm_word w | None => true end
  end.

Fixpoint range_frm_ok (segs : list Segment) (a : Z) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => if fetch_frm_at segs a then range_frm_ok segs (a + 2) k' else false
  end.

Lemma range_frm_ok_at : forall segs k a j, range_frm_ok segs a k = true -> (j < k)%nat ->
  fetch_frm_at segs (a + 2 * Z.of_nat j) = true.
Proof.
  induction k as [|k IH]; intros a j H Hj; [lia|]. cbn [range_frm_ok] in H.
  destruct (fetch_frm_at segs a) eqn:E; [|discriminate].
  destruct j as [|j]. { replace (a + 2 * Z.of_nat 0) with a by lia. exact E. }
  replace (a + 2 * Z.of_nat (S j)) with ((a + 2) + 2 * Z.of_nat j) by lia. apply IH; [exact H | lia].
Qed.

(* [comment removed for export] *)
Definition seg_frm_ok (segs : list Segment) (s : Segment) : bool :=
  if seg_executable s then
    if Z.even (Z.of_N (seg_base s)) then range_frm_ok segs (Z.of_N (seg_base s)) (Z.to_nat ((Z.of_N (seg_size s) + 1) / 2))
    else false
  else true.

(* [comment removed for export] *)
Definition rom_frm_ok (segs : list Segment) : bool := no_wx segs && forallb (seg_frm_ok segs) segs.

Lemma rom_frm_at : forall segs (a : word) seg, rom_frm_ok segs = true -> In seg segs -> seg_executable seg = true ->
  Z.of_N (seg_base seg) <= bv_unsigned a < Z.of_N (seg_base seg) + Z.of_N (seg_size seg) -> bv_unsigned a mod 2 = 0 ->
  fetch_frm_at segs (bv_unsigned a) = true.
Proof.
  intros segs a seg H Hin Hx Hr Ha. unfold rom_frm_ok in H. apply andb_true_iff in H as [_ H].
  rewrite forallb_forall in H. pose proof (H seg Hin) as Hs. unfold seg_frm_ok in Hs. rewrite Hx in Hs.
  destruct (Z.even (Z.of_N (seg_base seg))) eqn:He; [|discriminate]. apply Z.even_spec in He. destruct He as [b Hb].
  set (j := (bv_unsigned a - Z.of_N (seg_base seg)) / 2).
  assert (Hj : bv_unsigned a = Z.of_N (seg_base seg) + 2 * j).
  { unfold j. rewrite Hb in *. pose proof (Z.mod_pos_bound (bv_unsigned a) 2 ltac:(lia)).
    rewrite Z.mod_eq in Ha by lia. zify. Z.div_mod_to_equations. lia. }
  assert (Hj0 : 0 <= j) by (unfold j; apply Z.div_pos; lia).
  rewrite Hj. replace j with (Z.of_nat (Z.to_nat j)) by lia. apply (range_frm_ok_at _ _ _ _ Hs).
  assert (j < (Z.of_N (seg_size seg) + 1) / 2). { unfold j. Z.div_mod_to_equations. lia. }
  lia.
Qed.

Lemma fetch_word_frm : forall segs a w, rom_frm_ok segs = true -> fetch_word segs a = Some w -> frm_word w = true.
Proof.
  intros segs a w H Hf. pose proof Hf as Hf0. unfold fetch_word in Hf.
  destruct (negb (bv_unsigned a mod 2 =? 0)) eqn:Ea; [discriminate|]. apply negb_false_iff, Z.eqb_eq in Ea.
  unfold code_read in Hf. destruct (find_segment _ _ _) as [seg|] eqn:F; [|discriminate].
  destruct (find_segment_in _ _ _ _ F) as (Hin & H1 & H2).
  destruct (seg_executable seg) eqn:Ex; [|discriminate].
  pose proof (rom_frm_at segs a seg H Hin Ex ltac:(lia) Ea) as HA. unfold fetch_frm_at in HA.
  rewrite Z_to_bv_bv_unsigned, Hf0 in HA. exact HA.
Qed.

Lemma fetch_tail_frm : forall segs a w, rom_frm_ok segs = true -> fetch_word segs a = None -> fetch_tail segs a = Some w ->
  frm_word w = true.
Proof.
  intros segs a w H Hn Hf. pose proof Hf as Hf0. unfold fetch_tail in Hf.
  destruct (negb (bv_unsigned a mod 2 =? 0)) eqn:Ea; [discriminate|]. apply negb_false_iff, Z.eqb_eq in Ea.
  destruct (fetch_half segs a) as [h0|] eqn:Fh; [|discriminate]. unfold fetch_half, code_read in Fh.
  destruct (find_segment _ _ _) as [seg|] eqn:F; [|discriminate].
  destruct (find_segment_in _ _ _ _ F) as (Hin & H1 & H2).
  destruct (seg_executable seg) eqn:Ex; [|discriminate].
  pose proof (rom_frm_at segs a seg H Hin Ex ltac:(lia) Ea) as HA. unfold fetch_frm_at in HA.
  rewrite Z_to_bv_bv_unsigned, Hn, Hf0 in HA. exact HA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Runs.
Variable segs : list Segment.
Hypothesis Hrom : rom_frm_ok segs = true.

Lemma step_frm : forall st st', RiscvSemantics.step segs st = MachineOk st' -> frm0 (ms_fcsr st) -> frm0 (ms_fcsr st').
Proof using Hrom.
  intros st st' H H0. unfold RiscvSemantics.step, drop_access_report in H.
  destruct (step_accesses segs st) as [r| |] eqn:E; try discriminate. injection H as <-.
  assert (Hn : no_wx segs = true). { unfold rom_frm_ok in Hrom. apply andb_true_iff in Hrom as [X _]. exact X. }
  unfold step_accesses in E.
  destruct (fetch_word segs (ms_pc st)) as [w|] eqn:Fw.
  { exact (decode_exec_frm segs st w r (fetch_word_frm segs _ w Hrom Fw) E H0). }
  rewrite fetch_word_ov_no_wx in E by exact Hn. rewrite fetch_tail_any_no_wx in E by exact Hn.
  destruct (fetch_tail segs (ms_pc st)) as [w|] eqn:Ft.
  { exact (decode_exec_frm segs st w r (fetch_tail_frm segs _ w Hrom Fw Ft) E H0). }
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) as [st1| |] eqn:Ff; try discriminate.
  exfalso. exact (fetch_failure_not_ok _ _ _ _ Ff).
Qed.

Lemma mstep_frm : forall ms ms', mstep segs ms ms' -> frm0 (ms_fcsr ms) -> frm0 (ms_fcsr ms').
Proof using Hrom. intros ms ms' [_ H] H0. exact (step_frm ms ms' H H0). Qed.

Lemma msteps_frm : forall ms ms', msteps segs ms ms' -> frm0 (ms_fcsr ms) -> frm0 (ms_fcsr ms').
Proof using Hrom.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 H1 _ IH]; intros H0; [exact H0|]. exact (IH (mstep_frm ms ms1 H1 H0)).
Qed.

(* [comment removed for export] *)
Lemma evt_frm0 : forall (Q : machine_state -> Prop) ms, evt segs Q ms -> frm0 (ms_fcsr ms) ->
  evt segs (fun ms' => Q ms' /\ frm0 (ms_fcsr ms')) ms.
Proof using Hrom.
  intros Q ms (ms' & Hr & HQ) H0. exists ms'. split; [exact Hr|]. split; [exact HQ | exact (msteps_frm ms ms' Hr H0)].
Qed.

End Runs.
