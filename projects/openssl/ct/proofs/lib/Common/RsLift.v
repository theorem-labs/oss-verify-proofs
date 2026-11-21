(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 from openssl/pem's Common/RsLift.v (whose segs ++ tail and step-transfer lemmas come from coturn/FuzzStunClient's Common/StoreOk.v), with the module paths of this unit, this unit's two-constructor ITree, an induction over the tail in place of one over its Forall premise, and the arms of this unit's getid and config-open nodes; it carries the proof library's walks over the binary's own segments to the run's segment list run_segments, the binary's segments followed by the vDSO pair. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Vdso Run.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* ========================================================================= *)
(* Segment lists of the form segs ++ tail (copied from the coturn library's   *)
(* Common/StoreOk.v transfer section).  [find_segment] returns the FIRST      *)
(* covering segment, so a range the binary's own segments cover reads the    *)
(* same over segs ++ tail.                                                    *)
(* ========================================================================= *)

Lemma find_segment_app : forall segs tail addr n,
  find_segment (segs ++ tail) addr n
  = match find_segment segs addr n with
    | Some s => Some s
    | None => find_segment tail addr n
    end.
Proof.
  induction segs as [|seg rest IH]; intros tail addr n; [reflexivity|].
  cbn [find_segment app].
  destruct (Z.leb (Z.of_N (seg_base seg)) addr
            && Z.leb (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool;
    [reflexivity | apply IH].
Qed.

Lemma find_segment_app_prefix : forall segs tail addr n,
  find_segment segs addr n <> None ->
  find_segment (segs ++ tail) addr n = find_segment segs addr n.
Proof.
  intros segs tail addr n Hhit. rewrite find_segment_app.
  destruct (find_segment segs addr n); [reflexivity | congruence].
Qed.

Lemma find_segment_run_segments : forall segs inp (sp mbase : word) addr n,
  find_segment segs addr n <> None ->
  find_segment (run_segments segs inp sp mbase) addr n = find_segment segs addr n.
Proof.
  intros segs inp sp mbase addr n Hhit.
  unfold run_segments. apply find_segment_app_prefix. exact Hhit.
Qed.

(* A range that misses every tail segment finds over segs ++ tail exactly what it finds over segs. *)
Lemma find_segment_app_miss : forall segs tail addr n,
  find_segment tail addr n = None ->
  find_segment (segs ++ tail) addr n = find_segment segs addr n.
Proof.
  intros segs tail addr n Hmiss. rewrite find_segment_app.
  destruct (find_segment segs addr n); [reflexivity | exact Hmiss].
Qed.

(* Disjointness from each tail segment is a miss. *)
Lemma find_segment_disjoint : forall tail addr n,
  1 <= n ->
  Forall (fun s => addr + n <= Z.of_N (seg_base s)
                   \/ Z.of_N (seg_base s) + Z.of_N (seg_size s) <= addr) tail ->
  find_segment tail addr n = None.
Proof.
  intros tail addr n Hn Hall.
  induction tail as [|s rest IH]; [reflexivity|].
  pose proof (Forall_inv Hall) as Hs. pose proof (Forall_inv_tail Hall) as Hrest. cbv beta in Hs.
  cbn [find_segment].
  destruct Hs as [Hs|Hs].
  - rewrite (proj2 (Z.leb_gt (Z.of_N (seg_base s)) addr)) by lia. exact (IH Hrest).
  - rewrite (proj2 (Z.leb_gt (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))) by lia.
    destruct (Z.leb (Z.of_N (seg_base s)) addr); exact (IH Hrest).
Qed.

Lemma memory_read_app_some : forall segs tail addr n bs,
  memory_read segs addr n = Some bs ->
  memory_read (segs ++ tail) addr n = Some bs.
Proof.
  intros segs tail addr n bs H. unfold memory_read in *. rewrite find_segment_app. revert H.
  destruct (find_segment segs (bv_unsigned addr) (Z.of_N n)); intros H; [exact H | discriminate H].
Qed.

Lemma memory_read_app_miss : forall segs tail addr n,
  find_segment tail (bv_unsigned addr) (Z.of_N n) = None ->
  memory_read (segs ++ tail) addr n = memory_read segs addr n.
Proof.
  intros segs tail addr n Hmiss. unfold memory_read.
  rewrite (find_segment_app_miss segs tail _ _ Hmiss). reflexivity.
Qed.

Lemma seg_rom_app_some : forall segs tail a b,
  seg_rom segs a = Some b -> seg_rom (segs ++ tail) a = Some b.
Proof.
  intros segs tail a b H. unfold seg_rom in *. revert H.
  destruct (memory_read segs a 1) as [bs|] eqn:E; intros H; [|discriminate H].
  rewrite (memory_read_app_some segs tail a 1 bs E). exact H.
Qed.

Lemma seg_rom_app_miss : forall segs tail a,
  find_segment tail (bv_unsigned a) 1 = None ->
  seg_rom (segs ++ tail) a = seg_rom segs a.
Proof.
  intros segs tail a Hmiss. unfold seg_rom.
  rewrite (memory_read_app_miss segs tail a 1 Hmiss). reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* A machine step that succeeds over segs succeeds the same way over segs ++  *)
(* tail, when the tail segments are neither executable nor writable (the vDSO  *)
(* pair is "r--"): fetches and the writable view are EQUAL over both lists,    *)
(* and a load that reads over segs reads the same bytes over segs ++ tail.     *)
(* ------------------------------------------------------------------------- *)

Definition tail_inert (tail : list Segment) : Prop :=
  Forall (fun s => seg_executable s = false /\ seg_writable s = false) tail.

Lemma find_segment_in : forall l addr n s, find_segment l addr n = Some s -> In s l.
Proof.
  induction l as [|s0 rest IH]; intros addr n s H; [discriminate H|].
  cbn [find_segment] in H.
  destruct (Z.leb (Z.of_N (seg_base s0)) addr
            && Z.leb (addr + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
  - injection H as <-. left. reflexivity.
  - right. exact (IH addr n s H).
Qed.

Section StepTransfer.
Variables (segs tail : list Segment).
Hypothesis Hin : tail_inert tail.

Lemma tail_hit_inert : forall addr n s, find_segment tail addr n = Some s ->
  seg_executable s = false /\ seg_writable s = false.
Proof.
  intros addr n s H. unfold tail_inert in Hin. rewrite Forall_forall in Hin.
  exact (Hin s (find_segment_in tail addr n s H)).
Qed.

Lemma code_read_app : forall a n, code_read (segs ++ tail) a n = code_read segs a n.
Proof.
  intros a n. unfold code_read. rewrite find_segment_app.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)); [reflexivity|].
  destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
  destruct (tail_hit_inert _ _ _ E) as [Hx _]. rewrite Hx. reflexivity.
Qed.

Lemma code_read_ov_app : forall m a n, code_read_ov (segs ++ tail) m a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov. rewrite find_segment_app.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)); [reflexivity|].
  destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
  destruct (tail_hit_inert _ _ _ E) as [Hx _]. rewrite Hx. reflexivity.
Qed.

Lemma fetch_word_app : forall a, fetch_word (segs ++ tail) a = fetch_word segs a.
Proof. intros a. unfold fetch_word. rewrite code_read_app. reflexivity. Qed.

Lemma fetch_word_ov_app : forall m a, fetch_word_ov (segs ++ tail) m a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_app. reflexivity. Qed.

Lemma fetch_half_app : forall a, fetch_half (segs ++ tail) a = fetch_half segs a.
Proof. intros a. unfold fetch_half. rewrite code_read_app. reflexivity. Qed.

Lemma fetch_half_any_app : forall m a, fetch_half_any (segs ++ tail) m a = fetch_half_any segs m a.
Proof.
  intros m a. unfold fetch_half_any, fetch_half_ov.
  rewrite fetch_half_app, code_read_ov_app. reflexivity.
Qed.

Lemma fetch_tail_any_app : forall m a, fetch_tail_any (segs ++ tail) m a = fetch_tail_any segs m a.
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_app. reflexivity. Qed.

Lemma wview_app : forall m a, wview (segs ++ tail) m a = wview segs m a.
Proof.
  intros m a. unfold wview. destruct (m a); [reflexivity|].
  rewrite find_segment_app.
  destruct (find_segment segs (bv_unsigned a) 1); [reflexivity|].
  destruct (find_segment tail (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
  destruct (tail_hit_inert _ _ _ E) as [_ Hw]. rewrite Hw. reflexivity.
Qed.

Lemma store_ok_app : forall n m a, store_ok (segs ++ tail) m a n = store_ok segs m a n.
Proof.
  induction n as [|n IH]; intros m a; [reflexivity|].
  cbn [store_ok]. rewrite wview_app.
  destruct (wview segs m a); [apply IH | reflexivity].
Qed.

Lemma ov_read_bytes_app_some : forall n m a bs,
  ov_read_bytes segs m a n = Some bs -> ov_read_bytes (segs ++ tail) m a n = Some bs.
Proof.
  induction n as [|n IH]; intros m a bs H; [exact H|].
  cbn [ov_read_bytes] in H |- *.
  assert (Hb : forall b, (match m a with
                         | Some b => Some b
                         | None => match memory_read segs a 1 with Some (b :: _) => Some b | _ => None end
                         end) = Some b ->
                        (match m a with
                         | Some b => Some b
                         | None => match memory_read (segs ++ tail) a 1 with Some (b :: _) => Some b | _ => None end
                         end) = Some b).
  { intros b0 E. destruct (m a) as [b1|]; [exact E|].
    destruct (memory_read segs a 1) as [l|] eqn:Er; [|discriminate E].
    rewrite (memory_read_app_some segs tail a 1 l Er). exact E. }
  destruct (match m a with
            | Some b => Some b
            | None => match memory_read segs a 1 with Some (b :: _) => Some b | _ => None end
            end) as [b|] eqn:E0; [|discriminate H].
  rewrite (Hb b eq_refl).
  match type of H with context [ov_read_bytes segs m ?a1 n] =>
    destruct (ov_read_bytes segs m a1 n) as [rest|] eqn:E; [|discriminate H];
    rewrite (IH m a1 rest E) end.
  exact H.
Qed.

Lemma interp_eff_accesses_app_ok : forall t m r,
  interp_eff_accesses segs t m = MachineOk r ->
  interp_eff_accesses (segs ++ tail) t m = MachineOk r.
Proof.
  induction t as [c|x|x|x|x|x|n a k IHk|n a v k IHk]; intros m r Hr;
    cbn [interp_eff_accesses] in Hr |- *; try discriminate Hr; try exact Hr.
  - (* ELoad *)
    destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:E.
    + rewrite (ov_read_bytes_app_some _ _ _ _ E).
      destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:Ei;
        try discriminate Hr.
      rewrite (IHk _ _ _ Ei). exact Hr.
    + destruct (range_meets_vvar segs a (width_bytes n)); discriminate Hr.
  - (* EStore *)
    rewrite store_ok_app.
    destruct (store_ok segs m a (width_bytes n)); [|discriminate Hr].
    destruct (interp_eff_accesses segs k
                (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [rep| |] eqn:Ei;
      try discriminate Hr.
    rewrite (IHk _ _ Ei). exact Hr.
Qed.

Lemma decode_exec_accesses_app_ok : forall st w r,
  decode_exec_accesses segs st w = MachineOk r ->
  decode_exec_accesses (segs ++ tail) st w = MachineOk r.
Proof.
  intros st w r. unfold decode_exec_accesses.
  destruct (is_ecall w); [intro H; exact H|].
  destruct (decode_any w) as [[i isz]|]; [|intro H; exact H].
  match goal with |- context [interp_eff_accesses segs ?tt ?mm] =>
    destruct (interp_eff_accesses segs tt mm) as [rep| |] eqn:Ei end;
    intros H; try discriminate H.
  rewrite (interp_eff_accesses_app_ok _ _ _ Ei). exact H.
Qed.

Lemma fetch_failure_not_ok : forall m a st, fetch_failure segs m a <> MachineOk st.
Proof.
  intros m a st. unfold fetch_failure. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Lemma step_accesses_app_ok : forall st r,
  step_accesses segs st = MachineOk r -> step_accesses (segs ++ tail) st = MachineOk r.
Proof.
  intros st r. unfold step_accesses.
  rewrite fetch_word_app, fetch_word_ov_app, fetch_tail_any_app.
  destruct (fetch_word segs (ms_pc st)); [apply decode_exec_accesses_app_ok|].
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)); [apply decode_exec_accesses_app_ok|].
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)); [apply decode_exec_accesses_app_ok|].
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) as [x| |] eqn:Ef; intros H;
    [exfalso; exact (fetch_failure_not_ok _ _ _ Ef) | discriminate H | discriminate H].
Qed.

Lemma step_app_ok : forall st st',
  RiscvSemantics.step segs st = MachineOk st' -> RiscvSemantics.step (segs ++ tail) st = MachineOk st'.
Proof.
  intros st st'. unfold RiscvSemantics.step, drop_access_report.
  destruct (step_accesses segs st) as [rep| |] eqn:E; intros H; try discriminate H.
  rewrite (step_accesses_app_ok _ _ E). exact H.
Qed.

Lemma mi_account_step_app_ok : forall ms model p,
  mi_account_step segs ms model = MachineOk p ->
  mi_account_step (segs ++ tail) ms model = MachineOk p.
Proof.
  intros ms model p. unfold mi_account_step.
  destruct (RiscvSemantics.step_accesses segs ms) as [rep| |] eqn:E; intros H; try discriminate H.
  rewrite (step_accesses_app_ok _ _ E). exact H.
Qed.

End StepTransfer.

(* ------------------------------------------------------------------------- *)
(* The vDSO pair is "r--": neither executable nor writable.                  *)
(* ------------------------------------------------------------------------- *)

Local Transparent vdso_segments.

Lemma vdso_segments_inert : forall kb (sp mbase : word), tail_inert (vdso_segments kb sp mbase).
Proof.
  intros kb sp mbase. unfold tail_inert, vdso_segments. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply Forall_nil|].
  apply Forall_cons; [split; reflexivity|].
  apply Forall_cons; [split; reflexivity|].
  apply Forall_nil.
Qed.

(* [Run.segments_reserved]'s [filter] is stdpp's ([Riscv.Prelude] exports
   stdpp, which shadows [List.filter] in [Run]), so the drop lemma is stated
   over stdpp's [filter] with its [Decision] instance. *)
Lemma filter_app_drop : forall (A : Type) (P : A -> Prop) (HP : forall x, Decision (P x)) (l V : list A),
  Forall (fun x => ~ P x) V -> filter P (l ++ V) = filter P l.
Proof.
  intros A P HP l V HV. induction l as [|x l IH]; cbn [app].
  - induction HV as [|y V Hy _ IHV]; [reflexivity|]. cbn.
    destruct (decide (P y)); [contradiction|exact IHV].
  - cbn. destruct (decide (P x)); [f_equal; exact IH|exact IH].
Qed.

(* The reservations the model's ledger starts from ignore the kernel's own
   mappings ([Run.segments_reserved] filters [seg_kernel_map]), so the run's
   list reserves what the binary's list reserves. *)
Lemma segments_reserved_run_segments : forall segs inp (sp mbase : word),
  segments_reserved (run_segments segs inp sp mbase) = segments_reserved segs.
Proof.
  intros segs inp sp mbase. unfold segments_reserved, run_segments. f_equal.
  apply filter_app_drop.
  unfold vdso_segments. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end; [apply Forall_nil|].
  repeat apply Forall_cons; try apply Forall_nil;
    intro Hc; cbn in Hc; first [exact Hc | discriminate Hc | destruct Hc].
Qed.

Global Opaque vdso_segments.

(* ------------------------------------------------------------------------- *)
(* The ROM a run's machine state carries.  [Run.init_machine_state] reads   *)
(* the run's list, so a run's states carry [seg_rom (segs ++ tail)] where   *)
(* the walks' states carry [seg_rom segs].  A machine step never reads      *)
(* [ms_rom] and copies it through, so the walks transfer state by state.    *)
(* ------------------------------------------------------------------------- *)

Definition with_rom (ms : machine_state) (r : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := r |}.

Definition rs_ms (segs tail : list Segment) (ms : machine_state) : machine_state :=
  with_rom ms (seg_rom (segs ++ tail)).

Lemma decode_exec_accesses_with_rom : forall S st r w,
  decode_exec_accesses S (with_rom st r) w =
  match decode_exec_accesses S st w with
  | MachineOk rep => MachineOk (@mkAccessReport _ (with_rom (@access_value _ rep) r) (@accessed_ranges _ rep))
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.
Proof.
  intros S st r w. unfold decode_exec_accesses.
  destruct (is_ecall w); [reflexivity|].
  destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); reflexivity].
  cbn [with_rom ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem].
  destruct (interp_eff_accesses S _ _) as [rep| |]; [|reflexivity|reflexivity].
  destruct rep as [[c m'] rg]. reflexivity.
Qed.

Lemma step_accesses_with_rom : forall S st r,
  step_accesses S (with_rom st r) =
  match step_accesses S st with
  | MachineOk rep => MachineOk (@mkAccessReport _ (with_rom (@access_value _ rep) r) (@accessed_ranges _ rep))
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.
Proof.
  intros S st r. unfold step_accesses.
  change (ms_pc (with_rom st r)) with (ms_pc st).
  change (ms_mem (with_rom st r)) with (ms_mem st).
  destruct (fetch_word S (ms_pc st)); [apply decode_exec_accesses_with_rom|].
  destruct (fetch_word_ov S (ms_mem st) (ms_pc st)); [apply decode_exec_accesses_with_rom|].
  destruct (fetch_tail_any S (ms_mem st) (ms_pc st)); [apply decode_exec_accesses_with_rom|].
  destruct (fetch_failure S (ms_mem st) (ms_pc st)) as [x| |] eqn:Ef;
    [exfalso; exact (fetch_failure_not_ok S _ _ _ Ef) | reflexivity | reflexivity].
Qed.

Lemma step_with_rom : forall S st st' r,
  RiscvSemantics.step S st = MachineOk st' ->
  RiscvSemantics.step S (with_rom st r) = MachineOk (with_rom st' r).
Proof.
  intros S st st' r H. unfold RiscvSemantics.step, drop_access_report in *.
  rewrite step_accesses_with_rom.
  destruct (step_accesses S st) as [rep| |]; [|discriminate H|discriminate H].
  injection H as <-. reflexivity.
Qed.

Lemma nret_rs : forall segs tail ms eff,
  nret (rs_ms segs tail ms) eff = rs_ms segs tail (nret ms eff).
Proof. intros segs tail [] eff. reflexivity. Qed.

Section WalkRs.
Variables (segs tail : list Segment).
Hypothesis Hin : tail_inert tail.

Lemma mstep_rs : forall ms ms', mstep segs ms ms' ->
  mstep (segs ++ tail) (rs_ms segs tail ms) (rs_ms segs tail ms').
Proof.
  intros ms ms' [Hsvc Hst]. split; [exact Hsvc|].
  apply step_with_rom. exact (step_app_ok segs tail Hin ms ms' Hst).
Qed.

Lemma msteps_rs : forall ms ms', Exec.msteps segs ms ms' ->
  Exec.msteps (segs ++ tail) (rs_ms segs tail ms) (rs_ms segs tail ms').
Proof.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 H1 _ IH]; [apply msteps_refl|].
  eapply msteps_cons; [exact (mstep_rs ms ms1 H1)| exact IH].
Qed.

Lemma evt_rs : forall (P : machine_state -> Prop) ms, evt segs P ms ->
  evt (segs ++ tail) (fun x => exists y, x = rs_ms segs tail y /\ P y) (rs_ms segs tail ms).
Proof.
  intros P ms (ms' & Hm & HP). exists (rs_ms segs tail ms'). split; [exact (msteps_rs ms ms' Hm)|].
  exists ms'. split; [reflexivity| exact HP].
Qed.

(* Every node of a walk over segs is a node over segs ++ tail at the state with
   the run's ROM, and each ITree node's continuation follows. *)
Section ImplRs.
Variable nd : Type.
Variables (at1 at2 : nd -> machine_state -> Prop).
Hypothesis Hat : forall n ms, at1 n ms -> at2 n (rs_ms segs tail ms).

Lemma impl_rs : forall R (t : itree nd R) (Q : R -> machine_state -> Prop) ms,
  impl segs at1 t Q ms ->
  impl (segs ++ tail) at2 t (fun r x => exists y, x = rs_ms segs tail y /\ Q r y) (rs_ms segs tail ms).
Proof.
  (* this tree's [ITree.itree] has two constructors, [Ret] and [Vis] (no choice node) *)
  intros R t. induction t as [r|n k IH]; intros Q ms H; cbn [ITree.impl] in H |- *.
  - exact (evt_rs _ ms H).
  - eapply evt_mono; [exact (evt_rs _ ms H)|]. intros x (y & -> & Hy1 & Hy2).
    split; [exact (Hat n y Hy1)|]. intros rsp. rewrite nret_rs. exact (IH rsp Q (nret y rsp) (Hy2 rsp)).
Qed.
End ImplRs.

(* ------------------------------------------------------------------------- *)
(* The library's syscall nodes over segs ++ tail.                            *)
(*                                                                           *)
(* Per-node side condition (option (b) of the run-segments repair): every   *)
(* a node's syscall reads that fails over segs must miss the tail.  Every    *)
(* read premise of [Nodes.at_node] is a SUCCESSFUL read ([bytes_at]: each    *)
(* byte reads [Some]), and a read that succeeds over segs reads the same    *)
(* bytes over segs ++ tail ([seg_rom_app_some]); the writable view is equal  *)
(* over both lists ([wview_app]); the node's [ms_rom] premise is the run's   *)
(* ROM by construction.  So every node's side condition is discharged from  *)
(* its own premises, and [at_node] holds over the run's list.               *)
(* ------------------------------------------------------------------------- *)

Lemma mrd_app_some : forall m a b,
  mrd segs m a = Some b -> mrd (segs ++ tail) m a = Some b.
Proof.
  intros m a b H. unfold mrd in *. destruct (m a); [exact H|].
  exact (seg_rom_app_some segs tail a b H).
Qed.

Lemma bytes_at_app : forall m a bs, bytes_at segs m a bs -> bytes_at (segs ++ tail) m a bs.
Proof.
  intros m a bs (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (H2 i Hi) as E.
  destruct (nth_error bs i) as [b|] eqn:En; [exact (mrd_app_some _ _ _ E)|].
  apply nth_error_None in En. lia.
Qed.

Lemma wr_at_app : forall m a n, wr_at segs m a n -> wr_at (segs ++ tail) m a n.
Proof.
  intros m a n (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (wview_app segs tail Hin). exact (H2 i Hi).
Qed.

Lemma at_node_rs : forall n ms, at_node segs n ms -> at_node (segs ++ tail) n (rs_ms segs tail ms).
Proof.
  intros n [regs fregs pcv svc resv fcsr mem rom] H. unfold rs_ms, with_rom.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  destruct n as [fd bufs|path|fd buf count|fd|fd req| |code|req|a l p f|a l|a l p|k|];
    cbn [at_node] in H |- *; try exact H.
  - (* writev: the iovec array and every buffer read successfully *)
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8 & iovs & Hb & Hf).
    refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj eq_refl (conj H8
              (ex_intro _ iovs (conj (bytes_at_app _ _ _ Hb) _)))))))))).
    eapply Forall2_impl; [|exact Hf]. intros iov bs (A & B & C).
    exact (conj A (conj B (bytes_at_app _ _ _ C))).
  - (* openat: the path and its terminator read successfully *)
    destruct H as (H1 & H2 & H3 & H4 & _ & H6 & Hb).
    exact (conj H1 (conj H2 (conj H3 (conj H4 (conj eq_refl (conj H6 (bytes_at_app _ _ _ Hb))))))).
  - (* read: the buffer is writable, and the writable view is equal *)
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hw).
    exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (wr_at_app _ _ _ Hw)))))))).
  - (* openat of the config path: the path and its terminator read successfully, below TASK_SIZE *)
    destruct H as (H1 & H2 & H3 & _ & H5 & Hb).
    exact (conj H1 (conj H2 (conj H3 (conj eq_refl (conj H5 (bytes_at_app _ _ _ Hb)))))).
Qed.

Theorem impl_rs_nodes : forall R (t : itree node R) (Q : R -> machine_state -> Prop) ms,
  impl segs (at_node segs) t Q ms ->
  impl (segs ++ tail) (at_node (segs ++ tail)) t
       (fun r x => exists y, x = rs_ms segs tail y /\ Q r y) (rs_ms segs tail ms).
Proof. exact (impl_rs node (at_node segs) (at_node (segs ++ tail)) at_node_rs). Qed.

End WalkRs.
