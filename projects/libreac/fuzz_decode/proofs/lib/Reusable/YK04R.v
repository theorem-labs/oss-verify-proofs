(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: kit companion of YK04.v (target-independent; copy with the module path changed).
   The converse of YK04.step_accesses_restrict: a full step whose access ranges avoid H is the same step on the
   restricted state. With it, a footprint run (fsteps, the kit form of Lib/ExecF.v mstepsF) whose footprint avoids H
   is a run of the restricted state, which YA0n.SRr_msteps lifts into a world walk (YA0nR.v). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK0i YK11 YK04.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma ranges_avoid_hd : forall H a n l, ranges_avoid H ((a, n) :: l) -> range_avoids H a n.
Proof. intros H a n l Hr. apply Hr. left. reflexivity. Qed.

Lemma ranges_avoid_tl : forall H x l, ranges_avoid H (x :: l) -> ranges_avoid H l.
Proof. intros H x l Hr a n Hin. apply Hr. right. exact Hin. Qed.

Section d.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma interp_eff_accesses_restrict_conv : forall t m c mf' rs,
  interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, mf') rs) ->
  ranges_avoid H rs ->
  interp_eff_accesses segs t (mrestrict H m) = MachineOk (@mkAccessReport _ (c, mrestrict H mf') rs).
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c mf' rs Hi Hrs; cbn [interp_eff_accesses] in Hi |- *; try discriminate.
  - injection Hi as <- <- <-. reflexivity.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:Hrd; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m)
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    pose proof (ranges_avoid_hd H a (width_bytes n) rs1 Hrs) as Hav.
    rewrite (ov_read_bytes_mrestrict_eq segs H (width_bytes n) m a Hav), Hrd.
    rewrite (IH _ m c1 m1 rs1 Hk (ranges_avoid_tl H _ rs1 Hrs)). reflexivity.
  - destruct (store_ok segs m a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    pose proof (ranges_avoid_hd H a (width_bytes n) rs1 Hrs) as Hav.
    rewrite (store_ok_mrestrict_eq segs H (width_bytes n) m a Hav), Hso.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict H (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      by (rewrite Hlen; exact Hav).
    rewrite (IH _ c1 m1 rs1 Hk (ranges_avoid_tl H _ rs1 Hrs)). reflexivity.
Qed.

Lemma decode_exec_accesses_restrict_conv : forall ms w ms' rs,
  decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ ms' rs) ->
  ranges_avoid H rs ->
  decode_exec_accesses segs (restrict H ms) w = MachineOk (@mkAccessReport _ (restrict H ms') rs).
Proof.
  intros ms w ms' rs Hd Hrs. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-. reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    destruct (interp_eff_accesses segs
      (exec (Z_to_bv 64 isz) i
        {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
           c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
           c_resv := ms_resv ms |})
      (ms_mem ms)) as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict].
    rewrite (interp_eff_accesses_restrict_conv _ _ c1 m1 rs1 Hint Hrs).
    reflexivity.
Qed.

(* A full step whose access ranges avoid H is a step of the restricted state, with the same report. *)
Theorem step_accesses_restrict_conv : forall ms ms' rs,
  step_accesses segs ms = MachineOk (@mkAccessReport _ ms' rs) ->
  ranges_avoid H rs ->
  step_accesses segs (restrict H ms) = MachineOk (@mkAccessReport _ (restrict H ms') rs).
Proof.
  intros ms ms' rs Hs Hrs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc. cbn [ms_mem restrict].
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict by assumption.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict_conv ms w ms' rs Hs Hrs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict_conv ms w ms' rs Hs Hrs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict_conv ms w ms' rs Hs Hrs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
    || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
       | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
       | None => false end); discriminate.
Qed.

(* The step keeps every hidden byte: YK04.step_accesses_restrict on the restricted step, and determinism. *)
Corollary step_accesses_avoid_keeps_hidden : forall ms ms' rs,
  step_accesses segs ms = MachineOk (@mkAccessReport _ ms' rs) ->
  ranges_avoid H rs ->
  ms' = unrestrict H (ms_mem ms) (restrict H ms').
Proof.
  intros ms ms' rs Hs Hrs.
  pose proof (step_accesses_restrict_conv ms ms' rs Hs Hrs) as Hr.
  destruct (step_accesses_restrict segs H HH Hwx ms (restrict H ms') rs Hr) as (Hfull & _ & _).
  rewrite Hs in Hfull. injection Hfull as E. exact E.
Qed.
End d.

Section f.
Variable segs : list Segment.

(* The footprint run: a step with no pending service call whose every access (address, width) lies in RNG.
   The same predicate as Lib/ExecF.v mstepF / mstepsF, where acc_in RNG acc := RNG (bv_unsigned (fst acc)) (snd acc). *)
Definition fstep (RNG : Z -> nat -> Prop) (ms ms' : machine_state) : Prop :=
  ms_svc_pending ms = None /\
  exists accs, step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' accs)
          /\ Forall (fun acc => RNG (bv_unsigned (fst acc)) (snd acc)) accs.

Inductive fsteps (RNG : Z -> nat -> Prop) : machine_state -> machine_state -> Prop :=
| fsteps_refl : forall ms, fsteps RNG ms ms
| fsteps_cons : forall ms ms1 ms2, fstep RNG ms ms1 -> fsteps RNG ms1 ms2 -> fsteps RNG ms ms2.

(* RNG avoids H: every footprint entry is a range of visible bytes. *)
Definition fp_avoids (H : word -> bool) (RNG : Z -> nat -> Prop) : Prop :=
  forall (a : word) (n : nat), RNG (bv_unsigned a) n -> range_avoids H a n.

Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Lemma ranges_avoid_of_fp : forall RNG accs,
  fp_avoids H RNG -> Forall (fun acc => RNG (bv_unsigned (fst acc)) (snd acc)) accs -> ranges_avoid H accs.
Proof.
  intros RNG accs Hfp HF a n Hin.
  apply Hfp. exact (proj1 (Forall_forall _ accs) HF (a, n) Hin).
Qed.

Lemma munrestrict_agree : forall (full full' m : word -> option byte),
  (forall x, H x = true -> full' x = full x) -> munrestrict H full' m = munrestrict H full m.
Proof.
  intros full full' m Hag. apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x) eqn:Hx; [exact (Hag x Hx) | reflexivity].
Qed.

Theorem fsteps_restrict : forall RNG ms ms',
  fsteps RNG ms ms' -> fp_avoids H RNG ->
  msteps segs (restrict H ms) (restrict H ms')
  /\ ms' = unrestrict H (ms_mem ms) (restrict H ms').
Proof.
  intros RNG ms ms' Hrun Hfp. induction Hrun as [ms | ms ms1 ms2 [Hsvc (accs & Hs & HF)] _ IH].
  - split; [apply mst_refl | symmetry; apply unrestrict_restrict].
  - pose proof (ranges_avoid_of_fp RNG accs Hfp HF) as Hrs.
    destruct IH as [Hrest Heq2].
    pose proof (step_accesses_avoid_keeps_hidden segs H HH Hwx ms ms1 accs Hs Hrs) as Heq1.
    split.
    + eapply mst_step; [exact Hsvc | | exact Hrest].
      unfold RiscvSemantics.step, drop_access_report.
      rewrite (step_accesses_restrict_conv segs H HH Hwx ms ms1 accs Hs Hrs). reflexivity.
    + rewrite Heq2 at 1. unfold unrestrict. f_equal.
      apply munrestrict_agree. intros x Hx.
      rewrite Heq1. cbn [ms_mem unrestrict]. unfold munrestrict. rewrite Hx. reflexivity.
Qed.
End f.
