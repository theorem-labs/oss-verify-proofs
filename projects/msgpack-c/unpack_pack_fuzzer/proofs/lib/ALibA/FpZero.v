(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Definition fp_zero (RNG : footprint) : footprint := fun b j => RNG b j \/ j = 0%nat.

Lemma rng_fp_zero : forall RNG a, 0 <= a <= 2 ^ 64 -> rng (fp_zero RNG) a 0.
Proof.
  intros RNG a Ha. split; [lia|]. split; [lia|]. intros b j Hb Hj. right. lia.
Qed.

Lemma rng_fp_zero_mono : forall RNG lo len, rng RNG lo len -> rng (fp_zero RNG) lo len.
Proof. intros RNG lo len (A & B & H). split; [exact A|]. split; [exact B|]. intros b j Hb Hj. left. apply H; assumption. Qed.

Definition acc_pos (a : word) (n : nat) : Prop := (1 <= n)%nat.
Fixpoint eff_pos (t : eff) : Prop :=
  match t with
  | ELoad n a k => (1 <= width_bytes n)%nat /\ forall v, eff_pos (k v)
  | EStore n a v k => (1 <= width_bytes n)%nat /\ eff_pos k
  | _ => True
  end.

Lemma exec_csr_pos : forall op rd operand writes csr c, eff_pos (exec_csr op rd operand writes csr c).
Proof.
  intros. unfold exec_csr.
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x
         | |- context [if ?x then _ else _] => destruct x
         end; cbn; auto.
Qed.

Lemma exec_pos : forall sz i c, eff_pos (exec sz i c).
Proof.
  intros sz i c. destruct i; cbn [exec];
    try exact I;
    try (apply exec_csr_pos).
  all: repeat match goal with
         | |- eff_pos (exec_csr _ _ _ _ _ _) => apply exec_csr_pos
         | |- context [match ?x with _ => _ end] => destruct x
         | |- context [if ?x then _ else _] => destruct x
         end; cbn; auto.
  all: try (unfold load_val, store_val; repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; cbn; repeat split; intros; auto; try lia).
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_pos : forall t m report, eff_pos t -> interp_eff_accesses segs t m = MachineOk report ->
  Forall (fun an : word * nat => (1 <= snd an)%nat) (@accessed_ranges _ report).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m report HP H; cbn in H; try discriminate.
  - injection H as <-. constructor.
  - destruct HP as [Pn Pk]. destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn. constructor; [exact Pn| exact (IH _ m r (Pk _) Hr)].
  - destruct HP as [Pn Pk]. destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| |] eqn:Hr; try discriminate.
    injection H as <-. cbn. constructor; [exact Pn| exact (IH _ r Pk Hr)].
Qed.

Lemma decode_exec_pos : forall ms w report, decode_exec_accesses segs ms w = MachineOk report ->
  Forall (fun an : word * nat => (1 <= snd an)%nat) (@accessed_ranges _ report).
Proof.
  intros ms w report H. unfold decode_exec_accesses in H.
  destruct (is_ecall w); [injection H as <-; constructor|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate H].
  destruct (interp_eff_accesses segs _ (ms_mem ms)) as [r| |] eqn:Hr; try discriminate.
  pose proof (interp_pos _ _ _ (exec_pos _ i _) Hr) as P.
  destruct r as [[c' m'] acc]. cbn in H. injection H as <-. exact P.
Qed.

Lemma step_accesses_pos : forall ms report, step_accesses segs ms = MachineOk report ->
  Forall (fun an : word * nat => (1 <= snd an)%nat) (@accessed_ranges _ report).
Proof.
  intros ms report H. unfold step_accesses in H.
  repeat match type of H with
         | match ?x with _ => _ end = _ => destruct x eqn:?
         end; try discriminate H; try (eapply decode_exec_pos; eassumption).
  injection H as <-. constructor.
Qed.

Lemma mstepF_fp_zero : forall RNG ms ms', mstepF segs (fp_zero RNG) ms ms' -> mstepF segs RNG ms ms'.
Proof.
  intros RNG ms ms' (SV & accs & SA & FA). split; [exact SV|]. exists accs. split; [exact SA|].
  pose proof (step_accesses_pos ms _ SA) as P. cbn [accessed_ranges] in P.
  rewrite Forall_forall in *. intros an Hin. destruct (FA an Hin) as [X|X]; [exact X|]. specialize (P an Hin). lia.
Qed.

Lemma mstepsF_fp_zero : forall RNG ms ms', mstepsF segs (fp_zero RNG) ms ms' -> mstepsF segs RNG ms ms'.
Proof. intros RNG ms ms' H. induction H; [constructor| econstructor; [apply mstepF_fp_zero; eassumption| assumption]]. Qed.

Theorem evtF_fp_zero : forall RNG Q ms, evtF segs (fp_zero RNG) Q ms -> evtF segs RNG Q ms.
Proof. intros RNG Q ms (ms' & S & HQ). exists ms'. split; [apply mstepsF_fp_zero; exact S| exact HQ]. Qed.
End WithSegs.
