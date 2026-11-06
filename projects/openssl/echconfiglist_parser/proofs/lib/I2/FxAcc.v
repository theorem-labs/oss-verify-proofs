(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition exec_addr (i : instr) (c : core) : word :=
  match i with
  | Load _ _ _ rs1 imm | FLoad _ _ rs1 imm => bv_add (rget c rs1) (sext 64 imm)
  | Store _ rs1 _ imm | FStore _ rs1 _ imm => bv_add (rget c rs1) (sext 64 imm)
  | Lr _ _ _ _ rs1 | Sc _ _ _ _ rs1 _ => rget c rs1
  | Amo _ _ _ _ _ rs1 _ => rget c rs1
  | _ => w0
  end.

(* [comment removed for export] *)
Definition lz_core (ms : machine_state) : core :=
  {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms;
     c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |}.

(* [comment removed for export] *)
Definition exec_nbytes (i : instr) : nat :=
  match i with
  | Load msz _ _ _ _ | Store msz _ _ _ =>
      match msz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end
  | Lr wd _ _ _ _ | Sc wd _ _ _ _ _ | Amo _ wd _ _ _ _ _ =>
      match wd with AW => 4 | AD => 8 end
  | FLoad fmt _ _ _ | FStore fmt _ _ _ =>
      match fmt with FMT_S => 4 | FMT_D => 8 end
  | _ => 0
  end%nat.

(* [comment removed for export] *)
Inductive acc_in (S : word -> nat -> Prop) : eff -> Prop :=
| ai_done : forall c, acc_in S (EDone c)
| ai_illegal : forall c, acc_in S (EIllegal c)
| ai_defined_illegal : forall c, acc_in S (EDefinedIllegal c)
| ai_ecall : forall c, acc_in S (EEcall c)
| ai_ebreak : forall c, acc_in S (EEbreak c)
| ai_fault : forall c, acc_in S (EFault c)
| ai_load : forall n a k, S a (width_bytes n) -> (forall v, acc_in S (k v)) -> acc_in S (ELoad n a k)
| ai_store : forall n a v k, S a (width_bytes n) -> acc_in S k -> acc_in S (EStore n a v k).

Ltac acc_in_tac :=
  repeat first
    [ apply ai_done | apply ai_illegal | apply ai_defined_illegal | apply ai_ecall
    | apply ai_ebreak | apply ai_fault
    | apply ai_load; [split; reflexivity | intros ?]
    | apply ai_store; [split; reflexivity |]
    | match goal with
      | |- acc_in _ (if ?x then _ else _) => destruct x
      | |- acc_in _ (match ?x with _ => _ end) => destruct x
      | |- acc_in _ ((match ?x with _ => _ end) _) => destruct x
      | |- acc_in _ (?f (match ?x with _ => _ end)) => destruct x
      | |- acc_in _ (?f (match ?x with _ => _ end) _) => destruct x
      end ].

Theorem exec_acc_in : forall sz i c,
  acc_in (fun a n => a = exec_addr i c /\ n = exec_nbytes i) (exec sz i c).
Proof.
  intros sz i c.
  destruct i; cbn [exec exec_addr exec_nbytes]; unfold load_val, store_val, exec_csr; cbv zeta; acc_in_tac.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_acc_in : forall S t, acc_in S t -> forall m report,
  interp_eff_accesses segs t m = MachineOk report ->
  Forall (fun r : word * nat => S (fst r) (snd r)) (@accessed_ranges _ report).
Proof.
  intros S t Ht. induction Ht as [c | c | c | c | c | c | n a k HS Hk IH | n a v k HS Hk IH];
    intros m report H; cbn [interp_eff_accesses] in H; try discriminate H.
  - inversion H; subst. constructor.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs |]; [| discriminate H].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m)
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [accessed_ranges]. constructor; [exact HS | exact (IH _ m r0 E)].
  - destruct (store_ok segs m a (width_bytes n)); [| discriminate H].
    destruct (interp_eff_accesses segs k
                (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [accessed_ranges]. constructor; [exact HS | exact (IH _ r0 E)].
Qed.

(* [comment removed for export] *)
Theorem step_accesses_exact : forall ms w i isz report,
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, isz) ->
  step_accesses segs ms = MachineOk report ->
  Forall (fun r : word * nat => fst r = exec_addr i (lz_core ms) /\ snd r = exec_nbytes i)
         (@accessed_ranges _ report).
Proof.
  intros ms w i isz report Hf He Hd H. unfold step_accesses in H. rewrite Hf in H.
  unfold decode_exec_accesses in H. rewrite He, Hd in H. fold (lz_core ms) in H.
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 isz) i (lz_core ms)) (ms_mem ms))
    as [r0 | |] eqn:E; try discriminate H.
  pose proof (interp_acc_in _ _ (exec_acc_in (Z_to_bv 64 isz) i (lz_core ms)) _ _ E) as HF.
  destruct (@access_value _ r0) as [c m']. inversion H; subst. cbn [accessed_ranges]. exact HF.
Qed.

(* [comment removed for export] *)
Theorem step_accesses_sc_fail : forall ms w wd x y rd rs1 rs2 isz report,
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Sc wd x y rd rs1 rs2, isz) ->
  amo_aligned wd (rget (lz_core ms) rs1) = true ->
  match ms_resv ms with
  | Some r => Z.eqb (bv_unsigned r) (bv_unsigned (rget (lz_core ms) rs1))
  | None => false
  end = false ->
  step_accesses segs ms = MachineOk report ->
  @accessed_ranges _ report = [].
Proof.
  intros ms w wd x y rd rs1 rs2 isz report Hf He Hd Hal Hres H.
  unfold step_accesses in H. rewrite Hf in H.
  unfold decode_exec_accesses in H. rewrite He, Hd in H. fold (lz_core ms) in H.
  cbn [exec] in H. cbv zeta in H. rewrite Hal in H. cbn [negb] in H.
  change (c_resv (lz_core ms)) with (ms_resv ms) in H. rewrite Hres in H.
  cbn [interp_eff_accesses] in H. inversion H; subst. reflexivity.
Qed.

End WithSegs.

