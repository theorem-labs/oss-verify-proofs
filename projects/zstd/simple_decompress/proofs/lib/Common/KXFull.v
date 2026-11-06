(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mkRf (f : nat -> word) : bvmap 5 word :=
  mkR (f 1%nat) (f 2%nat) (f 3%nat) (f 4%nat) (f 5%nat) (f 6%nat) (f 7%nat) (f 8%nat) (f 9%nat) (f 10%nat)
      (f 11%nat) (f 12%nat) (f 13%nat) (f 14%nat) (f 15%nat) (f 16%nat) (f 17%nat) (f 18%nat) (f 19%nat) (f 20%nat)
      (f 21%nat) (f 22%nat) (f 23%nat) (f 24%nat) (f 25%nat) (f 26%nat) (f 27%nat) (f 28%nat) (f 29%nat) (f 30%nat) (f 31%nat).

(* [comment removed for export] *)
Definition mkRl (l : list word) : bvmap 5 word := mkRf (fun n => nth (pred n) l w0).

Lemma mkRl_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 =
  mkRl [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31].
Proof. reflexivity. Qed.

Definition rfull (R : bvmap 5 word) : Prop := exists f, R = mkRf f.

Lemma rfull_mkRf : forall f, rfull (mkRf f). Proof. intro f. exists f. reflexivity. Qed.
Lemma rfull_mkRl : forall l, rfull (mkRl l). Proof. intro l. apply rfull_mkRf. Qed.

Definition regn (n : nat) : reg := Z_to_bv 5 (Z.of_nat n).

Lemma rfull_canon : forall R, rfull R -> R = mkRf (fun n => reg_get R (regn n)).
Proof. intros R [f ->]. reflexivity. Qed.

Lemma reg_cases : forall k : reg, exists n, (n < 32)%nat /\ k = regn n.
Proof.
  intro k. pose proof (bv_unsigned_in_range 5 k) as H. unfold bv_modulus in H. cbn in H.
  exists (Z.to_nat (bv_unsigned k)). split; [lia|].
  unfold regn. rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
  unfold bv_modulus. cbn. lia.
Qed.

Lemma rfull_set : forall R (k : reg) v, is_x0 k = false -> rfull R -> rfull (bvmap_set k v R).
Proof.
  intros R k v Hk [f ->]. destruct (reg_cases k) as (n & Hn & ->).
  destruct n as [|n]; [vm_compute in Hk; discriminate Hk|].
  let rec go i :=
    lazymatch i with
    | 32%nat => exfalso; lia
    | _ => destruct n as [|n]; [exists (fun j => if Nat.eqb j i then v else f j); reflexivity | go (S i)]
    end in go 1%nat.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cfull (c : core) : Prop := rfull (c_regs c).

Inductive eff_full : eff -> Prop :=
| FDone : forall c, cfull c -> eff_full (EDone c)
| FIllegal : forall c, eff_full (EIllegal c)
| FDefIllegal : forall c, eff_full (EDefinedIllegal c)
| FEcall : forall c, eff_full (EEcall c)
| FEbreak : forall c, eff_full (EEbreak c)
| FFault : forall c, eff_full (EFault c)
| FLoad : forall n a k, (forall v, eff_full (k v)) -> eff_full (ELoad n a k)
| FStore : forall n a v k, eff_full k -> eff_full (EStore n a v k).

Local Ltac core_tac := unfold cfull, rset, fset, with_pc, with_fcsr, with_resv, with_regs, with_fregs, accrue, fwrite, inval_resv in *; simpl in *.

Lemma cfull_rset : forall r v c, cfull c -> cfull (rset r v c).
Proof.
  intros r v [R F p f s] H. unfold cfull, rset in *. destruct (is_x0 r) eqn:E; [exact H|].
  unfold with_regs. simpl in *. apply rfull_set; assumption.
Qed.
Lemma cfull_fset : forall r v c, cfull c -> cfull (fset r v c).
Proof. intros r v [R F p f s] H. core_tac. exact H. Qed.
Lemma cfull_with_pc : forall v c, cfull c -> cfull (with_pc v c).
Proof. intros v [R F p f s] H. core_tac. exact H. Qed.
Lemma cfull_with_fcsr : forall v c, cfull c -> cfull (with_fcsr v c).
Proof. intros v [R F p f s] H. core_tac. exact H. Qed.
Lemma cfull_with_resv : forall v c, cfull c -> cfull (with_resv v c).
Proof. intros v [R F p f s] H. core_tac. exact H. Qed.
Lemma cfull_accrue : forall fl c, cfull c -> cfull (accrue fl c).
Proof. intros fl [R F p f s] H. core_tac. exact H. Qed.
Lemma cfull_fwrite : forall fmt r v c, cfull c -> cfull (fwrite fmt r v c).
Proof. intros fmt r v c H. unfold fwrite. destruct fmt; apply cfull_fset; exact H. Qed.
Lemma cfull_inval_resv : forall a c, cfull c -> cfull (inval_resv a c).
Proof.
  intros a [R F p f s] H. unfold cfull, inval_resv, with_resv in *. simpl in *.
  destruct s as [r|]; [destruct (Z.eqb _ _)|]; simpl; exact H.
Qed.
Lemma cfull_if : forall (b : bool) c1 c2, cfull c1 -> cfull c2 -> cfull (if b then c1 else c2).
Proof. intros [] c1 c2 H1 H2; assumption. Qed.

Local Ltac solve_core H :=
  repeat first [ apply cfull_rset | apply cfull_fset | apply cfull_with_pc
               | apply cfull_with_fcsr | apply cfull_with_resv | apply cfull_accrue
               | apply cfull_fwrite | apply cfull_inval_resv | apply cfull_if
               | match goal with |- cfull (match ?X with _ => _ end) => destruct X end ];
  exact H.

Local Ltac full_struct H :=
  repeat first
    [ apply FDone; solve_core H
    | apply FIllegal | apply FDefIllegal | apply FEcall | apply FEbreak | apply FFault
    | apply FLoad; intros ?
    | apply FStore
    | match goal with |- eff_full (match ?X with _ => _ end) => destruct X end
    | match goal with |- eff_full (match ?X with _ => _ end _) => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec load_val store_val exec_csr].

Lemma exec_full : forall sz i c, cfull c -> eff_full (exec sz i c).
Proof.
  intros sz i c H. destruct i; unfold_exec; full_struct H.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_full : forall t, eff_full t -> forall m r,
  interp_eff_accesses segs t m = MachineOk r -> cfull (fst (@access_value _ r)).
Proof.
  induction 1 as [c Hc| | | | | |n a k Hk IH|n a v k Hk IH]; intros m r Hr; cbn [interp_eff_accesses] in Hr; try discriminate.
  - injection Hr as <-. exact Hc.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:E; try discriminate.
    injection Hr as <-. cbn. exact (IH _ _ _ E).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [rep| |] eqn:E; try discriminate.
    injection Hr as <-. cbn. exact (IH _ _ E).
Qed.

(* [comment removed for export] *)
Lemma interp_mem_inv : forall t m r,
  interp_eff_accesses segs t m = MachineOk r -> mem_inv segs m -> mem_inv segs (snd (@access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r Hr MI; cbn [interp_eff_accesses] in Hr; try discriminate.
  - injection Hr as <-. exact MI.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [rep| |] eqn:E; try discriminate.
    injection Hr as <-. cbn. exact (IH _ _ _ E MI).
  - destruct (store_ok segs m a (width_bytes n)) eqn:Hok; [|discriminate].
    destruct (interp_eff_accesses segs k _) as [rep| |] eqn:E; try discriminate.
    injection Hr as <-. cbn. apply (IH _ _ E). apply mem_inv_store; [exact MI|].
    rewrite length_Z_to_le_bytes. exact Hok.
Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mszb (sz : msize) : nat := match sz with SZ1 => 1 | SZ2 => 2 | SZ4 => 4 | SZ8 => 8 end.

Definition rgetR (R : bvmap 5 word) (r : reg) : word := if is_x0 r then w0 else reg_get R r.

(* [comment removed for export] *)
Definition acc_of (i : instr) (R : bvmap 5 word) : option (list (word * nat)) :=
  match i with
  | Load msz _ _ rs1 imm => Some [(rgetR R rs1 + sext 64 imm, mszb msz)]
  | Store msz rs1 _ imm => Some [(rgetR R rs1 + sext 64 imm, mszb msz)]
  | Lui _ _ | Auipc _ _ | Jal _ _ | Jalr _ _ _ | Branch _ _ _ _ | OpImm _ _ _ _ | ShiftImm _ _ _ _ | Op _ _ _ _
  | OpImm32 _ _ _ | ShiftImm32 _ _ _ _ | Op32 _ _ _ _ | Mul _ _ _ _ | Mul32 _ _ _ _ => Some []
  | _ => None
  end.

Section WithSegs2.
Variable segs : list Segment.

Lemma exec_acc : forall sz i R F pc fc rv m r l,
  acc_of i R = Some l ->
  interp_eff_accesses segs (exec sz i (Core R F pc fc rv)) m = MachineOk r ->
  @accessed_ranges _ r = l.
Proof.
  intros sz i R F pc fc rv m r l Ha Hr.
  destruct i; cbn [acc_of] in Ha; try discriminate Ha; injection Ha as <-;
    cbv beta iota zeta delta [exec load_val store_val] in Hr;
    try (cbn [interp_eff_accesses] in Hr; injection Hr as <-; reflexivity).
  - (* [comment removed for export] *)
    destruct sz0; cbn [interp_eff_accesses] in Hr;
      (destruct (ov_read_bytes segs m _ _) as [bs|]; [|discriminate Hr]);
      cbn [interp_eff_accesses] in Hr; injection Hr as <-; reflexivity.
  - (* [comment removed for export] *)
    destruct sz0; cbn [interp_eff_accesses] in Hr;
      (destruct (store_ok segs m _ _); [|discriminate Hr]);
      cbn [interp_eff_accesses] in Hr; injection Hr as <-; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_acc_full : forall R F pc fc rv m ro w i ms' l,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  rfull R -> acc_of i R = Some l ->
  RiscvSemantics.step segs (MS R F pc fc rv m ro) = MachineOk ms' ->
  rfull (ms_regs ms') /\
  RiscvSemantics.step_accesses segs (MS R F pc fc rv m ro) = MachineOk (@mkAccessReport machine_state ms' l) /\
  (mem_inv segs m -> mem_inv segs (ms_mem ms')).
Proof.
  intros R F pc fc rv m ro w i ms' l Hf He Hd HR Ha Hs.
  change (RiscvSemantics.step segs (MS R F pc fc rv m ro)) with
    (drop_access_report (RiscvSemantics.step_accesses segs (MS R F pc fc rv m ro))) in Hs.
  rewrite (stepF_gen segs R F pc fc rv m ro w i 4%Z Hf He Hd) in *.
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 4) i (Core R F pc fc rv)) m) as [rep| |] eqn:E;
    cbn [lift_resultF drop_access_report] in Hs; try discriminate Hs.
  pose proof (interp_full segs _ (exec_full (Z_to_bv 64 4) i (Core R F pc fc rv) HR) m rep E) as HF.
  pose proof (exec_acc _ _ _ _ _ _ _ _ _ _ Ha E) as HA.
  pose proof (interp_mem_inv segs _ m rep E) as HM.
  destruct rep as [[c m'] accs]. cbn [lift_resultF drop_access_report access_value accessed_ranges fst snd] in *.
  injection Hs as <-. subst accs. split; [exact HF |]. split; [reflexivity | exact HM].
Qed.

End WithSegs2.
