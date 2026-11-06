(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import PropExec MState Mem Exec Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition shaped (R : bvmap 5 word) : Prop :=
  exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word,
    R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

Lemma shaped_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  shaped (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof. intros. unfold shaped. do 31 eexists. reflexivity. Qed.

(* [comment removed for export] *)
Lemma reg_cases : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)).
  pose proof (bv_unsigned_in_range 5 r) as H. unfold bv_modulus in H. cbn in H.
  split; [| lia]. rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma shaped_set : forall (R : bvmap 5 word) (r : reg) (v : word),
  is_x0 r = false -> shaped R -> shaped (bvmap_set r v R).
Proof.
  intros R r v H0 (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  destruct (reg_cases r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [ first [ discriminate H0
    | lazymatch goal with |- shaped ?t => let t' := eval cbv in t in change (shaped t') end; unfold shaped; do 31 eexists; reflexivity ] |]).
  exfalso; lia.
Qed.

(* [comment removed for export] *)
Definition cshaped (c : core) : Prop := shaped (c_regs c).

Fixpoint eff_shaped (t : eff) : Prop :=
  match t with
  | EDone c => cshaped c
  | ELoad n a k => forall v, eff_shaped (k v)
  | EStore n a v k => eff_shaped k
  | _ => True
  end.
Lemma ShDone : forall c, cshaped c -> eff_shaped (EDone c). Proof. intros c H; exact H. Qed.
Lemma ShIllegal : forall c, eff_shaped (EIllegal c). Proof. intros; exact I. Qed.
Lemma ShDefinedIllegal : forall c, eff_shaped (EDefinedIllegal c). Proof. intros; exact I. Qed.
Lemma ShEcall : forall c, eff_shaped (EEcall c). Proof. intros; exact I. Qed.
Lemma ShEbreak : forall c, eff_shaped (EEbreak c). Proof. intros; exact I. Qed.
Lemma ShFault : forall c, eff_shaped (EFault c). Proof. intros; exact I. Qed.
Lemma ShLoad : forall n a k, (forall v, eff_shaped (k v)) -> eff_shaped (ELoad n a k). Proof. intros n a k H; exact H. Qed.
Lemma ShStore : forall n a v k, eff_shaped k -> eff_shaped (EStore n a v k). Proof. intros n a v k H; exact H. Qed.

Local Ltac core_tac :=
  unfold cshaped, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv, accrue, fwrite, inval_resv in *; simpl in *.

Lemma cshaped_rset : forall r v c, cshaped c -> cshaped (rset r v c).
Proof. intros r v [R F p f s] H. core_tac. destruct (is_x0 r) eqn:E; simpl; [exact H| apply shaped_set; assumption]. Qed.
Lemma cshaped_fset : forall r v c, cshaped c -> cshaped (fset r v c).
Proof. intros r v [R F p f s] H. core_tac. exact H. Qed.
Lemma cshaped_with_pc : forall v c, cshaped c -> cshaped (with_pc v c).
Proof. intros v [R F p f s] H. core_tac. exact H. Qed.
Lemma cshaped_with_fcsr : forall v c, cshaped c -> cshaped (with_fcsr v c).
Proof. intros v [R F p f s] H. core_tac. exact H. Qed.
Lemma cshaped_with_resv : forall v c, cshaped c -> cshaped (with_resv v c).
Proof. intros v [R F p f s] H. core_tac. exact H. Qed.
Lemma cshaped_accrue : forall fl c, cshaped c -> cshaped (accrue fl c).
Proof. intros fl [R F p f s] H. core_tac. exact H. Qed.
Lemma cshaped_fwrite : forall fmt r v c, cshaped c -> cshaped (fwrite fmt r v c).
Proof. intros fmt r v c H. destruct fmt; apply cshaped_fset; exact H. Qed.
Lemma cshaped_inval_resv : forall a c, cshaped c -> cshaped (inval_resv a c).
Proof. intros a [R F p f s] H. core_tac. destruct s as [r|]; [destruct (Z.eqb _ _)|]; simpl; exact H. Qed.
Lemma cshaped_if : forall (b : bool) c1 c2, cshaped c1 -> cshaped c2 -> cshaped (if b then c1 else c2).
Proof. intros [] c1 c2 H1 H2; assumption. Qed.

Local Ltac solve_core HR :=
  repeat first [ apply cshaped_rset | apply cshaped_fset | apply cshaped_with_pc
               | apply cshaped_with_fcsr | apply cshaped_with_resv | apply cshaped_accrue
               | apply cshaped_fwrite | apply cshaped_inval_resv | apply cshaped_if
               | match goal with |- cshaped (match ?X with _ => _ end) => destruct X end ];
  exact HR.

Local Ltac sh_struct HR :=
  repeat lazymatch goal with
  | |- eff_shaped (EDone _) => apply ShDone; solve_core HR
  | |- eff_shaped (EIllegal _) => exact I
  | |- eff_shaped (EDefinedIllegal _) => exact I
  | |- eff_shaped (EEcall _) => exact I
  | |- eff_shaped (EEbreak _) => exact I
  | |- eff_shaped (EFault _) => exact I
  | |- eff_shaped (ELoad _ _ _) => apply ShLoad; intros ?
  | |- eff_shaped (EStore _ _ _ _) => apply ShStore
  | |- eff_shaped (match ?X with _ => _ end) => destruct X
  | |- eff_shaped (match ?X with _ => _ end _) => destruct X
  end.

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_shaped : forall R F pc fc rv sz i, shaped R -> eff_shaped (exec sz i (Core R F pc fc rv)).
Proof.
  intros R F pc fc rv sz i HR.
  assert (HC : cshaped (Core R F pc fc rv)) by exact HR.
  destruct i; unfold_exec; sh_struct HC.
Qed.

(* [comment removed for export] *)
Lemma interp_acc_shaped : forall segs t m r, eff_shaped t ->
  interp_eff_accesses segs t m = MachineOk r -> cshaped (fst (@access_value _ r)).
Proof.
  intros segs t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r HS HI; cbn [interp_eff_accesses] in HI;
    try discriminate HI.
  - injection HI as <-. cbn. exact HS.
  - cbn [eff_shaped] in HS.
    destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate HI].
    destruct (interp_eff_accesses segs (k _) m) as [r'| |] eqn:E; try discriminate HI.
    injection HI as <-. cbn. eapply IH; [apply HS| exact E].
  - cbn [eff_shaped] in HS.
    destruct (store_ok segs m a (width_bytes n)); [|discriminate HI].
    destruct (interp_eff_accesses segs k _) as [r'| |] eqn:E; try discriminate HI.
    injection HI as <-. cbn. eapply IH; [exact HS| exact E].
Qed.

Lemma decode_exec_shaped : forall segs ms w r, shaped (ms_regs ms) ->
  decode_exec_accesses segs ms w = MachineOk r -> shaped (ms_regs (@access_value _ r)).
Proof.
  intros segs ms w r HR H. unfold decode_exec_accesses in H.
  destruct (is_ecall w). { injection H as <-. cbn. exact HR. }
  destruct (decode_any w) as [[i isz]|]. 2:{ destruct (is_defined_illegal w); discriminate H. }
  destruct (interp_eff_accesses segs _ (ms_mem ms)) as [rep| |] eqn:E; try discriminate H.
  pose proof (interp_acc_shaped segs _ _ _ (exec_shaped _ _ _ _ _ _ i HR) E) as HC.
  destruct (@access_value _ rep) as [c m'] eqn:EV. injection H as <-. cbn in *. exact HC.
Qed.

Theorem step_shaped : forall segs ms ms', shaped (ms_regs ms) ->
  RiscvSemantics.step segs ms = MachineOk ms' -> shaped (ms_regs ms').
Proof.
  intros segs ms ms' HR H. unfold RiscvSemantics.step, step_accesses in H.
  repeat lazymatch type of H with
  | drop_access_report (match ?X with Some w => _ | None => _ end) = _ =>
      destruct X as [w|];
      [ destruct (decode_exec_accesses segs ms w) as [r| |] eqn:E; try discriminate H;
        cbn [drop_access_report] in H; injection H as <-; eapply decode_exec_shaped; eassumption |]
  end.
  unfold fetch_failure in H. destruct (negb _); [discriminate H|]. cbv zeta in H.
  lazymatch type of H with context [if ?b then _ else _] => destruct b end; discriminate H.
Qed.

Theorem msteps_shaped : forall segs ms ms', msteps segs ms ms' -> shaped (ms_regs ms) -> shaped (ms_regs ms').
Proof.
  intros segs ms ms' H. induction H as [|ms ms1 ms2 [_ S] _ IH]; intros HR; [exact HR|].
  apply IH. eapply step_shaped; eassumption.
Qed.
