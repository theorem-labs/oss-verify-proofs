(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import PropExec MState Frame Exec RegsEquiv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition rfull (R : bvmap 5 word) : Prop :=
  exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

Lemma rfull_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  rfull (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof. intros. unfold rfull. do 31 eexists. reflexivity. Qed.

Lemma rfull_set : forall R (k : reg) v, rfull R -> is_x0 k = false -> rfull (bvmap_set k v R).
Proof.
  intros R k v (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->) Hk.
  destruct (reg_of_nat k) as (n & -> & Hn).
  do 32 (destruct n as [|n];
         [ first [ discriminate Hk
                 | unfold rfull; do 31 eexists;
                   lazymatch goal with |- ?L = _ => let L' := eval vm_compute in L in change L with L' end;
                   unfold mkR; reflexivity ] | ]).
  lia.
Qed.


Definition core_full (c : core) : Prop := rfull (c_regs c).

Inductive eff_full : eff -> Prop :=
| FullDone : forall c, core_full c -> eff_full (EDone c)
| FullIllegal : forall c, eff_full (EIllegal c)
| FullDefIllegal : forall c, eff_full (EDefinedIllegal c)
| FullEcall : forall c, eff_full (EEcall c)
| FullEbreak : forall c, eff_full (EEbreak c)
| FullFault : forall c, eff_full (EFault c)
| FullLoad : forall n a k, (forall v, eff_full (k v)) -> eff_full (ELoad n a k)
| FullStore : forall n a v k, eff_full k -> eff_full (EStore n a v k).

Local Ltac core_tac :=
  unfold core_full, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_full_rset : forall r v c, core_full c -> core_full (rset r v c).
Proof.
  intros r v [R F p f s] H. core_tac. destruct (is_x0 r) eqn:E; simpl; [exact H| apply rfull_set; assumption].
Qed.
Lemma core_full_fset : forall r v c, core_full c -> core_full (fset r v c).
Proof. intros r v [R F p f s] H. core_tac. exact H. Qed.
Lemma core_full_with_pc : forall v c, core_full c -> core_full (with_pc v c).
Proof. intros v [R F p f s] H. core_tac. exact H. Qed.
Lemma core_full_with_fcsr : forall v c, core_full c -> core_full (with_fcsr v c).
Proof. intros v [R F p f s] H. core_tac. exact H. Qed.
Lemma core_full_with_resv : forall v c, core_full c -> core_full (with_resv v c).
Proof. intros v [R F p f s] H. core_tac. exact H. Qed.
Lemma core_full_accrue : forall fl c, core_full c -> core_full (accrue fl c).
Proof. intros fl [R F p f s] H. core_tac. exact H. Qed.
Lemma core_full_fwrite : forall fmt r v c, core_full c -> core_full (fwrite fmt r v c).
Proof. intros fmt r v c H. destruct fmt; apply core_full_fset; exact H. Qed.
Lemma core_full_inval_resv : forall a c, core_full c -> core_full (inval_resv a c).
Proof.
  intros a [R F p f s] H. core_tac. destruct s as [r|]; [destruct (Z.eqb _ _)|]; simpl; exact H.
Qed.
Lemma core_full_if : forall (b : bool) c1 c2, core_full c1 -> core_full c2 -> core_full (if b then c1 else c2).
Proof. intros [] c1 c2 H1 H2; assumption. Qed.
Lemma core_full_mk : forall R F pc fc rv, rfull R -> core_full (Core R F pc fc rv).
Proof. intros. exact H. Qed.

Local Ltac solve_core HR :=
  repeat first [ apply core_full_rset | apply core_full_fset | apply core_full_with_pc
               | apply core_full_with_fcsr | apply core_full_with_resv | apply core_full_accrue
               | apply core_full_fwrite | apply core_full_inval_resv | apply core_full_if
               | match goal with |- core_full (match ?X with _ => _ end) => destruct X end ];
  apply (core_full_mk _ _ _ _ _ HR).

Local Ltac full_struct HR :=
  repeat first
    [ apply FullDone; solve_core HR
    | apply FullIllegal | apply FullDefIllegal | apply FullEcall | apply FullEbreak | apply FullFault
    | apply FullLoad; intros ?
    | apply FullStore
    | match goal with |- eff_full (match ?X with _ => _ end) => destruct X end
    | match goal with |- eff_full (match ?X with _ => _ end _) => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_full_core : forall R F pc fc rv sz i, rfull R -> eff_full (exec sz i (Core R F pc fc rv)).
Proof.
  intros R F pc fc rv sz i HR.
  destruct i; unfold_exec; full_struct HR.
Qed.


Section WithSegs.
Variable segs : list Segment.

Lemma interp_eff_accesses_full : forall t, eff_full t -> forall m,
  match interp_eff_accesses segs t m with
  | MachineOk r => core_full (fst (access_value _ r))
  | _ => True
  end.
Proof.
  intros t H. induction H; intros m; cbn [interp_eff_accesses access_value fst]; auto.
  - (* port727: a declined load is MachineUnmodeled on the vvar range at , as in Lib/RegsEquiv *)
    destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|destruct (range_meets_vvar segs a (width_bytes n)); exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [r| |]; cbn [access_value] in *; auto.
  - destruct (store_ok segs m a (width_bytes n)); [|exact I].
    specialize (IHeff_full (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [r| |]; cbn [access_value] in *; auto.
Qed.

Lemma decode_exec_accesses_full : forall ms w, rfull (ms_regs ms) ->
  match decode_exec_accesses segs ms w with
  | MachineOk r => rfull (ms_regs (access_value _ r))
  | _ => True
  end.
Proof.
  intros [R F pc svc rv fc m ro] w HR. cbn [ms_regs] in HR.
  unfold decode_exec_accesses. destruct (is_ecall w).
  - cbn. exact HR.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom].
    pose proof (interp_eff_accesses_full _ (exec_full_core R F pc fc rv (Z_to_bv 64 isz) i HR) m) as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc fc rv)) m) as [[[c m1] acc]| |]; cbn in *; auto.
Qed.

Lemma step_accesses_full : forall ms, rfull (ms_regs ms) ->
  match RiscvSemantics.step_accesses segs ms with
  | MachineOk r => rfull (ms_regs (access_value _ r))
  | _ => True
  end.
Proof.
  intros ms HR. unfold RiscvSemantics.step_accesses.
  destruct (fetch_word segs (ms_pc ms)); [apply decode_exec_accesses_full; exact HR|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)); [apply decode_exec_accesses_full; exact HR|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)); [apply decode_exec_accesses_full; exact HR|].
  unfold fetch_failure.
  (* port727: a pc in the vDSO text is MachineUnmodeled at (); split every test, as in
     Lib/RegsEquiv *)
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; exact I.
Qed.

Theorem step_rfull : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> rfull (ms_regs ms) -> rfull (ms_regs ms').
Proof.
  intros ms ms' HS HR. pose proof (step_accesses_full ms HR) as K.
  unfold RiscvSemantics.step in HS. destruct (RiscvSemantics.step_accesses segs ms) as [r| |]; cbn in HS; try discriminate.
  injection HS as <-. exact K.
Qed.

Theorem msteps_rfull : forall ms ms', msteps segs ms ms' -> rfull (ms_regs ms) -> rfull (ms_regs ms').
Proof.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 [_ HS] _ IH]; intros HR; [exact HR|].
  apply IH. exact (step_rfull _ _ HS HR).
Qed.

End WithSegs.
