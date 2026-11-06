(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import MState Frame.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import BrRegs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition rcanon (R : bvmap 5 word) : Prop := R = canon_regs R.

Lemma rcanon_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  rcanon (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof. intros. reflexivity. Qed.

Lemma rcanon_set : forall R (r : reg) v, rcanon R -> is_x0 r = false -> rcanon (bvmap_set r v R).
Proof.
  intros R r v HR Hr. unfold rcanon in *. rewrite HR. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [first [discriminate Hr | reflexivity] |]). lia.
Qed.

Definition core_canon (c : core) : Prop := rcanon (c_regs c).

Inductive eff_canon : eff -> Prop :=
| CnDone : forall c, core_canon c -> eff_canon (EDone c)
| CnIllegal : forall c, eff_canon (EIllegal c)
| CnDefIllegal : forall c, eff_canon (EDefinedIllegal c)
| CnEcall : forall c, eff_canon (EEcall c)
| CnEbreak : forall c, eff_canon (EEbreak c)
| CnFault : forall c, eff_canon (EFault c)
| CnLoad : forall n a k, (forall v, eff_canon (k v)) -> eff_canon (ELoad n a k)
| CnStore : forall n a v k, eff_canon k -> eff_canon (EStore n a v k).

Local Ltac cc_tac :=
  unfold core_canon, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
         accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_canon_rset : forall r v c, core_canon c -> core_canon (rset r v c).
Proof.
  intros r v [R F p f s] H. unfold core_canon, rset, with_regs in *; simpl in *.
  destruct (is_x0 r) eqn:E; simpl; [exact H|]. apply rcanon_set; assumption.
Qed.
Lemma core_canon_fset : forall r v c, core_canon c -> core_canon (fset r v c).
Proof. intros r v [R F p f s] H. cc_tac. exact H. Qed.
Lemma core_canon_with_pc : forall v c, core_canon c -> core_canon (with_pc v c).
Proof. intros v [R F p f s] H. cc_tac. exact H. Qed.
Lemma core_canon_with_fcsr : forall v c, core_canon c -> core_canon (with_fcsr v c).
Proof. intros v [R F p f s] H. cc_tac. exact H. Qed.
Lemma core_canon_with_resv : forall v c, core_canon c -> core_canon (with_resv v c).
Proof. intros v [R F p f s] H. cc_tac. exact H. Qed.
Lemma core_canon_accrue : forall fl c, core_canon c -> core_canon (accrue fl c).
Proof. intros fl [R F p f s] H. cc_tac. exact H. Qed.
Lemma core_canon_fwrite : forall fmt r v c, core_canon c -> core_canon (fwrite fmt r v c).
Proof. intros fmt r v c H. destruct fmt; apply core_canon_fset; exact H. Qed.
Lemma core_canon_inval_resv : forall a c, core_canon c -> core_canon (inval_resv a c).
Proof.
  intros a [R F p f s] H. cc_tac. destruct s as [r|]; [destruct (Z.eqb _ _)|]; simpl; exact H.
Qed.
Lemma core_canon_if : forall (b : bool) c1 c2, core_canon c1 -> core_canon c2 -> core_canon (if b then c1 else c2).
Proof. intros [] c1 c2 H1 H2; assumption. Qed.

Local Ltac solve_cc HR :=
  repeat first [ apply core_canon_rset | apply core_canon_fset | apply core_canon_with_pc
               | apply core_canon_with_fcsr | apply core_canon_with_resv | apply core_canon_accrue
               | apply core_canon_fwrite | apply core_canon_inval_resv | apply core_canon_if
               | match goal with |- core_canon (match ?X with _ => _ end) => destruct X end ];
  first [ exact HR | assumption ].

Local Ltac cn_struct HR :=
  repeat first
    [ apply CnDone; solve_cc HR
    | apply CnIllegal | apply CnDefIllegal | apply CnEcall | apply CnEbreak | apply CnFault
    | apply CnLoad; intros ?
    | apply CnStore
    | match goal with |- eff_canon (match ?X with _ => _ end) => destruct X end
    | match goal with |- eff_canon (match ?X with _ => _ end _) => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_canon_core : forall R F pc fc rv sz i,
  rcanon R -> eff_canon (exec sz i (Core R F pc fc rv)).
Proof.
  intros R F pc fc rv sz i HR.
  assert (HC : core_canon (Core R F pc fc rv)) by exact HR.
  destruct i; unfold_exec; cn_struct HC.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_eff_accesses_canon : forall t, eff_canon t -> forall m,
  match interp_eff_accesses segs t m with
  | MachineOk a => core_canon (fst (@access_value _ a))
  | _ => True
  end.
Proof.
  intros t H. induction H; intros m; cbn [interp_eff_accesses]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [[[c1 m1] acc1]| |]; cbn in *; exact H0.
  - destruct (store_ok segs m a (width_bytes n)); [| exact I].
    specialize (IHeff_canon (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [[[c1 m1] acc1]| |]; cbn in *; exact IHeff_canon.
Qed.

Lemma decode_exec_accesses_canon : forall ms w, rcanon (ms_regs ms) ->
  match decode_exec_accesses segs ms w with
  | MachineOk a => rcanon (ms_regs (@access_value _ a))
  | _ => True
  end.
Proof.
  intros ms w HR. destruct ms as [R F pc svc rv fc m ro]; simpl in *.
  unfold RiscvSemantics.decode_exec_accesses. destruct (is_ecall w); [exact HR|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I]. simpl.
  pose proof (interp_eff_accesses_canon _ (exec_canon_core R F pc fc rv (Z_to_bv 64 isz) i HR) m) as K.
  destruct (interp_eff_accesses segs (exec _ i (Core R F pc fc rv)) m) as [[[c m1] acc1]| |]; simpl in *; exact K.
Qed.

Lemma step_canon : forall ms ms', rcanon (ms_regs ms) -> RiscvSemantics.step segs ms = MachineOk ms' -> rcanon (ms_regs ms').
Proof.
  intros ms ms' HR Hs. unfold RiscvSemantics.step, RiscvSemantics.drop_access_report, RiscvSemantics.step_accesses, ms_pc in Hs.
  destruct (fetch_word segs (ms_pc_val ms)).
  { pose proof (decode_exec_accesses_canon ms b HR) as K.
    destruct (decode_exec_accesses segs ms b) as [a| |]; cbn in Hs; try discriminate. injection Hs as <-. exact K. }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)).
  { pose proof (decode_exec_accesses_canon ms b HR) as K.
    destruct (decode_exec_accesses segs ms b) as [a| |]; cbn in Hs; try discriminate. injection Hs as <-. exact K. }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)).
  { pose proof (decode_exec_accesses_canon ms b HR) as K.
    destruct (decode_exec_accesses segs ms b) as [a| |]; cbn in Hs; try discriminate. injection Hs as <-. exact K. }
  unfold fetch_failure in Hs. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Lemma msteps_canon : forall ms ms', CatSim.msteps segs ms ms' -> rcanon (ms_regs ms) -> rcanon (ms_regs ms').
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intros HR; [exact HR|].
  apply IH. eapply step_canon; eassumption.
Qed.

Lemma msteps_canon_mkR : forall ms ms', CatSim.msteps segs ms ms' -> rcanon (ms_regs ms) ->
  ms_regs ms' = canon_regs (ms_regs ms').
Proof. intros ms ms' H HR. exact (msteps_canon ms ms' H HR). Qed.

End WithSegs.
