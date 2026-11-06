(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.
Module FrmKeepNs0.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FrmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.FrmKit.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0041.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.

Module FRMS0.
Definition XLO : Z := 0x38000.
Definition XSZ : Z := 0x87000.

Lemma segs_facts :
  forallb (fun seg => negb (seg_executable seg && seg_writable seg)
                      && (negb (seg_executable seg) || ((Z.of_N (seg_base seg) =? XLO) && (Z.of_N (seg_size seg) =? XSZ)))) RSEGS = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

(* [comment removed for export] *)
Lemma FSCAN : forallb (FrmFastScan.FRMF.fseg FRM.word_frm_safe RSEGS 270 1024) RSEGS = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma no_wx : forall seg, In seg RSEGS -> seg_executable seg && seg_writable seg = false.
Proof.
  intros seg IN. pose proof (proj1 (forallb_forall _ _) segs_facts seg IN) as H. cbn beta in H.
  apply andb_true_iff in H as [H _]. apply negb_true_iff in H. exact H.
Qed.
Lemma xseg : forall seg, In seg RSEGS -> seg_executable seg = true -> Z.of_N (seg_base seg) = XLO /\ Z.of_N (seg_size seg) = XSZ.
Proof.
  intros seg IN X. pose proof (proj1 (forallb_forall _ _) segs_facts seg IN) as H. cbn beta in H.
  apply andb_true_iff in H as [_ H]. rewrite X in H. cbn [negb orb] in H. apply andb_true_iff in H as [H1 H2].
  split; apply Z.eqb_eq; assumption.
Qed.

Theorem fetch_safe : forall a w, fetch_word RSEGS a = Some w \/ fetch_tail RSEGS a = Some w -> FRM.word_frm_safe w = true.
Proof. exact (FrmFastScan.FRMF.fetch_safe_of_fscan_FRM RSEGS 270 1024 FSCAN). Qed.

(* [comment removed for export] *)
Theorem step_fz : forall s s', RiscvSemantics.step RSEGS s = MachineOk s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof. exact (FRM.step_fz RSEGS no_wx fetch_safe). Qed.
Theorem msteps_fz : forall s s', msteps RSEGS s s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof. exact (FRM.msteps_fz RSEGS no_wx fetch_safe). Qed.
Theorem msteps_fz_mkst (fx fx' : FPState) R R' pc pc' M M' :
  msteps RSEGS (@mkst fx R pc M (seg_rom RSEGS)) (@mkst fx' R' pc' M' (seg_rom RSEGS)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').
Proof. exact (FRM.msteps_fz_mkst RSEGS no_wx fetch_safe fx fx' R R' pc pc' M M'). Qed.
End FRMS0.

(* [comment removed for export] *)
Ltac frm_solve := FRMK.frm_solve_with FRMS0.msteps_fz_mkst.

End FrmKeepNs0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BMode.
Module WdFrmAny.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FPSteps OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.FrmKeep OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0047.FrmKeepNs0.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Import BMode.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FRMA.
Import FRM. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Definition frm_of (f : bv 32) : Z := Z.land (Z.shiftr (bv_unsigned f) 5) 7.

Lemma frm_of_accrue (f : bv 32) (b : Z) : 0 <= b < 32 -> frm_of (Z_to_bv 32 (Z.lor (bv_unsigned f) b)) = frm_of f.
Proof.
  intros Hb. unfold frm_of. pose proof (fp_u32_range f) as Hr.
  rewrite fp_u_Z2bv32 by (apply (fp_Z_lor_range 32); lia).
  rewrite Z.shiftr_lor. rewrite (Z.shiftr_div_pow2 b 5) by lia.
  rewrite (Z.div_small b (2^5)) by lia. rewrite Z.lor_0_r. reflexivity.
Qed.

Lemma frm_of_slice0_5 (f : bv 32) (v : word) : frm_of (slice_set f 0 5 v) = frm_of f.
Proof.
  unfold frm_of, slice_set. pose proof (fp_u32_range f) as Hr.
  change (Z.shiftl (Z.ones 5) 0) with 31%Z. rewrite Z.shiftl_0_r.
  assert (H1 : (0 <= Z.land (bv_unsigned f) (Z.lnot 31) < 2^32)%Z) by (apply fp_Z_land_range_l; lia).
  assert (H2 : (0 <= Z.land (bv_unsigned v) 31 < 2^32)%Z).
  { split; [apply Z.land_nonneg; right; lia|].
    rewrite Z.land_comm. apply (proj2 (fp_Z_land_range_l 32 31 (bv_unsigned v) ltac:(lia) ltac:(lia))). }
  rewrite fp_u_Z2bv32 by (apply (fp_Z_lor_range 32); lia).
  rewrite Z.shiftr_lor, !Z.shiftr_land.
  change (Z.shiftr (Z.lnot 31) 5) with (-1)%Z. change (Z.shiftr 31 5) with 0%Z.
  rewrite Z.land_m1_r, Z.land_0_r, Z.lor_0_r. reflexivity.
Qed.

Section Keep.
Variable c0 : Z.

(* [comment removed for export] *)
Fixpoint eff_fk (e : eff) : Prop :=
  match e with
  | EDone c => frm_of (c_fcsr c) = c0
  | ELoad n a k => forall v, eff_fk (k v)
  | EStore n a v k => eff_fk k
  | _ => True
  end.

Lemma fk_accrue fl c : frm_of (c_fcsr c) = c0 -> frm_of (c_fcsr (accrue fl c)) = c0.
Proof. intros H. rewrite fc_accrue. rewrite frm_of_accrue by apply fp_fflags_bits_range. exact H. Qed.

Ltac fk_core FZ :=
  repeat first [ exact FZ
               | rewrite fc_rset | rewrite fc_with_pc | rewrite fc_with_resv | rewrite fc_with_regs | rewrite fc_fset
               | rewrite fc_fwrite | rewrite fc_inval_resv | apply fk_accrue ].

Ltac fk_tree FZ :=
  repeat first [ lazymatch goal with
                 | |- eff_fk (match ?x with _ => _ end) => destruct x
                 | |- eff_fk ((match ?x with _ => _ end) _) => destruct x
                 | |- eff_fk (EDone _) => cbn [eff_fk]
                 | |- eff_fk (ELoad _ _ _) => cbn [eff_fk]; intros ?
                 | |- eff_fk (EStore _ _ _ _) => cbn [eff_fk]
                 | |- eff_fk (exec_csr _ _ _ _ _ _) => fail
                 | |- eff_fk _ => exact I
                 | |- frm_of (c_fcsr (match ?x with _ => _ end)) = _ => destruct x
                 | |- frm_of _ = _ => progress (fk_core FZ)
                 end ].

Lemma exec_csr_fk op rd operand writes csr c :
  frm_of (c_fcsr c) = c0 -> csr_frm_unsafe writes csr = false -> eff_fk (exec_csr op rd operand writes csr c).
Proof.
  intros FZ SF. unfold exec_csr, csr_slice. cbv zeta. unfold csr_frm_unsafe in SF.
  destruct (Z.eqb_spec (bv_unsigned csr) 1) as [E1|N1].
  - cbn [eff_fk]. rewrite fc_rset. destruct writes; [| exact FZ]. cbn [c_fcsr with_fcsr]. rewrite frm_of_slice0_5. exact FZ.
  - destruct (Z.eqb_spec (bv_unsigned csr) 2) as [E2|N2].
    + destruct writes; [cbn in SF; rewrite ?E2 in SF; cbn in SF; discriminate|]. cbn [eff_fk]. rewrite fc_rset. exact FZ.
    + destruct (Z.eqb_spec (bv_unsigned csr) 3) as [E3|N3]; [| exact I].
      destruct writes; [cbn in SF; rewrite ?E3 in SF; cbn in SF; discriminate|]. cbn [eff_fk]. rewrite fc_rset. exact FZ.
Qed.

Lemma exec_fk (sz : word) (i : instr) (c : core) :
  frm_of (c_fcsr c) = c0 -> instr_frm_safe i = true -> eff_fk (exec sz i c).
Proof.
  intros FZ SF. destruct i; cbv beta iota zeta delta [exec load_val store_val]; try (fk_tree FZ).
  - cbn [instr_frm_safe csr_writes] in SF. apply negb_true_iff in SF. apply exec_csr_fk; [fk_core FZ| exact SF].
  - cbn [instr_frm_safe csr_writes] in SF. apply negb_true_iff in SF. apply exec_csr_fk; [fk_core FZ| exact SF].
Qed.

Lemma interp_fk segs : forall e m rep, eff_fk e -> interp_eff_accesses segs e m = MachineOk rep -> frm_of (c_fcsr (fst (@access_value _ rep))) = c0.
Proof.
  induction e as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m rep FZ H; cbn [interp_eff_accesses] in H; try discriminate.
  - injection H as <-. exact FZ.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| | ] eqn:E; try discriminate.
    injection H as <-. cbn [access_value fst]. exact (IH _ m r (FZ _) E).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r| | ] eqn:E; try discriminate.
    injection H as <-. cbn [access_value fst]. exact (IH _ r FZ E).
Qed.

Lemma decode_exec_fk segs st w rep :
  frm_of (ms_fcsr st) = c0 -> word_frm_safe w = true -> decode_exec_accesses segs st w = MachineOk rep -> frm_of (ms_fcsr (@access_value _ rep)) = c0.
Proof.
  intros FZ SF H. unfold decode_exec_accesses in H. unfold word_frm_safe in SF.
  destruct (is_ecall w); [injection H as <-; exact FZ|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
  destruct (interp_eff_accesses _ _) as [r| | ] eqn:E; try discriminate.
  pose proof (interp_fk segs _ _ r (exec_fk (Z_to_bv 64 isz) i (Core (ms_regs st) (ms_fregs st) (ms_pc_val st) (ms_fcsr st) (ms_resv st)) FZ SF) E) as FZ'.
  destruct (@access_value _ r) as [c m'] eqn:Er. cbv beta iota zeta in H. injection H as <-. cbn [access_value ms_fcsr fst] in *. exact FZ'.
Qed.

Section Generic.
Variable segs : list Segment. Context {bmK : BMode}.
Hypothesis no_wx : forall seg, In seg segs -> seg_executable seg && seg_writable seg = false.
Hypothesis fetch_safe : forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> word_frm_safe w = true.

Theorem step_fk : forall s s', RiscvSemantics.step segs s = MachineOk s' -> frm_of (ms_fcsr s) = c0 -> frm_of (ms_fcsr s') = c0.
Proof.
  intros s s' H FZ. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc s)) as [w|] eqn:F1.
  - destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
    exact (decode_exec_fk segs s w r FZ (fetch_safe _ _ (or_introl F1)) E).
  - rewrite (fetch_word_ov_none segs no_wx), (fetch_tail_any_eq segs no_wx) in H.
    destruct (fetch_tail segs (ms_pc s)) as [w|] eqn:F2.
    + destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
      exact (decode_exec_fk segs s w r FZ (fetch_safe _ _ (or_intror F2)) E).
    + exfalso. unfold fetch_failure in H. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Theorem msteps_fk : forall s s', msteps segs s s' -> frm_of (ms_fcsr s) = c0 -> frm_of (ms_fcsr s') = c0.
Proof.
  intros s s' H. induction H as [ms| ms ms' ms'' P ST MS IH]; intros FZ; [exact FZ|].
  apply IH. exact (step_fk ms ms' ST FZ).
Qed.
End Generic.
End Keep.

(* [comment removed for export] *)
Theorem msteps_frm_keep_s : forall s s', msteps FrmKeepNs0.RSEGS s s' -> frm_of (ms_fcsr s') = frm_of (ms_fcsr s).
Proof. intros s s' H. exact (msteps_fk (frm_of (ms_fcsr s)) FrmKeepNs0.RSEGS FRMS0.no_wx FRMS0.fetch_safe s s' H eq_refl). Qed.

End FRMA.

End WdFrmAny.
