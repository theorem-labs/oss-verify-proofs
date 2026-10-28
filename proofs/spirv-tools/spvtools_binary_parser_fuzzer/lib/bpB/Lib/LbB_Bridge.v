(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require PropExec CatSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BExec BLFrame BegsEquivM.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma msteps_bridge : forall segs a b, CatSim.msteps segs a b -> BExec.msteps segs a b.
Proof.
  intros segs a b H. induction H as [ms | ms ms' ms'' Hsvc Hstep _ IH].
  - apply msteps_refl.
  - eapply msteps_cons; [split; eassumption | exact IH].
Qed.

Lemma mkst_MS : forall F fc R pc m ro, @PropExec.mkst (PropExec.mkFP F fc) R pc m ro = MS R F pc fc None m ro.
Proof. reflexivity. Qed.

Lemma evt_of_msteps : forall segs (Q : machine_state -> Prop) a b,
  CatSim.msteps segs a b -> evt segs Q b -> evt segs Q a.
Proof.
  intros segs Q a b H (c & Hbc & HQ). exists c. split; [|exact HQ].
  eapply BExec.msteps_trans; [apply msteps_bridge; exact H | exact Hbc].
Qed.

Lemma evt_of_msteps_done : forall segs (Q : machine_state -> Prop) a b,
  CatSim.msteps segs a b -> Q b -> evt segs Q a.
Proof. intros segs Q a b H HQ. eapply evt_of_msteps; [exact H | apply evt_done; exact HQ]. Qed.

Definition rfull (R : bvmap 5 word) : Prop := R = mkR_of R.

Lemma rfull_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  rfull (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof. intros. unfold rfull. vm_compute. reflexivity. Qed.

Lemma rfull_set_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
    (k : reg) (v : word),
  is_x0 k = false ->
  rfull (bvmap_set k v (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)).
Proof.
  intros. destruct (reg_of_nat k) as (n & -> & Hn). unfold rfull.
  do 32 (destruct n as [|n]; [first [discriminate | vm_compute; reflexivity] |]). lia.
Qed.

Lemma rfull_set : forall R (k : reg) v, rfull R -> is_x0 k = false -> rfull (bvmap_set k v R).
Proof. intros R k v HR Hk. rewrite HR. unfold mkR_of. apply rfull_set_mkR. exact Hk. Qed.

Lemma rfull_eq : forall R, rfull R ->
  R = mkR (PropExec.getr R 1) (PropExec.getr R 2) (PropExec.getr R 3) (PropExec.getr R 4) (PropExec.getr R 5) (PropExec.getr R 6)
          (PropExec.getr R 7) (PropExec.getr R 8) (PropExec.getr R 9) (PropExec.getr R 10) (PropExec.getr R 11) (PropExec.getr R 12)
          (PropExec.getr R 13) (PropExec.getr R 14) (PropExec.getr R 15) (PropExec.getr R 16) (PropExec.getr R 17) (PropExec.getr R 18)
          (PropExec.getr R 19) (PropExec.getr R 20) (PropExec.getr R 21) (PropExec.getr R 22) (PropExec.getr R 23) (PropExec.getr R 24)
          (PropExec.getr R 25) (PropExec.getr R 26) (PropExec.getr R 27) (PropExec.getr R 28) (PropExec.getr R 29) (PropExec.getr R 30)
          (PropExec.getr R 31).
Proof. intros R HR. exact HR. Qed.

Definition core_full (c : core) : Prop := rfull (c_regs c).

Inductive eff_full : eff -> Prop :=
| FulDone : forall c, core_full c -> eff_full (EDone c)
| FulIllegal : forall c, eff_full (EIllegal c)
| FulEcall : forall c, eff_full (EEcall c)
| FulEbreak : forall c, eff_full (EEbreak c)
| FulFault : forall c, eff_full (EFault c)
| FulDefIllegal : forall c, eff_full (EDefinedIllegal c)
| FulLoad : forall n a k, (forall v, eff_full (k v)) -> eff_full (ELoad n a k)
| FulStore : forall n a v k, eff_full k -> eff_full (EStore n a v k).

Lemma core_full_mk : forall R F pc fc rv, rfull R -> core_full (Core R F pc fc rv).
Proof. intros. exact H. Qed.
Lemma core_full_rset : forall r v c, core_full c -> core_full (rset r v c).
Proof.
  intros r v [R F p f s] H. unfold rset. destruct (is_x0 r) eqn:E; [exact H|].
  unfold core_full, with_regs. cbn [c_regs]. apply rfull_set; [exact H | exact E].
Qed.
Lemma core_full_fset : forall r v c, core_full c -> core_full (fset r v c).
Proof. intros r v [R F p f s] H. exact H. Qed.
Lemma core_full_with_pc : forall v c, core_full c -> core_full (with_pc v c).
Proof. intros v [R F p f s] H. exact H. Qed.
Lemma core_full_with_fcsr : forall v c, core_full c -> core_full (with_fcsr v c).
Proof. intros v [R F p f s] H. exact H. Qed.
Lemma core_full_with_resv : forall v c, core_full c -> core_full (with_resv v c).
Proof. intros v [R F p f s] H. exact H. Qed.
Lemma core_full_accrue : forall fl c, core_full c -> core_full (accrue fl c).
Proof. intros fl [R F p f s] H. exact H. Qed.
Lemma core_full_fwrite : forall fmt r v c, core_full c -> core_full (fwrite fmt r v c).
Proof. intros fmt r v c H. destruct fmt; apply core_full_fset; exact H. Qed.
Lemma core_full_inval_resv : forall a c, core_full c -> core_full (inval_resv a c).
Proof.
  intros a [R F p f s] H. unfold inval_resv. cbn [c_resv].
  destruct s as [r|]; [destruct (Z.eqb _ _)|]; exact H.
Qed.
Lemma core_full_if : forall (b : bool) c1 c2, core_full c1 -> core_full c2 -> core_full (if b then c1 else c2).
Proof. intros [] c1 c2 H1 H2; assumption. Qed.

Local Ltac solve_full HR :=
  repeat first [ apply core_full_rset | apply core_full_fset | apply core_full_with_pc
               | apply core_full_with_fcsr | apply core_full_with_resv | apply core_full_accrue
               | apply core_full_fwrite | apply core_full_inval_resv | apply core_full_if
               | match goal with |- core_full (match ?X with _ => _ end) => destruct X end ];
  first [ exact (core_full_mk _ _ _ _ _ HR) | exact HR ].

Local Ltac full_struct HR :=
  repeat first
    [ apply FulDone; solve_full HR
    | apply FulIllegal | apply FulEcall | apply FulEbreak | apply FulFault | apply FulDefIllegal
    | apply FulLoad; intros ?
    | apply FulStore
    | match goal with |- eff_full (match ?X with _ => _ end) => destruct X end
    | match goal with |- eff_full (match ?X with _ => _ end _) => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_full_core : forall R F pc fc rv sz i,
  rfull R -> eff_full (exec sz i (Core R F pc fc rv)).
Proof.
  intros R F pc fc rv sz i HR.
  destruct i; unfold_exec; full_struct HR.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_full : forall t, eff_full t -> forall m a,
  interp_eff_accesses segs t m = MachineOk a -> core_full (fst (access_value _ a)).
Proof.
  intros t H. induction H as [c Hc | c | c | c | c | c | n a k Hk IH | n a v k Hk IH]; intros m r Hr;
    cbn [interp_eff_accesses] in Hr; try discriminate.
  - injection Hr as <-. exact Hc.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k _) m) as [ra| |] eqn:E; try discriminate.
    injection Hr as <-. cbn. exact (IH _ m ra E).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [ra| |] eqn:E; try discriminate.
    injection Hr as <-. cbn. exact (IH _ ra E).
Qed.

Lemma decode_exec_full : forall st w a,
  decode_exec_accesses segs st w = MachineOk a -> rfull (ms_regs st) -> rfull (ms_regs (access_value _ a)).
Proof.
  intros st w a Ha HR. unfold decode_exec_accesses in Ha. destruct (is_ecall w).
  - injection Ha as <-. exact HR.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
    pose proof (interp_full _ (exec_full_core (ms_regs st) (ms_fregs st) (ms_pc_val st) (ms_fcsr st) (ms_resv st) (Z_to_bv 64 isz) i HR)
                  (ms_mem st)) as K.
    destruct (interp_eff_accesses segs _ (ms_mem st)) as [r| |] eqn:E; try discriminate.
    destruct (access_value _ r) as [c m'] eqn:Ev. injection Ha as <-. cbn.
    specialize (K r eq_refl). rewrite Ev in K. exact K.
Qed.

Lemma fetch_failure_not_ok : forall m addr st', fetch_failure segs m addr <> MachineOk st'.
Proof.
  intros m addr st'. unfold fetch_failure.
  destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Lemma step_full : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> rfull (ms_regs ms) -> rfull (ms_regs ms').
Proof.
  intros ms ms' Hs HR. unfold RiscvSemantics.step in Hs.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |] eqn:E; cbn in Hs; try discriminate.
  injection Hs as <-. unfold RiscvSemantics.step_accesses in E.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (decode_exec_full _ _ _ E HR)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (decode_exec_full _ _ _ E HR)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (decode_exec_full _ _ _ E HR)|].
  destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) as [st'| |] eqn:F; try discriminate.
  exfalso. exact (fetch_failure_not_ok _ _ _ F).
Qed.

Lemma msteps_full : forall a b, CatSim.msteps segs a b -> rfull (ms_regs a) -> rfull (ms_regs b).
Proof.
  intros a b H. induction H as [ms | ms ms' ms'' Hsvc Hstep _ IH]; intros HR; [exact HR|].
  apply IH. exact (step_full _ _ Hstep HR).
Qed.

Lemma interp_mem_inv : forall t m r, interp_eff_accesses segs t m = MachineOk r ->
  mem_inv segs m -> mem_inv segs (snd (access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r Hr HI; cbn [interp_eff_accesses] in Hr; try discriminate.
  - injection Hr as <-. exact HI.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k _) m) as [ra| |] eqn:E; try discriminate.
    injection Hr as <-. cbn. exact (IH _ m ra E HI).
  - destruct (store_ok segs m a (width_bytes n)) eqn:Hok; [|discriminate].
    destruct (interp_eff_accesses segs k _) as [ra| |] eqn:E; try discriminate.
    injection Hr as <-. cbn. apply (IH _ ra E). apply mem_inv_store; [exact HI|].
    rewrite length_Z_to_le_bytes. exact Hok.
Qed.

Lemma step_mem_inv : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' ->
  mem_inv segs (ms_mem ms) -> mem_inv segs (ms_mem ms').
Proof.
  intros ms ms' Hs HI. unfold RiscvSemantics.step in Hs.
  destruct (RiscvSemantics.step_accesses segs ms) as [a| |] eqn:E; cbn in Hs; try discriminate.
  injection Hs as <-. unfold RiscvSemantics.step_accesses in E.
  assert (D : forall w, decode_exec_accesses segs ms w = MachineOk a -> mem_inv segs (ms_mem (access_value _ a))).
  { intros w Hd. unfold decode_exec_accesses in Hd. destruct (is_ecall w).
    - injection Hd as <-. exact HI.
    - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses segs _ (ms_mem ms)) as [r| |] eqn:Ei; try discriminate.
      pose proof (interp_mem_inv _ _ _ Ei HI) as K.
      destruct (access_value _ r) as [c m'] eqn:Ev. injection Hd as <-. cbn. cbn in K. exact K. }
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (D w E)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (D w E)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (D w E)|].
  destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) as [st'| |] eqn:F; try discriminate.
  exfalso. exact (fetch_failure_not_ok _ _ _ F).
Qed.

Lemma msteps_mem_inv : forall a b, CatSim.msteps segs a b -> mem_inv segs (ms_mem a) -> mem_inv segs (ms_mem b).
Proof.
  intros a b H. induction H as [ms | ms ms' ms'' Hsvc Hstep _ IH]; intros HI; [exact HI|].
  apply IH. exact (step_mem_inv _ _ Hstep HI).
Qed.
End WithSegs.

