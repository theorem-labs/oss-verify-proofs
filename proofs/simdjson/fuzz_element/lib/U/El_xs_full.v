(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import MState Frame Exec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition fullR (R : bvmap 5 word) : Prop :=
  exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

Lemma fullR_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  fullR (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof. intros. repeat eexists. Qed.

Lemma bv_key_cases : forall r : reg, is_x0 r = false ->
  let p := bv_key r in
  (p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7 \/ p = 8 \/ p = 9 \/ p = 10 \/ p = 11 \/ p = 12 \/ p = 13 \/ p = 14 \/ p = 15 \/ p = 16 \/ p = 17
  \/ p = 18 \/ p = 19 \/ p = 20 \/ p = 21 \/ p = 22 \/ p = 23 \/ p = 24 \/ p = 25 \/ p = 26 \/ p = 27 \/ p = 28 \/ p = 29 \/ p = 30 \/ p = 31 \/ p = 32)%positive.
Proof.
  intros r Hr. unfold is_x0 in Hr. apply Z.eqb_neq in Hr.
  pose proof (bv_unsigned_in_range 5 r) as Hb. unfold bv_modulus in Hb. cbn in Hb.
  cbv zeta. unfold bv_key. lia.
Qed.

Lemma fullR_set : forall (R : bvmap 5 word) (r : reg) (v : word),
  fullR R -> is_x0 r = false -> fullR (bvmap_set r v R).
Proof.
  intros R r v (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
                x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->) Hr.
  pose proof (bv_key_cases r Hr) as Hp. cbv zeta in Hp.
  unfold bvmap_set. unfold fullR, mkR.
  repeat (destruct Hp as [Hp | Hp]; [rewrite Hp; cbn [tset]; repeat eexists; reflexivity |]).
  rewrite Hp; cbn [tset]; repeat eexists; reflexivity.
Qed.

Lemma fullR_eq : forall R, fullR R ->
  R = mkR (reg_get R (Z_to_bv 5 1)) (reg_get R (Z_to_bv 5 2)) (reg_get R (Z_to_bv 5 3)) (reg_get R (Z_to_bv 5 4)) (reg_get R (Z_to_bv 5 5))
          (reg_get R (Z_to_bv 5 6)) (reg_get R (Z_to_bv 5 7)) (reg_get R (Z_to_bv 5 8)) (reg_get R (Z_to_bv 5 9)) (reg_get R (Z_to_bv 5 10))
          (reg_get R (Z_to_bv 5 11)) (reg_get R (Z_to_bv 5 12)) (reg_get R (Z_to_bv 5 13)) (reg_get R (Z_to_bv 5 14)) (reg_get R (Z_to_bv 5 15))
          (reg_get R (Z_to_bv 5 16)) (reg_get R (Z_to_bv 5 17)) (reg_get R (Z_to_bv 5 18)) (reg_get R (Z_to_bv 5 19)) (reg_get R (Z_to_bv 5 20))
          (reg_get R (Z_to_bv 5 21)) (reg_get R (Z_to_bv 5 22)) (reg_get R (Z_to_bv 5 23)) (reg_get R (Z_to_bv 5 24)) (reg_get R (Z_to_bv 5 25))
          (reg_get R (Z_to_bv 5 26)) (reg_get R (Z_to_bv 5 27)) (reg_get R (Z_to_bv 5 28)) (reg_get R (Z_to_bv 5 29)) (reg_get R (Z_to_bv 5 30))
          (reg_get R (Z_to_bv 5 31)).
Proof.
  intros R (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 &
            x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  reflexivity.
Qed.

Definition core_full (c : core) : Prop := fullR (c_regs c).

Lemma core_full_rset : forall r v c, core_full c -> core_full (rset r v c).
Proof.
  intros r v c H. unfold rset. destruct (is_x0 r) eqn:E; [exact H|].
  unfold core_full, with_regs in *. cbn. apply fullR_set; assumption.
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
Proof. intros fmt r v [R F p f s] H. unfold fwrite. cbn. destruct fmt; exact H. Qed.
Lemma core_full_inval_resv : forall a c, core_full c -> core_full (inval_resv a c).
Proof. intros a [R F p f s] H. unfold inval_resv. cbn. destruct s as [w|]; [destruct (Z.eqb _ _)|]; exact H. Qed.
Lemma core_full_if : forall (b : bool) c1 c2, core_full c1 -> core_full c2 -> core_full (if b then c1 else c2).
Proof. intros [] c1 c2 H1 H2; assumption. Qed.

Inductive eff_full : eff -> Prop :=
| EF_Done : forall c, core_full c -> eff_full (EDone c)
| EF_Illegal : forall c, eff_full (EIllegal c)
| EF_DefinedIllegal : forall c, eff_full (EDefinedIllegal c)
| EF_Ecall : forall c, eff_full (EEcall c)
| EF_Ebreak : forall c, eff_full (EEbreak c)
| EF_Fault : forall c, eff_full (EFault c)
| EF_Load : forall n a k, (forall v, eff_full (k v)) -> eff_full (ELoad n a k)
| EF_Store : forall n a v k, eff_full k -> eff_full (EStore n a v k).

Local Ltac solve_core H :=
  repeat first [ apply core_full_rset | apply core_full_fset | apply core_full_with_pc
               | apply core_full_with_fcsr | apply core_full_with_resv | apply core_full_accrue
               | apply core_full_fwrite | apply core_full_inval_resv | apply core_full_if
               | match goal with |- core_full (match ?X with _ => _ end) => destruct X end ];
  exact H.

Local Ltac full_struct H :=
  repeat first
    [ apply EF_Done; solve_core H
    | apply EF_Illegal | apply EF_DefinedIllegal | apply EF_Ecall | apply EF_Ebreak | apply EF_Fault
    | apply EF_Load; intros ?
    | apply EF_Store
    | match goal with |- eff_full (match ?X with _ => _ end) => destruct X end
    | match goal with |- eff_full (match ?X with _ => _ end _) => destruct X end
    | match goal with |- eff_full (if ?X then _ else _) => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_full : forall R F pc fc rv sz i,
  fullR R -> eff_full (exec sz i (Core R F pc fc rv)).
Proof.
  intros R F pc fc rv sz i HR.
  assert (H : core_full (Core R F pc fc rv)) by exact HR.
  destruct i; unfold_exec; full_struct H.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_full : forall t, eff_full t -> forall m,
  match interp_eff_accesses segs t m with
  | MachineOk r => core_full (fst (access_value _ r))
  | _ => True
  end.
Proof.
  intros t H. induction H; intros m; cbn [interp_eff_accesses access_value fst]; auto.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| exact I].
    specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
    destruct (interp_eff_accesses segs (k _) m) as [r| |]; cbn in *; try exact H0; exact I.
  - destruct (store_ok segs m a (width_bytes n)); [| exact I].
    specialize (IHeff_full (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
    destruct (interp_eff_accesses segs k _) as [r| |]; cbn in *; try exact IHeff_full; exact I.
Qed.

Lemma decode_exec_full : forall ms w ms' rs,
  fullR (ms_regs ms) ->
  decode_exec_accesses segs ms w = MachineOk (mkAccessReport _ ms' rs) -> fullR (ms_regs ms').
Proof.
  intros ms w ms' rs HF Hd. unfold decode_exec_accesses in Hd.
  destruct (is_ecall w).
  - injection Hd as <- _. cbn. exact HF.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
    destruct ms as [R F pc svc rv fc m ro]. cbn in Hd, HF.
    pose proof (interp_full _ (exec_full R F pc fc rv (Z_to_bv 64 isz) i HF) m) as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc fc rv)) m) as [[[c m1] rs1]| |]; try discriminate.
    injection Hd as <- _. cbn in *. exact K.
Qed.

Lemma step_full : forall ms ms',
  fullR (ms_regs ms) -> RiscvSemantics.step segs ms = MachineOk ms' -> fullR (ms_regs ms').
Proof.
  intros ms ms' HF Hs. unfold RiscvSemantics.step, drop_access_report, RiscvSemantics.step_accesses, ms_pc in Hs.
  destruct (fetch_word segs (ms_pc_val ms)) as [w|].
  { destruct (decode_exec_accesses segs ms w) as [[x rs]| |] eqn:Hd; try discriminate. injection Hs as <-. eapply decode_exec_full; eauto. }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)) as [w|].
  { destruct (decode_exec_accesses segs ms w) as [[x rs]| |] eqn:Hd; try discriminate. injection Hs as <-. eapply decode_exec_full; eauto. }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)) as [w|].
  { destruct (decode_exec_accesses segs ms w) as [[x rs]| |] eqn:Hd; try discriminate. injection Hs as <-. eapply decode_exec_full; eauto. }
  unfold fetch_failure in Hs. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Lemma msteps_full : forall ms ms',
  Exec.msteps segs ms ms' -> fullR (ms_regs ms) -> fullR (ms_regs ms').
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [_ Hs] _ IH]; intros HF; [exact HF|].
  apply IH. eapply step_full; eauto.
Qed.

End WithSegs.
