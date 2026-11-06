(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Frame RegsEquiv Exec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition rfull (R : bvmap 5 word) : Prop :=
  exists x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word,
    R = mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.

Lemma rfull_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  rfull (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof. intros. unfold rfull. do 31 eexists. reflexivity. Qed.

Lemma rfull_canon : forall R, rfull R ->
  R = mkR (reg_get R 1) (reg_get R 2) (reg_get R 3) (reg_get R 4) (reg_get R 5) (reg_get R 6) (reg_get R 7) (reg_get R 8)
          (reg_get R 9) (reg_get R 10) (reg_get R 11) (reg_get R 12) (reg_get R 13) (reg_get R 14) (reg_get R 15) (reg_get R 16)
          (reg_get R 17) (reg_get R 18) (reg_get R 19) (reg_get R 20) (reg_get R 21) (reg_get R 22) (reg_get R 23) (reg_get R 24)
          (reg_get R 25) (reg_get R 26) (reg_get R 27) (reg_get R 28) (reg_get R 29) (reg_get R 30) (reg_get R 31).
Proof.
  intros R (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21
             & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->).
  reflexivity.
Qed.

Lemma rfull_set : forall R (r : reg) v, rfull R -> is_x0 r = false -> rfull (bvmap_set r v R).
Proof.
  intros R r v (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21
                  & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->) Hr.
  destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [first [discriminate Hr | unfold rfull; do 31 eexists; reflexivity]|]).
  exfalso; lia.
Qed.

(* [comment removed for export] *)
Definition cfull (c : core) : Prop := rfull (c_regs c).

Lemma cfull_rset : forall r v c, cfull c -> cfull (rset r v c).
Proof.
  intros r v [R F p f s] H. unfold cfull, rset, with_regs in *. cbn [c_regs] in *.
  destruct (is_x0 r) eqn:E; cbn [c_regs]; [exact H | apply rfull_set; assumption].
Qed.
Lemma cfull_fset : forall r v c, cfull c -> cfull (fset r v c).
Proof. intros r v [R F p f s] H. exact H. Qed.
Lemma cfull_with_pc : forall v c, cfull c -> cfull (with_pc v c).
Proof. intros v [R F p f s] H. exact H. Qed.
Lemma cfull_with_fcsr : forall v c, cfull c -> cfull (with_fcsr v c).
Proof. intros v [R F p f s] H. exact H. Qed.
Lemma cfull_with_resv : forall v c, cfull c -> cfull (with_resv v c).
Proof. intros v [R F p f s] H. exact H. Qed.
Lemma cfull_accrue : forall fl c, cfull c -> cfull (accrue fl c).
Proof. intros fl [R F p f s] H. exact H. Qed.
Lemma cfull_fwrite : forall fmt r v c, cfull c -> cfull (fwrite fmt r v c).
Proof. intros fmt r v c H. destruct fmt; apply cfull_fset; exact H. Qed.
Lemma cfull_inval_resv : forall a c, cfull c -> cfull (inval_resv a c).
Proof.
  intros a [R F p f s] H. unfold cfull, inval_resv, with_resv in *. cbn [c_regs c_resv] in *.
  destruct s as [r|]; [destruct (Z.eqb _ _)|]; exact H.
Qed.
Lemma cfull_if : forall (b : bool) c1 c2, cfull c1 -> cfull c2 -> cfull (if b then c1 else c2).
Proof. intros [] c1 c2 H1 H2; assumption. Qed.

(* [comment removed for export] *)
Inductive eff_full : eff -> Prop :=
| FDone : forall c, cfull c -> eff_full (EDone c)
| FIllegal : forall c, eff_full (EIllegal c)
| FDefIllegal : forall c, eff_full (EDefinedIllegal c)
| FEcall : forall c, eff_full (EEcall c)
| FEbreak : forall c, eff_full (EEbreak c)
| FFault : forall c, eff_full (EFault c)
| FLoad : forall n a k, (forall v, eff_full (k v)) -> eff_full (ELoad n a k)
| FStore : forall n a v k, eff_full k -> eff_full (EStore n a v k).

Local Ltac solve_core H0 :=
  repeat first [ apply cfull_rset | apply cfull_fset | apply cfull_with_pc
               | apply cfull_with_fcsr | apply cfull_with_resv | apply cfull_accrue
               | apply cfull_fwrite | apply cfull_inval_resv | apply cfull_if
               | match goal with |- cfull (match ?X with _ => _ end) => destruct X end ];
  exact H0.

Local Ltac full_struct H0 :=
  repeat first
    [ apply FDone; solve_core H0
    | apply FIllegal | apply FDefIllegal | apply FEcall | apply FEbreak | apply FFault
    | apply FLoad; intros ?
    | apply FStore
    | match goal with |- eff_full (match ?X with _ => _ end) => destruct X end
    | match goal with |- eff_full (match ?X with _ => _ end _) => destruct X end ].

Local Ltac unfold_exec :=
  cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
                            with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_full : forall R F pc fc rv sz i, rfull R -> eff_full (exec sz i (Core R F pc fc rv)).
Proof.
  intros R F pc fc rv sz i HR.
  assert (H0 : cfull (Core R F pc fc rv)) by exact HR.
  destruct i; unfold_exec; full_struct H0.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_eff_accesses_full : forall t, eff_full t -> forall m r,
  interp_eff_accesses segs t m = MachineOk r -> cfull (fst (access_value _ r)).
Proof.
  intros t H. induction H; intros m r E; cbn [interp_eff_accesses] in E; try discriminate.
  - injection E as <-. exact H.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k _) m) as [r'| |] eqn:E'; try discriminate.
    injection E as <-. cbn [access_value]. exact (H0 _ _ _ E').
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r'| |] eqn:E'; try discriminate.
    injection E as <-. cbn [access_value]. exact (IHeff_full _ _ E').
Qed.

Lemma decode_exec_accesses_full : forall ms w r,
  rfull (ms_regs ms) -> decode_exec_accesses segs ms w = MachineOk r -> rfull (ms_regs (access_value _ r)).
Proof.
  intros [R F pc svc rv fc m ro] w r HR E. cbn [ms_regs] in HR. unfold decode_exec_accesses in E.
  destruct (is_ecall w).
  - injection E as <-. exact HR.
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
    cbn in E.
    pose proof (interp_eff_accesses_full _ (exec_full R F pc fc rv (Z_to_bv 64 isz) i HR) m) as K.
    destruct (interp_eff_accesses segs (exec _ i (Core R F pc fc rv)) m) as [[[c m1] acc]| |] eqn:E1; try discriminate.
    specialize (K _ eq_refl). cbn [access_value fst] in K.
    injection E as <-. cbn [access_value ms_regs]. exact K.
Qed.

Lemma step_rfull : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> rfull (ms_regs ms) -> rfull (ms_regs ms').
Proof.
  intros ms ms' E HR. unfold RiscvSemantics.step, RiscvSemantics.step_accesses in E.
  assert (D : forall w, drop_access_report (decode_exec_accesses segs ms w) = MachineOk ms' -> rfull (ms_regs ms')).
  { intros w Ew. destruct (decode_exec_accesses segs ms w) as [r| |] eqn:Er; try discriminate.
    cbn in Ew. injection Ew as <-. exact (decode_exec_accesses_full ms w r HR Er). }
  destruct (fetch_word segs (ms_pc ms)); [exact (D _ E)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)); [exact (D _ E)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)); [exact (D _ E)|].
  unfold fetch_failure in E. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Lemma msteps_rfull : forall ms ms', msteps segs ms ms' -> rfull (ms_regs ms) -> rfull (ms_regs ms').
Proof.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 [_ Hs] _ IH]; intros HR; [exact HR|].
  apply IH. exact (step_rfull _ _ Hs HR).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive wrel : (word -> option byte) -> (word -> option byte) -> Prop :=
| wrel_refl : forall m, wrel m m
| wrel_store : forall m a bs m', store_ok segs m a (length bs) = true -> wrel (write_to_mem m a bs) m' -> wrel m m'.

Lemma wrel_trans : forall a b c, wrel a b -> wrel b c -> wrel a c.
Proof. intros a b c H. induction H; intros K; [exact K|]. eapply wrel_store; [eassumption|]. apply IHwrel. exact K. Qed.

Lemma interp_eff_accesses_wrel : forall t m r,
  interp_eff_accesses segs t m = MachineOk r -> wrel m (snd (access_value _ r)).
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r E; cbn [interp_eff_accesses] in E; try discriminate.
  - injection E as <-. apply wrel_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k _) m) as [r'| |] eqn:E'; try discriminate.
    injection E as <-. cbn [access_value]. exact (IH _ _ _ E').
  - destruct (store_ok segs m a (width_bytes n)) eqn:Hok; [|discriminate].
    destruct (interp_eff_accesses segs k _) as [r'| |] eqn:E'; try discriminate.
    injection E as <-. cbn [access_value].
    eapply wrel_store; [|exact (IH _ _ E')]. rewrite length_Z_to_le_bytes. exact Hok.
Qed.

Lemma step_wrel : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> wrel (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' E. unfold RiscvSemantics.step, RiscvSemantics.step_accesses in E.
  assert (D : forall w, drop_access_report (decode_exec_accesses segs ms w) = MachineOk ms' -> wrel (ms_mem ms) (ms_mem ms')).
  { intros w Ew. destruct ms as [R F pc svc rv fc m ro]. unfold decode_exec_accesses in Ew. cbn [ms_mem] in *.
    destruct (is_ecall w).
    - cbn in Ew. injection Ew as <-. apply wrel_refl.
    - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
      cbn in Ew.
      destruct (interp_eff_accesses segs (exec _ i (Core R F pc fc rv)) m) as [[[c m1] acc]| |] eqn:E1; try discriminate.
      pose proof (interp_eff_accesses_wrel _ _ _ E1) as K. cbn [access_value snd] in K.
      cbn in Ew. injection Ew as <-. cbn [ms_mem]. exact K. }
  destruct (fetch_word segs (ms_pc ms)); [exact (D _ E)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)); [exact (D _ E)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)); [exact (D _ E)|].
  unfold fetch_failure in E. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Lemma msteps_wrel : forall ms ms', msteps segs ms ms' -> wrel (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 [_ Hs] _ IH]; [apply wrel_refl|].
  eapply wrel_trans; [exact (step_wrel _ _ Hs) | exact IH].
Qed.

(* [comment removed for export] *)
Lemma wrel_mem_inv : forall m m', wrel m m' -> mem_inv segs m -> mem_inv segs m'.
Proof. intros m m' H. induction H; intros MI; [exact MI|]. apply IHwrel. apply mem_inv_store; assumption. Qed.

Lemma wrel_wmono : forall m m', wrel m m' -> wmono segs m m'.
Proof.
  intros m m' H. induction H; [apply wmono_refl|].
  eapply wmono_trans; [|exact IHwrel]. intros x Hx. apply wview_write_mono. exact Hx.
Qed.

Lemma mrd_write_mono : forall bs m a x, (exists b, mrd segs m x = Some b) -> exists b, mrd segs (write_to_mem m a bs) x = Some b.
Proof.
  induction bs as [|b0 bs IH]; intros m a x H; cbn [write_to_mem]; [exact H|].
  apply IH. unfold mrd in *. destruct (bv_eqb x a); [eexists; reflexivity | exact H].
Qed.

Lemma wrel_stk : forall m m', wrel m m' -> forall lo hi, stk segs m lo hi -> stk segs m' lo hi.
Proof.
  intros m m' H. induction H; intros lo hi S; [exact S|].
  apply IHwrel. destruct S as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|].
  intros x Hx. destruct (S3 x Hx) as [Hw Hr]. split; [apply wview_write_mono; exact Hw | apply mrd_write_mono; exact Hr].
Qed.

End WithSegs.
