(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain FxRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mkRl (l : list word) : bvmap 5 word :=
  Frame.mkR (nth 0 l w0) (nth 1 l w0) (nth 2 l w0) (nth 3 l w0) (nth 4 l w0) (nth 5 l w0) (nth 6 l w0) (nth 7 l w0)
      (nth 8 l w0) (nth 9 l w0) (nth 10 l w0) (nth 11 l w0) (nth 12 l w0) (nth 13 l w0) (nth 14 l w0) (nth 15 l w0)
      (nth 16 l w0) (nth 17 l w0) (nth 18 l w0) (nth 19 l w0) (nth 20 l w0) (nth 21 l w0) (nth 22 l w0) (nth 23 l w0)
      (nth 24 l w0) (nth 25 l w0) (nth 26 l w0) (nth 27 l w0) (nth 28 l w0) (nth 29 l w0) (nth 30 l w0).

Definition canonR (R : bvmap 5 word) : Prop := exists l, R = mkRl l.

Lemma canonR_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  canonR (Frame.mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof.
  intros. exists [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31].
  reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint lupd (n : nat) (v : word) (l : list word) : list word :=
  match n, l with
  | O, [] => [v]
  | O, _ :: r => v :: r
  | S n', [] => w0 :: lupd n' v []
  | S n', x :: r => x :: lupd n' v r
  end.

Lemma nth_lupd : forall n k v l, nth k (lupd n v l) w0 = if Nat.eqb k n then v else nth k l w0.
Proof.
  induction n as [|n IH]; intros k v l; destruct l as [|x r]; destruct k as [|k]; cbn [lupd nth Nat.eqb]; try reflexivity.
  - destruct k; reflexivity.
  - rewrite IH. destruct (Nat.eqb k n); destruct k; reflexivity.
  - apply IH.
Qed.

(* [comment removed for export] *)
Lemma tset_mkRl : forall (n : nat) v l, (n < 31)%nat ->
  tset (Pos.of_nat (n + 2)) v (mkRl l) = mkRl (lupd n v l).
Proof.
  intros n v l Hn. unfold mkRl. rewrite !nth_lupd.
  do 31 (destruct n as [|n]; [cbn; reflexivity |]). lia.
Qed.

Lemma canonR_set : forall (r : reg) v R, is_x0 r = false -> canonR R -> canonR (bvmap_set r v R).
Proof.
  intros r v R Hr [l ->]. unfold is_x0 in Hr. apply Z.eqb_neq in Hr.
  pose proof (bv_unsigned_in_range _ r) as Hrng. change (bv_modulus 5) with 32 in Hrng.
  unfold bvmap_set, bv_key.
  set (n := Z.to_nat (bv_unsigned r - 1)).
  replace (Z.to_pos (bv_unsigned r + 1)) with (Pos.of_nat (n + 2)) by (subst n; lia).
  exists (lupd n v l). apply tset_mkRl. subst n. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma c_regs_rset : forall rd v c,
  c_regs (Sem.rset rd v c) = if is_x0 rd then c_regs c else bvmap_set rd v (c_regs c).
Proof. intros rd v c. unfold Sem.rset. destruct (is_x0 rd); reflexivity. Qed.
Lemma c_regs_with_pc : forall p c, c_regs (with_pc p c) = c_regs c. Proof. reflexivity. Qed.
Lemma c_regs_with_resv : forall p c, c_regs (with_resv p c) = c_regs c. Proof. reflexivity. Qed.
Lemma c_regs_inval_resv : forall a c, c_regs (inval_resv a c) = c_regs c.
Proof. intros a c. unfold inval_resv. destruct (c_resv c) as [r|]; [|reflexivity].
  destruct (bv_unsigned r =? bv_unsigned a)%Z; reflexivity. Qed.

Lemma canonR_rset : forall rd v c, canonR (c_regs c) -> canonR (c_regs (Sem.rset rd v c)).
Proof.
  intros rd v c H. rewrite c_regs_rset. destruct (is_x0 rd) eqn:E; [exact H|].
  apply canonR_set; [exact E | exact H].
Qed.

(* [comment removed for export] *)
Inductive ecanon : eff -> Prop :=
| ec_done : forall c, canonR (c_regs c) -> ecanon (EDone c)
| ec_illegal : forall c, ecanon (EIllegal c)
| ec_defined_illegal : forall c, ecanon (EDefinedIllegal c)
| ec_ecall : forall c, ecanon (EEcall c)
| ec_ebreak : forall c, ecanon (EEbreak c)
| ec_fault : forall c, ecanon (EFault c)
| ec_load : forall n a k, (forall v, ecanon (k v)) -> ecanon (ELoad n a k)
| ec_store : forall n a v k, ecanon k -> ecanon (EStore n a v k).

Ltac canon_leaf :=
  repeat first [ apply canonR_rset
               | rewrite c_regs_with_pc
               | rewrite c_regs_with_resv
               | rewrite c_regs_inval_resv ];
  assumption.

Ltac ecanon_tac :=
  repeat first
    [ apply ec_done; canon_leaf
    | apply ec_illegal | apply ec_defined_illegal | apply ec_ecall
    | apply ec_ebreak | apply ec_fault
    | apply ec_load; intros ?
    | apply ec_store
    | match goal with
      | |- ecanon (if ?x then _ else _) => destruct x
      | |- ecanon (match ?x with _ => _ end) => destruct x
      | |- ecanon ((match ?x with _ => _ end) _) => destruct x
      | |- ecanon (?f (match ?x with _ => _ end)) => destruct x
      | |- ecanon (?f (match ?x with _ => _ end) _) => destruct x
      end ].

(* [comment removed for export] *)
Lemma exec_canon : forall pc i fi sz c,
  compile pc i = Some fi -> canonR (c_regs c) -> ecanon (exec sz i c).
Proof.
  intros pc i fi sz c Hc HR.
  destruct i; cbn [compile] in Hc; try discriminate Hc;
    cbn [exec]; unfold load_val, store_val; cbv zeta; ecanon_tac.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma interp_canon : forall t, ecanon t -> forall m report,
  interp_eff_accesses segs t m = MachineOk report ->
  canonR (c_regs (fst (@access_value _ report))).
Proof.
  intros t Ht. induction Ht as [c Hc | c | c | c | c | c | n a k Hk IH | n a v k Hk IH];
    intros m report H; cbn [interp_eff_accesses] in H; try discriminate H.
  - inversion H; subst. cbn. exact Hc.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs |]; [| discriminate H].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m)
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [access_value]. exact (IH _ m r0 E).
  - destruct (store_ok segs m a (width_bytes n)); [| discriminate H].
    destruct (interp_eff_accesses segs k
                (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v))))
      as [r0 | |] eqn:E; try discriminate H.
    inversion H; subst. cbn [access_value]. exact (IH _ r0 E).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Variable IM : fimage.
Variable rho : int -> word.
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Variable code : itrie finstr.
Variable RO : itrie unit.
Hypothesis Hcode : code_ok segs code.

Local Abbreviation Rr := (R segs IM rho).

Theorem fx_step_canon : forall F ms F' ms',
  Rr F ms -> fx_step IM code RO F = FNext F' -> step segs ms = MachineOk ms' ->
  canonR (ms_regs ms) -> canonR (ms_regs ms').
Proof.
  intros F ms F' ms' HR H Hs HC. unfold fx_step in H.
  destruct (iget (f_pc F) code) as [fi|] eqn:Hi; [|discriminate].
  destruct (code_entry segs IM rho code Hcode F ms fi HR Hi)
    as (Hpc & w & Hf & [[He ->] | (He & i & Hd & Hc)]); [discriminate|].
  unfold step, step_accesses in Hs. rewrite Hf in Hs. unfold decode_exec_accesses in Hs. rewrite He, Hd in Hs.
  match type of Hs with
  | context [interp_eff_accesses segs (exec ?szw i ?c0) ?m0] =>
      destruct (interp_eff_accesses segs (exec szw i c0) m0) as [report | |] eqn:E; try discriminate Hs;
      pose proof (interp_canon _ (exec_canon (to_Z (f_pc F)) i fi szw c0 Hc HC) _ _ E) as HC'
  end.
  cbn [drop_access_report] in Hs.
  destruct report as [[c' m'] acc]. cbn [access_value fst] in HC', Hs.
  injection Hs as <-. cbn [ms_regs]. exact HC'.
Qed.

Theorem fx_run_canon : forall bp k F F' r cnt,
  (k <= 61)%nat ->
  fx_run IM code RO bp k F = (F', r, cnt) ->
  forall ms ms', Rr F ms -> rsteps segs (nat_of_int cnt) ms = MachineOk ms' ->
  canonR (ms_regs ms) -> canonR (ms_regs ms').
Proof.
  intros bp k. induction k as [|k IH]; intros F F' r cnt Hk H ms ms' HR Hn HC.
  - cbn [fx_run] in H. destruct (f_pc F =? bp)%uint63.
    { injection H as <- <- <-. change (nat_of_int 0) with 0%nat in Hn. cbn [rsteps] in Hn. congruence. }
    destruct (fx_step IM code RO F) as [s'| |c] eqn:Es; injection H as <- <- <-;
      try (change (nat_of_int 0) with 0%nat in Hn; cbn [rsteps] in Hn; congruence).
    destruct (fx_step_sound segs IM rho Hrho0 code RO Hcode F ms s' HR Es) as (ms1 & Hs & _).
    change (nat_of_int 1) with 1%nat in Hn. cbn [rsteps] in Hn. rewrite (R_svc _ _ _ _ _ HR), Hs in Hn.
    injection Hn as <-. exact (fx_step_canon F ms s' ms1 HR Es Hs HC).
  - cbn [fx_run] in H. destruct (fx_run IM code RO bp k F) as [[s1 r1] n1] eqn:E1.
    destruct (fx_run_sound segs IM rho Hrho0 code RO Hcode bp k F s1 r1 n1 ltac:(lia) E1) as (Hb1 & IH1).
    assert (Hpow : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k) by (rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia).
    assert (Hlt : 2 ^ Z.of_nat (S k) <= 2 ^ 62) by (apply Z.pow_le_mono_r; lia).
    destruct (IH1 ms HR) as (ms1 & Hn1 & HR1 & _).
    destruct (stop_is_fuel r1) eqn:Er.
    + destruct (fx_run IM code RO bp k s1) as [[s2 r2] n2] eqn:E2. injection H as <- <- <-.
      destruct (fx_run_sound segs IM rho Hrho0 code RO Hcode bp k s1 s2 r2 n2 ltac:(lia) E2) as (Hb2 & IH2).
      destruct (IH2 ms1 HR1) as (ms2 & Hn2 & _).
      pose proof (Uint63.to_Z_bounded n1). pose proof (Uint63.to_Z_bounded n2).
      assert (Hadd : to_Z (n1 + n2)%uint63 = to_Z n1 + to_Z n2).
      { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2^63). lia. }
      assert (Hn12 : rsteps segs (nat_of_int (n1 + n2)%uint63) ms = MachineOk ms2).
      { unfold nat_of_int. rewrite Hadd, Z2Nat.inj_add by lia. exact (rsteps_trans segs _ _ _ _ _ Hn1 Hn2). }
      rewrite Hn12 in Hn. injection Hn as <-.
      exact (IH _ _ _ _ ltac:(lia) E2 ms1 ms2 HR1 Hn2 (IH _ _ _ _ ltac:(lia) E1 ms ms1 HR Hn1 HC)).
    + injection H as <- <- <-. rewrite Hn1 in Hn. injection Hn as <-.
      exact (IH _ _ _ _ ltac:(lia) E1 ms ms1 HR Hn1 HC).
Qed.

(* [comment removed for export] *)
Definition rv (F : fstate) (r : Z) : word := dv rho (FxState.rget F (of_Z r)).

Lemma reg_get_mkRl : forall l (r : reg), is_x0 r = false ->
  reg_get (mkRl l) r = nth (Z.to_nat (bv_unsigned r - 1)) l w0.
Proof.
  intros l r Hr. unfold is_x0 in Hr. apply Z.eqb_neq in Hr.
  pose proof (bv_unsigned_in_range _ r) as Hrng. change (bv_modulus 5) with 32 in Hrng.
  unfold reg_get, bvmap_get, bv_key.
  set (n := Z.to_nat (bv_unsigned r - 1)).
  replace (Z.to_pos (bv_unsigned r + 1)) with (Pos.of_nat (n + 2)) by (subst n; lia).
  assert (Hn : (n < 31)%nat) by (subst n; lia). clearbody n.
  unfold mkRl.
  do 31 (destruct n as [|n]; [cbn -[nth]; reflexivity |]). lia.
Qed.

Theorem canonR_R : forall F ms,
  Rr F ms -> canonR (ms_regs ms) ->
  ms = MS (Frame.mkR (rv F 1) (rv F 2) (rv F 3) (rv F 4) (rv F 5) (rv F 6) (rv F 7) (rv F 8) (rv F 9) (rv F 10)
               (rv F 11) (rv F 12) (rv F 13) (rv F 14) (rv F 15) (rv F 16) (rv F 17) (rv F 18) (rv F 19) (rv F 20)
               (rv F 21) (rv F 22) (rv F 23) (rv F 24) (rv F 25) (rv F 26) (rv F 27) (rv F 28) (rv F 29) (rv F 30) (rv F 31))
          (ms_fregs ms) (Z_to_bv 64 (to_Z (f_pc F))) (ms_fcsr ms) (option_map (dv rho) (f_resv F)) (ms_mem ms) (ms_rom ms).
Proof.
  intros F ms HR [l El].
  pose proof (R_regs _ _ _ _ _ HR) as Hregs.
  assert (Hl : forall k : nat, (k < 31)%nat -> nth k l w0 = rv F (Z.of_nat k + 1)).
  { intros k Hk. specialize (Hregs (Z_to_bv 5 (Z.of_nat k + 1))).
    unfold Sem.rget in Hregs. cbn [core_of c_regs] in Hregs. rewrite El in Hregs.
    assert (Hx : is_x0 (Z_to_bv 5 (Z.of_nat k + 1)) = false).
    { unfold is_x0. rewrite Z_to_bv_unsigned. apply Z.eqb_neq. unfold bv_wrap. change (bv_modulus 5) with 32.
      rewrite Z.mod_small; lia. }
    rewrite Hx in Hregs. rewrite reg_get_mkRl in Hregs by exact Hx.
    rewrite Z_to_bv_unsigned in Hregs. unfold bv_wrap in Hregs. change (bv_modulus 5) with 32 in Hregs.
    rewrite Z.mod_small in Hregs by lia.
    replace (Z.to_nat (Z.of_nat k + 1 - 1)) with k in Hregs by lia.
    rewrite Hregs. unfold rv, ireg. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. reflexivity. }
  rewrite (MS_eta ms) at 1 by exact (R_svc _ _ _ _ _ HR).
  rewrite <- (R_pc _ _ _ _ _ HR), <- (R_resv _ _ _ _ _ HR). f_equal.
  rewrite El. unfold mkRl.
  rewrite !(Hl _) by lia. reflexivity.
Qed.
End WithSegs.
