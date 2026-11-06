(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim FPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require FrmKeep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FRMC.

Definition csr_frm_unsafe (writes : bool) (csr : bv 12) : bool :=
  writes && ((bv_unsigned csr =? 2) || (bv_unsigned csr =? 3)).
Definition csr_writes (op : csrop) (nz : bool) : bool := match op with CSR_RW => true | _ => nz end.

Definition op_clear (op : csrop) : bool := match op with CSR_RC => true | _ => false end.
Definition instr_frm_safe (i : instr) : bool :=
  match i with
  | Csr op rd rs1 csr => op_clear op || negb (csr_frm_unsafe (csr_writes op (negb (is_x0 rs1))) csr)
  | CsrI op rd uimm csr => op_clear op || negb (csr_frm_unsafe (csr_writes op (negb (Z.eqb (bv_unsigned uimm) 0))) csr)
  | _ => true
  end.
Definition word_frm_safe (w : bv 32) : bool :=
  match decode_any w with Some (i, _) => instr_frm_safe i | None => true end.

Fixpoint eff_fz (e : eff) : Prop :=
  match e with
  | EDone c => frm_zero (c_fcsr c)
  | ELoad n a k => forall v, eff_fz (k v)
  | EStore n a v k => eff_fz k
  | _ => True
  end.

Lemma fc_rset r v c : c_fcsr (rset r v c) = c_fcsr c.
Proof. unfold rset. destruct (is_x0 r); [reflexivity|]. destruct c; reflexivity. Qed.
Lemma fc_with_pc v c : c_fcsr (with_pc v c) = c_fcsr c. Proof. destruct c; reflexivity. Qed.
Lemma fc_with_resv v c : c_fcsr (with_resv v c) = c_fcsr c. Proof. destruct c; reflexivity. Qed.
Lemma fc_with_regs f c : c_fcsr (with_regs f c) = c_fcsr c. Proof. destruct c; reflexivity. Qed.
Lemma fc_with_fregs f c : c_fcsr (with_fregs f c) = c_fcsr c. Proof. destruct c; reflexivity. Qed.
Lemma fc_fset r v c : c_fcsr (fset r v c) = c_fcsr c. Proof. unfold fset. apply fc_with_fregs. Qed.
Lemma fc_fwrite fmt r v c : c_fcsr (fwrite fmt r v c) = c_fcsr c. Proof. unfold fwrite. destruct fmt; apply fc_fset. Qed.
Lemma fc_inval_resv a c : c_fcsr (inval_resv a c) = c_fcsr c.
Proof. unfold inval_resv. destruct (c_resv c) as [r0|]; [destruct (bv_unsigned r0 =? bv_unsigned a); [apply fc_with_resv| reflexivity]| reflexivity]. Qed.
Lemma fc_accrue fl c : c_fcsr (accrue fl c) = Z_to_bv 32 (Z.lor (bv_unsigned (c_fcsr c)) (fflags_bits fl)).
Proof. destruct c; reflexivity. Qed.
Lemma fz_accrue fl c : frm_zero (c_fcsr c) -> frm_zero (c_fcsr (accrue fl c)).
Proof. intros H. rewrite fc_accrue. apply fp_frm_zero_accrue; [apply fp_fflags_bits_range| exact H]. Qed.

Ltac fz_core FZ :=
  repeat first [ exact FZ
               | rewrite fc_rset | rewrite fc_with_pc | rewrite fc_with_resv | rewrite fc_with_regs | rewrite fc_fset
               | rewrite fc_fwrite | rewrite fc_inval_resv | apply fz_accrue ].

Ltac fz_tree FZ :=
  repeat first [ lazymatch goal with
                 | |- eff_fz (match ?x with _ => _ end) => destruct x
                 | |- eff_fz ((match ?x with _ => _ end) _) => destruct x
                 | |- eff_fz (EDone _) => cbn [eff_fz]
                 | |- eff_fz (ELoad _ _ _) => cbn [eff_fz]; intros ?
                 | |- eff_fz (EStore _ _ _ _) => cbn [eff_fz]
                 | |- eff_fz (exec_csr _ _ _ _ _ _) => fail
                 | |- eff_fz _ => exact I
                 | |- frm_zero (c_fcsr (match ?x with _ => _ end)) => destruct x
                 | |- frm_zero _ => progress (fz_core FZ)
                 end ].

Lemma fz_bits (u : Z) : Z.land (Z.shiftr u 5) 7 = 0 <-> (forall i, 5 <= i < 8 -> Z.testbit u i = false).
Proof.
  split.
  - intros H i Hi. assert (T : Z.testbit (Z.land (Z.shiftr u 5) 7) (i - 5) = false) by (rewrite H; apply Z.bits_0).
    rewrite Z.land_spec, Z.shiftr_spec in T by lia. replace (i - 5 + 5) with i in T by lia.
    assert (B : Z.testbit 7 (i - 5) = true) by (assert (i - 5 = 0 \/ i - 5 = 1 \/ i - 5 = 2) as [->|[->| ->]] by lia; reflexivity).
    rewrite B, andb_true_r in T. exact T.
  - intros H. apply Z.bits_inj'. intros n Hn. rewrite Z.bits_0, Z.land_spec, Z.shiftr_spec by lia.
    destruct (Z_lt_dec n 3) as [Lt|Ge].
    + rewrite H by lia. reflexivity.
    + replace (Z.testbit 7 n) with false; [apply andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. change (Z.log2 7) with 2. lia.
Qed.

Lemma fz_clear (f : bv 32) (lo len : Z) (y : word) :
  ((lo = 5 /\ len = 3) \/ (lo = 0 /\ len = 8)) -> frm_zero f -> frm_zero (slice_set f lo len (bv_and (slice_get f lo len) y)).
Proof.
  intros C FZ. unfold frm_zero in *. apply fz_bits. intros i Hi. pose proof (proj1 (fz_bits _) FZ) as B.
  assert (I3 : i = 5 \/ i = 6 \/ i = 7) by lia.
  unfold slice_set. rewrite Z_to_bv_unsigned, bv_wrap_spec_low by (cbn; lia).
  rewrite Z.lor_spec. apply orb_false_iff. split.
  - rewrite Z.land_spec. replace (Z.testbit (Z.lnot (Z.shiftl (Z.ones len) lo)) i) with false; [apply andb_false_r|].
    destruct C as [[-> ->]|[-> ->]]; destruct I3 as [->|[->| ->]]; reflexivity.
  - rewrite Z.land_spec. replace (Z.testbit (Z.shiftl (bv_unsigned (bv_and (slice_get f lo len) y)) lo) i) with false; [reflexivity|]. symmetry.
    rewrite Z.shiftl_spec by lia. rewrite bv_and_unsigned, Z.land_spec. unfold slice_get. rewrite Z_to_bv_unsigned.
    assert (LO : 0 <= i - lo < 64) by (destruct C as [[-> ->]|[-> ->]]; lia).
    rewrite bv_wrap_spec_low by (cbn; lia). rewrite Z.land_spec, Z.shiftr_spec by lia. replace (i - lo + lo) with i by lia.
    rewrite (B i Hi). reflexivity.
Qed.

Lemma exec_csr_fz op rd operand writes csr c :
  frm_zero (c_fcsr c) -> op_clear op || negb (csr_frm_unsafe writes csr) = true -> eff_fz (exec_csr op rd operand writes csr c).
Proof.
  intros FZ SF. unfold exec_csr, csr_slice. cbv zeta. unfold csr_frm_unsafe in SF.
  destruct (Z.eqb_spec (bv_unsigned csr) 1) as [E1|N1].
  - cbn [eff_fz]. rewrite fc_rset. destruct writes; [| exact FZ]. apply fp_frm_zero_slice0_5. exact FZ.
  - destruct (Z.eqb_spec (bv_unsigned csr) 2) as [E2|N2].
    + cbn [eff_fz]. rewrite fc_rset. destruct writes; [| exact FZ].
      destruct op; cbn in SF; try discriminate SF.
      cbn. apply fz_clear; [left; split; reflexivity| exact FZ].
    + destruct (Z.eqb_spec (bv_unsigned csr) 3) as [E3|N3]; [| exact I].
      cbn [eff_fz]. rewrite fc_rset. destruct writes; [| exact FZ].
      destruct op; cbn in SF; try discriminate SF.
      cbn. apply fz_clear; [right; split; reflexivity| exact FZ].
Qed.

Lemma exec_fz (sz : word) (i : instr) (c : core) :
  frm_zero (c_fcsr c) -> instr_frm_safe i = true -> eff_fz (exec sz i c).
Proof.
  intros FZ SF. destruct i; cbv beta iota zeta delta [exec load_val store_val]; try (fz_tree FZ).
  -   cbn [instr_frm_safe] in SF. apply exec_csr_fz; [fz_core FZ| exact SF].
  -   cbn [instr_frm_safe] in SF. apply exec_csr_fz; [fz_core FZ| exact SF].
Qed.

Lemma interp_fz segs : forall e m rep, eff_fz e -> interp_eff_accesses segs e m = MachineOk rep -> frm_zero (c_fcsr (fst (@access_value _ rep))).
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

Lemma decode_exec_fz segs st w rep :
  frm_zero (ms_fcsr st) -> word_frm_safe w = true -> decode_exec_accesses segs st w = MachineOk rep -> frm_zero (ms_fcsr (@access_value _ rep)).
Proof.
  intros FZ SF H. unfold decode_exec_accesses in H. unfold word_frm_safe in SF.
  destruct (is_ecall w); [injection H as <-; exact FZ|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
  destruct (interp_eff_accesses _ _) as [r| | ] eqn:E; try discriminate.
  pose proof (interp_fz segs _ _ r (exec_fz (Z_to_bv 64 isz) i (Core (ms_regs st) (ms_fregs st) (ms_pc_val st) (ms_fcsr st) (ms_resv st)) FZ SF) E) as FZ'.
  destruct (@access_value _ r) as [c m'] eqn:Er. cbv beta iota zeta in H. injection H as <-. cbn [access_value ms_fcsr fst] in *. exact FZ'.
Qed.

Lemma find_segment_In : forall l a n seg, find_segment l a n = Some seg -> In seg l.
Proof.
  induction l as [|s l IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (_ && _); [injection H as <-; left; reflexivity| right; exact (IH _ _ _ H)].
Qed.
Lemma find_segment_range : forall l a n seg, find_segment l a n = Some seg ->
  Z.of_N (seg_base seg) <= a /\ a + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  induction l as [|s l IH]; intros a n seg H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb_spec (Z.of_N (seg_base s)) a) as [L1|L1]; destruct (Z.leb_spec (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))) as [L2|L2]; cbn [andb] in H;
    first [injection H as <-; split; assumption | exact (IH _ _ _ H)].
Qed.

Section Generic.
Variable segs : list Segment. Context {bmK : BMode}.

Hypothesis no_wx : forall seg, In seg segs -> seg_executable seg && seg_writable seg = false.

Lemma code_read_ov_none m a n : code_read_ov segs m a n = None.
Proof.
  unfold code_read_ov. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|reflexivity].
  rewrite (no_wx seg (find_segment_In _ _ _ _ E)). reflexivity.
Qed.
Lemma fetch_word_ov_none m a : fetch_word_ov segs m a = None.
Proof. unfold fetch_word_ov. rewrite code_read_ov_none. destruct (negb _); reflexivity. Qed.
Lemma fetch_half_any_eq m a : fetch_half_any segs m a = fetch_half segs a.
Proof. unfold fetch_half_any. destruct (fetch_half segs a); [reflexivity|]. unfold fetch_half_ov. rewrite code_read_ov_none. reflexivity. Qed.
Lemma fetch_tail_any_eq m a : fetch_tail_any segs m a = fetch_tail segs a.
Proof. unfold fetch_tail_any, fetch_tail. rewrite !fetch_half_any_eq. reflexivity. Qed.

Lemma code_read_seg a n bs : code_read segs a n = Some bs ->
  exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + Z.of_N n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold code_read. destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:E; [|discriminate].
  destruct (seg_executable seg) eqn:X; [|discriminate]. intros _. exists seg.
  split; [exact (find_segment_In _ _ _ _ E)|]. split; [exact X|]. exact (find_segment_range _ _ _ _ E).
Qed.
Lemma fetch_word_seg a w : fetch_word segs a = Some w ->
  bv_unsigned a mod 2 = 0 /\ exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 4 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold fetch_word. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  destruct (code_read segs a 4) as [bs|] eqn:C; [|discriminate]. intros _. split; [exact E|]. exact (code_read_seg a 4 bs C).
Qed.
Lemma fetch_tail_seg a w : fetch_tail segs a = Some w ->
  bv_unsigned a mod 2 = 0 /\ exists seg, In seg segs /\ seg_executable seg = true /\ Z.of_N (seg_base seg) <= bv_unsigned a /\ bv_unsigned a + 2 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg).
Proof.
  unfold fetch_tail. destruct (Z.eqb_spec (bv_unsigned a mod 2) 0) as [E|NE]; cbn [negb]; [|discriminate].
  unfold fetch_half at 1. destruct (code_read segs a 2) as [bs|] eqn:C; [|discriminate]. intros _. split; [exact E|]. exact (code_read_seg a 2 bs C).
Qed.

Definition ok_at (a : Z) : bool :=
  (match fetch_word segs (Z_to_bv 64 a) with Some w => word_frm_safe w | None => true end)
  && (match fetch_tail segs (Z_to_bv 64 a) with Some w => word_frm_safe w | None => true end).
Fixpoint scan1 (f : nat) (a : Z) : bool := match f with O => true | S f' => ok_at a && scan1 f' (a + 2) end.
Fixpoint scan2 (g f : nat) (a : Z) : bool := match g with O => true | S g' => scan1 f a && scan2 g' f (a + 2 * Z.of_nat f) end.

Lemma scan1_sound : forall f a0, scan1 f a0 = true -> forall a, a0 <= a < a0 + 2 * Z.of_nat f -> (a - a0) mod 2 = 0 -> ok_at a = true.
Proof.
  induction f as [|f IH]; intros a0 H a Ha Hm; [cbn [Z.of_nat] in Ha; lia|].
  cbn [scan1] in H. apply andb_true_iff in H as [H0 H1].
  destruct (Z.eq_dec a a0) as [->|NE]; [exact H0|].
  apply (IH (a0 + 2) H1); [lia|]. replace (a - (a0 + 2)) with (a - a0 + (-1) * 2) by lia. rewrite Z.mod_add by lia. exact Hm.
Qed.
Lemma scan2_sound : forall g f a0, scan2 g f a0 = true -> forall a, a0 <= a < a0 + 2 * Z.of_nat f * Z.of_nat g -> (a - a0) mod 2 = 0 -> ok_at a = true.
Proof.
  induction g as [|g IH]; intros f a0 H a Ha Hm; [cbn [Z.of_nat] in Ha; lia|].
  cbn [scan2] in H. apply andb_true_iff in H as [H0 H1].
  destruct (Z_lt_le_dec a (a0 + 2 * Z.of_nat f)) as [LT|GE].
  - exact (scan1_sound f a0 H0 a ltac:(lia) Hm).
  - apply (IH f (a0 + 2 * Z.of_nat f) H1); [lia|]. replace (a - (a0 + 2 * Z.of_nat f)) with (a - a0 + (- Z.of_nat f) * 2) by lia.
    rewrite Z.mod_add by lia. exact Hm.
Qed.

Theorem fetch_safe_of_scan (xlo xsz : Z) (g f : nat) :
  (forall seg, In seg segs -> seg_executable seg = true -> Z.of_N (seg_base seg) = xlo /\ Z.of_N (seg_size seg) = xsz) ->
  xlo mod 2 = 0 -> xsz <= 2 * Z.of_nat f * Z.of_nat g -> scan2 g f xlo = true ->
  forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> word_frm_safe w = true.
Proof.
  intros XS XE COV SC a w H.
  assert (R : bv_unsigned a mod 2 = 0 /\ xlo <= bv_unsigned a < xlo + xsz).
  { destruct H as [H|H]; [destruct (fetch_word_seg a w H) as (E & seg & IN & X & B1 & B2)| destruct (fetch_tail_seg a w H) as (E & seg & IN & X & B1 & B2)];
      destruct (XS seg IN X) as (EB & ES); split; [exact E| lia| exact E| lia]. }
  destruct R as (EA & RA).
  assert (OK : ok_at (bv_unsigned a) = true).
  { apply (scan2_sound g f xlo SC); [lia|]. rewrite Zminus_mod, EA, XE. reflexivity. }
  unfold ok_at in OK. rewrite Z_to_bv_bv_unsigned in OK. apply andb_true_iff in OK as [O1 O2].
  destruct H as [H|H]; [rewrite H in O1; exact O1| rewrite H in O2; exact O2].
Qed.

Hypothesis fetch_safe : forall a w, fetch_word segs a = Some w \/ fetch_tail segs a = Some w -> word_frm_safe w = true.

Theorem step_fz : forall s s', RiscvSemantics.step segs s = MachineOk s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
  intros s s' H FZ. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc s)) as [w|] eqn:F1.
  - destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
    exact (decode_exec_fz segs s w r FZ (fetch_safe _ _ (or_introl F1)) E).
  - rewrite fetch_word_ov_none, fetch_tail_any_eq in H.
    destruct (fetch_tail segs (ms_pc s)) as [w|] eqn:F2.
    + destruct (decode_exec_accesses segs s w) as [r| | ] eqn:E; try discriminate. cbn [drop_access_report] in H. injection H as <-.
      exact (decode_exec_fz segs s w r FZ (fetch_safe _ _ (or_intror F2)) E).
    + exfalso. unfold fetch_failure in H. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

Theorem msteps_fz : forall s s', msteps segs s s' -> frm_zero (ms_fcsr s) -> frm_zero (ms_fcsr s').
Proof.
  intros s s' H. induction H as [ms| ms ms' ms'' P ST MS IH]; intros FZ; [exact FZ|].
  apply IH. exact (step_fz ms ms' ST FZ).
Qed.

Corollary msteps_fz_mkst (fx fx' : FPState) R R' pc pc' M M' :
  msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) -> frm_zero (@fp_csr fx) -> frm_zero (@fp_csr fx').
Proof. intros MS FZ. exact (msteps_fz _ _ MS FZ). Qed.
End Generic.

Lemma safe_of_coarse (w : bv 32) : FrmKeep.FRM.word_frm_safe w = true -> word_frm_safe w = true.
Proof.
  unfold FrmKeep.FRM.word_frm_safe, word_frm_safe. destruct (decode_any w) as [[i sz]|]; [|reflexivity].
  destruct i; cbn [FrmKeep.FRM.instr_frm_safe instr_frm_safe]; try reflexivity; intros H; apply orb_true_iff; right; exact H.
Qed.
End FRMC.
