(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import base.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim FPSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FrmInv.

Definition fp_ok (fx : FPState) : Prop := frm_zero (@fp_csr fx).
Lemma fp_ok_fx0 : fp_ok fx0.
Proof. exact fp_frm_zero_fx0. Qed.

Definition frm_bits0 (z : Z) : Prop := Z.testbit z 5 = false /\ Z.testbit z 6 = false /\ Z.testbit z 7 = false.

Lemma frm_zero_bits : forall f : bv 32, frm_zero f <-> frm_bits0 (bv_unsigned f).
Proof.
  intros f. unfold frm_zero, frm_bits0. split.
  - intros H. assert (T : forall k, 0 <= k < 3 -> Z.testbit (bv_unsigned f) (k + 5) = false).
    { intros k Hk. assert (X : Z.testbit (Z.land (Z.shiftr (bv_unsigned f) 5) 7) k = false) by (rewrite H; apply Z.bits_0).
      rewrite Z.land_spec, Z.shiftr_spec in X by lia.
      assert (Y : Z.testbit 7 k = true) by (assert (k = 0 \/ k = 1 \/ k = 2) as [-> | [-> | ->]] by lia; reflexivity).
      rewrite Y, andb_true_r in X. exact X. }
    repeat split; [exact (T 0 ltac:(lia)) | exact (T 1 ltac:(lia)) | exact (T 2 ltac:(lia))].
  - intros (H5 & H6 & H7). apply Z.bits_inj'. intros n Hn. rewrite Z.bits_0, Z.land_spec, Z.shiftr_spec by lia.
    destruct (Z.eq_dec n 0) as [-> | N0]; [change (0 + 5) with 5; rewrite H5; reflexivity|].
    destruct (Z.eq_dec n 1) as [-> | N1]; [change (1 + 5) with 6; rewrite H6; reflexivity|].
    destruct (Z.eq_dec n 2) as [-> | N2]; [change (2 + 5) with 7; rewrite H7; reflexivity|].
    replace (Z.testbit 7 n) with false; [apply andb_false_r|].
    symmetry. change 7 with (Z.ones 3). apply Z.ones_spec_high. lia.
Qed.

Lemma u32_testbit : forall z i, 0 <= i < 32 -> Z.testbit (bv_unsigned (Z_to_bv 32 z)) i = Z.testbit z i.
Proof. intros z i Hi. rewrite Z_to_bv_unsigned. apply bv_wrap_spec_low. lia. Qed.

Lemma u64_testbit : forall z i, 0 <= i < 64 -> Z.testbit (bv_unsigned (Z_to_bv 64 z)) i = Z.testbit z i.
Proof. intros z i Hi. rewrite Z_to_bv_unsigned. apply bv_wrap_spec_low. lia. Qed.

Lemma frm_zero_accrue : forall (f : bv 32) fl, frm_zero f -> frm_zero (Z_to_bv 32 (Z.lor (bv_unsigned f) (fflags_bits fl))).
Proof. intros f fl H. apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact H]. Qed.

Lemma slice_set_bit : forall (f : bv 32) lo len (v : word) i, 0 <= i < 32 -> 0 <= lo -> 0 <= len ->
  Z.testbit (bv_unsigned (slice_set f lo len v)) i =
  if (Z.leb lo i && Z.ltb i (lo + len))%bool then Z.testbit (bv_unsigned v) (i - lo) else Z.testbit (bv_unsigned f) i.
Proof.
  intros f lo len v i Hi Hlo Hlen. unfold slice_set. rewrite u32_testbit by exact Hi.
  rewrite Z.lor_spec, !Z.land_spec, Z.lnot_spec by lia.
  assert (M : Z.testbit (Z.shiftl (Z.ones len) lo) i = (Z.leb lo i && Z.ltb i (lo + len))%bool).
  { destruct (Z.leb_spec lo i) as [L|L]; cbn [andb].
    - rewrite Z.shiftl_spec by lia. destruct (Z.ltb_spec i (lo + len)) as [L2|L2].
      + apply Z.ones_spec_low. lia.
      + apply Z.ones_spec_high. lia.
    - apply Z.shiftl_spec_low. lia. }
  rewrite M. destruct (Z.leb lo i && Z.ltb i (lo + len))%bool eqn:E; cbn [negb].
  - rewrite andb_false_r, andb_true_r, orb_false_l. apply andb_prop in E as [E1 _]. apply Z.leb_le in E1.
    apply Z.shiftl_spec. lia.
  - rewrite andb_true_r, andb_false_r, orb_false_r. reflexivity.
Qed.

Lemma slice_get_bit : forall (f : bv 32) lo len i, 0 <= i < 64 -> 0 <= lo -> 0 <= len ->
  Z.testbit (bv_unsigned (slice_get f lo len)) i = (Z.ltb i len && Z.testbit (bv_unsigned f) (i + lo))%bool.
Proof.
  intros f lo len i Hi Hlo Hlen. unfold slice_get. rewrite u64_testbit by exact Hi.
  rewrite Z.land_spec, Z.shiftr_spec by lia. rewrite andb_comm. f_equal.
  destruct (Z.ltb_spec i len); [apply Z.ones_spec_low | apply Z.ones_spec_high]; lia.
Qed.

Lemma rc_bit : forall (old x : word) i, Z.testbit (bv_unsigned old) i = false -> 0 <= i < 64 ->
  Z.testbit (bv_unsigned (bv_and old (bv_not x))) i = false.
Proof. intros old x i H Hi. rewrite bv_and_unsigned, Z.land_spec, H. reflexivity. Qed.

Definition csr_frm (csr : bv 12) : bool := (Z.eqb (bv_unsigned csr) 2 || Z.eqb (bv_unsigned csr) 3)%bool.
Definition op_sets (op : csrop) : bool := match op with CSR_RC => false | _ => true end.

Definition frm_bad (i : instr) : bool :=
  match i with
  | Csr op _ rs1 csr => (csr_frm csr && op_sets op && match op with CSR_RW => true | _ => negb (is_x0 rs1) end)%bool
  | CsrI op _ uimm csr => (csr_frm csr && op_sets op && match op with CSR_RW => true | _ => negb (Z.eqb (bv_unsigned uimm) 0) end)%bool
  | _ => false
  end.

Definition cz (c : core) : Prop := frm_zero (c_fcsr c).

Inductive eff_all (P : core -> Prop) : eff -> Prop :=
| EA_done : forall c, P c -> eff_all P (EDone c)
| EA_ill : forall c, eff_all P (EIllegal c)
| EA_dill : forall c, eff_all P (EDefinedIllegal c)
| EA_ecall : forall c, eff_all P (EEcall c)
| EA_ebreak : forall c, eff_all P (EEbreak c)
| EA_fault : forall c, eff_all P (EFault c)
| EA_load : forall n a k, (forall v, eff_all P (k v)) -> eff_all P (ELoad n a k)
| EA_store : forall n a v k, eff_all P k -> eff_all P (EStore n a v k).

Lemma interp_eff_all : forall (segs : list Segment) P t m rep,
  eff_all P t -> interp_eff_accesses segs t m = MachineOk rep -> P (fst (@access_value _ rep)).
Proof.
  intros segs P t m rep H. revert m rep. induction H; intros m rep E; cbn [interp_eff_accesses] in E; try discriminate.
  - injection E as <-. cbn. assumption.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r| |] eqn:E2; try discriminate.
    injection E as <-. cbn [access_value]. eapply H0. exact E2.
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [r| |] eqn:E2; try discriminate.
    injection E as <-. cbn [access_value]. eapply IHeff_all. exact E2.
Qed.

Lemma cz_rset : forall r v c, cz c -> cz (rset r v c).
Proof. intros r v c H. unfold rset. destruct (is_x0 r); exact H. Qed.
Lemma cz_fset : forall r v c, cz c -> cz (fset r v c).
Proof. intros r v c H. exact H. Qed.
Lemma cz_with_pc : forall v c, cz c -> cz (with_pc v c).
Proof. intros v c H. exact H. Qed.
Lemma cz_with_resv : forall v c, cz c -> cz (with_resv v c).
Proof. intros v c H. exact H. Qed.
Lemma cz_inval_resv : forall a c, cz c -> cz (inval_resv a c).
Proof. intros a c H. unfold inval_resv. destruct (c_resv c); [destruct (Z.eqb _ _)|]; exact H. Qed.
Lemma cz_fwrite : forall fmt r v c, cz c -> cz (fwrite fmt r v c).
Proof. intros fmt r v c H. destruct fmt; exact H. Qed.
Lemma cz_accrue : forall fl c, cz c -> cz (accrue fl c).
Proof. intros fl c H. unfold cz, accrue. cbn [c_fcsr with_fcsr]. apply frm_zero_accrue. exact H. Qed.

Create HintDb czdb.
Local Hint Resolve cz_rset cz_fset cz_with_pc cz_with_resv cz_inval_resv cz_fwrite cz_accrue : czdb.

Lemma exec_csr_cz : forall op rd operand (writes : bool) csr c,
  cz c -> (csr_frm csr && op_sets op && writes)%bool = false ->
  eff_all cz (exec_csr op rd operand writes csr c).
Proof.
  intros op rd operand writes csr c H Hb. unfold exec_csr, csr_slice. cbv zeta.
  destruct (Z.eqb_spec (bv_unsigned csr) 1) as [E1|N1].
  {
    constructor. apply cz_rset. destruct writes; [|exact H]. unfold cz. cbn [c_fcsr with_fcsr]. apply fp_frm_zero_slice0_5. exact H. }
  destruct (Z.eqb_spec (bv_unsigned csr) 2) as [E2|N2].
  {
    constructor. apply cz_rset. destruct writes; [|exact H]. unfold csr_frm in Hb. rewrite E2 in Hb. cbn in Hb. rewrite andb_true_r in Hb.
    destruct op; try discriminate. unfold cz in *. cbn [c_fcsr with_fcsr]. apply frm_zero_bits. apply frm_zero_bits in H. destruct H as (H5 & H6 & H7).
    assert (O : forall i, 0 <= i < 3 -> Z.testbit (bv_unsigned (bv_and (slice_get (c_fcsr c) 5 3) (bv_not operand))) i = false).
    { intros i Hi. apply rc_bit; [|lia]. rewrite slice_get_bit by lia.
      assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia; cbn; assumption. }
    unfold frm_bits0. rewrite !slice_set_bit by lia. cbn. repeat split; apply O; lia. }
  destruct (Z.eqb_spec (bv_unsigned csr) 3) as [E3|N3]; [|constructor].
  {
    constructor. apply cz_rset. destruct writes; [|exact H]. unfold csr_frm in Hb. rewrite E3 in Hb. cbn in Hb. rewrite andb_true_r in Hb.
    destruct op; try discriminate. unfold cz in *. cbn [c_fcsr with_fcsr]. apply frm_zero_bits. apply frm_zero_bits in H. destruct H as (H5 & H6 & H7).
    assert (O : forall i, 5 <= i < 8 -> Z.testbit (bv_unsigned (bv_and (slice_get (c_fcsr c) 0 8) (bv_not operand))) i = false).
    { intros i Hi. apply rc_bit; [|lia]. rewrite slice_get_bit by lia. rewrite Z.add_0_r.
      assert (i = 5 \/ i = 6 \/ i = 7) as [-> | [-> | ->]] by lia; cbn; assumption. }
    unfold frm_bits0. rewrite !slice_set_bit by lia. cbn. repeat split; apply O; lia. }
Qed.

Lemma exec_cz : forall sz i c, frm_bad i = false -> cz c -> eff_all cz (exec sz i c).
Proof.
  intros sz i c Hb H.
  destruct i; cbn [exec frm_bad] in *;
    try (constructor; auto 6 with czdb; fail).
  -   unfold load_val. destruct sz0; constructor; intros; constructor; auto with czdb.
  -   unfold store_val. destruct sz0; constructor; constructor; auto with czdb.
  -   destruct (negb (amo_aligned w (rget c rs1))); [constructor|]. destruct w; constructor; intros; constructor; auto 6 with czdb.
  -   destruct (negb (amo_aligned w (rget c rs1))); [constructor|].
    destruct (match c_resv c with Some r => _ | None => false end); [|constructor; auto 6 with czdb].
    destruct w; constructor; constructor; auto 6 with czdb.
  -   destruct (negb (amo_aligned w (rget c rs1))); [constructor|].
    destruct w; constructor; intros; constructor; constructor; auto 6 with czdb.
  -   destruct (csr_write_illegal _ csr); [constructor|]. apply exec_csr_cz; [auto with czdb | exact Hb].
  -   destruct (csr_write_illegal _ csr); [constructor|]. apply exec_csr_cz; [auto with czdb | exact Hb].
  -   destruct fmt; constructor; intros; constructor; auto with czdb.
  -   destruct fmt; constructor; constructor; auto with czdb.
  -   destruct (resolve_rm rm _); [|constructor].
    destruct op; cbv zeta; match goal with |- context [fp_fma ?a ?b ?c ?d ?e] => destruct (fp_fma a b c d e) end; constructor; auto 6 with czdb.
  -   destruct (resolve_rm rm _); [|constructor].
    destruct op; cbv zeta;
      match goal with |- context [let '(_, _) := ?X in _] => destruct X end; constructor; auto 6 with czdb.
  -   destruct (resolve_rm rm _); [|constructor].
    match goal with |- context [let '(_, _) := ?X in _] => destruct X end; constructor; auto 6 with czdb.
  -   constructor. destruct fmt; auto with czdb.
  -   match goal with |- context [let '(_, _) := ?X in _] => destruct X end; constructor; auto 6 with czdb.
  -   destruct op; cbv zeta; match goal with |- context [let '(_, _) := ?X in _] => destruct X end; constructor; auto 6 with czdb.
  -   destruct (resolve_rm rm _); [|constructor]. cbv zeta.
    destruct dst, src; cbn; try constructor;
      try (match goal with |- context [let '(_, _) := ?X in _] => destruct X end; constructor); auto 6 with czdb.
  -   constructor. destruct dir, fmt; auto with czdb.
Qed.

Fixpoint range_all (f : Z -> bool) (a : Z) (n : positive) : bool :=
  match n with
  | xH => f a
  | xO p => (range_all f a p && range_all f (a + Zpos p) p)%bool
  | xI p => (f a && range_all f (a + 1) p && range_all f (a + 1 + Zpos p) p)%bool
  end.

Lemma range_all_sound : forall f n a, range_all f a n = true -> forall z, a <= z < a + Zpos n -> f z = true.
Proof.
  intros f n. induction n as [p IH | p IH |]; intros a H z Hz; cbn [range_all] in H.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    destruct (Z.eq_dec z a) as [-> | N]; [exact H1|].
    destruct (Z_lt_le_dec z (a + 1 + Zpos p)); [apply (IH _ H2); lia | apply (IH _ H3); lia].
  - apply andb_prop in H as [H1 H2].
    destruct (Z_lt_le_dec z (a + Zpos p)); [apply (IH _ H1); lia | apply (IH _ H2); lia].
  - assert (z = a) as -> by lia. exact H.
Qed.

Section Image.
Variable segs : list Segment.

Definition word_ok (w : bv 32) : bool :=
  match decode_any w with Some (i, _) => negb (frm_bad i) | None => true end.

Definition addr_ok (a : Z) : bool :=
  match fetch_word segs (Z_to_bv 64 a) with
  | Some w => word_ok w
  | None => match fetch_tail segs (Z_to_bv 64 a) with Some w => word_ok w | None => true end
  end.

Definition text_safe : Prop :=
  forall s, In s segs -> seg_executable s = true ->
    seg_writable s = false /\
    forall a, Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s) -> addr_ok a = true.

Definition seg_ok (s : Segment) : bool :=
  if seg_executable s then
    (negb (seg_writable s) &&
     match seg_size s with N0 => true | Npos n => range_all addr_ok (Z.of_N (seg_base s)) n end)%bool
  else true.
Definition text_frm_safe : bool := forallb seg_ok segs.

Lemma text_frm_safe_sound : text_frm_safe = true -> text_safe.
Proof.
  intros SAFE s Hin Hx. unfold text_frm_safe in SAFE. rewrite forallb_forall in SAFE. specialize (SAFE s Hin). unfold seg_ok in SAFE. rewrite Hx in SAFE.
  apply andb_prop in SAFE as [Hw Hr]. split; [destruct (seg_writable s); [discriminate | reflexivity]|].
  intros a Ha. destruct (seg_size s) as [|sz] eqn:Es; [cbn in Ha; lia|].
  apply (range_all_sound _ _ _ Hr). cbn in Ha. lia.
Qed.

Hypothesis SAFE : text_safe.

Lemma find_segment_in : forall l a n s, find_segment l a n = Some s ->
  In s l /\ Z.of_N (seg_base s) <= a /\ a + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction l as [|x l IH]; intros a n s H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb_spec (Z.of_N (seg_base x)) a) as [L1|L1]; cbn [andb] in H.
  - destruct (Z.leb_spec (a + n) (Z.of_N (seg_base x) + Z.of_N (seg_size x))) as [L2|L2].
    + injection H as <-. split; [left; reflexivity | lia].
    + destruct (IH _ _ _ H) as [? ?]. split; [right; assumption | assumption].
  - destruct (IH _ _ _ H) as [? ?]. split; [right; assumption | assumption].
Qed.

Lemma exec_addr_ok : forall (pc : word) n s, 0 < n ->
  find_segment segs (bv_unsigned pc) n = Some s -> seg_executable s = true ->
  seg_writable s = false /\ addr_ok (bv_unsigned pc) = true.
Proof.
  intros pc n s Hn Hf Hx. destruct (find_segment_in _ _ _ _ Hf) as (Hin & Hlo & Hhi).
  destruct (SAFE s Hin Hx) as [Hw Hr]. split; [exact Hw|]. apply Hr. lia.
Qed.

Lemma code_read_seg : forall (pc : word) n bs, code_read segs pc n = Some bs -> (0 < n)%N ->
  addr_ok (bv_unsigned pc) = true.
Proof.
  intros pc n bs H Hn. unfold code_read in H. destruct (find_segment segs (bv_unsigned pc) (Z.of_N n)) as [s|] eqn:Hf; [|discriminate].
  destruct (seg_executable s) eqn:Hx; cbn [andb] in H; [|discriminate].
  exact (proj2 (exec_addr_ok pc (Z.of_N n) s ltac:(lia) Hf Hx)).
Qed.

Lemma code_read_ov_none : forall m (pc : word) n, (0 < n)%N -> code_read_ov segs m pc n = None.
Proof.
  intros m pc n Hn. unfold code_read_ov. destruct (find_segment segs (bv_unsigned pc) (Z.of_N n)) as [s|] eqn:Hf; [|reflexivity].
  destruct (seg_executable s) eqn:Hx; cbn [andb]; [|reflexivity].
  rewrite (proj1 (exec_addr_ok pc (Z.of_N n) s ltac:(lia) Hf Hx)). reflexivity.
Qed.

Lemma fetch_word_ok : forall pc w, fetch_word segs pc = Some w -> word_ok w = true.
Proof.
  intros pc w H. assert (A : addr_ok (bv_unsigned pc) = true).
  { unfold fetch_word in H. destruct (negb _); [discriminate|].
    destruct (code_read segs pc 4) as [bs|] eqn:E; [|discriminate]. exact (code_read_seg pc 4 bs E ltac:(lia)). }
  unfold addr_ok in A. rewrite Z_to_bv_bv_unsigned, H in A. exact A.
Qed.

Lemma fetch_tail_ok : forall pc w, fetch_word segs pc = None -> fetch_tail segs pc = Some w -> word_ok w = true.
Proof.
  intros pc w Hn H. assert (A : addr_ok (bv_unsigned pc) = true).
  { unfold fetch_tail in H. destruct (negb _); [discriminate|]. unfold fetch_half in H.
    destruct (code_read segs pc 2) as [bs|] eqn:E; [|discriminate]. exact (code_read_seg pc 2 bs E ltac:(lia)). }
  unfold addr_ok in A. rewrite Z_to_bv_bv_unsigned, Hn, H in A. exact A.
Qed.

Lemma fetch_tail_any_eq : forall m pc, fetch_tail_any segs m pc = fetch_tail segs pc.
Proof.
  intros m pc. unfold fetch_tail_any, fetch_tail.
  assert (HA : forall a, fetch_half_any segs m a = fetch_half segs a).
  { intros a. unfold fetch_half_any, fetch_half_ov. rewrite code_read_ov_none by lia. destruct (fetch_half segs a); reflexivity. }
  rewrite !HA. reflexivity.
Qed.

Lemma decode_exec_frm : forall st w rep,
  word_ok w = true -> decode_exec_accesses segs st w = MachineOk rep ->
  frm_zero (ms_fcsr st) -> frm_zero (ms_fcsr (@access_value _ rep)).
Proof.
  intros st w rep Hw H Hz. unfold decode_exec_accesses in H. destruct (is_ecall w).
  - injection H as <-. exact Hz.
  - unfold word_ok in Hw. destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    apply negb_true_iff in Hw.
    match type of H with context [interp_eff_accesses segs ?t ?m] => destruct (interp_eff_accesses segs t m) as [r| |] eqn:E end; try discriminate.
    match type of E with interp_eff_accesses _ (exec ?sz _ ?c0) _ = _ =>
      pose proof (interp_eff_all segs cz _ _ r (exec_cz sz i c0 Hw Hz) E) as C end.
    destruct (@access_value _ r) as [c m']. injection H as <-. exact C.
Qed.

Theorem step_frm_zero : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' -> frm_zero (ms_fcsr ms) -> frm_zero (ms_fcsr ms').
Proof.
  intros ms ms' H Hz. unfold RiscvSemantics.step, step_accesses in H.
  destruct (fetch_word segs (ms_pc ms)) as [w|] eqn:F1.
  { destruct (decode_exec_accesses segs ms w) as [rep| |] eqn:E; try discriminate. injection H as <-.
    exact (decode_exec_frm ms w rep (fetch_word_ok _ _ F1) E Hz). }
  assert (F2 : fetch_word_ov segs (ms_mem ms) (ms_pc ms) = None).
  { unfold fetch_word_ov. destruct (negb _); [reflexivity|]. rewrite code_read_ov_none by lia. reflexivity. }
  rewrite F2, fetch_tail_any_eq in H.
  destruct (fetch_tail segs (ms_pc ms)) as [w|] eqn:F3.
  { destruct (decode_exec_accesses segs ms w) as [rep| |] eqn:E; try discriminate. injection H as <-.
    exact (decode_exec_frm ms w rep (fetch_tail_ok _ _ F1 F3) E Hz). }
  unfold fetch_failure in H. destruct (negb _); [discriminate|].
  match type of H with context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Theorem msteps_frm_zero : forall ms ms', msteps segs ms ms' -> frm_zero (ms_fcsr ms) -> frm_zero (ms_fcsr ms').
Proof. intros ms ms' H. induction H; intros Hz; [exact Hz|]. apply IHmsteps. eapply step_frm_zero; eassumption. Qed.

Theorem msteps_fp_ok : forall (fx fx' : FPState) R pc M rom R' pc' M' rom',
  msteps segs (@mkst fx R pc M rom) (@mkst fx' R' pc' M' rom') -> fp_ok fx -> fp_ok fx'.
Proof. intros fx fx' R pc M rom R' pc' M' rom' H Hz. exact (msteps_frm_zero _ _ H Hz). Qed.

End Image.
End FrmInv.
