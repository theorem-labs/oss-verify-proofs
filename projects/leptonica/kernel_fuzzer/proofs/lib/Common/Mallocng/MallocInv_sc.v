(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_tables MallocInv_steps MallocInv_hints.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stc_yw (n : word) : word :=
  let a0 := v_addi n 1 in
  let a2 := v_or (v_srliw a0 2) a0 in
  let a0' := v_srliw a0 1 in
  let a2' := v_or a2 a0' in
  let a2'' := v_srliw a2' 2 in
  let x := v_or a2'' a0' in
  let x1 := v_or (v_srli x 4) x in
  let x2 := v_or (v_srli x1 8) x1 in
  let x3 := v_or (v_srli (v_slli x2 33) 49) x2 in
  v_and (v_addi x3 1) (v_xori x3 (-1)).

Definition stc_dw (n : word) : word := v_srliw (v_mul (stc_yw n) DEBRUIJN_MULT) 27.

(* [comment removed for export] *)
Definition stc_tw (d : word) : word := v_xori (v_slli d 2) 124.

Definition stc_rest2 (n t i c0 : word) : M word := mret (v_or i (v_xori (v_sltu n c0) 1)).

Definition stc_rest (tbl n d : word) : M word :=
  let t := stc_tw d in
  let i1 := v_sub (wlit 121) t in
  c1 <- m_lhu (v_add tbl (v_slli i1 1)) ;;
  (if c_ltu n c1
   then let i := v_sub (wlit 120) t in
        c0 <- m_lhu (v_add tbl (v_slli i 1)) ;;
        mret (v_or i (v_xori (v_sltu n c0) 1))
   else let i := v_sub (wlit 122) t in
        c0 <- m_lhu (v_add tbl (v_slli i 1)) ;;
        mret (v_or i (v_xori (v_sltu n c0) 1))).

Lemma stc_unfold : forall tbl n,
  m_size_to_class_big tbl n = (d <- m_lbu (v_add A_DEBRUIJN (stc_dw n)) ;; stc_rest tbl n d).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition U (w : word) : Z := bv_unsigned w.
Definition stcT (d : Z) : Z := U (stc_tw (Z_to_bv 64 (debruijn d))).
Definition stcI1 (t : Z) : Z := U (v_sub (wlit 121) (Z_to_bv 64 t)).
Definition stcI (lt : bool) (t : Z) : Z := U (v_sub (wlit (if lt then 120 else 122)) (Z_to_bv 64 t)).
Definition stcR (n16 i : Z) : Z :=
  U (v_or (Z_to_bv 64 i) (v_xori (v_sltu (Z_to_bv 64 n16) (Z_to_bv 64 (size_class i))) 1)).

Definition stc_d (n16 : Z) : Z := U (stc_dw (Z_to_bv 64 n16)).
Definition stc_t (n16 : Z) : Z := stcT (stc_d n16).
Definition stc_i1 (n16 : Z) : Z := stcI1 (stc_t n16).
Definition stc_lt (n16 : Z) : bool := n16 <? size_class (stc_i1 n16).
Definition stc_i (n16 : Z) : Z := stcI (stc_lt n16) (stc_t n16).
Definition stc (n16 : Z) : Z := stcR n16 (stc_i n16).

Definition chk_stc (n16 : Z) : bool :=
  let d := stc_d n16 in
  let t := stcT d in
  let i1 := stcI1 t in
  let lt := n16 <? size_class i1 in
  let i := stcI lt t in
  let c := stcR n16 i in
  (d <? 32)
  && (0 <=? i1) && (i1 <? 48)
  && (0 <=? i) && (i <? 48)
  && (c <? 48)
  && (n16 <? size_class c)
  && (c =? size_to_class_z (16 * n16)).

Lemma chk_stcs : forallb chk_stc (Zseq 10 (Z.to_nat 8181)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stc_facts : forall n16, 10 <= n16 < 8191 ->
  stc_d n16 < 32 /\
  v_add A_DEBRUIJN (Z_to_bv 64 (stc_d n16)) = Z_to_bv 64 (T_DEBRUIJN + stc_d n16) /\
  stc_i1 n16 < 48 /\
  v_add A_SIZE_CLASSES (v_slli (Z_to_bv 64 (stc_i1 n16)) 1) = Z_to_bv 64 (T_SIZE_CLASSES + 2 * stc_i1 n16) /\
  stc_i n16 < 48 /\
  v_add A_SIZE_CLASSES (v_slli (Z_to_bv 64 (stc_i n16)) 1) = Z_to_bv 64 (T_SIZE_CLASSES + 2 * stc_i n16) /\
  0 <= stc n16 < 48 /\ n16 < size_class (stc n16) /\ stc n16 = size_to_class_z (16 * n16).
Proof.
  intros n16 Hn.
  pose proof (proj1 (forallb_forall _ _) chk_stcs n16 (Zseq_In (Z.to_nat 8181) 10 n16 ltac:(rewrite Z2Nat.id by llia; llia))) as H.
  unfold chk_stc in H. cbv zeta in H.
  change (stcT (stc_d n16)) with (stc_t n16) in H. change (stcI1 (stc_t n16)) with (stc_i1 n16) in H.
  change (n16 <? size_class (stc_i1 n16)) with (stc_lt n16) in H. change (stcI (stc_lt n16) (stc_t n16)) with (stc_i n16) in H.
  change (stcR n16 (stc_i n16)) with (stc n16) in H.
  repeat (apply andb_prop in H; destruct H as [H ?X]).
  repeat match goal with
         | G : (_ <? _) = true |- _ => apply Z.ltb_lt in G
         | G : (_ =? _) = true |- _ => apply Z.eqb_eq in G
         end.
  repeat match goal with G : (_ <=? _) = true |- _ => apply Z.leb_le in G end.
  pose proof (u64_range (Z_to_bv 64 (stc n16))).
  assert (0 <= stc n16) by (unfold stc, stcR, U; apply u64_range).
  assert (0 <= stc_d n16) by (unfold stc_d, U; apply u64_range).
  assert (TAB : forall i, 0 <= i < 48 -> v_add A_SIZE_CLASSES (v_slli (Z_to_bv 64 i) 1) = Z_to_bv 64 (T_SIZE_CLASSES + 2 * i)).
  { intros i Hi. rewrite A_SIZE_CLASSES_eq, v_slli_Z, v_add_Z by lia. f_equal. change (2^1) with 2. lia. }
  repeat split; auto; try lia.
  rewrite A_DEBRUIJN_eq, v_add_Z. reflexivity.
Qed.

Section STC.
  Context {R : Type}.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Theorem ts_size_to_class_big : forall s (n16 : Z) (k : word -> M R) P,
    rodata_clear (ms_mem s) -> WIN s -> 10 <= n16 < 8191 ->
    tsafe (k (Z_to_bv 64 (stc n16)) s) P ->
    tsafe ((x <- m_size_to_class_big A_SIZE_CLASSES (Z_to_bv 64 n16) ;; k x) s) P.
  Proof.
    intros s n16 k P HRO HWIN Hn Hk.
    destruct (stc_facts n16 Hn) as (D32 & ED & I1 & EI1 & I0 & EI0 & Hs & Hlt & _).
    assert (D0 : 0 <= stc_d n16) by (unfold stc_d, U; apply u64_range).
    assert (I10 : 0 <= stc_i1 n16) by (unfold stc_i1, stcI1, U; apply u64_range).
    assert (I00 : 0 <= stc_i n16) by (unfold stc_i, stcI, U; apply u64_range).
    rewrite stc_unfold. reassoc.
    replace (stc_dw (Z_to_bv 64 n16)) with (Z_to_bv 64 (stc_d n16))
      by (unfold stc_d, U; apply Z_to_bv_bv_unsigned).
    rewrite ED. eapply ts_lbu_debruijn; [exact HRO | exact HWIN | llia |].
    unfold stc_rest. reassoc.
    replace (stc_tw (Z_to_bv 64 (debruijn (stc_d n16)))) with (Z_to_bv 64 (stc_t n16))
      by (unfold stc_t, stcT, U; apply Z_to_bv_bv_unsigned).
    replace (v_sub (wlit 121) (Z_to_bv 64 (stc_t n16))) with (Z_to_bv 64 (stc_i1 n16))
      by (unfold stc_i1, stcI1, U; apply Z_to_bv_bv_unsigned).
    rewrite EI1. eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |].
    pose proof (size_class_bound (stc_i1 n16) ltac:(llia)) as Hc1.
    rewrite c_ltu_Z by llia. fold (stc_lt n16).
    assert (EI : forall c, v_sub (wlit c) (Z_to_bv 64 (stc_t n16)) = Z_to_bv 64 (U (v_sub (wlit c) (Z_to_bv 64 (stc_t n16)))))
      by (intros c; unfold U; symmetry; apply Z_to_bv_bv_unsigned).
    destruct (stc_lt n16) eqn:EL.
    - reassoc. rewrite (EI 120).
      replace (U (v_sub (wlit 120) (Z_to_bv 64 (stc_t n16)))) with (stc_i n16) by (unfold stc_i, stcI; rewrite EL; reflexivity).
      rewrite EI0. eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |].
      apply ts_bind_ret.
      replace (v_or (Z_to_bv 64 (stc_i n16)) (v_xori (v_sltu (Z_to_bv 64 n16) (Z_to_bv 64 (size_class (stc_i n16)))) 1))
        with (Z_to_bv 64 (stc n16)) by (unfold stc, stcR, U; apply Z_to_bv_bv_unsigned).
      exact Hk.
    - reassoc. rewrite (EI 122).
      replace (U (v_sub (wlit 122) (Z_to_bv 64 (stc_t n16)))) with (stc_i n16) by (unfold stc_i, stcI; rewrite EL; reflexivity).
      rewrite EI0. eapply ts_lhu_size_class; [exact HRO | exact HWIN | llia |].
      apply ts_bind_ret.
      replace (v_or (Z_to_bv 64 (stc_i n16)) (v_xori (v_sltu (Z_to_bv 64 n16) (Z_to_bv 64 (size_class (stc_i n16)))) 1))
        with (Z_to_bv 64 (stc n16)) by (unfold stc, stcR, U; apply Z_to_bv_bv_unsigned).
      exact Hk.
  Qed.
End STC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint ctzf (fuel : nat) (v : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if Z.odd v then 0 else 1 + ctzf f (v / 2)
  end.
Definition ctz32 (v : Z) : Z := ctzf 32 v.

Lemma land_double : forall a b (r t : bool),
  Z.land (2 * a + Z.b2z r) (2 * b + Z.b2z t) = 2 * Z.land a b + Z.b2z (r && t).
Proof.
  intros a b r t. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec. destruct (Z.eq_dec n 0) as [-> | Hne].
  - rewrite !Z.testbit_0_r. reflexivity.
  - replace n with (Z.succ (n - 1)) by llia. rewrite !Z.testbit_succ_r by llia. rewrite Z.land_spec. reflexivity.
Qed.

Lemma Z_decomp2 : forall a, a = 2 * (a / 2) + Z.b2z (Z.odd a).
Proof. intros a. pose proof (Z.div_mod a 2 ltac:(llia)) as E. rewrite Zmod_odd in E. destruct (Z.odd a); cbn [Z.b2z]; llia. Qed.

Lemma land_compl : forall m a, (0 <= a < 2 ^ Z.of_nat m) -> Z.land a (2 ^ Z.of_nat m - 1 - a) = 0.
Proof.
  induction m as [|m IH]; intros a Ha.
  - cbn in Ha. replace a with 0 by llia. reflexivity.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in * by llia.
    pose proof (Z_decomp2 a) as E. pose proof (Z.mod_pos_bound a 2 ltac:(llia)) as Hr.
    assert (Hq : 0 <= a / 2 < 2 ^ Z.of_nat m) by (destruct (Z.odd a); cbn [Z.b2z] in E; llia).
    rewrite E at 1.
    replace (2 * 2 ^ Z.of_nat m - 1 - a) with (2 * (2 ^ Z.of_nat m - 1 - a / 2) + Z.b2z (negb (Z.odd a))).
    2:{ destruct (Z.odd a); cbn [Z.b2z negb] in *; llia. }
    rewrite land_double, IH by llia. destruct (Z.odd a); reflexivity.
Qed.

Lemma land_neg_low : forall n v, (0 < v < 2 ^ Z.of_nat n) ->
  Z.land v (2 ^ Z.of_nat n - v) = 2 ^ (ctzf n v) /\ 0 <= ctzf n v < Z.of_nat n /\
  Z.testbit v (ctzf n v) = true /\ (forall j, 0 <= j < ctzf n v -> Z.testbit v j = false).
Proof.
  induction n as [|n IH]; intros v Hv; [cbn in Hv; llia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in * by llia. cbn [ctzf].
  pose proof (Z_decomp2 v) as E.
  destruct (Z.odd v) eqn:Ho; cbn [Z.b2z] in E.
  - (* [comment removed for export] *)
    split; [| split; [llia | split; [rewrite Z.bit0_odd; exact Ho | intros j Hj; llia]]].
    rewrite E at 1. change 1 with (Z.b2z true) at 1.
    replace (2 * 2 ^ Z.of_nat n - v) with (2 * (2 ^ Z.of_nat n - 1 - v / 2) + Z.b2z true) by (cbn [Z.b2z]; llia).
    rewrite land_double. rewrite land_compl by llia. reflexivity.
  - (* [comment removed for export] *)
    rewrite Z.add_0_r in E.
    assert (Hh : 0 < v / 2 < 2 ^ Z.of_nat n) by llia.
    destruct (IH (v / 2) Hh) as (L & R & B & Bl).
    split; [| split; [llia | split]].
    + rewrite E at 1. replace (2 * 2 ^ Z.of_nat n - v) with (2 * (2 ^ Z.of_nat n - v / 2) + Z.b2z false) by (cbn [Z.b2z]; llia).
      replace (2 * (v / 2)) with (2 * (v / 2) + Z.b2z false) by (cbn [Z.b2z]; llia).
      rewrite land_double, L. cbn [andb Z.b2z]. rewrite Z.add_0_r, <- Z.pow_succ_r by llia. f_equal. llia.
    + rewrite E at 1. replace (1 + ctzf n (v / 2)) with (Z.succ (ctzf n (v / 2))) by llia. rewrite Z.double_bits_succ. exact B.
    + intros j Hj. rewrite E at 1. destruct (Z.eq_dec j 0) as [-> | Hne]; [apply Z.testbit_even_0|].
      replace j with (Z.succ (j - 1)) by llia. rewrite Z.double_bits_succ. apply Bl. llia.
Qed.

Lemma ctz32_spec : forall v, 0 < v < 2^32 ->
  Z.land v (2^32 - v) = 2 ^ (ctz32 v) /\ 0 <= ctz32 v < 32 /\
  Z.testbit v (ctz32 v) = true /\ (forall j, 0 <= j < ctz32 v -> Z.testbit v j = false).
Proof. intros v Hv. unfold ctz32. change (2^32) with (2 ^ Z.of_nat 32) in Hv. exact (land_neg_low 32 v Hv). Qed.

Lemma sub_lowbit_testbit : forall v k j, 0 <= v -> 0 <= k -> 0 <= j -> Z.testbit v k = true ->
  Z.testbit (v - 2 ^ k) j = if j =? k then false else Z.testbit v j.
Proof.
  intros v k j Hv Hk Hj Hb.
  assert (E : v - 2 ^ k = Z.ldiff v (2 ^ k)).
  { pose proof (Z.add_nocarry_lxor (Z.ldiff v (2 ^ k)) (2 ^ k)) as X.
    assert (D : Z.land (Z.ldiff v (2 ^ k)) (2 ^ k) = 0).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.bits_0, Z.pow2_bits_eqb by llia.
      destruct (k =? n); destruct (Z.testbit v n); reflexivity. }
    specialize (X D).
    assert (L : Z.lxor (Z.ldiff v (2 ^ k)) (2 ^ k) = v).
    { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec, Z.pow2_bits_eqb by llia.
      destruct (k =? n) eqn:En; [apply Z.eqb_eq in En; subst n; rewrite Hb; reflexivity | destruct (Z.testbit v n); reflexivity]. }
    llia. }
  rewrite E, Z.ldiff_spec, Z.pow2_bits_eqb by llia. rewrite Z.eqb_sym.
  destruct (j =? k); destruct (Z.testbit v j); reflexivity.
Qed.

Lemma sub_lowbit_range : forall v k, 0 <= v < 2^32 -> 0 <= k -> Z.testbit v k = true -> 0 <= v - 2 ^ k < 2^32.
Proof.
  intros v k Hv Hk Hb. split; [| llia].
  destruct (Z.lt_ge_cases v (2 ^ k)) as [Hlt | Hge]; [| llia].
  exfalso. rewrite Z.testbit_true in Hb by llia. rewrite Z.div_small in Hb by llia. cbn in Hb. llia.
Qed.

(* [comment removed for export] *)
Lemma v_subw_w32 : forall a b, v_subw (w32 a) (w32 b) = w32 (a - b).
Proof.
  intros a b. rewrite !w32_eq. rewrite v_subw_Z by apply sx32_range.
  rewrite swrap32_sx32. rewrite <- sx32_mod. rewrite Zminus_mod, !sx32_eqmod, <- Zminus_mod. rewrite sx32_mod. reflexivity.
Qed.

Lemma lowbit_w32 : forall v, 0 < v < 2^32 ->
  v_and (w32 v) (v_subw w0 (w32 v)) = w32 (2 ^ ctz32 v).
Proof.
  intros v Hv. destruct (ctz32_spec v Hv) as (L & R & _).
  replace w0 with (w32 0) by (rewrite w32_eq; reflexivity).
  rewrite v_subw_w32. rewrite <- (w32_mod (0 - v)).
  replace ((0 - v) mod 2^32) with (2^32 - v).
  2:{ replace (0 - v) with ((2^32 - v) + (-1) * 2^32) by llia. rewrite Z.mod_add by llia. rewrite Z.mod_small by llia. reflexivity. }
  rewrite v_and_w32 by llia. rewrite L. reflexivity.
Qed.

Lemma pow2_ctz_range : forall v, 0 < v < 2^32 -> 0 < 2 ^ ctz32 v < 2^32.
Proof.
  intros v Hv. destruct (ctz32_spec v Hv) as (_ & R & _). split; [apply Z.pow_pos_nonneg; llia | apply Z.pow_lt_mono_r; llia].
Qed.

(* [comment removed for export] *)
Definition dbi (k : Z) : Z := U (v_srliw (v_mul (w32 (2 ^ k)) DEBRUIJN_MULT) 27).
Definition chk_dbi (k : Z) : bool :=
  (dbi k <? 32) && (debruijn (dbi k) =? k).
Lemma chk_dbis : forallb chk_dbi (Zseq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dbi_facts : forall k, 0 <= k < 32 ->
  0 <= dbi k < 32 /\ debruijn (dbi k) = k /\ v_add A_DEBRUIJN (Z_to_bv 64 (dbi k)) = Z_to_bv 64 (T_DEBRUIJN + dbi k).
Proof.
  intros k Hk.
  pose proof (proj1 (forallb_forall _ _) chk_dbis k (Zseq_In 32 0 k ltac:(llia))) as H.
  unfold chk_dbi in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.eqb_eq in H2.
  assert (0 <= dbi k) by (unfold dbi, U; apply u64_range).
  split; [lia|]. split; [exact H2|]. rewrite A_DEBRUIJN_eq, v_add_Z. reflexivity.
Qed.

Section CTZ.
  Context {R : Type}.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Theorem ts_ctz32 : forall s (v : Z) (k : word -> M R) P,
    rodata_clear (ms_mem s) -> WIN s -> 0 < v < 2^32 ->
    tsafe (k (Z_to_bv 64 (ctz32 v)) s) P ->
    tsafe ((x <- m_ctz32 (w32 v) ;; k x) s) P.
  Proof.
    intros s v k P HRO HWIN Hv Hk. unfold m_ctz32.
    rewrite lowbit_w32 by exact Hv.
    destruct (ctz32_spec v Hv) as (_ & Hr & _).
    destruct (dbi_facts (ctz32 v) Hr) as (D1 & D2 & D3).
    replace (v_srliw (v_mul (w32 (2 ^ ctz32 v)) DEBRUIJN_MULT) 27) with (Z_to_bv 64 (dbi (ctz32 v)))
      by (unfold dbi, U; apply Z_to_bv_bv_unsigned).
    rewrite D3. eapply ts_lbu_debruijn; [exact HRO | exact HWIN | llia |]. rewrite D2. exact Hk.
  Qed.
End CTZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma testbit_small_high : forall a n m, 0 <= a < 2^n -> 0 <= n <= m -> Z.testbit a m = false.
Proof.
  intros a n m Ha Hm. rewrite <- (Z.mod_small a (2^n)) by llia. apply Z.mod_pow2_bits_high. llia.
Qed.

Lemma lor_lt_pow2 : forall a b n, 0 <= n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros a b n Hn Ha Hb.
  assert (E : Z.lor a b = (Z.lor a b) mod 2^n).
  { apply Z.bits_inj'. intros m Hm. destruct (Z.lt_ge_cases m n) as [L | G].
    - rewrite Z.mod_pow2_bits_low by llia. reflexivity.
    - rewrite Z.mod_pow2_bits_high by llia. rewrite Z.lor_spec.
      rewrite (testbit_small_high a n m), (testbit_small_high b n m) by llia. reflexivity. }
  rewrite E. apply Z.mod_pos_bound. llia.
Qed.

Lemma land_lt_pow2 : forall a b n, 0 <= n -> 0 <= a < 2^n -> 0 <= b -> 0 <= Z.land a b < 2^n.
Proof.
  intros a b n Hn Ha Hb.
  assert (E : Z.land a b = (Z.land a b) mod 2^n).
  { apply Z.bits_inj'. intros m Hm. destruct (Z.lt_ge_cases m n) as [L | G].
    - rewrite Z.mod_pow2_bits_low by llia. reflexivity.
    - rewrite Z.mod_pow2_bits_high by llia. rewrite Z.land_spec. rewrite (testbit_small_high a n m) by llia. reflexivity. }
  rewrite E. apply Z.mod_pos_bound. llia.
Qed.

Lemma aib_byte_facts : forall lo hi, 0 <= lo < 32 -> 0 <= hi < 256 ->
  0 <= Z.lor lo (Z.land hi 224) < 256 /\ Z.lor lo (Z.land hi 224) mod 32 = lo.
Proof.
  intros lo hi Hlo Hhi.
  pose proof (land_lt_pow2 hi 224 8 ltac:(llia) ltac:(llia) ltac:(llia)) as Hx. change (2^8) with 256 in Hx.
  split. { apply (lor_lt_pow2 lo _ 8); try llia. all: change (2^8) with 256; llia. }
 
  change 32 with (2^5). rewrite <- Z.land_ones by llia. rewrite Z.land_lor_distr_l.
  rewrite <- Z.land_assoc. replace (Z.land 224 (Z.ones 5)) with 0 by reflexivity. rewrite Z.land_0_r, Z.lor_0_r.
  rewrite Z.land_ones by llia. apply Z.mod_small. change (2^5) with 32. llia.
Qed.

Lemma land_high32 : forall fr k, 0 <= fr < 2^32 -> 0 <= k <= 32 -> Z.land fr (2^32 - 2^k) = fr - fr mod 2^k.
Proof.
  intros fr k Hfr Hk.
  assert (E : Z.land fr (2^32 - 2^k) = Z.ldiff fr (Z.ones k)).
  { apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.ldiff_spec, Z.testbit_ones by llia.
    replace (2^32 - 2^k) with ((2^(32 - k) - 1) * 2^k).
    2:{ rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by llia. replace (32 - k + k) with 32 by llia. llia. }
    destruct (Z.lt_ge_cases m k) as [L | G].
    - rewrite Z.mul_pow2_bits_low by llia. replace (m <? k) with true by (symmetry; apply Z.ltb_lt; llia).
      replace (0 <=? m) with true by (symmetry; apply Z.leb_le; llia). cbn. rewrite Bool.andb_false_r. reflexivity.
    - rewrite Z.mul_pow2_bits by llia. replace (m <? k) with false by (symmetry; apply Z.ltb_ge; llia).
      replace (0 <=? m) with true by (symmetry; apply Z.leb_le; llia). cbn [negb andb].
      destruct (Z.lt_ge_cases m 32) as [L32 | G32].
      + replace (2^(32-k) - 1) with (Z.ones (32 - k)) by (rewrite Z.ones_equiv; llia). rewrite Z.ones_spec_low by llia. rewrite Bool.andb_true_r. reflexivity.
      + rewrite (testbit_small_high fr 32 m) by llia. reflexivity. }
  rewrite E. rewrite Z.ldiff_ones_r, Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by llia.
  pose proof (Z.div_mod fr (2^k) ltac:(llia)). llia.
Qed.

Lemma mod_div_swap : forall a b c, 0 < b -> 0 < c -> (a mod (b * c)) / b = (a / b) mod c.
Proof.
  intros a b c Hb Hc.
  pose proof (Z.div_mod a (b * c) ltac:(llia)) as E. pose proof (Z.mod_pos_bound a (b * c) ltac:(llia)) as R.
  set (q := a / (b * c)) in *. set (r := a mod (b * c)) in *.
  assert (Hr : 0 <= r / b < c) by (split; [apply Z.div_pos; llia | apply Z.div_lt_upper_bound; llia]).
  assert (E2 : a / b = c * q + r / b).
  { rewrite E. replace (b * c * q + r) with (r + (c * q) * b) by llia. rewrite Z.div_add by llia. llia. }
  rewrite E2. replace (c * q + r / b) with (r / b + q * c) by llia. rewrite Z.mod_add by llia. rewrite Z.mod_small by llia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma decay_d : forall w, 0 <= w < 2^32 ->
  v_addi (v_srli (v_slli (w32 w) 52) 58) (-7) = Z_to_bv 64 ((w / 64) mod 64 - 7).
Proof.
  intros w Hw. rewrite w32_eq. pose proof (sx32_range w) as Hs.
  rewrite v_slli_Z by llia. rewrite <- (ZZ_mod (sx32 w * 2^52)).
  pose proof (Z.mod_pos_bound (sx32 w * 2^52) (2^64) ltac:(llia)) as Hm.
  rewrite v_srli_Z by llia. rewrite v_addi_Z. f_equal.
  assert (E1 : (sx32 w * 2^52) mod 2^64 = (sx32 w mod 2^12) * 2^52).
  { change (2^64) with (2^12 * 2^52). rewrite Z.mul_mod_distr_r by llia. reflexivity. }
  assert (E2 : sx32 w mod 2^12 = w mod 2^12).
  { unfold sx32. rewrite (Z.mod_small w (2^32)) by llia. destruct (w <? 2^31); [reflexivity|].
    replace (w + (2^64 - 2^32)) with (w + (2^52 - 2^20) * 2^12) by llia. rewrite Z.mod_add by llia. reflexivity. }
  rewrite E1, E2. change (2^58) with (2^6 * 2^52). rewrite Z.div_mul_cancel_r by llia.
  change (2^12) with (2^6 * 2^6). rewrite mod_div_swap by llia. change (2^6) with 64. llia.
Qed.

(* [comment removed for export] *)
Lemma v_subw_0_w32 : forall x, v_subw w0 (w32 x) = w32 (- x).
Proof. intros x. replace w0 with (w32 0) by (rewrite w32_eq; reflexivity). rewrite v_subw_w32. f_equal. Qed.

Lemma act_mask_words : forall fr a, 0 <= fr < 2^32 -> 0 <= a < 32 ->
  let act2 := w32 (2 ^ (a + 1)) in
  v_and (w32 fr) (v_subw w0 act2) = w32 (fr - fr mod 2^(a+1)) /\
  v_and (w32 fr) (v_addiw act2 (-1)) = w32 (fr mod 2^(a+1)) /\
  0 <= fr mod 2^(a+1) < 2^32 /\ 0 <= fr - fr mod 2^(a+1) < 2^32.
Proof.
  intros fr a Hfr Ha act2. subst act2.
  assert (Hp : 0 < 2^(a+1) <= 2^32) by (split; [apply Z.pow_pos_nonneg; llia | apply Z.pow_le_mono_r; llia]).
  pose proof (Z.mod_pos_bound fr (2^(a+1)) ltac:(llia)) as Hm.
  assert (Hle : fr mod 2^(a+1) <= fr) by (apply Z.mod_le; llia).
  split; [| split; [| llia]].
  - rewrite v_subw_0_w32. rewrite <- (w32_mod (- 2^(a+1))).
    replace ((- 2^(a+1)) mod 2^32) with (2^32 - 2^(a+1)).
    2:{ destruct (Z.eq_dec (a + 1) 32) as [E | NE].
        - rewrite E. rewrite Z.sub_diag. rewrite Z_mod_zero_opp_full; [reflexivity|]. apply Z.mod_same. llia.
        - replace (- 2^(a+1)) with ((2^32 - 2^(a+1)) + (-1) * 2^32) by llia. rewrite Z.mod_add by llia.
          symmetry. apply Z.mod_small. assert (2^(a+1) < 2^32) by (apply Z.pow_lt_mono_r; llia). llia. }
    rewrite v_and_w32 by llia. rewrite land_high32 by llia. reflexivity.
  - rewrite v_addiw_w32. replace (2 ^ (a + 1) + -1) with (2 ^ (a + 1) - 1) by llia. rewrite v_and_w32 by llia. rewrite land_ones_low by llia. reflexivity.
Qed.

End WithLayout.
