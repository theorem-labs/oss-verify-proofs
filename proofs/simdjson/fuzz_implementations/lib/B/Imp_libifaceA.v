(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_libiface D_auxv X_aexdefs Sj_acps Atp_activewA Pj_defsA Imp_hdefs0A Imp_ios_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition IMP_AVL_GUARD_A : Z := 0x6bc100.
Definition IMP_AVP_SPAN_A : Z := 0x6bc160.
Definition IMP_AVP_GUARD_A : Z := 0x6bc180.
Definition IMP_AVP_ARR_A : Z := 0x6bc1a0.

Definition g00 : list cell := [C1 z8; C1 z8].
Definition g11 : list cell := [C1 one8; C1 one8].

Definition imp_staticsA (v : option Z) (m : mem) : Prop :=
  match v with
  | None =>
      lib0 m
      /\ rw_cells bsegs m IMP_AVL_GUARD_A g00
      /\ rw_cells bsegs m IMP_AVP_SPAN_A [C8 (wz 0); C8 (wz 0)] /\ rw_cells bsegs m IMP_AVP_GUARD_A g00 /\ rw_cells bsegs m IMP_AVP_ARR_A [C8 (wz 0)]
      /\ rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz 0); C8 (wz 0); C8 (wz 0)] /\ rw_cells bsegs m IMP_GUARD_A g00
  | Some A8 =>
      sj_lib m
      /\ rw_cells bsegs m IMP_AVL_GUARD_A g11
      /\ rw_cells bsegs m IMP_AVP_SPAN_A [C8 (wz IMP_AVP_ARR_A); C8 (wz 1)] /\ rw_cells bsegs m IMP_AVP_GUARD_A g11 /\ rw_cells bsegs m IMP_AVP_ARR_A [C8 (wz SJ_SINGLETON)]
      /\ rw_cells bsegs m IMP_VEC_OBJ_A [C8 (wz A8); C8 (wz (A8 + 8)); C8 (wz (A8 + 8))] /\ rw_cells bsegs m IMP_GUARD_A g11
      /\ rw_cells bsegs m A8 [C8 (wz SJ_SINGLETON)] /\ 0 < A8 /\ A8 mod 16 = 0
  end.

Definition imp_tplocA (m : mem) : Prop := rw_cells bsegs m (TPV_A - 48) [C8 (wz (LIBC_A + 56))].

Definition imp_libA (v : option Z) (m : mem) : Prop := imp_staticsA v m /\ LOCBA m /\ locx3 m /\ imp_tplocA m /\ lockwA m.

Lemma imp_libA_pj : forall v m, imp_libA v m -> pj_libA sj_lib m.
Proof.
  intros [A8|] m (ST & LB & _ & _ & LK); (split; [| split; [right; exact LB| exact LK]]).
  - exact (proj1 ST).
  - left. exact (proj1 ST).
Qed.

Definition aex4A (m : mem) : Prop :=
  (exists (p1 p2 : list byte) (f4 f5 : word), rw_cells bsegs m AEX (aex_tbl 4 p1 p2 (wz X_CALL) f4 f5))
  /\ (exists a4 a5 : word, rw_cells bsegs m AEX_A0 (aex_args (wz X_AEXGUARD) a4 a5)).
Definition aex6A (m : mem) : Prop :=
  (exists (p1 p2 : list byte), rw_cells bsegs m AEX (aex_tbl 6 p1 p2 (wz X_CALL) (wz X_VECDTOR) (wz X_ATCXA)))
  /\ rw_cells bsegs m AEX_A0 (aex_args (wz X_AEXGUARD) (wz AEX_VEC_OBJ) (wz 0)).

Definition aexvA (v : option Z) (m : mem) : Prop := match v with None => aex4A m | Some _ => aex6A m end.

Lemma aex_reg_aex4A : forall m, aex_reg m -> aex4A m.
Proof. intros m (H1 & H2 & _). exact (conj H1 H2). Qed.
Lemma aex_lib_aex6A : forall m, aex_lib m -> aex6A m.
Proof. intros m (H1 & H2 & _). exact (conj H1 H2). Qed.
Lemma aex6A_aex_lib : forall m, aex6A m -> rw_cells bsegs m TR_LATCH [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m AEF_INCB [C1 (Z_to_bv 8 0)] -> aex_lib m.
Proof. intros m [H1 H2] L F. exact (conj H1 (conj H2 (conj L F))). Qed.

Definition IMP_FP_A : list (Z * Z) := [(IMP_VEC_OBJ_A, IMP_VEC_OBJ_A + 24); (IMP_GUARD_A, IMP_GUARD_A + 2); (IMP_AVL_GUARD_A, IMP_AVL_GUARD_A + 2)].

Definition IMP_AEX_W : list (Z * Z) := [(AEX, AEX + 80); (AEX_A0, AEX_A0 + 48)].

Definition IMP_XFP_A : list (Z * Z) := LIB_FP ++ IMP_FP_A ++ IMP_AEX_W.

Definition xnewA (v : option Z) (A8 : Z) : list (Z * Z) := match v with Some _ => [] | None => [(A8, 8)] end.

Definition imp_lib_rng (v : option Z) (x : Z) : Prop :=
  (0x6bc000 <= x < 0x6bc018) \/ (0x6bc040 <= x < 0x6bc042) \/ (0x6bc100 <= x < 0x6bc102) \/ (0x6bc120 <= x < 0x6bc128) \/ (0x6bc140 <= x < 0x6bc142)
  \/ (0x6bc160 <= x < 0x6bc170) \/ (0x6bc180 <= x < 0x6bc182) \/ (0x6bc1a0 <= x < 0x6bc1a8) \/ (0x6bc1c0 <= x < 0x6bc1ec) \/ (0x6bc220 <= x < 0x6bc222)
  \/ (PJ_LOC_LO_A <= x < PJ_LOC_LO_A + 3760) \/ (PJ_LOCKW_A <= x < PJ_LOCKW_A + 4) \/ (TPV_A - 48 <= x < TPV_A - 40)
  \/ (match v with Some A8 => A8 <= x < A8 + 8 | None => False end).

Lemma lib0_agree : forall m m', lib0 m -> agree_on (fun x => (0x6bc120 <= x < 0x6bc128) \/ (0x6bc140 <= x < 0x6bc142) \/ (0x6bc1c0 <= x < 0x6bc1ec) \/ (0x6bc220 <= x < 0x6bc222)) m m' -> lib0 m'.
Proof.
  intros m m' (L1 & L2 & L3 & L4) AG. unfold lib0.
  repeat split;
    first [ apply (rw_cells_agree_nw bsegs m m' _ _ L1) | apply (rw_cells_agree_nw bsegs m m' _ _ L2) | apply (rw_cells_agree_nw bsegs m m' _ _ L3) | apply (rw_cells_agree_nw bsegs m m' _ _ L4) ];
    intros a Ha; apply AG; cbn [cells_size csize Nat.add length] in Ha; lia.
Qed.
Lemma lib1_agree : forall m m', lib1 m -> agree_on (fun x => (0x6bc120 <= x < 0x6bc128) \/ (0x6bc140 <= x < 0x6bc142) \/ (0x6bc1c0 <= x < 0x6bc1ec) \/ (0x6bc220 <= x < 0x6bc222)) m m' -> lib1 m'.
Proof.
  intros m m' (L1 & L2 & L3 & L4) AG. unfold lib1.
  repeat split;
    first [ apply (rw_cells_agree_nw bsegs m m' _ _ L1) | apply (rw_cells_agree_nw bsegs m m' _ _ L2) | apply (rw_cells_agree_nw bsegs m m' _ _ L3) | apply (rw_cells_agree_nw bsegs m m' _ _ L4) ];
    intros a Ha; apply AG; cbn [cells_size csize Nat.add length] in Ha; unfold one8 in *; lia.
Qed.
Lemma sj_lib_agree : forall m m', sj_lib m -> agree_on (fun x => (0x6bc120 <= x < 0x6bc128) \/ (0x6bc140 <= x < 0x6bc142) \/ (0x6bc1c0 <= x < 0x6bc1ec) \/ (0x6bc220 <= x < 0x6bc222)) m m' -> sj_lib m'.
Proof. intros m m' [L|L] AG; [left; exact (lib0_agree m m' L AG)| right; exact (lib1_agree m m' L AG)]. Qed.

Lemma imp_staticsA_agree : forall v m m', imp_staticsA v m -> agree_on (imp_lib_rng v) m m' -> imp_staticsA v m'.
Proof.
  intros [A8|] m m' ST AG; unfold imp_staticsA, imp_lib_rng, IMP_AVL_GUARD_A, IMP_AVP_SPAN_A, IMP_AVP_GUARD_A, IMP_AVP_ARR_A, IMP_VEC_OBJ_A, IMP_GUARD_A, g00, g11 in *.
  - destruct ST as (S0 & S1 & S2 & S3 & S4 & S5 & S6 & S7 & P0 & P16).
    split; [apply (sj_lib_agree m m' S0); intros a Ha; apply AG; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S1); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S2); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S3); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S4); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S5); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S6); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S7); intros a Ha; apply AG; cbn in Ha; lia|]. lia.
  - destruct ST as (S0 & S1 & S2 & S3 & S4 & S5 & S6).
    split; [apply (lib0_agree m m' S0); intros a Ha; apply AG; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S1); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S2); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S3); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S4); intros a Ha; apply AG; cbn in Ha; lia|].
    split; [apply (rw_cells_agree_nw bsegs m m' _ _ S5); intros a Ha; apply AG; cbn in Ha; lia|].
    apply (rw_cells_agree_nw bsegs m m' _ _ S6); intros a Ha; apply AG; cbn in Ha; lia.
Qed.

Lemma imp_libA_agree : forall v m m', imp_libA v m -> agree_on (imp_lib_rng v) m m' -> imp_libA v m'.
Proof.
  intros v m m' (ST & LB & (X1 & X2 & X3) & TP & LK) AG. split; [exact (imp_staticsA_agree v m m' ST AG)|]. split; [| split; [| split]].
  - destruct LB as (j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & j10 & j11 & j12 & j13 & j14 & j15 & H). exists j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, j14, j15.
    apply (rw_cells_agree_nw bsegs m m' _ _ H). intros a Ha. apply AG. rewrite locb_cellsA_size in Ha. unfold imp_lib_rng. do 10 right. left. lia.
  - unfold locx3, LOC_CVC, LOC_CVW in *. split; [| split];
      [apply (rw_cells_agree_nw bsegs m m' _ _ X1)| apply (rw_cells_agree_nw bsegs m m' _ _ X2)| apply (rw_cells_agree_nw bsegs m m' _ _ X3)];
      intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; unfold imp_lib_rng, PJ_LOC_LO_A; do 10 right; left; lia.
  - unfold imp_tplocA in *. apply (rw_cells_agree_nw bsegs m m' _ _ TP). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. unfold imp_lib_rng. do 12 right. left. lia.
  - unfold lockwA in *. apply (rw_cells_agree_nw bsegs m m' _ _ LK). intros a Ha. apply AG. cbn [cells_size csize Nat.add] in Ha. unfold imp_lib_rng. do 11 right. left. lia.
Qed.

Lemma imp_lib_rng_cases : forall v x, imp_lib_rng v x ->
  (client_static x /\ 0x6bc000 <= x < 0x6de75c) \/ (exists A8, v = Some A8 /\ A8 <= x < A8 + 8).
Proof.
  intros v x H. unfold imp_lib_rng, PJ_LOC_LO_A, PJ_LOCKW_A, TPV_A in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]];
    try (left; split; [apply client_static_intro; lia| lia]).
  destruct v as [A8|]; [right; exists A8; split; [reflexivity| exact H]| destruct H].
Qed.

Lemma imp_lib_rng_fp : forall v x, imp_lib_rng v x -> in_ranges (LIB_FP ++ IMP_FP_A) x \/ (exists A8, v = Some A8 /\ A8 <= x < A8 + 8).
Proof.
  intros v x H. unfold imp_lib_rng, PJ_LOC_LO_A, PJ_LOCKW_A, TPV_A in H. unfold in_ranges, LIB_FP, IMP_FP_A, IMP_VEC_OBJ_A, IMP_GUARD_A, IMP_AVL_GUARD_A.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]].
  - left. exists 0x6bc000, (0x6bc000 + 24). split; [apply in_or_app; right; cbn; left; reflexivity| lia].
  - left. exists 0x6bc040, (0x6bc040 + 2). split; [apply in_or_app; right; cbn; right; left; reflexivity| lia].
  - left. exists 0x6bc100, (0x6bc100 + 2). split; [apply in_or_app; right; cbn; right; right; left; reflexivity| lia].
  - left. exists 0x6bc120, 0x6bc128. split; [apply in_or_app; left; cbn; tauto| lia].
  - left. exists 0x6bc140, 0x6bc148. split; [apply in_or_app; left; cbn; tauto| lia].
  - left. exists 0x6bc160, 0x6bc170. split; [apply in_or_app; left; cbn; tauto| lia].
  - left. exists 0x6bc180, 0x6bc188. split; [apply in_or_app; left; cbn; tauto| lia].
  - left. exists 0x6bc1a0, 0x6bc1a8. split; [apply in_or_app; left; cbn; tauto| lia].
  - left. exists 0x6bc1c0, 0x6bc1f0. split; [apply in_or_app; left; cbn; tauto| lia].
  - left. exists 0x6bc220, 0x6bc228. split; [apply in_or_app; left; cbn; tauto| lia].
  - left. exists 0x6bcc28, 0x6bdad8. split; [apply in_or_app; left; cbn; tauto| lia].
  - left. exists 0x6de758, 0x6de75c. split; [apply in_or_app; left; cbn; tauto| lia].
  - left. exists 0x6be3b8, 0x6be3c0. split; [apply in_or_app; left; cbn; tauto| lia].
  - destruct v as [A8|]; [right; exists A8; split; [reflexivity| exact H]| destruct H].
Qed.

Definition FUZZ_COST_IMP : Z := 3 * 2^31.

Definition FUZZ_LIVE_IMP : Z := 16.

Definition FUZZ_STACK_IMP : Z := FUZZ_STACK.

Section LibIfaceImp.
Variable RT : rt_sig.
Variable LIBv : option Z -> mem -> Prop.

Definition fuzz_one_cps_imp : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z) (v : option Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = wz d -> a1 = wz (Z.of_nat (length bs)) -> tp = wz TP_A ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE_IMP <= LIVE_MAX -> FUZZ_COST_IMP <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->

  LIBv v m -> aexvA v m -> (forall A8, v = Some A8 -> In (A8, 8) (rt_live RT Σ)) ->
  io_ssp m -> libc_nl m -> el_xdataA m -> el_auxvA (bv_unsigned sp) m -> rt_sp0 RT Σ <= bv_unsigned sp + FUZZ_SP0GAP ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK_IMP <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ -> frm0 fc ->
  cps bsegs (fun c => ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_fuzz m)) c /\ frm0 (ms_fcsr (cfg_ms c)))
    (fun c => (exists (Σ' : rts RT) (A8 : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IMP_XFP_A m m'
         /\ LIBv (Some A8) m' /\ aex6A m') c
       /\ (forall B, v = Some B -> A8 = B)
       /\ rt_live RT Σ' = xnewA v A8 ++ rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST_IMP <= rt_credit RT Σ') /\ frm0 (ms_fcsr (cfg_ms c))).

End LibIfaceImp.

