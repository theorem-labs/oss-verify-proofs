(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Stdio AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_anndefs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition ATPA_SPLITINTO : Z := 0xb1fa8.
Definition ATPA_SPLIT : Z := 0xb49dc.
Definition ATPA_FIND : Z := 0xb4af8.
Definition ATPA_PUSHR : Z := 0xb4c24.
Definition ATPA_PUSHC : Z := 0xb53ac.
Definition ATPA_EMPL : Z := 0xb2370.
Definition ATPA_ANNINC : Z := 0xb4de4.
Definition ATPA_ANNSHRINK : Z := 0xb4e8c.
Definition ATPA_SWAPOUT : Z := 0xb4f34.
Definition ATPA_SBDTOR : Z := 0xb50a0.
Definition ATPA_ALLOCATE : Z := 0xb518c.
Definition ATPA_ANNDEL : Z := 0xb51c8.
Definition ATPA_VDEALLOC : Z := 0xb556c.
Definition ATPA_DESTROY : Z := 0xb91a8.
Definition ATPA_OPNEW : Z := 0x163020.
Definition ATPA_OPDEL : Z := 0x1064b8.
Definition ATPA_SEP : Z := 0x23780.
Definition TPVB : Z := 0x6a7e68.

Definition atp_elsA (D : Z) (d : list Z) : list (Z * Z) :=
  map (pview D) (poffs d) ++ repeat (0, 0) (atp_P d - length (poffs d)).

Lemma atp_elsA_length : forall D d, length (atp_elsA D d) = atp_P d.
Proof. intros D d. unfold atp_elsA, atp_P. rewrite length_app, length_map, repeat_length, poffs_length. lia. Qed.

Definition vrepA (m : mem) (V A cap size : Z) (els : list (Z * Z)) : Prop :=
  size = zlength els /\ 0 <= size <= cap /\ cap <= 2^25 /\ 0 <= A /\ A + 16 * cap < 2^63
  /\ rw_cells asegs m V [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 16 * size)); C8 (Z_to_bv 64 (A + 16 * cap))]
  /\ ((cap = 0 /\ A = 0) \/ (1 <= cap /\ A mod 16 = 0 /\ 0 < A /\ rw_cells asegs m A (velts els))).

Definition vblockA (A cap size : Z) : list (Z * Z) := if cap =? 0 then [] else ann_block A (16 * cap) (16 * size).
Definition vliveA (live : list (Z * Z)) (A cap size : Z) (L0 : list (Z * Z)) : Prop := live = vblockA A cap size ++ L0.

Definition vcost_push (cap size : Z) : Z := if size <? cap then 0 else mcost (16 * vcap_next cap size).
Fixpoint vcost_pushes (n : nat) (cap size : Z) : Z :=
  match n with
  | O => 0
  | S n' => vcost_push cap size + vcost_pushes n' (if size <? cap then cap else vcap_next cap size) (size + 1)
  end.
Definition vcap_after (cap size : Z) : Z := if size <? cap then cap else vcap_next cap size.

Fixpoint vcap_iter (n : nat) (cap size : Z) : Z :=
  match n with O => cap | S n' => vcap_iter n' (vcap_after cap size) (size + 1) end.

Lemma vcap_after_ge : forall c s, 0 <= s <= c -> s + 1 <= vcap_after c s <= Z.max (2 * c) (s + 1).
Proof. intros c s H. unfold vcap_after, vcap_next. destruct (Z.ltb_spec s c); lia. Qed.

Lemma vcap_iter_inv : forall n c s, 0 <= s <= c -> c <= 2 * s -> s + Z.of_nat n <= vcap_iter n c s <= 2 * (s + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros c s H1 H2; cbn [vcap_iter]; [lia|].
  assert (G : s + 1 <= vcap_after c s <= 2 * (s + 1)) by (unfold vcap_after, vcap_next; destruct (Z.ltb_spec s c); lia).
  specialize (IH (vcap_after c s) (s + 1) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma vcost_push_nonneg : forall c s, 0 <= s <= c -> 0 <= vcost_push c s.
Proof. intros c s H. unfold vcost_push. destruct (s <? c); [lia|]. unfold mcost, vcap_next. destruct (_ <=? _); unfold DCOST; lia. Qed.

Lemma vcost_pushes_nonneg : forall n c s, 0 <= s <= c -> 0 <= vcost_pushes n c s.
Proof.
  induction n as [|n IH]; intros c s H; cbn [vcost_pushes]; [lia|].
  pose proof (vcost_push_nonneg c s H). pose proof (vcap_after_ge c s H) as G.
  specialize (IH (if s <? c then c else vcap_next c s) (s + 1)). unfold vcap_after in G. specialize (IH ltac:(lia)). lia.
Qed.

Lemma vcost_pushes_S : forall n c s, vcost_pushes (S n) c s = vcost_push c s + vcost_pushes n (vcap_after c s) (s + 1).
Proof. intros. reflexivity. Qed.
Lemma vcap_iter_S0 : forall n c s, vcap_iter (S n) c s = vcap_iter n (vcap_after c s) (s + 1).
Proof. intros. reflexivity. Qed.

Lemma vcost_pushes_snoc : forall n c s,
  vcost_pushes (S n) c s = vcost_pushes n c s + vcost_push (vcap_iter n c s) (s + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros c s.
  - rewrite vcost_pushes_S. cbn [vcost_pushes vcap_iter]. rewrite Nat2Z.inj_0, !Z.add_0_r. lia.
  - rewrite vcost_pushes_S, (IH (vcap_after c s) (s + 1)), vcost_pushes_S, vcap_iter_S0.
    replace (s + 1 + Z.of_nat n) with (s + Z.of_nat (S n)) by lia. lia.
Qed.

Lemma vcap_iter_S : forall n c s, vcap_iter (S n) c s = vcap_after (vcap_iter n c s) (s + Z.of_nat n).
Proof.
  induction n as [|n IH]; intros c s; [cbn [vcap_iter]; rewrite Nat2Z.inj_0, !Z.add_0_r; reflexivity|].
  rewrite vcap_iter_S0, (IH (vcap_after c s) (s + 1)), vcap_iter_S0. f_equal. lia.
Qed.

Section HIface.
Variable RT : rt_sig.

Definition push_postA (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (lo V cap size : Z) (els : list (Z * Z)) (x : Z * Z) (L0 : list (Z * Z)) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (A' : Z),
    ASTA RT Σ' PMc (fun ms => exists (v : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp L0 (rt_frames RT Σ) (bv_unsigned sp) [(V, V + 24)] m m'
         /\ vrepA m' V A' (vcap_after cap size) (size + 1) (els ++ [x])) c
    /\ vliveA (rt_live RT Σ') A' (vcap_after cap size) (size + 1) L0
    /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ - vcost_push cap size <= rt_credit RT Σ'.

Definition push_cpsA (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V X A cap size xd xl : Z) (els : list (Z * Z)) (L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 X -> tp = Z_to_bv 64 0x6a7e68 ->
  vrepA m V A cap size els -> vliveA (rt_live RT Σ) A cap size L0 -> (forall p n, In (p, n) L0 -> 0 < n) ->
  size + 1 <= 2^24 ->
  rw_cells asegs m X [C8 (Z_to_bv 64 xd); C8 (Z_to_bv 64 xl)] ->

  fobj RT Σ m V 24 -> bv_unsigned sp <= X -> X + 32 <= USTACK_TOP -> X mod 8 = 0 ->
  Z.of_nat (length L0) + 4 <= LIVE_MAX -> vcost_push cap size <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 224 + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (push_postA Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo V cap size els (xd, xl) L0 m).

End HIface.

Definition ATPA_FIND_STACK : Z := 96 + RT_STACK.
Definition ATPA_PUSH_STACK : Z := 224 + RT_STACK.
Definition ATPA_SPLIT_STACK : Z := 128 + ATPA_PUSH_STACK.
Definition ATPA_SPLITINTO_STACK : Z := 192 + ATPA_SPLIT_STACK.
Definition ATPA_DESTROY_STACK : Z := 128 + RT_STACK.

Section HIface2.
Variable RT : rt_sig.

Definition find_resA (l : list Z) : Z := match find_sep l with Some i => Z.of_nat i | None => -1 end.

Definition find_cpsA : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (X P : Z) (l : list Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 X -> a1 = Z_to_bv 64 ATPA_SEP -> a2 = Z_to_bv 64 4 -> a3 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x6a7e68 ->
  bv_unsigned sp <= X -> X + 16 <= USTACK_TOP -> X mod 8 = 0 ->
  rw_cells asegs m X [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 (zlength l))] ->
  bytes_at asegs m P (to_bytes l) -> Forall (fun c => 0 <= c < 256) l -> zlength l < 2^26 ->
  (exists p k, In (p, k) (rt_live RT Σ) /\ p <= P /\ P + zlength l <= p + k) ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + ATPA_FIND_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc ATPA_FIND m)))
    (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (find_resA l)) m' ms
         /\ rt_after_f RT Σ (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [] m m')).

Definition split_postA (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (lo V D : Z) (d : list Z) (L0 : list (Z * Z)) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (A' : Z),
    ASTA RT Σ' PMc (fun ms => exists (v : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp L0 (rt_frames RT Σ) (bv_unsigned sp) [(V, V + 24)] m m'
         /\ vrepA m' V A' (vcap_iter (length (poffs d)) 0 0) (zlength (poffs d)) (map (pview D) (poffs d))) c
    /\ vliveA (rt_live RT Σ') A' (vcap_iter (length (poffs d)) 0 0) (zlength (poffs d)) L0
    /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ - vcost_pushes (length (poffs d)) 0 0 <= rt_credit RT Σ'.

Definition split_cpsA : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V D : Z) (d : list Z) (jv : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 V -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 (zlength d) -> tp = Z_to_bv 64 0x6a7e68 ->
  d <> [] -> bytes_at asegs m D (to_bytes d) -> Forall (fun c => 0 <= c < 256) d -> zlength d < 2^26 ->
  (exists p k, In (p, k) (rt_live RT Σ) /\ p <= D /\ D + zlength d <= p + k) -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  fobj RT Σ m V 24 -> rw_cells asegs m V [CB 24 jv] ->
  Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX -> vcost_pushes (length (poffs d)) 0 0 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + ATPA_SPLIT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc ATPA_SPLIT m)))
    (split_postA Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo V D d (rt_live RT Σ) m).

Definition splitinto_postA (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (lo RV FD D : Z) (d : list Z) (L0 : list (Z * Z)) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (A' : Z),
    ASTA RT Σ' PMc (fun ms => exists (v : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp L0 (rt_frames RT Σ) (bv_unsigned sp) [(RV, RV + 24); (FD, FD + 16)] m m'
         /\ vrepA m' RV A' (vcap_iter (length (poffs d)) 0 0) (zlength (poffs d)) (map (pview D) (poffs d))
         /\ rw_cells asegs m' FD [C8 (Z_to_bv 64 (D + zlength d)); C8 (Z_to_bv 64 0)]) c
    /\ vliveA (rt_live RT Σ') A' (vcap_iter (length (poffs d)) 0 0) (zlength (poffs d)) L0
    /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ - 1 - vcost_pushes (length (poffs d)) 0 0 <= rt_credit RT Σ'.

Definition splitinto_cpsA : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (RV FD D : Z) (d : list Z) (jv : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 RV -> a1 = Z_to_bv 64 FD -> tp = Z_to_bv 64 0x6a7e68 ->
  bytes_at asegs m D (to_bytes d) -> Forall (fun c => 0 <= c < 256) d -> zlength d < 2^26 -> 0 <= D -> (d = [] \/ 0 < D) ->
  ((exists p k, In (p, k) (rt_live RT Σ) /\ p <= D /\ D + zlength d <= p + k) \/ (d = [] /\ D < SEGTOP_A)) ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  fobj RT Σ m RV 24 -> rw_cells asegs m RV [CB 24 jv] ->
  bv_unsigned sp <= FD -> FD + 24 <= USTACK_TOP -> FD mod 8 = 0 ->
  rw_cells asegs m FD [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (zlength d))] ->
  Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX -> 1 + vcost_pushes (length (poffs d)) 0 0 <= rt_credit RT Σ ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX2)%nat ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + ATPA_SPLITINTO_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc ATPA_SPLITINTO m)))
    (splitinto_postA Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo RV FD D d (rt_live RT Σ) m).

Definition empl_cpsA : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (V A cap size : Z) (els : list (Z * Z)) (L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 V -> tp = Z_to_bv 64 0x6a7e68 ->
  vrepA m V A cap size els -> vliveA (rt_live RT Σ) A cap size L0 -> (forall p n, In (p, n) L0 -> 0 < n) ->
  size + 1 <= 2^24 -> fobj RT Σ m V 24 ->
  Z.of_nat (length L0) + 4 <= LIVE_MAX -> vcost_push cap size <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + ATPA_PUSH_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc ATPA_EMPL m)))
    (push_postA RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo V cap size els (0, 0) L0 m).

Definition vdestroy_cpsA : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (C V A cap size : Z) (els : list (Z * Z)) (L0 : list (Z * Z)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 C -> tp = Z_to_bv 64 0x6a7e68 ->
  bv_unsigned sp <= C -> C + 8 <= USTACK_TOP -> C mod 8 = 0 -> rw_cells asegs m C [C8 (Z_to_bv 64 V)] ->
  vrepA m V A cap size els -> vliveA (rt_live RT Σ) A cap size L0 -> (forall p n, In (p, n) L0 -> 0 < n) -> 1 <= cap -> fobj RT Σ m V 24 ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + ATPA_DESTROY_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> unwind_ok ra s0 sp -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc ATPA_DESTROY m)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (v : word) m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp L0 (rt_frames RT Σ) (bv_unsigned sp) [(V, V + 24)] m m') c
       /\ rt_live RT Σ' = L0 /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

End HIface2.
