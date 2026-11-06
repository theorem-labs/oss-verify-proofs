(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import RT_iface RT_traces RT_gaps_iface I_strcmp_spec Lept_kit D_iface D_defs D_libiface Lept_iface Gm_iface Fh_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition fh_gen_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pixs name : Z) (vs : pixv) (cvs : cmapv) (i : nat),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 pixs -> a2 = Z_to_bv 64 name ->
  pix_obj (rt_live RT Σ) m pixs vs cvs -> p_d vs = 1 -> p_data vs <> 0 -> 64 < p_w vs -> 64 < p_h vs -> hm_name_arg RT Σ m name i ->
  LIB_SEL m -> lenv RT Σ m sp lo (LSTK 10) -> lres RT Σ 4 4 FHMTGEN_COST -> bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pixFHMTGen_1 m)))
    (fun c => exists (Σ' : rts RT) (pixd : Z) (vd : pixv) (cvd : cmapv),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 pixd) m' ms
          /\ lpost RT Σ Σ' m m' sp lo /\ keepsL RT (rt_live RT Σ) Σ sp [] m m'
          /\ pix_obj (rt_live RT Σ') m' pixd vd cvd /\ p_w vd = p_w vs /\ p_h vd = p_h vs /\ p_d vd = 1 /\ p_data vd <> 0) c
       /\ live_destroy pixd vd cvd (rt_live RT Σ') = rt_live RT Σ
       /\ (forall p n, In (p, n) (rt_live RT Σ') -> 0 < n) /\ Z.of_nat (length (rt_live RT Σ')) <= Z.of_nat (length (rt_live RT Σ)) + 4
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - FHMTGEN_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition hm_cmp_ok (i k : nat) : bool :=
  (strcmp_sz (hm_name i) (hm_name k) <=? 8) && (0 <? strcmp_sz (hm_name i) (hm_name k))
  && (if Nat.eqb i k then strcmp_res (hm_name i) (hm_name k) =? 0 else negb (strcmp_res (hm_name i) (hm_name k) =? 0))
  && (Z.of_nat (length (hm_name i)) =? 8) && (Z.of_nat (length (hm_name k)) =? 8)
  && (-1 <=? strcmp_res (hm_name i) (hm_name k)) && (strcmp_res (hm_name i) (hm_name k) <=? 1).
Lemma hm_cmp_all : forallb (fun i => forallb (fun k => hm_cmp_ok i k) (seq 0 10)) (seq 0 10) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hm_cmp : forall i k, (i < 10)%nat -> (k < 10)%nat ->
  0 < strcmp_sz (hm_name i) (hm_name k) <= 8 /\ strcmp_ok (hm_name i) (hm_name k) /\ length (hm_name i) = 8%nat
  /\ (i = k -> strcmp_res (hm_name i) (hm_name k) = 0) /\ (i <> k -> strcmp_res (hm_name i) (hm_name k) <> 0)
  /\ -1 <= strcmp_res (hm_name i) (hm_name k) <= 1.
Proof.
  intros i k Hi Hk. pose proof hm_cmp_all as A. rewrite forallb_forall in A.
  specialize (A i ltac:(apply in_seq; lia)). rewrite forallb_forall in A. specialize (A k ltac:(apply in_seq; lia)).
  unfold hm_cmp_ok in A. repeat (apply andb_prop in A; let B := fresh "B" in destruct A as [A B]).
  apply Z.leb_le in A. apply Z.ltb_lt in B4. apply Z.eqb_eq in B2. apply Z.eqb_eq in B1. apply Z.leb_le in B0. apply Z.leb_le in B.
  split; [lia|]. split; [unfold strcmp_ok; lia|]. split; [lia|].
  destruct (Nat.eqb_spec i k) as [E|NE].
  - apply Z.eqb_eq in B3. split; [intros _; exact B3|]. split; [intros C; contradiction| lia].
  - apply negb_true_iff in B3. apply Z.eqb_neq in B3. split; [intros C; contradiction|]. split; [intros _; exact B3| lia].
Qed.

(* [comment removed for export] *)
Lemma sel_names_client : forall x, 0xf0f40 <= x < 0xf1260 -> client_static x.
Proof.
  intros x Hx. split; [exists 0xf0c90, 0xf5858; split; [left; reflexivity| lia]|].
  intros (l & h & Hin & Hx'). unfold RT_STATIC in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma lib_sel_row : forall (m : mem) (k : nat), LIB_SEL m -> (k < 10)%nat ->
  bytes_at asegs m (SEL_NAMES_AT + 80 * Z.of_nat k) (hm_name k).
Proof.
  intros m k [[_ HB] _] Hk. unfold hm_name, SEL_NAMES_AT.
  rewrite <- (firstn_skipn (80 * k) (cells_bytes LIB_SEL_CELLS)) in HB.
  apply (proj1 (bytes_at_app asegs m _ _ _)) in HB. destruct HB as [_ S2].
  assert (LF : Z.of_nat (length (firstn (80 * k) (cells_bytes LIB_SEL_CELLS))) = 80 * Z.of_nat k).
  { rewrite length_firstn. change (length (cells_bytes LIB_SEL_CELLS)) with 800%nat. lia. }
  rewrite LF in S2.
  rewrite <- (firstn_skipn 8 (skipn (80 * k) (cells_bytes LIB_SEL_CELLS))) in S2.
  exact (proj1 (proj1 (bytes_at_app asegs m _ _ _) S2)).
Qed.
