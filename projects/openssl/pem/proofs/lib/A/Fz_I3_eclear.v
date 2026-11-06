(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_free Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_sk Fz_T_mtl Fz_T_its Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0 Fz_I3_glx0 Fz_G_OSSL_ERR_STATE_new Fz_I3_icfast Fz_I3_egsiw Fz_I3_egsi Fz_I3_eclw Fz_W5_rep Fz_W5_agr Fz_W5_clear.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation TP_A := (0xba3ef0)%Z (only parsing).

(* [comment removed for export] *)
Lemma cells_size_repeat : forall c k, cells_size (repeat c k) = (k * csize c)%nat.
Proof. intros c k. induction k as [|k IH]; cbn [repeat cells_size]; [reflexivity|]. cbn [cells_size] in IH. rewrite IH. lia. Qed.

Lemma cells_size_pre : forall c c' k, csize c' = csize c -> cells_size (repeat c' k) = (k * csize c)%nat.
Proof. intros c c' k E. rewrite cells_size_repeat, E. reflexivity. Qed.

Lemma repeat_snoc : forall {X} (c : X) k, repeat c (S k) = repeat c k ++ [c].
Proof. intros X c k. induction k as [|k IH]; [reflexivity|]. cbn [repeat app]. cbn [repeat] in IH. rewrite IH at 1. reflexivity. Qed.

(* [comment removed for export] *)
Lemma arr_get : forall (m : mem) A c c' (k n : nat), rw_cells asegs m A (repeat c' k ++ repeat c (n - k)) -> (k < n)%nat -> csize c' = csize c ->
  rw_cells asegs m (A + Z.of_nat (k * csize c)) [c].
Proof.
  intros m A c c' k n whole k_lt sizes_match.
  pose proof (rw_cells_skip m A (repeat c' k) (repeat c (n - k)) whole) as untouched_tail.
  rewrite (cells_size_pre c c' k sizes_match) in untouched_tail.
  replace (n - k)%nat with (S (n - S k)) in untouched_tail by lia.
  exact (rw_cells_head m _ c (repeat c (n - S k)) untouched_tail).
Qed.

(* [comment removed for export] *)
Lemma arr_step : forall (m m' : mem) A c c' (k n : nat), rw_cells asegs m A (repeat c' k ++ repeat c (n - k)) -> (k < n)%nat -> csize c' = csize c ->
  wmono asegs m m' ->
  (forall x : word, A <= bv_unsigned x < A + Z.of_nat (n * csize c) ->
     ~ (A + Z.of_nat (k * csize c) <= bv_unsigned x < A + Z.of_nat (k * csize c) + Z.of_nat (csize c)) -> m' x = m x) ->
  rw_cells asegs m' (A + Z.of_nat (k * csize c)) [c'] ->
  rw_cells asegs m' A (repeat c' (S k) ++ repeat c (n - S k)).
Proof.
  intros m m' A c c' k n whole k_lt sizes_match grows same_elsewhere slot_now.
  assert (n_split : (n * csize c = k * csize c + csize c + (n - S k) * csize c)%nat)
    by (rewrite <- Nat.mul_succ_l, <- Nat.mul_add_distr_r; f_equal; lia).
  pose proof (Nat2Z.is_nonneg (k * csize c)) as head_nonneg.
  pose proof (Nat2Z.is_nonneg ((n - S k) * csize c)) as tail_nonneg.
  replace (n - k)%nat with (S (n - S k)) in whole by lia. cbn [repeat] in whole.
  apply rw_cells_app in whole as [done_old pending_old].
  rewrite (cells_size_pre c c' k sizes_match) in pending_old.
  apply rw_cells_tail in pending_old.
  rewrite repeat_snoc, <- app_assoc.
  apply rw_cells_app. split.
  - apply (rw_cells_agree asegs m m' A _ done_old); [| exact grows].
    intros x x_in. cbv beta in x_in. rewrite (cells_size_pre c c' k sizes_match) in x_in.
    apply same_elsewhere; [rewrite n_split, !Nat2Z.inj_add |]; lia.
  - rewrite (cells_size_pre c c' k sizes_match). apply rw_cells_app. split; [exact slot_now |].
    cbn [cells_size]. rewrite Nat.add_0_r, sizes_match.
    apply (rw_cells_agree asegs m m' _ _ pending_old); [| exact grows].
    intros x x_in. cbv beta in x_in. rewrite cells_size_repeat in x_in.
    apply same_elsewhere; [rewrite n_split, !Nat2Z.inj_add |]; lia.
Qed.

(* [comment removed for export] *)
Definition zb4 : cell := CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition ecl_arrs (m : mem) (E : Z) (k : nat) : Prop :=
     rw_cells asegs m E (repeat (C4 z64) k ++ repeat (C4 z64) (16 - k))
  /\ rw_cells asegs m (E + 64) (repeat (C4 z64) k ++ repeat (C4 z64) (16 - k))
  /\ rw_cells asegs m (E + 128) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells asegs m (E + 256) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells asegs m (E + 384) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells asegs m (E + 512) (repeat (C4 z64) k ++ repeat zb4 (16 - k))
  /\ rw_cells asegs m (E + 576) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells asegs m (E + 704) (repeat (C4 ECL_LNW) k ++ repeat (C4 z64) (16 - k))
  /\ rw_cells asegs m (E + 768) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells asegs m (E + 896) [C4 z64; C4 z64].

Lemma rw_CB_of_bytes_ec : forall (m : mem) a bs, bytes_at asegs m a bs -> wr_at asegs m a (Z.of_nat (length bs)) -> rw_cells asegs m a [CB (length bs) bs].
Proof.
  intros m a bs readable writable. unfold rw_cells, cells_at.
  cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, Nat.add_0_r. exact (conj (conj (conj eq_refl I) readable) writable).
Qed.

(* [comment removed for export] *)
Lemma ecl_arrs_of_zeros : forall (m : mem) E, bytes_at asegs m E (repeat (Z_to_bv 8 0) (Z.to_nat 904)) -> wr_at asegs m E 904 -> ecl_arrs m E 0.
Proof.
  intros m E zeros_read zeros_room.
  pose proof (rw_CB_of_bytes_ec m E _ zeros_read) as as_blob. rewrite repeat_length in as_blob.
  specialize (as_blob zeros_room).
  assert (peel : forall (A B : Z) (front back : list cell), rw_cells asegs m A (front ++ back) -> A + Z.of_nat (cells_size front) = B ->
                 rw_cells asegs m A front /\ rw_cells asegs m B back).
  { intros A B front back joined at_B. apply rw_cells_app in joined as [front_ok back_ok]. rewrite at_B in back_ok.
    exact (conj front_ok back_ok). }
  apply (rw_cells_recast m E _ (repeat (C4 z64) 16 ++ repeat (C4 z64) 16 ++ repeat (C8 z64) 16 ++ repeat (C8 z64) 16 ++ repeat (C8 z64) 16
                                  ++ repeat zb4 16 ++ repeat (C8 z64) 16 ++ repeat (C4 z64) 16 ++ repeat (C8 z64) 16 ++ [C4 z64; C4 z64])) in as_blob;
    [| vm_compute; repeat split | vm_compute; reflexivity].
  destruct (peel _ (E + 64) _ _ as_blob ltac:(rewrite cells_size_repeat; cbn [csize]; lia)) as [flags_z as_blob1].
  destruct (peel _ (E + 128) _ _ as_blob1 ltac:(rewrite cells_size_repeat; cbn [csize]; lia)) as [marks_z as_blob2].
  destruct (peel _ (E + 256) _ _ as_blob2 ltac:(rewrite cells_size_repeat; cbn [csize]; lia)) as [buffer_z as_blob3].
  destruct (peel _ (E + 384) _ _ as_blob3 ltac:(rewrite cells_size_repeat; cbn [csize]; lia)) as [data_z as_blob4].
  destruct (peel _ (E + 512) _ _ as_blob4 ltac:(rewrite cells_size_repeat; cbn [csize]; lia)) as [dsize_z as_blob5].
  destruct (peel _ (E + 576) _ _ as_blob5 ltac:(rewrite cells_size_repeat; cbn [csize zb4]; lia)) as [dflags_z as_blob6].
  destruct (peel _ (E + 704) _ _ as_blob6 ltac:(rewrite cells_size_repeat; cbn [csize]; lia)) as [file_z as_blob7].
  destruct (peel _ (E + 768) _ _ as_blob7 ltac:(rewrite cells_size_repeat; cbn [csize]; lia)) as [line_z as_blob8].
  destruct (peel _ (E + 896) _ _ as_blob8 ltac:(rewrite cells_size_repeat; cbn [csize]; lia)) as [func_z topbot_z].
  exact (conj flags_z (conj marks_z (conj buffer_z (conj data_z (conj dsize_z (conj dflags_z (conj file_z (conj line_z (conj func_z topbot_z))))))))).
Qed.

(* [comment removed for export] *)
Lemma ecl_arrs_get : forall (m : mem) E (k : nat), (k < 16)%nat -> ecl_arrs m E k ->
  rw_cells asegs m (E + 4 * Z.of_nat k) [C4 z64] /\ rw_cells asegs m (E + 4 * Z.of_nat k + 64) [C4 z64] /\ rw_cells asegs m (E + 8 * Z.of_nat k + 128) [C8 z64]
  /\ rw_cells asegs m (E + 8 * Z.of_nat k + 256) [C8 z64] /\ rw_cells asegs m (E + 8 * Z.of_nat k + 384) [C8 z64] /\ rw_cells asegs m (E + 4 * Z.of_nat k + 512) [zb4]
  /\ rw_cells asegs m (E + 8 * Z.of_nat k + 576) [C8 z64] /\ rw_cells asegs m (E + 4 * Z.of_nat k + 704) [C4 z64] /\ rw_cells asegs m (E + 8 * Z.of_nat k + 768) [C8 z64].
Proof.
  intros m E k k_lt (flags_a & marks_a & buffer_a & data_a & dsize_a & dflags_a & file_a & line_a & func_a & _).
  assert (moved : forall A B cs, rw_cells asegs m A cs -> A = B -> rw_cells asegs m B cs) by (intros A B cs held <-; exact held).
  pose proof (arr_get m _ _ _ k 16 flags_a k_lt eq_refl) as flags_k.
  pose proof (arr_get m _ _ _ k 16 marks_a k_lt eq_refl) as marks_k.
  pose proof (arr_get m _ _ _ k 16 buffer_a k_lt eq_refl) as buffer_k.
  pose proof (arr_get m _ _ _ k 16 data_a k_lt eq_refl) as data_k.
  pose proof (arr_get m _ _ _ k 16 dsize_a k_lt eq_refl) as dsize_k.
  pose proof (arr_get m _ _ _ k 16 dflags_a k_lt eq_refl) as dflags_k.
  pose proof (arr_get m _ _ _ k 16 file_a k_lt eq_refl) as file_k.
  pose proof (arr_get m _ _ _ k 16 line_a k_lt eq_refl) as line_k.
  pose proof (arr_get m _ _ _ k 16 func_a k_lt eq_refl) as func_k.
  cbn [csize zb4] in flags_k, marks_k, buffer_k, data_k, dsize_k, dflags_k, file_k, line_k, func_k.
  split; [apply (moved _ _ _ flags_k); lia |]. split; [apply (moved _ _ _ marks_k); lia |].
  split; [apply (moved _ _ _ buffer_k); lia |]. split; [apply (moved _ _ _ data_k); lia |].
  split; [apply (moved _ _ _ dsize_k); lia |]. split; [apply (moved _ _ _ dflags_k); lia |].
  split; [apply (moved _ _ _ file_k); lia |]. split; [apply (moved _ _ _ line_k); lia |].
  apply (moved _ _ _ func_k); lia.
Qed.

(* [comment removed for export] *)
Lemma ecl_arrs_step : forall (m m' : mem) E (k : nat), (k < 16)%nat -> ecl_arrs m E k -> wmono asegs m m' ->
  (forall x : word, E <= bv_unsigned x < E + 904 -> outside (ecl_W E (Z.of_nat k)) (bv_unsigned x) -> m' x = m x) ->
  rw_cells asegs m' (E + 4 * Z.of_nat k) [C4 z64] -> rw_cells asegs m' (E + 4 * Z.of_nat k + 64) [C4 z64] -> rw_cells asegs m' (E + 8 * Z.of_nat k + 128) [C8 z64] ->
  rw_cells asegs m' (E + 8 * Z.of_nat k + 256) [C8 z64] -> rw_cells asegs m' (E + 8 * Z.of_nat k + 384) [C8 z64] -> rw_cells asegs m' (E + 4 * Z.of_nat k + 512) [C4 z64] ->
  rw_cells asegs m' (E + 8 * Z.of_nat k + 576) [C8 z64] -> rw_cells asegs m' (E + 4 * Z.of_nat k + 704) [C4 ECL_LNW] -> rw_cells asegs m' (E + 8 * Z.of_nat k + 768) [C8 z64] ->
  ecl_arrs m' E (S k).
Proof.
  intros m m' E k k_lt arrays grows kept_outside new_flags new_marks new_buffer new_data new_dsize new_dflags new_file new_line new_func.
  destruct arrays as (flags_a & marks_a & buffer_a & data_a & dsize_a & dflags_a & file_a & line_a & func_a & topbot_a).
  assert (k_top : Z.of_nat k <= 15) by lia.
  assert (kept_window : forall lo hi (x : word), E <= lo -> hi <= E + 904 -> lo <= bv_unsigned x < hi ->
            outside (ecl_W E (Z.of_nat k)) (bv_unsigned x) -> m' x = m x)
    by (intros lo hi x lo_in hi_in x_in x_out; apply kept_outside; [lia | exact x_out]).
  assert (moved : forall A B cs, rw_cells asegs m' A cs -> A = B -> rw_cells asegs m' B cs) by (intros A B cs held <-; exact held).
  unfold ecl_arrs.
  refine (conj (arr_step m m' E _ _ k 16 flags_a k_lt eq_refl grows _ _) _);
    [ intros x x_in x_off; cbn [csize] in x_in, x_off; apply (kept_window E (E + 64) x); [lia | lia | lia |];
      unfold ecl_W; cbn [outside]; repeat split; lia
    | apply (moved _ _ _ new_flags); cbn [csize]; lia |].
  refine (conj (arr_step m m' (E + 64) _ _ k 16 marks_a k_lt eq_refl grows _ _) _);
    [ intros x x_in x_off; cbn [csize] in x_in, x_off; apply (kept_window (E + 64) (E + 128) x); [lia | lia | lia |];
      unfold ecl_W; cbn [outside]; repeat split; lia
    | apply (moved _ _ _ new_marks); cbn [csize]; lia |].
  refine (conj (arr_step m m' (E + 128) _ _ k 16 buffer_a k_lt eq_refl grows _ _) _);
    [ intros x x_in x_off; cbn [csize] in x_in, x_off; apply (kept_window (E + 128) (E + 256) x); [lia | lia | lia |];
      unfold ecl_W; cbn [outside]; repeat split; lia
    | apply (moved _ _ _ new_buffer); cbn [csize]; lia |].
  refine (conj (arr_step m m' (E + 256) _ _ k 16 data_a k_lt eq_refl grows _ _) _);
    [ intros x x_in x_off; cbn [csize] in x_in, x_off; apply (kept_window (E + 256) (E + 384) x); [lia | lia | lia |];
      unfold ecl_W; cbn [outside]; repeat split; lia
    | apply (moved _ _ _ new_data); cbn [csize]; lia |].
  refine (conj (arr_step m m' (E + 384) _ _ k 16 dsize_a k_lt eq_refl grows _ _) _);
    [ intros x x_in x_off; cbn [csize] in x_in, x_off; apply (kept_window (E + 384) (E + 512) x); [lia | lia | lia |];
      unfold ecl_W; cbn [outside]; repeat split; lia
    | apply (moved _ _ _ new_dsize); cbn [csize]; lia |].
  refine (conj (arr_step m m' (E + 512) _ _ k 16 dflags_a k_lt eq_refl grows _ _) _);
    [ intros x x_in x_off; cbn [csize zb4] in x_in, x_off; apply (kept_window (E + 512) (E + 576) x); [lia | lia | lia |];
      unfold ecl_W; cbn [outside]; repeat split; lia
    | apply (moved _ _ _ new_dflags); cbn [csize zb4]; lia |].
  refine (conj (arr_step m m' (E + 576) _ _ k 16 file_a k_lt eq_refl grows _ _) _);
    [ intros x x_in x_off; cbn [csize] in x_in, x_off; apply (kept_window (E + 576) (E + 704) x); [lia | lia | lia |];
      unfold ecl_W; cbn [outside]; repeat split; lia
    | apply (moved _ _ _ new_file); cbn [csize]; lia |].
  refine (conj (arr_step m m' (E + 704) _ _ k 16 line_a k_lt eq_refl grows _ _) _);
    [ intros x x_in x_off; cbn [csize] in x_in, x_off; apply (kept_window (E + 704) (E + 768) x); [lia | lia | lia |];
      unfold ecl_W; cbn [outside]; repeat split; lia
    | apply (moved _ _ _ new_line); cbn [csize]; lia |].
  refine (conj (arr_step m m' (E + 768) _ _ k 16 func_a k_lt eq_refl grows _ _) _);
    [ intros x x_in x_off; cbn [csize] in x_in, x_off; apply (kept_window (E + 768) (E + 896) x); [lia | lia | lia |];
      unfold ecl_W; cbn [outside]; repeat split; lia
    | apply (moved _ _ _ new_func); cbn [csize]; lia |].
  apply (rw_cells_agree asegs m m' _ _ topbot_a); [| exact grows].
  intros x x_in. cbv beta in x_in. cbn [cells_size csize Nat.add] in x_in.
  apply (kept_window (E + 896) (E + 904) x); [lia | lia | lia |].
  unfold ecl_W; cbn [outside]; repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition ECLR_SITES : list (Z * Z) := [(SITE_ecl_egsi, e_eclear)] ++ ECL_SITES ++ EG_SITES.
Definition ECLR_CALLS : list (Z * Z) := [(SITE_ecl_egsi, e_get_state)] ++ ECL_CALLS ++ EG_CALLS.

Definition eclear_first_stmt (RT : rt_sig) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (k kd MK SA P : Z) (pad top : word)
    (jm1 jm2 jp : list byte) (u : byte) (r0 g0 oldcb : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 960 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_eclear (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) ECLR_SITES ECLR_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 7 <= LIVE_MAX -> 3 <= rt_credit RT Σ -> cl_env m lb canary ->
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> (exists od : word, rw_cells asegs m G_IC_OPTSDONE [C8 od] /\ Z.land (bv_unsigned od) 2 = 2) ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 1 <= k < 128 ->
  rw_cells asegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] -> In (MK, 72) (rt_live RT Σ) -> MK mod 8 = 0 ->
  rw_cells asegs m MK [CB 24 jm1] -> rw_cells asegs m (MK + 24) [C8 (Z_to_bv 64 SA)] -> rw_cells asegs m (MK + 32) [CB 40 jm2] ->
  In (SA, 32) (rt_live RT Σ) -> SA mod 8 = 0 -> rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top z64 (Z_to_bv 64 P)) ->
  In (P, 128) (rt_live RT Σ) -> P mod 8 = 0 -> rw_cells asegs m P [C8 z64] -> rw_cells asegs m (P + 8) [CB 120 jp] ->
  rw_cells asegs m 0x5a9f20 [C4 (Z_to_bv 64 kd); C4 (Z_to_bv 64 0xffffffff)] -> 1 <= kd < 128 -> kd <> k ->
  rw_cells asegs m (TSD_MAIN + 8 * kd) [C8 z64] -> rw_cells asegs m (TP_A + -150) [C1 u] -> rw_cells asegs m 0xb9f4a0 [C4 z64] ->
  rw_cells asegs m 0xb9f4c0 [C4 r0] -> rw_cells asegs m 0xb9f4e0 [C8 g0] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_eclear m)))
    (fun c => exists (Σ' : rts RT) (E N H G SK LK D : Z) (u' : byte) (top' : word),
       ASTA RT Σ' PMc (fun ms => exists m' : mem,
              ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (E + 896)) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EG_W kd SA P) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
           /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 1) (Z_to_bv 64 P)) /\ rw_cells asegs m' P [C8 (Z_to_bv 64 E); CB 120 jp]
           /\ rw_cells asegs m' MK [CB 24 jm1; C8 (Z_to_bv 64 SA); CB 40 jm2] /\ ecl_arrs m' E 16
           /\ rw_cells asegs m' (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 H)] /\ rw_cells asegs m' (TP_A + -150) [C1 u'] /\ rw_cells asegs m' 0xb9f4a0 [C4 (Z_to_bv 64 2)]
           /\ rw_cells asegs m' 0xb9f4c0 [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m' 0xb9f4e0 [C8 (Z_to_bv 64 G)] /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
           /\ rw_cells asegs m' H [C8 (Z_to_bv 64 N)] /\ rw_cells asegs m' N [C8 z64; C8 z64; C8 (Z_to_bv 64 ERR_DEL_THREAD_STATE); C8 z64]
           /\ rw_cells asegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]
           /\ rw_cells asegs m' SK (Fz_T_sk.sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64 (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))
           /\ rw_cells asegs m' LK (mutex_cells z64 z64) /\ rw_cells asegs m' D [C8 (Z_to_bv 64 H); CB 24 (repeat (Z_to_bv 8 0) 24)]) c
       /\ rt_live RT Σ' = [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] ++ rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - 3 /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ Forall (fun b => 0x10007fff8000 <= fst b /\ fst b mod 16 = 0 /\ fst b + snd b < USTACK_TOP) [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)]).

(* [comment removed for export] *)
Definition EZ16 : list word := repeat z64 16.
Definition ecl_ls (k : nat) : list word := repeat ECL_LNW k ++ repeat z64 (16 - k).

Lemma ec_rw_u32 : forall (m : mem) A cs ws, rw_cells asegs m A cs -> cells_bytes cs = u32s ws -> cells_size cs = (4 * length ws)%nat -> u32arr asegs m A ws.
Proof. intros m A cs ws [[WF B] W] E1 E2. split; [rewrite <- E1; exact B | rewrite E2 in W; rewrite Nat2Z.inj_mul in W; exact W]. Qed.
Lemma ec_rw_u64 : forall (m : mem) A cs ws, rw_cells asegs m A cs -> cells_bytes cs = u64s ws -> cells_size cs = (8 * length ws)%nat -> u64arr asegs m A ws.
Proof. intros m A cs ws [[WF B] W] E1 E2. split; [rewrite <- E1; exact B | rewrite E2 in W; rewrite Nat2Z.inj_mul in W; exact W]. Qed.
Lemma ec_rw_u8 : forall (m : mem) A cs bs, rw_cells asegs m A cs -> cells_bytes cs = bs -> cells_size cs = length bs -> u8arr asegs m A bs.
Proof. intros m A cs bs [[WF B] W] E1 E2. split; [rewrite <- E1; exact B | rewrite E2 in W; exact W]. Qed.
Lemma ec_u32_rw : forall (m : mem) A ws cs, u32arr asegs m A ws -> cells_wf cs -> cells_bytes cs = u32s ws -> cells_size cs = (4 * length ws)%nat -> rw_cells asegs m A cs.
Proof. intros m A ws cs [B W] WF E1 E2. split; [split; [exact WF | rewrite E1; exact B]|]. rewrite E2, Nat2Z.inj_mul. exact W. Qed.
Lemma ec_u64_rw : forall (m : mem) A ws cs, u64arr asegs m A ws -> cells_wf cs -> cells_bytes cs = u64s ws -> cells_size cs = (8 * length ws)%nat -> rw_cells asegs m A cs.
Proof. intros m A ws cs [B W] WF E1 E2. split; [split; [exact WF | rewrite E1; exact B]|]. rewrite E2, Nat2Z.inj_mul. exact W. Qed.
Lemma ec_u8_rw : forall (m : mem) A bs cs, u8arr asegs m A bs -> cells_wf cs -> cells_bytes cs = bs -> cells_size cs = length bs -> rw_cells asegs m A cs.
Proof. intros m A bs cs [B W] WF E1 E2. split; [split; [exact WF | rewrite E1; exact B]|]. rewrite E2. exact W. Qed.

Lemma es_rep_of_arrs0 : forall (m : mem) E, ecl_arrs m E 0 -> es_rep m E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls 0) EZ16.
Proof.
  intros m E (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). cbn [Nat.sub repeat app] in A0, A1, A2, A3, A4, A5, A6, A7, A8.
  unfold es_rep, EZ16, ecl_ls. cbn [Nat.sub].
  split; [exact (ec_rw_u32 m _ _ (repeat z64 16) A0 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (ec_rw_u32 m _ _ (repeat z64 16) A1 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (ec_rw_u64 m _ _ (repeat z64 16) A2 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (ec_rw_u8 m _ _ (repeat (Z_to_bv 8 0) 128) A3 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_rw_u8 m _ _ (repeat (Z_to_bv 8 0) 128) A4 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_rw_u8 m _ _ (repeat (Z_to_bv 8 0) 64) A5 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_rw_u64 m _ _ (repeat z64 16) A6 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (ec_rw_u32 m _ _ (repeat z64 16) A7 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact (ec_rw_u64 m _ _ (repeat z64 16) A8 ltac:(vm_compute; reflexivity) ltac:(reflexivity))|]. split; [reflexivity|].
  split; [exact A9|]. lia.
Qed.

Lemma arrs16_of_es_rep : forall (m : mem) E top bot, es_rep m E top bot EZ16 EZ16 EZ16 EZ16 (ecl_ls 16) EZ16 ->
  rw_cells asegs m E (repeat (C4 z64) 16) /\ rw_cells asegs m (E + 64) (repeat (C4 z64) 16) /\ rw_cells asegs m (E + 128) (repeat (C8 z64) 16)
  /\ rw_cells asegs m (E + 256) (repeat (C8 z64) 16) /\ rw_cells asegs m (E + 384) (repeat (C8 z64) 16) /\ rw_cells asegs m (E + 512) (repeat (C4 z64) 16)
  /\ rw_cells asegs m (E + 576) (repeat (C8 z64) 16) /\ rw_cells asegs m (E + 704) (repeat (C4 ECL_LNW) 16) /\ rw_cells asegs m (E + 768) (repeat (C8 z64) 16)
  /\ rw_cells asegs m (E + 896) [C4 (Z_to_bv 64 top); C4 (Z_to_bv 64 bot)].
Proof.
  intros m E top bot (U0 & _ & U1 & _ & U2 & _ & U3 & U4 & U5 & U6 & _ & U7 & _ & U8 & _ & TB & _).
  unfold EZ16, ecl_ls in *. cbn [Nat.sub repeat app] in U7.
  split; [exact (ec_u32_rw m _ _ (repeat (C4 z64) 16) U0 ltac:(vm_compute; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_u32_rw m _ _ (repeat (C4 z64) 16) U1 ltac:(vm_compute; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_u64_rw m _ _ (repeat (C8 z64) 16) U2 ltac:(vm_compute; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_u8_rw m _ _ (repeat (C8 z64) 16) U3 ltac:(vm_compute; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_u8_rw m _ _ (repeat (C8 z64) 16) U4 ltac:(vm_compute; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_u8_rw m _ _ (repeat (C4 z64) 16) U5 ltac:(vm_compute; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_u64_rw m _ _ (repeat (C8 z64) 16) U6 ltac:(vm_compute; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_u32_rw m _ _ (repeat (C4 ECL_LNW) 16) U7 ltac:(vm_compute; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  split; [exact (ec_u64_rw m _ _ (repeat (C8 z64) 16) U8 ltac:(vm_compute; repeat split; exact I) ltac:(vm_compute; reflexivity) ltac:(reflexivity))|].
  exact TB.
Qed.

Lemma upd_repeat_same : forall {X} (x : X) n i, upd (repeat x n) i x = repeat x n.
Proof. intros X x n. induction n as [|n IH]; intros i; [destruct i; reflexivity|]. destruct i as [|i]; cbn [repeat upd]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma upd_ecl_ls : forall k, (k < 16)%nat -> upd (ecl_ls k) k ECL_LNW = ecl_ls (S k).
Proof.
  intros k Hk. unfold ecl_ls. replace (16 - k)%nat with (S (16 - S k)) by lia. cbn [repeat].
  generalize (repeat z64 (16 - S k)) as tl. clear Hk. induction k as [|k IH]; intros tl; cbn [repeat app upd]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Section Eclear.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_FRN : crypto_free_null_env_stmt RT.
Hypothesis C_EGSI : egsi_first_stmt RT.

(* [comment removed for export] *)
Definition ecl_loop_stmt (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (E : Z) (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c : word),
  fdfs_only PMc -> mat_stable PMc ->
  (k < 16)%nat -> E mod 8 = 0 -> In (E, 904) (rt_live RT Σ) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m (Z_to_bv 64 (bv_unsigned sp + -96)) lo ->
  rt_sp0 RT Σ - STACK_WIN <= bv_unsigned sp - 96 -> bv_unsigned sp + 16 <= USTACK_TOP ->
  cg_ctx (rt_cg RT Σ) e_eclear (bv_unsigned rac :: outer) -> uw_chain m sp s0c outer -> cg_has (rt_cg RT Σ) ECL_SITES ECL_CALLS ->
  cl_env m lb canary ->
  rw_cells asegs m (bv_unsigned sp + -96) (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c) ->
  es_rep m E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls k) EZ16 ->
  cps asegs (ASTA RT Σ PMc (eq (clr_head_st sp gp (Z_to_bv 64 TP_A) s11 F fc E (Z.of_nat k) m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s9' s10' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
         ms = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 E) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 CLR_FILE) s3' (Z_to_bv 64 SHB) (Z_to_bv 64 128) (Z_to_bv 64 64) (Z_to_bv 64 (-1)) (Z_to_bv 64 128)
                      s9' s10' s11 t3' t4' t5' t6')
                 F' (Z_to_bv 64 (clr_next 15)) fc' None m' (seg_rom asegs)
         /\ rt_after RT Σ' (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) [(E, E + 904)] m m'
         /\ cl_env m' lb canary
         /\ rw_cells asegs m' (bv_unsigned sp + -96) (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)
         /\ uw_chain m' sp s0c outer
         /\ es_rep m' E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls 16) EZ16) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

(* [comment removed for export] *)
Lemma ecl_iter : forall (k : nat) (Σ : rts RT) PMc (sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (E : Z) (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c : word),
  fdfs_only PMc -> mat_stable PMc ->
  (k < 16)%nat -> E mod 8 = 0 -> In (E, 904) (rt_live RT Σ) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m (Z_to_bv 64 (bv_unsigned sp + -96)) lo ->
  rt_sp0 RT Σ - STACK_WIN <= bv_unsigned sp - 96 -> bv_unsigned sp + 16 <= USTACK_TOP ->
  cg_ctx (rt_cg RT Σ) e_eclear (bv_unsigned rac :: outer) -> uw_chain m sp s0c outer -> cg_has (rt_cg RT Σ) ECL_SITES ECL_CALLS ->
  cl_env m lb canary ->
  rw_cells asegs m (bv_unsigned sp + -96) (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c) ->
  es_rep m E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls k) EZ16 ->
  cps asegs (ASTA RT Σ PMc (eq (clr_head_st sp gp (Z_to_bv 64 TP_A) s11 F fc E (Z.of_nat k) m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6)))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s9' s10' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
         ms = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0' t1' t2' sp (Z_to_bv 64 E) a0' a1' a2' a3' a4' a5' a6' a7'
                      (Z_to_bv 64 CLR_FILE) s3' (Z_to_bv 64 SHB) (Z_to_bv 64 ((Z.of_nat k + 1) * 8)) (Z_to_bv 64 ((Z.of_nat k + 1) * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128)
                      s9' s10' s11 t3' t4' t5' t6')
                 F' (Z_to_bv 64 (clr_next (Z.of_nat k))) fc' None m' (seg_rom asegs)
         /\ rt_after RT Σ' (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) [(E, E + 904)] m m'
         /\ cl_env m' lb canary
         /\ rw_cells asegs m' (bv_unsigned sp + -96) (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)
         /\ uw_chain m' sp s0c outer
         /\ es_rep m' E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls (S k)) EZ16) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).
Proof using AF AFP C_FRN.
  intros k Σ PMc sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 F fc m lo outer lb canary E
    rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c fdfs_ok mat_ok k_lt e_aligned e_live art0 inv0 call0 sp0_below sp_top
    ctx0 chain0 graph0 env0 frame0 rep0.
  intros T c0 at_head finish.
  (* where the error state and the frame lie *)
  pose proof (af_live_range RT AF Σ m E 904 art0 e_live) as (_ & e_below & _).
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 art0 e_live ltac:(lia)) as e_heap.
  pose proof (af_sp0_range RT AF Σ m art0) as sp0_range.
  pose proof (bv_unsigned_in_range 64 sp) as sp_range. unfold bv_modulus in sp_range. cbn [Z.of_N] in sp_range.
  destruct call0 as (stack0 & window0 & rt_room0 & top0 & align0).
  assert (sp_off96 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96)
    by (apply unsigned_lit; unfold STACK_WIN, SEGTOP_A, USTACK_TOP in *; lia).
  rewrite sp_off96 in stack0, rt_room0, top0, align0. unfold RT_STACK in rt_room0.
  assert (e_low : E + 904 <= lo) by lia.
  assert (e_cap : E + 904 <= 2 ^ 47) by (unfold USTACK_TOP in *; lia).
  assert (k_top : Z.of_nat k <= 15) by lia.
  (* the arrays of es_rep as cells, at any index *)
  assert (whole_run : forall (c : cell) (j : nat), (j <= 16)%nat -> repeat c j ++ repeat c (16 - j) = repeat c 16)
    by (intros c j j_le; rewrite <- repeat_app; f_equal; lia).
  assert (c4_words : forall (w : word) (j : nat), cells_bytes (repeat (C4 w) j) = u32s (repeat w j)).
  { intros w j. induction j as [| j more]; [reflexivity |]. cbn [repeat cells_bytes cbytes u32s]. rewrite more. reflexivity. }
  assert (c4_as_zb4 : forall j, cells_bytes (repeat (C4 z64) j) = cells_bytes (repeat zb4 j)).
  { intros j. induction j as [| j more]; [reflexivity |]. cbn [repeat cells_bytes]. rewrite more; f_equal; vm_compute; reflexivity. }
  assert (wf_run : forall (c : cell) (j : nat), cell_wf c -> cells_wf (repeat c j)).
  { intros c j c_wf. induction j as [| j more]; [exact I | exact (conj c_wf more)]. }
  assert (to_arrs : forall (mm : mem) (j : nat), (j <= 16)%nat -> es_rep mm E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls j) EZ16 -> ecl_arrs mm E j).
  { intros mm j j_le (fl_u & _ & mk_u & _ & bf_u & _ & dt_u & ds_u & df_u & fi_u & _ & ln_u & _ & fn_u & _ & tb_u & _).
    unfold EZ16, ecl_ls in *. unfold ecl_arrs. rewrite !whole_run by exact j_le.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ tb_u))))))))).
    - apply (ec_u32_rw mm _ _ _ fl_u); [vm_compute; repeat constructor | vm_compute; reflexivity | reflexivity].
    - apply (ec_u32_rw mm _ _ _ mk_u); [vm_compute; repeat constructor | vm_compute; reflexivity | reflexivity].
    - apply (ec_u64_rw mm _ _ _ bf_u); [vm_compute; repeat constructor | vm_compute; reflexivity | reflexivity].
    - apply (ec_u8_rw mm _ _ _ dt_u); [vm_compute; repeat constructor | vm_compute; reflexivity | reflexivity].
    - apply (ec_u8_rw mm _ _ _ ds_u); [vm_compute; repeat constructor | vm_compute; reflexivity | reflexivity].
    - apply (ec_u8_rw mm _ _ _ df_u).
      + apply cells_wf_app. split; apply wf_run; cbn; first [exact I | reflexivity].
      + rewrite cells_bytes_app, c4_as_zb4, <- cells_bytes_app, whole_run by exact j_le. vm_compute. reflexivity.
      + rewrite cells_size_app, !cells_size_repeat, repeat_length. cbn [csize zb4]. lia.
    - apply (ec_u64_rw mm _ _ _ fi_u); [vm_compute; repeat constructor | vm_compute; reflexivity | reflexivity].
    - apply (ec_u32_rw mm _ _ _ ln_u).
      + apply cells_wf_app. split; apply wf_run; exact I.
      + rewrite cells_bytes_app, !c4_words, u32s_app. reflexivity.
      + rewrite cells_size_app, !cells_size_repeat, length_app, !repeat_length. cbn [csize]. lia.
    - apply (ec_u64_rw mm _ _ _ fn_u); [vm_compute; repeat constructor | vm_compute; reflexivity | reflexivity]. }
  assert (to_rep : forall (mm : mem) (j : nat), (j <= 16)%nat -> ecl_arrs mm E j -> es_rep mm E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls j) EZ16).
  { intros mm j j_le (fl_c & mk_c & bf_c & dt_c & ds_c & df_c & fi_c & ln_c & fn_c & tb_c).
    rewrite !whole_run in fl_c, mk_c, bf_c, dt_c, ds_c, fi_c, fn_c by exact j_le.
    unfold es_rep, EZ16, ecl_ls.
    split; [apply (ec_rw_u32 mm _ _ _ fl_c); [vm_compute; reflexivity | reflexivity] |]. split; [reflexivity |].
    split; [apply (ec_rw_u32 mm _ _ _ mk_c); [vm_compute; reflexivity | reflexivity] |]. split; [reflexivity |].
    split; [apply (ec_rw_u64 mm _ _ _ bf_c); [vm_compute; reflexivity | reflexivity] |]. split; [reflexivity |].
    split; [apply (ec_rw_u8 mm _ _ _ dt_c); [vm_compute; reflexivity | reflexivity] |].
    split; [apply (ec_rw_u8 mm _ _ _ ds_c); [vm_compute; reflexivity | reflexivity] |].
    split.
    { apply (ec_rw_u8 mm _ _ _ df_c).
      - rewrite cells_bytes_app, c4_as_zb4, <- cells_bytes_app, whole_run by exact j_le. vm_compute. reflexivity.
      - rewrite cells_size_app, !cells_size_repeat, repeat_length. cbn [csize zb4]. lia. }
    split; [apply (ec_rw_u64 mm _ _ _ fi_c); [vm_compute; reflexivity | reflexivity] |]. split; [reflexivity |].
    split.
    { apply (ec_rw_u32 mm _ _ _ ln_c).
      - rewrite cells_bytes_app, !c4_words, u32s_app. reflexivity.
      - rewrite cells_size_app, !cells_size_repeat, length_app, !repeat_length. cbn [csize]. lia. }
    split; [rewrite length_app, !repeat_length; lia |].
    split; [apply (ec_rw_u64 mm _ _ _ fn_c); [vm_compute; reflexivity | reflexivity] |]. split; [reflexivity |].
    split; [exact tb_c | lia]. }
  (* moving facts across the stores of a walk and across a call of CRYPTO_free *)
  assert (moved : forall (mm : mem) A B cs, rw_cells asegs mm A cs -> A = B -> rw_cells asegs mm B cs) by (intros mm A B cs held <-; exact held).
  assert (art_keep : forall (ma mb : mem) (W : list (Z * Z)), ART RT Σ ma -> munch W ma mb -> wmono asegs ma mb ->
            (forall x, ~ outside W x -> E <= x < E + 904) -> ART RT Σ mb).
  { intros ma mb W art_a mu_ab wm_ab w_in.
    apply (af_frame RT AF Σ ma mb USTACK_TOP art_a); [unfold STACK_WIN, SEGTOP_A, USTACK_TOP in *; lia | | exact wm_ab].
    intros x not_cl. apply mu_ab. destruct (outside_dec W (bv_unsigned x)) as [x_out | x_in]; [exact x_out |].
    exfalso. apply not_cl. right; right; left. exists E, 904. split; [exact e_live | exact (w_in _ x_in)]. }
  assert (walk_above : forall (ma mb : mem) (W : list (Z * Z)), munch W ma mb -> (forall x, ~ outside W x -> E <= x < E + 904) ->
            agree_on (fun x => lo <= x < USTACK_TOP) ma mb).
  { intros ma mb W mu_ab w_in x x_rng. apply mu_ab. destruct (outside_dec W (bv_unsigned x)) as [x_out | x_in]; [exact x_out |].
    exfalso. pose proof (w_in _ x_in). cbv beta in x_rng. lia. }
  assert (call_above : forall (ma mb : mem), rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp - 96) ma mb ->
            agree_on (fun x => bv_unsigned sp - 96 <= x < USTACK_TOP) ma mb)
    by (intros ma mb pres_ab x x_rng; apply pres_ab; left; exact x_rng).
  assert (call_state : forall (ma mb : mem), rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp - 96) ma mb ->
            agree_on (fun x => E <= x < E + 904) ma mb).
  { intros ma mb pres_ab x x_rng. apply pres_ab. right; right; left. exists E, 904. split; [exact e_live | exact x_rng]. }
  assert (narrow : forall (P Q : Z -> Prop) (ma mb : mem), agree_on P ma mb -> (forall x, Q x -> P x) -> agree_on Q ma mb)
    by (intros P Q ma mb ag_ab sub x x_q; exact (ag_ab x (sub _ x_q))).
  assert (chain_ag : forall (P : Z -> Prop) (ma mb mc : mem), agree_on P ma mb -> agree_on P mb mc -> agree_on P ma mc)
    by (intros P ma mb mc ab bc x x_p; rewrite (bc x x_p); exact (ab x x_p)).
  assert (link_of : forall mm, rw_cells asegs mm (bv_unsigned sp + -96) (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c) ->
            rw_cells asegs mm (bv_unsigned sp - 16) [C8 s0c; C8 rac]).
  { intros mm saved. unfold clr_frame in saved.
    pose proof (rw_cells_skip mm _ [C8 s10c; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c] [C8 s0c; C8 rac] saved) as upper.
    cbn [cells_size csize Nat.add] in upper. apply (moved mm _ _ _ upper). lia. }
  assert (frame_size : Z.of_nat (cells_size (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)) = 96) by reflexivity.
  assert (site_in : forall r, In (r, e_eclear) ECL_SITES -> In (r, e_eclear) (cg_site (rt_cg RT Σ))) by (intros r r_in; exact (proj1 graph0 _ r_in)).
  assert (call_in : forall r g, In (r, g) ECL_CALLS -> In (r, g) (cg_call (rt_cg RT Σ))) by (intros r g r_in; exact (proj2 graph0 _ r_in)).
  (* the cells the round touches *)
  pose proof (to_arrs m k ltac:(lia) rep0) as arrs_m.
  destruct (ecl_arrs_get m E k k_lt arrs_m) as (fl_0 & mk_0 & bf_0 & dt_0 & ds_0 & df_0 & fi_0 & ln_0 & fn_0).
  apply (moved m _ (E + Z.of_nat k * 4)) in fl_0; [| lia]. apply (moved m _ (E + Z.of_nat k * 4 + 64)) in mk_0; [| lia].
  apply (moved m _ (E + Z.of_nat k * 8 + 128)) in bf_0; [| lia]. apply (moved m _ (E + Z.of_nat k * 8 + 256)) in dt_0; [| lia].
  apply (moved m _ (E + Z.of_nat k * 8 + 384)) in ds_0; [| lia]. apply (moved m _ (E + Z.of_nat k * 4 + 512)) in df_0; [| lia].
  apply (moved m _ (E + Z.of_nat k * 8 + 576)) in fi_0; [| lia]. apply (moved m _ (E + Z.of_nat k * 4 + 704)) in ln_0; [| lia].
  apply (moved m _ (E + Z.of_nat k * 8 + 768)) in fn_0; [| lia].
  destruct (af_acc_live RT AF Σ m E 904 art0 e_live) as (_ & acc_0).
  (* first stretch: the loop head to the call of CRYPTO_free for err_file *)
  assert (walk1 : evt asegs (fun ms => exists (a3' a4' : word) (mm : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_ecr_free1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 E)
                    z64 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 112) a3' a4' a5 a6 a7 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 (E + Z.of_nat k * 8 + 576)) (Z_to_bv 64 SHB)
                    (Z_to_bv 64 (Z.of_nat k * 8)) (Z_to_bv 64 (Z.of_nat k * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) (Z_to_bv 64 (E + Z.of_nat k * 8))
                    (Z_to_bv 64 ((E + Z.of_nat k * 8 + 576) ≫ 3 + SHB)) s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_CRYPTO_free) fc None mm (seg_rom asegs)
       /\ munch (ecl_W E (Z.of_nat k)) m mm /\ wmono asegs m mm /\ mem_inv asegs mm
       /\ rw_cells asegs mm (E + Z.of_nat k * 4) [C4 z64] /\ rw_cells asegs mm (E + Z.of_nat k * 4 + 64) [C4 z64]
       /\ rw_cells asegs mm (E + Z.of_nat k * 8 + 128) [C8 z64] /\ rw_cells asegs mm (E + Z.of_nat k * 8 + 256) [C8 z64]
       /\ rw_cells asegs mm (E + Z.of_nat k * 8 + 384) [C8 z64] /\ rw_cells asegs mm (E + Z.of_nat k * 4 + 512) [C4 z64]
       /\ rw_cells asegs mm (E + Z.of_nat k * 8 + 576) [C8 z64] /\ rw_cells asegs mm (E + Z.of_nat k * 4 + 704) [C4 ECL_LNW]
       /\ rw_cells asegs mm (E + Z.of_nat k * 8 + 768) [C8 z64])
    (clr_head_st sp gp (Z_to_bv 64 TP_A) s11 F fc E (Z.of_nat k) m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6)).
  { clear - k_lt e_aligned e_heap e_cap acc_0 inv0 fl_0 mk_0 bf_0 dt_0 ds_0 df_0 fi_0 ln_0 fn_0.
    assert (head_pc : CLR_LOOP = ECL_LOOP) by reflexivity.
    unfold clr_head_st. rewrite head_pc. clear head_pc.
    unfold ECL_LOOP, SHB, zb4, SITE_ecr_free1, e_CRYPTO_free, ECL_LNW in *.
    pose proof (munch_refl (ecl_W E (Z.of_nat k)) m) as mu_walk. pose proof (wmono_refl asegs m) as wm_walk. unfold ecl_W in mu_walk.
    lazymatch type of mu_walk with munch ?W _ _ => assert (sh_off : sh_fp W) by sh_fp_lia end.
    zstep. remember (E + Z.of_nat k * 4) as A4 eqn:A4_def.
    do 5 zstep. th_if_lit. do 4 zstep. th_if_lit.
    do 5 zstep. th_if_lit. zstep. fix_lit_store.
    do 5 zstep. th_if_lit. zstep. zstep. fix_lit_store.
    do 3 zstep. th_if_lit. zstep. fix_lit_store.
    do 5 zstep. th_if_lit. zstep. fix_lit_store.
    do 4 zstep. th_if_lit. zstep. fix_lit_store.
    do 5 zstep. th_if_lit. zstep. fix_lit_store.
    do 5 zstep. th_if_lit. zstep. fix_lit_store.
    do 5 zstep. th_if_lit. do 4 zstep.
    subst A4. apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity |].
    exact (conj mu_walk (conj wm_walk (conj inv0 (conj fl_0 (conj mk_0 (conj bf_0 (conj dt_0 (conj ds_0 (conj df_0 (conj fi_0 (conj ln_0 fn_0))))))))))). }
  cl_lift walk1 at_head c1 at_1.
  destruct (ASTA_unpack RT Σ _ _ c1 at_1)
    as (ms1 & (a3_1 & a4_1 & m1 & -> & mu_1 & wm_1 & inv_1 & fl_1 & mk_1 & bf_1 & dt_1 & ds_1 & df_1 & fi_1 & ln_1 & fn_1) & here_1).
  clear at_1.
  assert (w1_in : forall x, ~ outside (ecl_W E (Z.of_nat k)) x -> E <= x < E + 904)
    by (intros x x_in; unfold ecl_W in x_in; cbn [outside] in x_in; lia).
  pose proof (art_keep m m1 _ art0 mu_1 wm_1 w1_in) as art_1.
  pose proof (walk_above m m1 _ mu_1 w1_in) as above_1.
  assert (stk_1 : stk asegs m1 lo (bv_unsigned sp - 96)).
  { apply (stk_agree asegs m m1 lo _ stack0); [| exact wm_1]. apply (narrow _ _ m m1 above_1). intros x x_rng. lia. }
  assert (top_01 : agree_on (fun x => bv_unsigned sp - 96 <= x < USTACK_TOP) m m1)
    by (apply (narrow _ _ m m1 above_1); intros x x_rng; lia).
  assert (frame_1 : rw_cells asegs m1 (bv_unsigned sp + -96) (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)).
  { apply (rw_cells_agree asegs m m1 _ _ frame0); [| exact wm_1]. apply (narrow _ _ m m1 top_01). intros x x_rng. rewrite frame_size in x_rng. lia. }
  assert (env_1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary env0 mu_1); unfold ecl_W; cl_fp_lia).
  assert (f1_lit : bv_unsigned (Z_to_bv 64 SITE_ecr_free1) = SITE_ecr_free1) by (apply unsigned_lit; unfold SITE_ecr_free1; lia).
  destruct (cl_chain_call (rt_cg RT Σ) e_eclear e_CRYPTO_free SITE_ecr_free1 m m1 rac s0c sp (Z_to_bv 64 (bv_unsigned sp + -96)) outer ctx0
              (site_in SITE_ecr_free1 ltac:(unfold ECL_SITES; cbn [In]; tauto)) (call_in SITE_ecr_free1 e_CRYPTO_free ltac:(unfold ECL_CALLS; cbn [In]; tauto)) chain0
              (narrow _ (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1 top_01 ltac:(intros x x_rng; cbv beta in *; lia)) (link_of m1 frame_1)
              ltac:(rewrite sp_off96; lia) sp_top) as (ctx_c1 & chain_c1).
  rewrite <- f1_lit in ctx_c1.
  assert (callok_1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok, RT_STACK. rewrite sp_off96. exact (conj stk_1 (conj window0 (conj rt_room0 (conj top0 align0)))). }
  (* CRYPTO_free (err_file[k]), a null pointer *)
  apply (cps_realizes asegs _ _ T c1
           (C_FRN Σ PMc (Z_to_bv 64 SITE_ecr_free1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 E)
              z64 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 112) a3_1 a4_1 a5 a6 a7 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 (E + Z.of_nat k * 8 + 576)) (Z_to_bv 64 SHB)
              (Z_to_bv 64 (Z.of_nat k * 8)) (Z_to_bv 64 (Z.of_nat k * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) (Z_to_bv 64 (E + Z.of_nat k * 8))
              (Z_to_bv 64 ((E + Z.of_nat k * 8 + 576) ≫ 3 + SHB)) s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned rac :: outer) lb canary
              fdfs_ok mat_ok eq_refl eq_refl art_1 inv_1 callok_1 ctx_c1 chain_c1
              ltac:(rewrite f1_lit; apply call_in; unfold ECL_CALLS; cbn [In]; tauto) env_1) here_1).
  intros c2 (v_1 & at_2).
  destruct (ASTA_unpack RT Σ _ _ c2 at_2) as (ms2 & (m2 & back_2 & after_2 & pres_2 & env_2) & here_2). clear at_2.
  destruct back_2 as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & F_2 & fc_2 & ->).
  rewrite (ret_pc_even SITE_ecr_free1) in here_2 by (unfold SITE_ecr_free1; try reflexivity; lia).
  destruct after_2 as (art_2 & inv_2 & wm_2 & stk_2). rewrite sp_off96 in stk_2, pres_2.
  destruct (af_acc_live RT AF Σ m2 E 904 art_2 e_live) as (_ & acc_2).
  assert (fi_2 : rw_cells asegs m2 (E + Z.of_nat k * 8 + 576) [C8 z64]).
  { apply (rw_cells_agree asegs m1 m2 _ _ fi_1); [| exact wm_2]. apply (narrow _ _ m1 m2 (call_state m1 m2 pres_2)).
    intros x x_rng. cbn [cells_size csize Nat.add] in x_rng. lia. }
  assert (fn_2 : rw_cells asegs m2 (E + Z.of_nat k * 8 + 768) [C8 z64]).
  { apply (rw_cells_agree asegs m1 m2 _ _ fn_1); [| exact wm_2]. apply (narrow _ _ m1 m2 (call_state m1 m2 pres_2)).
    intros x x_rng. cbn [cells_size csize Nat.add] in x_rng. lia. }
  (* second stretch: clear err_file[k], then the call of CRYPTO_free for err_func *)
  assert (walk2 : evt asegs (fun ms => exists mm : mem,
       ms = MS (mkR (Z_to_bv 64 SITE_ecr_free2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0_2 t1_2 t2_2 sp (Z_to_bv 64 E)
                    z64 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 114) a3_2 a4_2 a5_2 a6_2 a7_2 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 (E + Z.of_nat k * 8 + 768)) (Z_to_bv 64 SHB)
                    (Z_to_bv 64 (Z.of_nat k * 8)) (Z_to_bv 64 (Z.of_nat k * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) (Z_to_bv 64 (E + Z.of_nat k * 8))
                    (Z_to_bv 64 ((E + Z.of_nat k * 8 + 768) ≫ 3 + SHB)) s11 t3_2 t4_2 t5_2 t6_2)
               F_2 (Z_to_bv 64 e_CRYPTO_free) fc_2 None mm (seg_rom asegs)
       /\ munch [(E + Z.of_nat k * 8 + 576, E + Z.of_nat k * 8 + 584)] m2 mm /\ wmono asegs m2 mm /\ mem_inv asegs mm
       /\ rw_cells asegs mm (E + Z.of_nat k * 8 + 576) [C8 z64] /\ rw_cells asegs mm (E + Z.of_nat k * 8 + 768) [C8 z64])
    (MS (mkR (Z_to_bv 64 SITE_ecr_free1) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0_2 t1_2 t2_2 sp (Z_to_bv 64 E)
             v_1 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 (E + Z.of_nat k * 8 + 576)) (Z_to_bv 64 SHB)
             (Z_to_bv 64 (Z.of_nat k * 8)) (Z_to_bv 64 (Z.of_nat k * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) (Z_to_bv 64 (E + Z.of_nat k * 8))
             (Z_to_bv 64 ((E + Z.of_nat k * 8 + 576) ≫ 3 + SHB)) s11 t3_2 t4_2 t5_2 t6_2)
        F_2 (Z_to_bv 64 SITE_ecr_free1) fc_2 None m2 (seg_rom asegs))).
  { clear - k_lt e_aligned e_heap e_cap acc_2 inv_2 fi_2 fn_2.
    unfold SHB, SITE_ecr_free1, SITE_ecr_free2, e_CRYPTO_free in *.
    pose proof (munch_refl [(E + Z.of_nat k * 8 + 576, E + Z.of_nat k * 8 + 584)] m2) as mu_walk. pose proof (wmono_refl asegs m2) as wm_walk.
    lazymatch type of mu_walk with munch ?W _ _ => assert (sh_off : sh_fp W) by sh_fp_lia end.
    zstep. zstep. th_if_lit. zstep. fix_lit_store.
    do 5 zstep. th_if_lit. do 4 zstep.
    apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity |].
    exact (conj mu_walk (conj wm_walk (conj inv_2 (conj fi_2 fn_2)))). }
  cl_lift walk2 here_2 c3 at_3.
  destruct (ASTA_unpack RT Σ _ _ c3 at_3) as (ms3 & (m3 & -> & mu_3 & wm_3 & inv_3 & fi_3 & fn_3) & here_3). clear at_3.
  assert (w2_in : forall x, ~ outside [(E + Z.of_nat k * 8 + 576, E + Z.of_nat k * 8 + 584)] x -> E <= x < E + 904)
    by (intros x x_in; cbn [outside] in x_in; lia).
  pose proof (art_keep m2 m3 _ art_2 mu_3 wm_3 w2_in) as art_3.
  pose proof (walk_above m2 m3 _ mu_3 w2_in) as above_3.
  assert (stk_3 : stk asegs m3 lo (bv_unsigned sp - 96)).
  { apply (stk_agree asegs m2 m3 lo _ stk_2); [| exact wm_3]. apply (narrow _ _ m2 m3 above_3). intros x x_rng. lia. }
  assert (top_03 : agree_on (fun x => bv_unsigned sp - 96 <= x < USTACK_TOP) m m3).
  { apply (chain_ag _ m m2 m3); [apply (chain_ag _ m m1 m2 top_01 (call_above m1 m2 pres_2)) |].
    apply (narrow _ _ m2 m3 above_3). intros x x_rng. lia. }
  pose proof (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ wm_1 wm_2) wm_3) as wm_03.
  assert (frame_3 : rw_cells asegs m3 (bv_unsigned sp + -96) (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)).
  { apply (rw_cells_agree asegs m m3 _ _ frame0); [| exact wm_03]. apply (narrow _ _ m m3 top_03). intros x x_rng. rewrite frame_size in x_rng. lia. }
  assert (env_3 : cl_env m3 lb canary) by (apply (cl_env_seg _ m2 m3 lb canary env_2 mu_3); cl_fp_lia).
  assert (f2_lit : bv_unsigned (Z_to_bv 64 SITE_ecr_free2) = SITE_ecr_free2) by (apply unsigned_lit; unfold SITE_ecr_free2; lia).
  destruct (cl_chain_call (rt_cg RT Σ) e_eclear e_CRYPTO_free SITE_ecr_free2 m m3 rac s0c sp (Z_to_bv 64 (bv_unsigned sp + -96)) outer ctx0
              (site_in SITE_ecr_free2 ltac:(unfold ECL_SITES; cbn [In]; tauto)) (call_in SITE_ecr_free2 e_CRYPTO_free ltac:(unfold ECL_CALLS; cbn [In]; tauto)) chain0
              (narrow _ (fun x => bv_unsigned sp <= x < USTACK_TOP) m m3 top_03 ltac:(intros x x_rng; cbv beta in *; lia)) (link_of m3 frame_3)
              ltac:(rewrite sp_off96; lia) sp_top) as (ctx_c2 & chain_c2).
  rewrite <- f2_lit in ctx_c2.
  assert (callok_3 : call_ok RT Σ m3 (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { unfold call_ok, RT_STACK. rewrite sp_off96. exact (conj stk_3 (conj window0 (conj rt_room0 (conj top0 align0)))). }
  (* CRYPTO_free (err_func[k]), a null pointer *)
  apply (cps_realizes asegs _ _ T c3
           (C_FRN Σ PMc (Z_to_bv 64 SITE_ecr_free2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0_2 t1_2 t2_2 sp (Z_to_bv 64 E)
              z64 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 114) a3_2 a4_2 a5_2 a6_2 a7_2 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 (E + Z.of_nat k * 8 + 768)) (Z_to_bv 64 SHB)
              (Z_to_bv 64 (Z.of_nat k * 8)) (Z_to_bv 64 (Z.of_nat k * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) (Z_to_bv 64 (E + Z.of_nat k * 8))
              (Z_to_bv 64 ((E + Z.of_nat k * 8 + 768) ≫ 3 + SHB)) s11 t3_2 t4_2 t5_2 t6_2 F_2 fc_2 m3 lo (bv_unsigned rac :: outer) lb canary
              fdfs_ok mat_ok eq_refl eq_refl art_3 inv_3 callok_3 ctx_c2 chain_c2
              ltac:(rewrite f2_lit; apply call_in; unfold ECL_CALLS; cbn [In]; tauto) env_3) here_3).
  intros c4 (v_2 & at_4).
  destruct (ASTA_unpack RT Σ _ _ c4 at_4) as (ms4 & (m4 & back_4 & after_4 & pres_4 & env_4) & here_4). clear at_4.
  destruct back_4 as (t0_4 & t1_4 & t2_4 & a1_4 & a2_4 & a3_4 & a4_4 & a5_4 & a6_4 & a7_4 & t3_4 & t4_4 & t5_4 & t6_4 & F_4 & fc_4 & ->).
  rewrite (ret_pc_even SITE_ecr_free2) in here_4 by (unfold SITE_ecr_free2; try reflexivity; lia).
  destruct after_4 as (art_4 & inv_4 & wm_4 & stk_4). rewrite sp_off96 in stk_4, pres_4.
  destruct (af_acc_live RT AF Σ m4 E 904 art_4 e_live) as (_ & acc_4).
  assert (fn_4 : rw_cells asegs m4 (E + Z.of_nat k * 8 + 768) [C8 z64]).
  { apply (rw_cells_agree asegs m3 m4 _ _ fn_3); [| exact wm_4]. apply (narrow _ _ m3 m4 (call_state m3 m4 pres_4)).
    intros x x_rng. cbn [cells_size csize Nat.add] in x_rng. lia. }
  (* last stretch: clear err_func[k], step the counters, branch back or out *)
  assert (walk3 : evt asegs (fun ms => exists (a0' : word) (mm : mem),
       ms = MS (mkR (Z_to_bv 64 SITE_ecr_free2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0_4 t1_4 t2_4 sp (Z_to_bv 64 E)
                    a0' a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 (E + Z.of_nat k * 8 + 768)) (Z_to_bv 64 SHB)
                    (Z_to_bv 64 ((Z.of_nat k + 1) * 8)) (Z_to_bv 64 ((Z.of_nat k + 1) * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) (Z_to_bv 64 (E + Z.of_nat k * 8))
                    (Z_to_bv 64 ((E + Z.of_nat k * 8 + 768) ≫ 3 + SHB)) s11 t3_4 t4_4 t5_4 t6_4)
               F_4 (Z_to_bv 64 (clr_next (Z.of_nat k))) fc_4 None mm (seg_rom asegs)
       /\ munch [(E + Z.of_nat k * 8 + 768, E + Z.of_nat k * 8 + 776)] m4 mm /\ wmono asegs m4 mm /\ mem_inv asegs mm
       /\ rw_cells asegs mm (E + Z.of_nat k * 8 + 768) [C8 z64])
    (MS (mkR (Z_to_bv 64 SITE_ecr_free2) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0_4 t1_4 t2_4 sp (Z_to_bv 64 E)
             v_2 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 (E + Z.of_nat k * 8 + 768)) (Z_to_bv 64 SHB)
             (Z_to_bv 64 (Z.of_nat k * 8)) (Z_to_bv 64 (Z.of_nat k * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) (Z_to_bv 64 (E + Z.of_nat k * 8))
             (Z_to_bv 64 ((E + Z.of_nat k * 8 + 768) ≫ 3 + SHB)) s11 t3_4 t4_4 t5_4 t6_4)
        F_4 (Z_to_bv 64 SITE_ecr_free2) fc_4 None m4 (seg_rom asegs))).
  { clear - k_lt k_top e_aligned e_heap e_cap acc_4 inv_4 fn_4.
    assert (back_pc : CLR_LOOP = ECL_LOOP) by reflexivity. assert (out_pc : CLR_DONE = ECL_DONE) by reflexivity.
    unfold clr_next. rewrite back_pc, out_pc. clear back_pc out_pc.
    unfold ECL_LOOP, ECL_DONE, SHB, SITE_ecr_free2 in *.
    pose proof (munch_refl [(E + Z.of_nat k * 8 + 768, E + Z.of_nat k * 8 + 776)] m4) as mu_walk. pose proof (wmono_refl asegs m4) as wm_walk.
    lazymatch type of mu_walk with munch ?W _ _ => assert (sh_off : sh_fp W) by sh_fp_lia end.
    zstep. zstep. th_if_lit. zstep. fix_lit_store.
    do 3 zstep. if_cases more_rounds; zify_cond more_rounds.
    - apply evt_done. do 2 eexists. split; [| exact (conj mu_walk (conj wm_walk (conj inv_4 fn_4)))].
      replace (Z.of_nat k =? 15) with false by (symmetry; apply Z.eqb_neq; lia).
      replace ((Z.of_nat k + 1) * 8) with (Z.of_nat k * 8 + 8) by lia. replace ((Z.of_nat k + 1) * 4) with (Z.of_nat k * 4 + 4) by lia.
      cbv delta [mkR]. reflexivity.
    - apply evt_done. do 2 eexists. split; [| exact (conj mu_walk (conj wm_walk (conj inv_4 fn_4)))].
      replace (Z.of_nat k =? 15) with true by (symmetry; apply Z.eqb_eq; lia).
      replace ((Z.of_nat k + 1) * 8) with (Z.of_nat k * 8 + 8) by lia. replace ((Z.of_nat k + 1) * 4) with (Z.of_nat k * 4 + 4) by lia.
      cbv delta [mkR]. reflexivity. }
  cl_lift walk3 here_4 c5 at_5.
  destruct (ASTA_unpack RT Σ _ _ c5 at_5) as (ms5 & (a0_5 & m5 & -> & mu_5 & wm_5 & inv_5 & fn_5) & here_5). clear at_5.
  assert (w3_in : forall x, ~ outside [(E + Z.of_nat k * 8 + 768, E + Z.of_nat k * 8 + 776)] x -> E <= x < E + 904)
    by (intros x x_in; cbn [outside] in x_in; lia).
  pose proof (art_keep m4 m5 _ art_4 mu_5 wm_5 w3_in) as art_5.
  pose proof (walk_above m4 m5 _ mu_5 w3_in) as above_5.
  assert (stk_5 : stk asegs m5 lo (bv_unsigned sp - 96)).
  { apply (stk_agree asegs m4 m5 lo _ stk_4); [| exact wm_5]. apply (narrow _ _ m4 m5 above_5). intros x x_rng. lia. }
  assert (top_05 : agree_on (fun x => bv_unsigned sp - 96 <= x < USTACK_TOP) m m5).
  { apply (chain_ag _ m m4 m5); [apply (chain_ag _ m m3 m4 top_03 (call_above m3 m4 pres_4)) |].
    apply (narrow _ _ m4 m5 above_5). intros x x_rng. lia. }
  pose proof (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ wm_03 wm_4) wm_5) as wm_05.
  (* the state block after the round *)
  assert (late_keep : forall a cs, rw_cells asegs m1 a cs -> E <= a -> a + Z.of_nat (cells_size cs) <= E + 904 ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) ->
               ~ (E + Z.of_nat k * 8 + 576 <= x < E + Z.of_nat k * 8 + 584) /\ ~ (E + Z.of_nat k * 8 + 768 <= x < E + Z.of_nat k * 8 + 776)) ->
            rw_cells asegs m5 a cs).
  { intros a cs cells_1 a_lo a_hi apart.
    apply (rw_cells_agree asegs m1 m5 a cs cells_1); [| exact (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ wm_2 wm_3) wm_4) wm_5)].
    intros x x_rng. cbv beta in x_rng. destruct (apart _ x_rng) as (off_file & off_func).
    rewrite (mu_5 x ltac:(cbn [outside]; split; [exact off_func | exact I])).
    rewrite (call_state m3 m4 pres_4 x ltac:(cbv beta; lia)).
    rewrite (mu_3 x ltac:(cbn [outside]; split; [exact off_file | exact I])).
    exact (call_state m1 m2 pres_2 x ltac:(cbv beta; lia)). }
  assert (fi_5 : rw_cells asegs m5 (E + Z.of_nat k * 8 + 576) [C8 z64]).
  { apply (rw_cells_agree asegs m3 m5 _ _ fi_3); [| exact (wmono_trans asegs _ _ _ wm_4 wm_5)].
    intros x x_rng. cbv beta in x_rng. cbn [cells_size csize Nat.add] in x_rng.
    rewrite (mu_5 x ltac:(cbn [outside]; split; [lia | exact I])). exact (call_state m3 m4 pres_4 x ltac:(cbv beta; lia)). }
  assert (same_out : forall x : word, E <= bv_unsigned x < E + 904 -> outside (ecl_W E (Z.of_nat k)) (bv_unsigned x) -> m5 x = m x).
  { intros x x_rng x_out. unfold ecl_W in x_out. cbn [outside] in x_out.
    rewrite (mu_5 x ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (call_state m3 m4 pres_4 x x_rng).
    rewrite (mu_3 x ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (call_state m1 m2 pres_2 x x_rng).
    apply mu_1. unfold ecl_W. cbn [outside]. exact x_out. }
  assert (carry : forall a b cs, rw_cells asegs m1 a cs -> a = b -> E <= a -> a + Z.of_nat (cells_size cs) <= E + 904 ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> E + Z.of_nat k * 8 + 584 <= x \/ x < E + Z.of_nat k * 8 + 576) ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> E + Z.of_nat k * 8 + 776 <= x \/ x < E + Z.of_nat k * 8 + 768) ->
            rw_cells asegs m5 b cs).
  { intros a b cs cells_1 a_b a_lo a_hi off_file off_func. apply (moved m5 a b cs); [| exact a_b].
    apply (late_keep a cs cells_1 a_lo a_hi). intros x x_rng. split; [pose proof (off_file x x_rng) | pose proof (off_func x x_rng)]; lia. }
  pose proof (carry _ (E + 4 * Z.of_nat k) _ fl_1) as fl_5. pose proof (carry _ (E + 4 * Z.of_nat k + 64) _ mk_1) as mk_5.
  pose proof (carry _ (E + 8 * Z.of_nat k + 128) _ bf_1) as bf_5. pose proof (carry _ (E + 8 * Z.of_nat k + 256) _ dt_1) as dt_5.
  pose proof (carry _ (E + 8 * Z.of_nat k + 384) _ ds_1) as ds_5. pose proof (carry _ (E + 4 * Z.of_nat k + 512) _ df_1) as df_5.
  pose proof (carry _ (E + 4 * Z.of_nat k + 704) _ ln_1) as ln_5.
  cbn [cells_size csize Nat.add] in fl_5, mk_5, bf_5, dt_5, ds_5, df_5, ln_5.
  specialize (fl_5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) ltac:(intros; lia)).
  specialize (mk_5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) ltac:(intros; lia)).
  specialize (bf_5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) ltac:(intros; lia)).
  specialize (dt_5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) ltac:(intros; lia)).
  specialize (ds_5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) ltac:(intros; lia)).
  specialize (df_5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) ltac:(intros; lia)).
  specialize (ln_5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) ltac:(intros; lia)).
  assert (fi_5' : rw_cells asegs m5 (E + 8 * Z.of_nat k + 576) [C8 z64]) by (apply (moved m5 _ _ _ fi_5); lia).
  assert (fn_5' : rw_cells asegs m5 (E + 8 * Z.of_nat k + 768) [C8 z64]) by (apply (moved m5 _ _ _ fn_5); lia).
  pose proof (ecl_arrs_step m m5 E k k_lt arrs_m wm_05 same_out fl_5 mk_5 bf_5 dt_5 ds_5 df_5 fi_5' ln_5 fn_5') as arrs_5.
  (* the round's result *)
  apply finish. exists Σ.
  refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))).
  apply (ASTA_conseq RT Σ PMc _ _ c5 here_5). intros ms <-.
  exists (Z_to_bv 64 SITE_ecr_free2), t0_4, t1_4, t2_4, a0_5, a1_4, a2_4, a3_4, a4_4, a5_4, a6_4, a7_4,
    (Z_to_bv 64 (E + Z.of_nat k * 8 + 768)), (Z_to_bv 64 (E + Z.of_nat k * 8)), (Z_to_bv 64 ((E + Z.of_nat k * 8 + 768) ≫ 3 + SHB)),
    t3_4, t4_4, t5_4, t6_4, F_4, fc_4, m5.
  split; [reflexivity |].
  rewrite sp_off96.
  split; [exact (conj art_5 (conj inv_5 (conj wm_05 stk_5))) |].
  split.
  { intros x x_cl x_out. cbn [outside] in x_out. destruct x_out as (x_off & _).
    rewrite (mu_5 x ltac:(cbn [outside]; split; [lia | exact I])). rewrite (pres_4 x x_cl).
    rewrite (mu_3 x ltac:(cbn [outside]; split; [lia | exact I])). rewrite (pres_2 x x_cl).
    apply mu_1. unfold ecl_W. cbn [outside]. repeat split; lia. }
  split; [apply (cl_env_seg _ m4 m5 lb canary env_4 mu_5); cl_fp_lia |].
  split.
  { apply (rw_cells_agree asegs m m5 _ _ frame0); [| exact wm_05]. apply (narrow _ _ m m5 top_05). intros x x_rng. rewrite frame_size in x_rng. lia. }
  split.
  { apply (uw_chain_agree outer m m5 sp s0c chain0). apply (narrow _ _ m m5 top_05). intros x x_rng. lia. }
  exact (to_rep m5 (S k) ltac:(lia) arrs_5).
Qed.

Lemma ecl_loop_ind : forall (n k : nat), (k + n = 15)%nat -> ecl_loop_stmt k.
Proof using AF AFP C_FRN.
  induction n as [| rounds_left later_rounds]; intros k k_sum;
    intros Σ PMc sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 F fc m lo outer lb canary E
      rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c fdfs_ok mat_ok k_lt e_aligned e_live art0 inv0 call0 sp0_below sp_top
      ctx0 chain0 graph0 env0 frame0 rep0.
  - (* the sixteenth round leaves the loop *)
    assert (k_last : k = 15%nat) by lia. subst k.
    exact (ecl_iter 15 Σ PMc sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 F fc m lo outer lb canary E
             rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c fdfs_ok mat_ok k_lt e_aligned e_live art0 inv0 call0 sp0_below sp_top
             ctx0 chain0 graph0 env0 frame0 rep0).
  - (* one round, then the loop from the next index *)
    intros T c0 at_head finish.
    apply (cps_realizes asegs _ _ T c0
             (ecl_iter k Σ PMc sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 F fc m lo outer lb canary E
                rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c fdfs_ok mat_ok k_lt e_aligned e_live art0 inv0 call0 sp0_below sp_top
                ctx0 chain0 graph0 env0 frame0 rep0) at_head).
    intros c1 (Σ1 & at_next & live_1 & frames_1 & sp0_1 & credit_1 & cg_1).
    destruct (ASTA_unpack RT Σ1 _ _ c1 at_next)
      as (ms1 & (ra_1 & t0_1 & t1_1 & t2_1 & a0_1 & a1_1 & a2_1 & a3_1 & a4_1 & a5_1 & a6_1 & a7_1 & s3_1 & s9_1 & s10_1
                 & t3_1 & t4_1 & t5_1 & t6_1 & F_1 & fc_1 & m1 & -> & after_1 & pres_1 & env_1 & frame_1 & chain_1 & rep_1) & here_1).
    clear at_next.
    assert (back_to_head : clr_next (Z.of_nat k) = CLR_LOOP).
    { unfold clr_next. replace (Z.of_nat k =? 15) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    rewrite back_to_head in here_1.
    replace ((Z.of_nat k + 1) * 8) with (Z.of_nat (S k) * 8) in here_1 by lia.
    replace ((Z.of_nat k + 1) * 4) with (Z.of_nat (S k) * 4) in here_1 by lia.
    destruct after_1 as (art_1 & inv_1 & grows_1 & stack_1).
    assert (callok_1 : call_ok RT Σ1 m1 (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
    { destruct call0 as (_ & window0 & rt_room0 & top0 & align0). unfold call_ok. rewrite sp0_1.
      exact (conj stack_1 (conj window0 (conj rt_room0 (conj top0 align0)))). }
    apply (cps_realizes asegs _ _ T c1
             (later_rounds (S k) ltac:(lia) Σ1 PMc sp gp s11 ra_1 t0_1 t1_1 t2_1 a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 s3_1 s9_1 s10_1
                t3_1 t4_1 t5_1 t6_1 F_1 fc_1 m1 lo outer lb canary E rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c
                fdfs_ok mat_ok ltac:(lia) e_aligned ltac:(rewrite live_1; exact e_live) art_1 inv_1 callok_1
                ltac:(rewrite sp0_1; exact sp0_below) sp_top ltac:(rewrite cg_1; exact ctx0) chain_1 ltac:(rewrite cg_1; exact graph0)
                env_1 frame_1 rep_1) here_1).
    intros c2 (Σ2 & at_end & live_2 & frames_2 & sp0_2 & credit_2 & cg_2).
    apply finish. exists Σ2.
    rewrite live_2, frames_2, sp0_2, credit_2, cg_2, live_1, frames_1, sp0_1, credit_1, cg_1.
    refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))).
    apply (ASTA_conseq RT Σ2 PMc _ _ c2 at_end).
    intros ms (ra_2 & t0_2 & t1_2 & t2_2 & a0_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & s3_2 & s9_2 & s10_2
               & t3_2 & t4_2 & t5_2 & t6_2 & F_2 & fc_2 & m2 & at_done & after_2 & pres_2 & env_2 & frame_2 & chain_2 & rep_2).
    exists ra_2, t0_2, t1_2, t2_2, a0_2, a1_2, a2_2, a3_2, a4_2, a5_2, a6_2, a7_2, s3_2, s9_2, s10_2, t3_2, t4_2, t5_2, t6_2, F_2, fc_2, m2.
    destruct after_2 as (art_2 & inv_2 & grows_2 & stack_2).
    rewrite live_1, frames_1 in pres_2.
    refine (conj at_done (conj _ (conj (pres_fp_trans _ _ _ _ m m1 m2 pres_1 pres_2) (conj env_2 (conj frame_2 (conj chain_2 rep_2)))))).
    exact (conj art_2 (conj inv_2 (conj (wmono_trans asegs m m1 m2 grows_1 grows_2) stack_2))).
Qed.

Theorem eclear_first_cps : eclear_first_stmt RT.
Proof using AF AFP C_FRN C_EGSI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary
    k kd MK SA P pad top jm1 jm2 jp u r0 g0 oldcb
    fdfs_ok mat_ok tp_fixed art0 inv0 call0 stack_room0 ctx0 chain0 graph0 nframes0 nlive0 credit0 env0
    ic_stop0 ic_opts0 ic_once0 ic_ret0 mko0 mkk0 k_bounds tslot0 mk_in mk_align mkh0 mksa0 mkt0
    sa_in sa_align sah0 p_in p_align pslot0 prest0 dkey0 kd_bounds kd_other dslot0 ub0 w4a0 w4c0 w4e0 ocb0.
  subst tp. intros T c0 at_entry finish.
  destruct call0 as (stack0 & window0 & rt_room0 & top0 & align0).
  destruct (af_client_consts RT AF Σ m art0) as (got0 & shadow0 & _ & _ & untouched0).
  pose proof (af_sp0_range RT AF Σ m art0) as sp0_range.
  unfold RT_STACK in stack_room0, rt_room0.
  assert (heap_and_stack : 0x10007fff8000 <= lo /\ bv_unsigned sp <= 2 ^ 47)
    by (pose proof (af_sp0_win RT AF Σ m art0); unfold STACK_WIN, USTACK_TOP in *; lia).
  destruct heap_and_stack as (lo_heap & sp_low47).
  assert (sp_off96 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  (* entry of ERR_clear_error to its call of ossl_err_get_state_int *)
  assert (walk0 : evt asegs (fun ms => exists mm : mem,
       ms = MS (mkR (Z_to_bv 64 SITE_ecl_egsi) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp s1 z64 a1 a2 a3 a4 a5 a6 a7
                    s2 s3 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_get_state) fc None mm (seg_rom asegs)
       /\ munch [(bv_unsigned sp + -96, bv_unsigned sp)] m mm /\ wmono asegs m mm /\ mem_inv asegs mm
       /\ rw_cells asegs mm (bv_unsigned sp + -96) (clr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)
       /\ stk asegs mm lo (bv_unsigned sp + -96))
    (entry_st ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_eclear m)).
  { clear - stack0 lo_heap sp_low47 stack_room0 got0 shadow0 untouched0 inv0.
    unfold entry_st, clr_frame, e_eclear, SITE_ecl_egsi, e_get_state, SHB, g_shadow_memory_dynamic_address, g_GOT_shadow_offset_cell in *.
    pose proof (bv_unsigned_in_range 64 sp) as sp_range. unfold bv_modulus in sp_range. cbn [Z.of_N] in sp_range.
    remember (bv_unsigned sp) as SP eqn:SP_def. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- SP_def.
    pose proof (munch_refl [(SP + -96, SP)] m) as mu_walk. pose proof (wmono_refl asegs m) as wm_walk.
    assert (ut_off : ut_fp [(SP + -96, SP)]) by ut_fp_lia.
    th_frame 96%nat [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat stack0.
    zstep. do 12 zstep. zstep.
    zstep. zstep. zstep. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity |].
    exact (conj mu_walk (conj wm_walk (conj inv0 (conj FR stack0)))). }
  cl_lift walk0 at_entry c1 at_1.
  destruct (ASTA_unpack RT Σ _ _ c1 at_1) as (ms1 & (m1 & -> & mu_1 & wm_1 & inv_1 & frame_1 & stk_1) & here_1). clear at_1.
  (* the call of ossl_err_get_state_int, the first one *)
  pose proof (cl_seg_ART RT AF Σ m m1 (bv_unsigned sp) 96 [] art0 ltac:(unfold STACK_WIN in *; lia) ltac:(unfold USTACK_TOP in *; lia) mu_1
                ltac:(intros x never; exfalso; exact (never I)) wm_1) as art_1.
  pose proof (cl_seg_pres RT AF Σ m m1 (bv_unsigned sp) 96 [] art0 ltac:(unfold STACK_WIN in *; lia) ltac:(lia) mu_1) as pres_1.
  pose proof (af_live_range RT AF Σ m MK 72 art0 mk_in) as (_ & mk_below & _).
  pose proof (af_live_range RT AF Σ m SA 32 art0 sa_in) as (_ & sa_below & _).
  pose proof (af_live_range RT AF Σ m P 128 art0 p_in) as (_ & p_below & _).
  assert (stay_1 : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= bv_unsigned sp - 96 -> rw_cells asegs m1 a cs).
  { intros a cs cells_m a_hi. apply (rw_cells_agree asegs m m1 a cs cells_m); [| exact wm_1].
    intros x x_rng. apply mu_1. cbn [outside]. cbv beta in x_rng. split; [lia | exact I]. }
  destruct ic_opts0 as (od & od_m & od_bit).
  pose proof (stay_1 _ _ ic_stop0) as stopped_1. pose proof (stay_1 _ _ od_m) as od_1.
  pose proof (stay_1 _ _ ic_once0) as base_once_1. pose proof (stay_1 _ _ ic_ret0) as base_ret_1.
  pose proof (stay_1 _ _ mko0) as key_once_1. pose proof (stay_1 _ _ mkk0) as key_1.
  pose proof (stay_1 _ _ tslot0) as slot_1. pose proof (stay_1 _ _ mkh0) as mk_head_1.
  pose proof (stay_1 _ _ mksa0) as mk_sa_1. pose proof (stay_1 _ _ mkt0) as mk_tail_1.
  pose proof (stay_1 _ _ sah0) as sa_hdr_1. pose proof (stay_1 _ _ pslot0) as p_slot_1.
  pose proof (stay_1 _ _ prest0) as p_rest_1. pose proof (stay_1 _ _ dkey0) as dkey_1.
  pose proof (stay_1 _ _ dslot0) as dslot_1. pose proof (stay_1 _ _ ub0) as ub_1.
  pose proof (stay_1 _ _ w4a0) as g4a0_1. pose proof (stay_1 _ _ w4c0) as g4c0_1.
  pose proof (stay_1 _ _ w4e0) as g4e0_1. pose proof (stay_1 _ _ ocb0) as oldcb_1.
  unfold sa_hdr in sa_hdr_1. cbn [cells_size csize Nat.add] in stopped_1, od_1, base_once_1, base_ret_1, key_once_1, key_1, slot_1,
    mk_head_1, mk_sa_1, mk_tail_1, sa_hdr_1, p_slot_1, p_rest_1, dkey_1, dslot_1, ub_1, g4a0_1, g4c0_1, g4e0_1, oldcb_1.
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in *.
  specialize (stopped_1 ltac:(lia)). specialize (od_1 ltac:(lia)). specialize (base_once_1 ltac:(lia)). specialize (base_ret_1 ltac:(lia)).
  specialize (key_once_1 ltac:(lia)). specialize (key_1 ltac:(lia)). specialize (slot_1 ltac:(lia)).
  specialize (mk_head_1 ltac:(lia)). specialize (mk_sa_1 ltac:(lia)). specialize (mk_tail_1 ltac:(lia)). specialize (sa_hdr_1 ltac:(lia)).
  specialize (p_slot_1 ltac:(lia)). specialize (p_rest_1 ltac:(lia)). specialize (dkey_1 ltac:(lia)). specialize (dslot_1 ltac:(lia)).
  specialize (ub_1 ltac:(lia)). specialize (g4a0_1 ltac:(lia)). specialize (g4c0_1 ltac:(lia)). specialize (g4e0_1 ltac:(lia)).
  specialize (oldcb_1 ltac:(lia)).
  assert (callok_1 : call_ok RT Σ m1 (Z_to_bv 64 (bv_unsigned sp + -96)) lo) by (cl_call_ok sp_off96 stk_1 window0 align0 6).
  assert (agree_top_1 : agree_on (fun x => bv_unsigned sp <= x < USTACK_TOP) m m1).
  { intros x x_rng. apply mu_1. cbn [outside]. cbv beta in x_rng. split; [lia | exact I]. }
  assert (link_1 : rw_cells asegs m1 (bv_unsigned sp - 16) [C8 s0; C8 ra]).
  { unfold clr_frame in frame_1.
    pose proof (rw_cells_skip m1 _ [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] frame_1) as upper.
    cbn [cells_size csize Nat.add] in upper. replace (bv_unsigned sp - 16) with (bv_unsigned sp + -96 + Z.of_nat 80) by lia. exact upper. }
  assert (gsi_site : In (SITE_ecl_egsi, e_eclear) (cg_site (rt_cg RT Σ)))
    by (apply (proj1 graph0); unfold ECLR_SITES; cbn [app In]; left; reflexivity).
  assert (gsi_call : In (SITE_ecl_egsi, e_get_state) (cg_call (rt_cg RT Σ)))
    by (apply (proj2 graph0); unfold ECLR_CALLS; cbn [app In]; left; reflexivity).
  destruct (cl_chain_call (rt_cg RT Σ) e_eclear e_get_state SITE_ecl_egsi m m1 ra s0 sp (Z_to_bv 64 (bv_unsigned sp + -96)) outer
              ctx0 gsi_site gsi_call chain0 agree_top_1 link_1 ltac:(rewrite sp_off96; lia) top0) as (ctx_g & chain_g).
  rewrite <- (unsigned_lit SITE_ecl_egsi) in ctx_g by (unfold SITE_ecl_egsi; lia).
  assert (graph_g : cg_has (rt_cg RT Σ) EG_SITES EG_CALLS) by (apply (cg_has_weaken _ _ _ _ _ graph0); vm_compute; reflexivity).
  assert (env_1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary env0 mu_1); cl_fp_lia).
  apply (cps_realizes asegs _ _ T c1
           (C_EGSI Σ PMc (Z_to_bv 64 SITE_ecl_egsi) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp s1 z64 a1 a2 a3 a4 a5 a6 a7
              s2 s3 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned ra :: outer) lb canary
              k kd MK SA P pad top jm1 jm2 jp u r0 g0 oldcb
              fdfs_ok mat_ok eq_refl eq_refl art_1 inv_1 callok_1 ltac:(rewrite sp_off96; unfold RT_STACK; lia) ctx_g chain_g graph_g
              nframes0 nlive0 credit0 env_1 stopped_1 (ex_intro _ od (conj od_1 od_bit)) base_once_1 base_ret_1 key_once_1 key_1 k_bounds
              slot_1 mk_in mk_align mk_head_1 mk_sa_1 mk_tail_1 sa_in sa_align sa_hdr_1 p_in p_align p_slot_1 p_rest_1
              dkey_1 kd_bounds kd_other dslot_1 ub_1 g4a0_1 g4c0_1 g4e0_1 oldcb_1) here_1).
  intros c2 (Σ2 & E & N & H & G & SK & LK & D & u' & top' & at_2 & live_2 & frames_2 & sp0_2 & credit_2 & cg_2 & fresh_2).
  destruct (ASTA_unpack RT Σ2 _ _ c2 at_2)
    as (ms2 & (m2 & back_2 & after_2 & pres_2 & env_2 & top'_val & sa_hdr_2 & p_cells_2 & mk_cells_2 & e_zero_2 & dslot_2 & ub_2
               & g4a0_2 & g4c0_2 & g4e0_2 & oldcb_2 & h_cell_2 & n_cells_2 & g_cells_2 & sk_cells_2 & lk_cells_2 & d_cells_2) & here_2).
  clear at_2.
  destruct back_2 as (t0_2 & t1_2 & t2_2 & a1_2 & a2_2 & a3_2 & a4_2 & a5_2 & a6_2 & a7_2 & t3_2 & t4_2 & t5_2 & t6_2 & F_2 & fc_2 & ->).
  rewrite (ret_pc_even SITE_ecl_egsi) in here_2 by (unfold SITE_ecl_egsi; try reflexivity; lia).
  pose proof (proj1 (Forall_forall _ _) fresh_2 (E, 904) ltac:(cbn [In]; tauto)) as (e_heap & e_al16 & e_top). cbn [fst snd] in e_heap, e_al16, e_top.
  assert (e_aligned : E mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (e_cap : E + 904 <= 2 ^ 47) by (unfold USTACK_TOP in e_top; lia).
  (* back from ossl_err_get_state_int: the state is not NULL, set up the loop *)
  assert (walk1 : evt asegs (fun ms => exists a0' : word,
       ms = clr_head_st sp gp (Z_to_bv 64 TP_A) s11 F_2 fc_2 E (Z.of_nat 0) m2 (Z_to_bv 64 SITE_ecl_egsi) t0_2 t1_2 t2_2
              a0' a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s3 s9 s10 t3_2 t4_2 t5_2 t6_2)
    (MS (mkR (Z_to_bv 64 SITE_ecl_egsi) (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0_2 t1_2 t2_2 sp s1
             (Z_to_bv 64 E) a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s2 s3 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3_2 t4_2 t5_2 t6_2)
        F_2 (Z_to_bv 64 SITE_ecl_egsi) fc_2 None m2 (seg_rom asegs))).
  { clear - e_heap e_cap.
    assert (head_pc : CLR_LOOP = ECL_LOOP) by reflexivity.
    unfold clr_head_st. rewrite head_pc. clear head_pc. unfold ECL_LOOP, SITE_ecl_egsi, SHB in *.
    zstep. if_cases null_state; zify_cond null_state.
    { exfalso. rewrite ?unsigned_lit in null_state by lia. lia. }
    do 7 zstep.
    apply evt_done. eexists. cbv delta [mkR]. reflexivity. }
  cl_lift walk1 here_2 c3 at_3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 at_3) as (ms3 & (a0_3 & ->) & here_3). clear at_3.
  (* the sixteen rounds *)
  destruct after_2 as (art_2 & inv_2 & wm_2 & stk_2). rewrite sp_off96 in stk_2, pres_2.
  assert (e_live : In (E, 904) (rt_live RT Σ2)) by (rewrite live_2; apply in_or_app; left; cbn [In]; tauto).
  assert (above_12 : agree_on (fun x => bv_unsigned sp + -96 <= x < USTACK_TOP) m1 m2).
  { intros x x_rng. apply pres_2; [left; cbv beta in x_rng; lia |].
    unfold EG_W, MTL_W, G_ALLOW_CUST. cbn [outside]. cbv beta in x_rng. repeat split; try exact I; lia. }
  assert (frame_2 : rw_cells asegs m2 (bv_unsigned sp + -96) (clr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)).
  { apply (rw_cells_agree asegs m1 m2 _ _ frame_1); [| exact wm_2]. intros x x_rng. apply above_12.
    cbv beta in *. unfold clr_frame in x_rng. cbn [cells_size csize Nat.add] in x_rng. lia. }
  assert (chain_2 : uw_chain m2 sp s0 outer).
  { apply (uw_chain_agree outer m m2 sp s0 chain0). intros x x_rng. cbv beta in x_rng.
    rewrite (above_12 x ltac:(cbv beta; lia)). exact (agree_top_1 x x_rng). }
  assert (callok_2 : call_ok RT Σ2 m2 (Z_to_bv 64 (bv_unsigned sp + -96)) lo).
  { destruct callok_1 as (_ & win_1 & room_1 & top_1 & align_1). unfold call_ok. rewrite sp0_2, sp_off96.
    rewrite sp_off96 in room_1, top_1, align_1. exact (conj stk_2 (conj win_1 (conj room_1 (conj top_1 align_1)))). }
  assert (rep_2 : es_rep m2 E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls 0) EZ16).
  { apply es_rep_of_arrs0. destruct e_zero_2 as ((_ & e_bytes) & e_room). cbn [cells_bytes cbytes cells_size csize] in e_bytes, e_room.
    rewrite app_nil_r in e_bytes. exact (ecl_arrs_of_zeros m2 E e_bytes e_room). }
  apply (cps_realizes asegs _ _ T c3
           (ecl_loop_ind 15 0 eq_refl Σ2 PMc sp gp s11 (Z_to_bv 64 SITE_ecl_egsi) t0_2 t1_2 t2_2 a0_3 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 s3 s9 s10
              t3_2 t4_2 t5_2 t6_2 F_2 fc_2 m2 lo outer (Z_to_bv 8 1) canary E ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10
              fdfs_ok mat_ok ltac:(lia) e_aligned e_live art_2 inv_2 callok_2 ltac:(rewrite sp0_2; unfold STACK_WIN, RT_STACK in *; lia) top0
              ltac:(rewrite cg_2; exact ctx0) chain_2 ltac:(rewrite cg_2; apply (cg_has_weaken _ _ _ _ _ graph0); vm_compute; reflexivity)
              env_2 frame_2 rep_2) here_3).
  intros c4 (Σ3 & at_4 & live_3 & frames_3 & sp0_3 & credit_3 & cg_3).
  destruct (ASTA_unpack RT Σ3 _ _ c4 at_4)
    as (ms4 & (ra_4 & t0_4 & t1_4 & t2_4 & a0_4 & a1_4 & a2_4 & a3_4 & a4_4 & a5_4 & a6_4 & a7_4 & s3_4 & s9_4 & s10_4
               & t3_4 & t4_4 & t5_4 & t6_4 & F_4 & fc_4 & m4 & -> & after_4 & pres_4 & env_4 & frame_4 & chain_4 & rep_4) & here_4).
  clear at_4.
  destruct after_4 as (art_4 & inv_4 & wm_4 & stk_4). rewrite sp_off96 in stk_4, pres_4.
  assert (e_live_3 : In (E, 904) (rt_live RT Σ3)) by (rewrite live_3; exact e_live).
  destruct (af_acc_live RT AF Σ3 m4 E 904 art_4 e_live_3) as (_ & acc_4).
  pose proof (af_live_range RT AF Σ2 m2 E 904 art_2 e_live) as (_ & e_below & _).
  assert (e_low : E + 904 <= lo) by (rewrite sp0_2 in e_below; lia).
  destruct (arrs16_of_es_rep m4 E 0 0 rep_4) as (fl_16 & mk_16 & bf_16 & dt_16 & ds_16 & df_16 & fi_16 & ln_16 & fn_16 & tb_16).
  (* after the rounds: top and bottom cleared, the frame popped, return *)
  assert (walk2 : evt asegs (fun ms => exists mm : mem,
       ret_st ra sp gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (E + 896)) mm ms
       /\ munch [(E + 896, E + 904)] m4 mm /\ wmono asegs m4 mm /\ mem_inv asegs mm
       /\ rw_cells asegs mm (E + 896) [C4 z64; C4 z64] /\ stk asegs mm lo (bv_unsigned sp))
    (MS (mkR ra_4 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 TP_A) t0_4 t1_4 t2_4 sp (Z_to_bv 64 E) a0_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4
             (Z_to_bv 64 CLR_FILE) s3_4 (Z_to_bv 64 SHB) (Z_to_bv 64 128) (Z_to_bv 64 64) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) s9_4 s10_4 s11
             t3_4 t4_4 t5_4 t6_4)
        F_4 (Z_to_bv 64 (clr_next 15)) fc_4 None m4 (seg_rom asegs))).
  { clear - e_heap e_cap e_aligned e_low acc_4 inv_4 tb_16 frame_4 stk_4 lo_heap sp_low47 stack_room0.
    assert (out_pc : CLR_DONE = ECL_DONE) by reflexivity.
    change (clr_next 15) with CLR_DONE. rewrite out_pc. clear out_pc.
    unfold ECL_DONE, ret_st, clr_frame, SHB in *.
    pose proof (bv_unsigned_in_range 64 sp) as sp_range. unfold bv_modulus in sp_range. cbn [Z.of_N] in sp_range.
    remember (bv_unsigned sp) as SP eqn:SP_def. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- SP_def.
    pose proof (munch_refl [(E + 896, E + 904)] m4) as mu_walk. pose proof (wmono_refl asegs m4) as wm_walk.
    lazymatch type of mu_walk with munch ?W _ _ => assert (sh_off : sh_fp W) by sh_fp_lia end.
    zstep. do 5 zstep. th_if_lit. zstep. fix_lit_store.
    do 5 zstep. th_if_lit. zstep. fix_lit_store.
    do 12 zstep. th_release frame_4 SP. zstep. zstep.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    apply evt_done. eexists. split; [do 16 eexists; cbv delta [mkR]; reflexivity |].
    exact (conj mu_walk (conj wm_walk (conj inv_4 (conj tb_16 stk_4)))). }
  cl_lift walk2 here_4 c5 at_5.
  destruct (ASTA_unpack RT Σ3 _ _ c5 at_5) as (ms5 & (m5 & back_5 & mu_5 & wm_5 & inv_5 & tb_5 & stk_5) & here_5). clear at_5.
  (* the error state block is apart from everything the caller owns *)
  assert (live_2' : rt_live RT Σ2 = [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ (E, 904) :: rt_live RT Σ)
    by (rewrite live_2; reflexivity).
  assert (e_apart : forall p n, In (p, n) ([(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ rt_live RT Σ) -> E + 904 <= p \/ p + n <= E)
    by (intros p n pn_in; exact (af_live_disj RT AF Σ2 m2 E 904 p n _ _ art_2 live_2' pn_in)).
  assert (fresh_e : forall x, aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) x -> x < E \/ E + 904 <= x).
  { intros x [x_stk | [x_static | [(p & n & pn_in & pn_rng) | [(f & kf & fk_in & f_rng) | (f & kf & fk_in & f_rng)]]]].
    - lia.
    - pose proof (client_static_range x x_static). unfold SEGTOP_A in *. lia.
    - destruct (e_apart p n ltac:(apply in_or_app; right; exact pn_in)); lia.
    - rewrite <- frames_2 in fk_in. pose proof (af_frames_range RT AF Σ2 m2 f kf art_2 fk_in) as (_ & _ & _ & f_apart).
      destruct (f_apart E 904 e_live); unfold fs_size in *; pose proof (Z.shiftl_nonneg 64 (Z.of_nat kf)); lia.
    - rewrite <- frames_2 in fk_in. pose proof (af_fshadow_apart RT AF Σ2 m2 f kf art_2 fk_in) as (sh_apart & _).
      destruct (sh_apart E 904 e_live); lia. }
  assert (late : forall a cs, rw_cells asegs m2 a cs ->
            (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) (bv_unsigned sp + -96) x /\ (x < E \/ E + 904 <= x)) ->
            rw_cells asegs m5 a cs).
  { intros a cs cells_2 cover. apply (rw_cells_agree asegs m2 m5 a cs cells_2); [| exact (wmono_trans asegs _ _ _ wm_4 wm_5)].
    intros x x_rng. cbv beta in x_rng. destruct (cover _ x_rng) as (x_cl & x_off).
    rewrite (mu_5 x ltac:(cbn [outside]; split; [lia | exact I])). apply pres_4; [exact x_cl | cbn [outside]; split; [lia | exact I]]. }
  assert (stat_ok : forall x, 12120464 <= x < 12205720 \/ 12341920 <= x < 12343248 ->
            aclient (rt_live RT Σ2) (rt_frames RT Σ2) (bv_unsigned sp + -96) x /\ (x < E \/ E + 904 <= x)).
  { intros x x_rng. split; [right; left; apply client_static_intro; lia | lia]. }
  assert (block_ok : forall p n x, In (p, n) ([(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ rt_live RT Σ) -> p <= x < p + n ->
            aclient (rt_live RT Σ2) (rt_frames RT Σ2) (bv_unsigned sp + -96) x /\ (x < E \/ E + 904 <= x)).
  { intros p n x pn_in x_rng. split.
    - right; right; left. exists p, n. split; [| exact x_rng]. rewrite live_2'. apply in_or_app. apply in_app_or in pn_in.
      destruct pn_in as [new_in | old_in]; [left; exact new_in | right; right; exact old_in].
    - destruct (e_apart p n pn_in); lia. }
  assert (sa_hdr_5 : rw_cells asegs m5 SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 1) (Z_to_bv 64 P))).
  { apply (late _ _ sa_hdr_2). intros x x_rng. unfold sa_hdr in x_rng. cbn [cells_size csize Nat.add] in x_rng.
    apply (block_ok SA 32); [apply in_or_app; right; exact sa_in | lia]. }
  assert (p_cells_5 : rw_cells asegs m5 P [C8 (Z_to_bv 64 E); CB 120 jp]).
  { apply (late _ _ p_cells_2). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
    apply (block_ok P 128); [apply in_or_app; right; exact p_in | lia]. }
  assert (mk_cells_5 : rw_cells asegs m5 MK [CB 24 jm1; C8 (Z_to_bv 64 SA); CB 40 jm2]).
  { apply (late _ _ mk_cells_2). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
    apply (block_ok MK 72); [apply in_or_app; right; exact mk_in | lia]. }
  assert (dslot_5 : rw_cells asegs m5 (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 H)])
    by (apply (late _ _ dslot_2); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng; apply stat_ok; lia).
  assert (ub_5 : rw_cells asegs m5 (TP_A + -150) [C1 u'])
    by (apply (late _ _ ub_2); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng; apply stat_ok; lia).
  assert (g4a0_5 : rw_cells asegs m5 0xb9f4a0 [C4 (Z_to_bv 64 2)])
    by (apply (late _ _ g4a0_2); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng; apply stat_ok; lia).
  assert (g4c0_5 : rw_cells asegs m5 0xb9f4c0 [C4 (Z_to_bv 64 1)])
    by (apply (late _ _ g4c0_2); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng; apply stat_ok; lia).
  assert (g4e0_5 : rw_cells asegs m5 0xb9f4e0 [C8 (Z_to_bv 64 G)])
    by (apply (late _ _ g4e0_2); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng; apply stat_ok; lia).
  assert (oldcb_5 : rw_cells asegs m5 (TP_A + -96) [C8 oldcb])
    by (apply (late _ _ oldcb_2); intros x x_rng; cbn [cells_size csize Nat.add] in x_rng; apply stat_ok; lia).
  assert (h_cell_5 : rw_cells asegs m5 H [C8 (Z_to_bv 64 N)]).
  { apply (late _ _ h_cell_2). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
    apply (block_ok H 8); [apply in_or_app; left; cbn [In]; tauto | lia]. }
  assert (n_cells_5 : rw_cells asegs m5 N [C8 z64; C8 z64; C8 (Z_to_bv 64 ERR_DEL_THREAD_STATE); C8 z64]).
  { apply (late _ _ n_cells_2). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
    apply (block_ok N 32); [apply in_or_app; left; cbn [In]; tauto | lia]. }
  assert (g_cells_5 : rw_cells asegs m5 G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)]).
  { apply (late _ _ g_cells_2). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
    apply (block_ok G 16); [apply in_or_app; left; cbn [In]; tauto | lia]. }
  assert (sk_cells_5 : rw_cells asegs m5 SK (Fz_T_sk.sk_cells (Z_to_bv 64 1) z64 (Z_to_bv 64 D) (Z_to_bv 64 1) (Z_to_bv 64 4) z64
                                               (Z_to_bv 64 TEV_CMP) (Z_to_bv 64 TEV_FREE) (Z_to_bv 64 TEV_COPY))).
  { apply (late _ _ sk_cells_2). intros x x_rng. unfold Fz_T_sk.sk_cells in x_rng. cbn [cells_size csize Nat.add] in x_rng.
    apply (block_ok SK 56); [apply in_or_app; left; cbn [In]; tauto | lia]. }
  assert (lk_cells_5 : rw_cells asegs m5 LK (mutex_cells z64 z64)).
  { apply (late _ _ lk_cells_2). intros x x_rng. unfold mutex_cells in x_rng. cbn [cells_size csize Nat.add] in x_rng.
    apply (block_ok LK 40); [apply in_or_app; left; cbn [In]; tauto | lia]. }
  assert (d_cells_5 : rw_cells asegs m5 D [C8 (Z_to_bv 64 H); CB 24 (repeat (Z_to_bv 8 0) 24)]).
  { apply (late _ _ d_cells_2). intros x x_rng. cbn [cells_size csize Nat.add] in x_rng.
    apply (block_ok D 32); [apply in_or_app; left; cbn [In]; tauto | lia]. }
  assert (arrs_5 : ecl_arrs m5 E 16).
  { assert (below_tb : forall a cs, rw_cells asegs m4 a cs -> a + Z.of_nat (cells_size cs) <= E + 896 -> rw_cells asegs m5 a cs).
    { intros a cs cells_4 a_hi. apply (rw_cells_agree asegs m4 m5 a cs cells_4); [| exact wm_5].
      intros x x_rng. apply mu_5. cbv beta in x_rng. cbn [outside]. split; [lia | exact I]. }
    refine (conj (below_tb _ _ fl_16 _) (conj (below_tb _ _ mk_16 _) (conj (below_tb _ _ bf_16 _) (conj (below_tb _ _ dt_16 _)
             (conj (below_tb _ _ ds_16 _) (conj (below_tb _ _ df_16 _) (conj (below_tb _ _ fi_16 _) (conj (below_tb _ _ ln_16 _)
             (conj (below_tb _ _ fn_16 _) tb_5))))))))); rewrite cells_size_repeat; cbn [csize]; lia. }
  assert (art_5 : ART RT Σ3 m5).
  { apply (af_frame RT AF Σ3 m4 m5 USTACK_TOP art_4); [rewrite sp0_3, sp0_2; unfold STACK_WIN, SEGTOP_A, USTACK_TOP in *; lia | | exact wm_5].
    intros x not_cl. apply mu_5. cbn [outside]. split; [| exact I]. intros x_in. apply not_cl.
    right; right; left. exists E, 904. split; [exact e_live_3 | lia]. }
  assert (pres_05 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EG_W kd SA P) m m5).
  { intros x x_cl x_out. pose proof (fresh_e _ x_cl) as x_off.
    rewrite (mu_5 x ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (pres_4 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ x_cl); [rewrite live_2; intros e e_in; apply in_or_app; right; exact e_in
                                                                        | rewrite frames_2; exact (fun e e_in => e_in) | lia])
                      ltac:(cbn [outside]; split; [lia | exact I])).
    rewrite (pres_2 x ltac:(apply (aclient_mono _ _ _ _ _ _ _ x_cl); [exact (fun e e_in => e_in) | exact (fun e e_in => e_in) | lia]) x_out).
    exact (pres_1 x x_cl I). }
  apply finish. exists Σ3, E, N, H, G, SK, LK, D, u', top'.
  rewrite live_3, frames_3, sp0_3, credit_3, cg_3, live_2, frames_2, sp0_2, credit_2, cg_2.
  refine (conj _ (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl fresh_2)))))).
  apply (ASTA_conseq RT Σ3 PMc _ _ c5 here_5). intros ms <-. exists m5.
  refine (conj back_5 (conj (conj art_5 (conj inv_5 (conj _ stk_5))) (conj pres_05 (conj _ (conj top'_val (conj sa_hdr_5 (conj p_cells_5
            (conj mk_cells_5 (conj arrs_5 (conj dslot_5 (conj ub_5 (conj g4a0_5 (conj g4c0_5 (conj g4e0_5 (conj oldcb_5 (conj h_cell_5
            (conj n_cells_5 (conj g_cells_5 (conj sk_cells_5 (conj lk_cells_5 d_cells_5)))))))))))))))))))).
  - exact (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ (wmono_trans asegs _ _ _ wm_1 wm_2) wm_4) wm_5).
  - apply (cl_env_seg _ m4 m5 _ canary env_4 mu_5). cl_fp_lia.
Qed.
End Eclear.
