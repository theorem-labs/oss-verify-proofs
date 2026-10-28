(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_free Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_sk Fz_T_mtl Fz_T_its Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0 Fz_I3_glx0 Fz_G_OSSL_ERR_STATE_new Fz_I3_icfast Fz_I3_egsiw Fz_I3_egsi Fz_I3_eclw Fz_W5_rep Fz_W5_agr Fz_W5_clear.
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
  intros m A c c' k n H Hk E. apply (proj1 (rw_cells_app m A _ _)) in H as [_ H2]. rewrite (cells_size_pre c c' k E) in H2.
  replace (n - k)%nat with (S (n - S k)) in H2 by lia. cbn [repeat] in H2. exact (rw_cells_head m _ c _ H2).
Qed.

(* [comment removed for export] *)
Lemma arr_step : forall (m m' : mem) A c c' (k n : nat), rw_cells asegs m A (repeat c' k ++ repeat c (n - k)) -> (k < n)%nat -> csize c' = csize c ->
  wmono asegs m m' ->
  (forall x : word, A <= bv_unsigned x < A + Z.of_nat (n * csize c) ->
     ~ (A + Z.of_nat (k * csize c) <= bv_unsigned x < A + Z.of_nat (k * csize c) + Z.of_nat (csize c)) -> m' x = m x) ->
  rw_cells asegs m' (A + Z.of_nat (k * csize c)) [c'] ->
  rw_cells asegs m' A (repeat c' (S k) ++ repeat c (n - S k)).
Proof.
  intros m m' A c c' k n H Hk E WM AG NEWc.
  apply (proj1 (rw_cells_app m A _ _)) in H as [H1 H2]. rewrite (cells_size_pre c c' k E) in H2.
  replace (n - k)%nat with (S (n - S k)) in H2 by lia. cbn [repeat] in H2. apply rw_cells_tail in H2.
  pose proof (rw_cells_bound _ _ _ _ H2) as B2. rewrite cells_size_repeat in B2.
  rewrite repeat_snoc, <- app_assoc. cbn [app].
  apply (proj2 (rw_cells_app m' A _ _)). rewrite (cells_size_pre c c' k E). split.
  - apply (rw_cells_agree asegs m m' _ _ H1); [| exact WM]. rewrite (cells_size_pre c c' k E). intros x Hx. apply AG; nia.
  - apply (proj2 (rw_cells_app m' _ [c'] _)). split; [exact NEWc|]. cbn [cells_size Nat.add]. rewrite Nat.add_0_r, E.
    apply (rw_cells_agree asegs m m' _ _ H2); [| exact WM]. rewrite cells_size_repeat. intros x Hx. apply AG; nia.
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
  intros m a bs BA WR. split.
  - split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact WR.
Qed.

(* [comment removed for export] *)
Lemma ecl_arrs_of_zeros : forall (m : mem) E, bytes_at asegs m E (repeat (Z_to_bv 8 0) (Z.to_nat 904)) -> wr_at asegs m E 904 -> ecl_arrs m E 0.
Proof.
  intros m E BA WR.
  pose proof (rw_CB_of_bytes_ec m E _ BA ltac:(rewrite repeat_length; exact WR)) as H. rewrite repeat_length in H.
  apply (rw_cells_recast m E _ (repeat (C4 z64) 16 ++ repeat (C4 z64) 16 ++ repeat (C8 z64) 16 ++ repeat (C8 z64) 16 ++ repeat (C8 z64) 16 ++ repeat zb4 16
                                ++ repeat (C8 z64) 16 ++ repeat (C4 z64) 16 ++ repeat (C8 z64) 16 ++ [C4 z64; C4 z64])) in H; [| vm_compute; repeat split; exact I | vm_compute; reflexivity].
  unfold ecl_arrs. cbn [Nat.sub]. rewrite !app_nil_l.
  Ltac ecl_split H A1 nxt :=
    lazymatch type of H with rw_cells _ ?mm ?A (?R1 ++ ?rest) =>
      apply (proj1 (rw_cells_app mm A R1 rest)) in H as [A1 H]; cbn [cells_size csize repeat Nat.add Nat.mul] in H;
      lazymatch type of H with rw_cells _ _ ?A' _ => replace A' with nxt in H by (cbn; lia) end
    end.
  ecl_split H A0 (E + 64). ecl_split H A1 (E + 128). ecl_split H A2 (E + 256). ecl_split H A3 (E + 384). ecl_split H A4 (E + 512).
  ecl_split H A5 (E + 576). ecl_split H A6 (E + 704). ecl_split H A7 (E + 768). ecl_split H A8 (E + 896).
  repeat (split; [assumption|]). exact H.
Qed.

(* [comment removed for export] *)
Lemma ecl_arrs_get : forall (m : mem) E (k : nat), (k < 16)%nat -> ecl_arrs m E k ->
  rw_cells asegs m (E + 4 * Z.of_nat k) [C4 z64] /\ rw_cells asegs m (E + 4 * Z.of_nat k + 64) [C4 z64] /\ rw_cells asegs m (E + 8 * Z.of_nat k + 128) [C8 z64]
  /\ rw_cells asegs m (E + 8 * Z.of_nat k + 256) [C8 z64] /\ rw_cells asegs m (E + 8 * Z.of_nat k + 384) [C8 z64] /\ rw_cells asegs m (E + 4 * Z.of_nat k + 512) [zb4]
  /\ rw_cells asegs m (E + 8 * Z.of_nat k + 576) [C8 z64] /\ rw_cells asegs m (E + 4 * Z.of_nat k + 704) [C4 z64] /\ rw_cells asegs m (E + 8 * Z.of_nat k + 768) [C8 z64].
Proof.
  intros m E k Hk (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  Ltac ecl_get m Hk A tgt := let H := fresh "G" in
    pose proof (arr_get m _ _ _ _ 16 A Hk eq_refl) as H; cbn [csize zb4] in H;
    lazymatch type of H with rw_cells _ _ ?X _ => replace X with tgt in H by lia end; exact H.
  split; [ecl_get m Hk A0 (E + 4 * Z.of_nat k)|]. split; [ecl_get m Hk A1 (E + 4 * Z.of_nat k + 64)|]. split; [ecl_get m Hk A2 (E + 8 * Z.of_nat k + 128)|].
  split; [ecl_get m Hk A3 (E + 8 * Z.of_nat k + 256)|]. split; [ecl_get m Hk A4 (E + 8 * Z.of_nat k + 384)|]. split; [ecl_get m Hk A5 (E + 4 * Z.of_nat k + 512)|].
  split; [ecl_get m Hk A6 (E + 8 * Z.of_nat k + 576)|]. split; [ecl_get m Hk A7 (E + 4 * Z.of_nat k + 704)| ecl_get m Hk A8 (E + 8 * Z.of_nat k + 768)].
Qed.

(* [comment removed for export] *)
Lemma ecl_arrs_step : forall (m m' : mem) E (k : nat), (k < 16)%nat -> ecl_arrs m E k -> wmono asegs m m' ->
  (forall x : word, E <= bv_unsigned x < E + 904 -> outside (ecl_W E (Z.of_nat k)) (bv_unsigned x) -> m' x = m x) ->
  rw_cells asegs m' (E + 4 * Z.of_nat k) [C4 z64] -> rw_cells asegs m' (E + 4 * Z.of_nat k + 64) [C4 z64] -> rw_cells asegs m' (E + 8 * Z.of_nat k + 128) [C8 z64] ->
  rw_cells asegs m' (E + 8 * Z.of_nat k + 256) [C8 z64] -> rw_cells asegs m' (E + 8 * Z.of_nat k + 384) [C8 z64] -> rw_cells asegs m' (E + 4 * Z.of_nat k + 512) [C4 z64] ->
  rw_cells asegs m' (E + 8 * Z.of_nat k + 576) [C8 z64] -> rw_cells asegs m' (E + 4 * Z.of_nat k + 704) [C4 ECL_LNW] -> rw_cells asegs m' (E + 8 * Z.of_nat k + 768) [C8 z64] ->
  ecl_arrs m' E (S k).
Proof.
  intros m m' E k Hk (A0 & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9) WM AG Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8.
  Ltac ecl_put m m' Hk WM AG A Y :=
    refine (arr_step m m' _ _ _ _ 16 A Hk eq_refl WM _ _);
    [ cbn [csize zb4]; intros x Hx Hn; apply AG; [lia|]; unfold ecl_W; cbn [outside]; repeat split; lia
    | cbn [csize zb4]; lazymatch goal with |- rw_cells _ _ ?X _ => lazymatch type of Y with rw_cells _ _ ?X' _ => replace X with X' by lia end end; exact Y ].
  split; [ecl_put m m' Hk WM AG A0 Y0|]. split; [ecl_put m m' Hk WM AG A1 Y1|]. split; [ecl_put m m' Hk WM AG A2 Y2|]. split; [ecl_put m m' Hk WM AG A3 Y3|].
  split; [ecl_put m m' Hk WM AG A4 Y4|]. split; [ecl_put m m' Hk WM AG A5 Y5|]. split; [ecl_put m m' Hk WM AG A6 Y6|]. split; [ecl_put m m' Hk WM AG A7 Y7|].
  split; [ecl_put m m' Hk WM AG A8 Y8|].
  apply (rw_cells_agree asegs m m' _ _ A9); [| exact WM]. cbn [cells_size csize Nat.add]. intros x Hx. apply AG; [lia|]. unfold ecl_W. cbn [outside]. repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition ECLR_SITES : list (Z * Z) := [(SITE_ecl_egsi, e_eclear)] ++ ECL_SITES ++ EG_SITES.
Definition ECLR_CALLS : list (Z * Z) := [(SITE_ecl_egsi, e_get_state)] ++ ECL_CALLS ++ EG_CALLS.

Definition eclear_first_stmt (RT : rt_sig) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (k kd MK SA P : Z) (pad top : word) (jm1 jm2 jp : list byte) (u : byte) (r0 g0 oldcb : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x3c0 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_eclear (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) ECLR_SITES ECLR_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 7 <= LIVE_MAX -> 3 + mcost 904 <= rt_credit RT Σ -> cl_env m lb canary ->
  (* [comment removed for export] *)
  rw_cells asegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells asegs m G_IC_OPTSDONE [C8 (Z_to_bv 64 2)] ->
  rw_cells asegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  (* [comment removed for export] *)
  rw_cells asegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells asegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 1 <= k < 128 ->
  rw_cells asegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] -> In (MK, 72) (rt_live RT Σ) -> In (SA, 32) (rt_live RT Σ) -> In (P, 128) (rt_live RT Σ) ->
  MK mod 16 = 0 -> SA mod 16 = 0 -> P mod 16 = 0 -> (SA + 32 <= P \/ P + 128 <= SA) -> (SA + 32 <= MK \/ MK + 72 <= SA) -> (P + 128 <= MK \/ MK + 72 <= P) ->
  rw_cells asegs m MK [CB 24 jm1; C8 (Z_to_bv 64 SA); CB 40 jm2] ->
  rw_cells asegs m SA (sa_hdr (Z_to_bv 64 1) pad top (Z_to_bv 64 0) (Z_to_bv 64 P)) -> rw_cells asegs m P [C8 (Z_to_bv 64 0); CB 120 jp] ->
  (* [comment removed for export] *)
  rw_cells asegs m DTOR_KEY [C4 (Z_to_bv 64 kd); C4 (Z_to_bv 64 0xffffffff)] -> 1 <= kd < 128 -> k <> kd -> rw_cells asegs m (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (TP_A + -150) [C1 u] -> rw_cells asegs m TEV_ONCE [C4 (Z_to_bv 64 0)] -> rw_cells asegs m TEV_RET [C4 r0] -> rw_cells asegs m TEV_REG [C8 g0] ->
  rw_cells asegs m (TP_A + -96) [C8 oldcb] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_eclear m)))
    (fun c => exists (Σ' : rts RT) (E N H G SK LK D : Z) (u' : byte) (top' : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (E + 896)) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EG_W kd SA P) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' G_IC_OPTSDONE [C8 (Z_to_bv 64 2)]
           /\ rw_cells asegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 1) (Z_to_bv 64 P)) /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
           /\ rw_cells asegs m' P [C8 (Z_to_bv 64 E); CB 120 jp]
           /\ ecl_arrs m' E 16
           /\ rw_cells asegs m' (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 H)] /\ rw_cells asegs m' (TP_A + -150) [C1 u']
           /\ rw_cells asegs m' TEV_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' TEV_RET [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m' TEV_REG [C8 (Z_to_bv 64 G)]
           /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb]
           /\ rw_cells asegs m' H [C8 (Z_to_bv 64 N)] /\ rw_cells asegs m' N [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ERR_DEL_THREAD_STATE); C8 (Z_to_bv 64 0)]
           /\ rw_cells asegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)] /\ rw_cells asegs m' LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' D [C8 (Z_to_bv 64 H); CB 24 (repeat (Z_to_bv 8 0) 24)]) c
       /\ rt_live RT Σ' = [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ (E, 904) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 3 - mcost 904 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < E /\ E mod 16 = 0 /\ E + 904 < USTACK_TOP).

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
                      (Z_to_bv 64 CLR_FILE) s3' (Z_to_bv 64 SHB) (Z_to_bv 64 128) (Z_to_bv 64 64) (Z_to_bv 64 (-1)) (Z_to_bv 64 128) s9' s10' s11 t3' t4' t5' t6')
                 F' (Z_to_bv 64 CLR_DONE) fc' None m' (seg_rom asegs)
         /\ rt_after RT Σ' (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) [(E, E + 904)] m m'
         /\ cl_env m' lb canary
         /\ rw_cells asegs m' (bv_unsigned sp + -96) (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)
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
Proof.
  intros k Σ PMc sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 F fc m lo outer lb canary E rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c
    FDO MST HK EAL INE ART0 MI0 CALL LOW1 SPT CTX UWC CGH CLE FR ES.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT1 & SPA1).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *. set (usp1 := usp + -96) in *.
  assert (EU1 : bv_unsigned (Z_to_bv 64 usp1) = usp1) by (apply unsigned_lit; unfold usp1, USTACK_TOP, RT_STACK, STACK_WIN in *; clear - LOW1 SPT SP0W; lia).
  rewrite EU1 in ST, LOR, SPT1, SPA1.
  pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as (R4a & R4 & _).
  assert (ELO : E + 904 <= lo) by (clear - R4 LOW; lia).
  assert (HLOS : 0x10007fff8000 <= lo) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; clear - LOW SP0W; lia).
  assert (HLO1 : lo <= usp - 96) by (unfold usp1, RT_STACK in *; clear - LOR; lia).
  assert (SPH : usp <= 2 ^ 47) by (unfold USTACK_TOP in *; clear - SPT; lia).
  pose proof (afp_live_hi RT GOBJ AFP Σ m E 904 ART0 INE ltac:(lia)) as EHI.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & _ & UT).
  pose proof (proj2 (af_acc_live RT AF Σ m E 904 ART0 INE)) as ACCE.
  assert (HI : 0 <= Z.of_nat k < 16) by (clear - HK; lia).
  assert (FZ : nth_error EZ16 (Z.to_nat (Z.of_nat k)) = Some (Z_to_bv 64 0)) by (rewrite Nat2Z.id; unfold EZ16; apply nth_error_repeat; exact HK).
  pose proof (clr_sA_walk ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 s11 t3 t4 t5 t6 F fc m lo E (Z.of_nat k) 0 0
                EZ16 EZ16 EZ16 EZ16 (ecl_ls k) EZ16 (Z_to_bv 64 0)
                HLO1 HLOS SPH UT ES HI FZ ACCE EAL EHI ELO MI0) as W1.
  cl_lift W1 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (b3 & b4 & m1 & -> & MU1 & WM1 & MI1 & ES1) & Hc1'). clear Hc1.
  fold usp in Hc1'. fold usp1 in Hc1'.
  rewrite Nat2Z.id, !upd_repeat_same in ES1. change (Z_to_bv 64 (-1)) with ECL_LNW in ES1. rewrite (upd_ecl_ls k HK) in ES1.
  assert (A01 : forall x : word, ~ (E <= bv_unsigned x < E + 904) -> m1 x = m x) by (intros x Hx; apply MU1; cbn [outside]; clear - Hx; lia).
  assert (ART1 : ART RT Σ m1).
  { apply (af_frame RT AF Σ m m1 usp1 ART0 ltac:(clear - LOW1; unfold usp1; lia)); [| exact WM1].
    intros x Hx. apply A01. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE | clear - Hin; lia]. }
  assert (AG01 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros x Hx; cbv beta in Hx; apply A01; clear - Hx ELO HLO1; lia).
  assert (CLE1 : cl_env m1 lb canary) by (apply (cl_env_seg _ m m1 lb canary CLE MU1); cl_fp_lia).
  assert (ST1 : stk asegs m1 lo usp1) by (apply (stk_agree_nw asegs m m1 _ _ ST); intros x Hx; cbv beta in Hx; apply A01; clear - Hx ELO; lia).
  assert (FR1 : rw_cells asegs m1 usp1 (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)).
  { apply (rw_cells_agree_nw asegs m m1 _ _ FR). intros x Hx. cbv beta in Hx. unfold clr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A01. unfold usp1 in *. clear - Hx ELO HLO1; lia. }
  assert (FRR1 : rw_cells asegs m1 (usp - 16) [C8 s0c; C8 rac]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s10c; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c]))
      by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m1 usp1 [C8 s10c; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c] [C8 s0c; C8 rac] FR1). }
  destruct (cl_chain_call (rt_cg RT Σ) e_eclear e_CRYPTO_free SITE_clr_f1 m m1 rac s0c sp (Z_to_bv 64 usp1) outer CTX
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWC AG01 FRR1 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX1 & UWC1).
  assert (CO1 : call_ok RT Σ m1 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; clear - ST1 LOW LOR SPT1 SPA1; tauto).
  apply (C_FRN Σ PMc (Z_to_bv 64 SITE_clr_f1) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 112)
           b3 b4 a5 a6 a7 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 (E + Z.of_nat k * 8 + 576)) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat k * 8)) (Z_to_bv 64 (Z.of_nat k * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128)
           (Z_to_bv 64 (E + Z.of_nat k * 8)) (Z_to_bv 64 ((E + Z.of_nat k * 8 + 576) ≫ 3 + SHB)) s11 t3 t4 t5 t6 F fc m1 lo (bv_unsigned rac :: outer) lb canary
           FDO MST eq_refl eq_refl ART1 MI1 CO1).
  { rewrite (unsigned_lit SITE_clr_f1) by (unfold SITE_clr_f1; lia). exact CTX1. }
  { exact UWC1. }
  { rewrite (unsigned_lit SITE_clr_f1) by (unfold SITE_clr_f1; lia). apply (proj2 CGH). wp_in_lit. }
  { exact CLE1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (v1 & Hc2).
  destruct (ASTA_unpack RT Σ _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2) & Hc2'). clear Hc2.
  destruct RS2 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_clr_f1) in Hc2' by (unfold SITE_clr_f1; lia).
  assert (A12 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x) -> m2 x = m1 x) by (intros x Hx; exact (PRES2 x Hx)).
  assert (ES2 : es_rep m2 E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls (S k)) EZ16).
  { apply (es_rep_agree_nw m1 m2 _ _ _ _ _ _ _ _ _ ES1). intros x Hx. cbv beta in Hx. apply A12. apply (acl_live _ _ _ E 904); [exact INE | clear - Hx; lia]. }
  assert (FR2 : rw_cells asegs m2 usp1 (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros x Hx. cbv beta in Hx. unfold clr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A12. left. unfold usp1, USTACK_TOP in *. clear - Hx SPT; lia. }
  assert (AG02 : agree_on (fun x => usp <= x < USTACK_TOP) m m2).
  { intros x Hx. cbv beta in Hx. rewrite (A12 x ltac:(left; unfold usp1; clear - Hx; lia)). exact (AG01 x Hx). }
  destruct (af_client_consts RT AF Σ m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (proj2 (af_acc_live RT AF Σ m2 E 904 ART2 INE)) as ACCE2.
  pose proof (clr_sB_walk sp gp (Z_to_bv 64 TP_A) w0 w1 w2 v1 g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 (E + Z.of_nat k * 8 + 576)) s11 w3 w4 w5 w6 F2 fc2 m2 lo E (Z.of_nat k) 0 0
                EZ16 EZ16 EZ16 EZ16 (ecl_ls (S k)) EZ16 (Z_to_bv 64 0)
                HLO1 HLOS SPH UT2 ES2 HI FZ ACCE2 EAL EHI ELO MI2) as W2.
  fold usp usp1 in W2.
  cl_lift W2 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & ES3) & Hc3'). clear Hc3.
  fold usp in Hc3'. fold usp1 in Hc3'.
  rewrite Nat2Z.id, upd_repeat_same in ES3.
  assert (ART3 : ART RT Σ m3).
  { apply (af_frame RT AF Σ m2 m3 usp1 ART2 ltac:(clear - LOW1; unfold usp1; lia)); [| exact WM3].
    intros x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE | clear - Hin; lia]. }
  assert (A23 : forall x : word, ~ (E <= bv_unsigned x < E + 904) -> m3 x = m2 x) by (intros x Hx; apply MU3; cbn [outside]; clear - Hx; lia).
  assert (ST3 : stk asegs m3 lo usp1) by (apply (stk_agree_nw asegs m2 m3 _ _ ST2); intros x Hx; cbv beta in Hx; apply A23; clear - Hx ELO; lia).
  assert (FR3 : rw_cells asegs m3 usp1 (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)).
  { apply (rw_cells_agree_nw asegs m2 m3 _ _ FR2). intros x Hx. cbv beta in Hx. unfold clr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A23. unfold usp1 in *. clear - Hx ELO HLO1; lia. }
  assert (AG03 : agree_on (fun x => usp <= x < USTACK_TOP) m m3).
  { intros x Hx. cbv beta in Hx. rewrite (A23 x ltac:(clear - Hx ELO HLO1; lia)). exact (AG02 x Hx). }
  assert (CLE3 : cl_env m3 lb canary) by (apply (cl_env_seg _ m2 m3 lb canary CLE2 MU3); cl_fp_lia).
  assert (FRR3 : rw_cells asegs m3 (usp - 16) [C8 s0c; C8 rac]).
  { replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s10c; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c]))
      by (cbn [cells_size csize Nat.add]; unfold usp1; lia).
    exact (rw_cells_skip m3 usp1 [C8 s10c; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c] [C8 s0c; C8 rac] FR3). }
  destruct (cl_chain_call (rt_cg RT Σ) e_eclear e_CRYPTO_free SITE_clr_f2 m m3 rac s0c sp (Z_to_bv 64 usp1) outer CTX
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWC AG03 FRR3 ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTX3 & UWC3).
  assert (CO3 : call_ok RT Σ m3 (Z_to_bv 64 usp1) lo) by (unfold call_ok; rewrite EU1; clear - ST3 LOW LOR SPT1 SPA1; tauto).
  apply (C_FRN Σ PMc (Z_to_bv 64 SITE_clr_f2) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) w0 w1 w2 sp (Z_to_bv 64 E) (Z_to_bv 64 0) (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 114)
           g3 g4 g5 g6 g7 (Z_to_bv 64 CLR_FILE) (Z_to_bv 64 (E + Z.of_nat k * 8 + 768)) (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.of_nat k * 8)) (Z_to_bv 64 (Z.of_nat k * 4)) (Z_to_bv 64 (-1)) (Z_to_bv 64 128)
           (Z_to_bv 64 (E + Z.of_nat k * 8)) (Z_to_bv 64 ((E + Z.of_nat k * 8 + 768) ≫ 3 + SHB)) s11 w3 w4 w5 w6 F2 fc2 m3 lo (bv_unsigned rac :: outer) lb canary
           FDO MST eq_refl eq_refl ART3 MI3 CO3).
  { rewrite (unsigned_lit SITE_clr_f2) by (unfold SITE_clr_f2; lia). exact CTX3. }
  { exact UWC3. }
  { rewrite (unsigned_lit SITE_clr_f2) by (unfold SITE_clr_f2; lia). apply (proj2 CGH). wp_in_lit. }
  { exact CLE3. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (v2 & Hc4).
  destruct (ASTA_unpack RT Σ _ _ c4 Hc4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4) & Hc4'). clear Hc4.
  destruct RS4 as (y0 & y1 & y2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & y3 & y4 & y5 & y6 & F4 & fc4 & ->).
  rewrite EU1 in ST4, PRES4. rewrite (ret_pc_even SITE_clr_f2) in Hc4' by (unfold SITE_clr_f2; lia).
  assert (A34 : forall x : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned x) -> m4 x = m3 x) by (intros x Hx; exact (PRES4 x Hx)).
  assert (ES4 : es_rep m4 E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls (S k)) EZ16).
  { apply (es_rep_agree_nw m3 m4 _ _ _ _ _ _ _ _ _ ES3). intros x Hx. cbv beta in Hx. apply A34. apply (acl_live _ _ _ E 904); [exact INE | clear - Hx; lia]. }
  assert (FR4 : rw_cells asegs m4 usp1 (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)).
  { apply (rw_cells_agree_nw asegs m3 m4 _ _ FR3). intros x Hx. cbv beta in Hx. unfold clr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A34. left. unfold usp1, USTACK_TOP in *. clear - Hx SPT; lia. }
  assert (AG04 : agree_on (fun x => usp <= x < USTACK_TOP) m m4).
  { intros x Hx. cbv beta in Hx. rewrite (A34 x ltac:(left; unfold usp1; clear - Hx; lia)). exact (AG03 x Hx). }
  destruct (af_client_consts RT AF Σ m4 ART4) as (_ & SHC4 & _ & _ & UT4).
  pose proof (proj2 (af_acc_live RT AF Σ m4 E 904 ART4 INE)) as ACCE4.
  pose proof (clr_sC_walk sp gp (Z_to_bv 64 TP_A) y0 y1 y2 v2 k1 k2 k3 k4 k5 k6 k7 (Z_to_bv 64 (E + Z.of_nat k * 8 + 768)) s11 y3 y4 y5 y6 F4 fc4 m4 lo E (Z.of_nat k) 0 0
                EZ16 EZ16 EZ16 EZ16 (ecl_ls (S k)) EZ16
                HLO1 HLOS SPH UT4 ES4 HI ACCE4 EAL EHI ELO MI4) as W3.
  fold usp usp1 in W3.
  cl_lift W3 Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ _ _ c5 Hc5) as (ms5 & (z0 & m5 & -> & MU5 & WM5 & MI5 & ES5) & Hc5'). clear Hc5.
  fold usp in Hc5'. fold usp1 in Hc5'.
  rewrite Nat2Z.id, upd_repeat_same in ES5.
  assert (ART5 : ART RT Σ m5).
  { apply (af_frame RT AF Σ m4 m5 usp1 ART4 ltac:(clear - LOW1; unfold usp1; lia)); [| exact WM5].
    intros x Hx. apply MU5. cbn [outside]. split; [| exact I]. intros Hin; apply Hx. apply (acl_live _ _ _ E 904); [exact INE | clear - Hin; lia]. }
  assert (A45 : forall x : word, ~ (E <= bv_unsigned x < E + 904) -> m5 x = m4 x) by (intros x Hx; apply MU5; cbn [outside]; clear - Hx; lia).
  assert (ST5 : stk asegs m5 lo usp1) by (apply (stk_agree_nw asegs m4 m5 _ _ ST4); intros x Hx; cbv beta in Hx; apply A45; clear - Hx ELO; lia).
  assert (FR5 : rw_cells asegs m5 usp1 (clr_frame rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c)).
  { apply (rw_cells_agree_nw asegs m4 m5 _ _ FR4). intros x Hx. cbv beta in Hx. unfold clr_frame in Hx. cbn [cells_size csize Nat.add] in Hx.
    apply A45. unfold usp1 in *. clear - Hx ELO HLO1; lia. }
  assert (AG05 : agree_on (fun x => usp <= x < USTACK_TOP) m m5).
  { intros x Hx. cbv beta in Hx. rewrite (A45 x ltac:(clear - Hx ELO HLO1; lia)). exact (AG04 x Hx). }
  assert (CLE5 : cl_env m5 lb canary) by (apply (cl_env_seg _ m4 m5 lb canary CLE4 MU5); cl_fp_lia).
  apply Hk. exists Σ. split; [| repeat split; reflexivity].
  eapply ASTA_conseq; [exact Hc5'|]. intros ms <-.
  exists (Z_to_bv 64 SITE_clr_f2), y0, y1, y2, z0, k1, k2, k3, k4, k5, k6, k7, (Z_to_bv 64 (E + Z.of_nat k * 8 + 768)), (Z_to_bv 64 (E + Z.of_nat k * 8)),
    (Z_to_bv 64 ((E + Z.of_nat k * 8 + 768) ≫ 3 + SHB)), y3, y4, y5, y6, F4, fc4, m5.
  fold usp. fold usp1.
  split; [reflexivity|]. rewrite EU1.
  split; [exact (conj ART5 (conj MI5 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM3 (wmono_trans asegs _ _ _ WM4 WM5)))) ST5)))|].
  split; [| exact (conj CLE5 (conj FR5 (conj (uw_chain_agree outer m m5 sp s0c UWC AG05) ES5)))].
  intros x Hx Ho. cbn [outside] in Ho. destruct Ho as [HnE _].
  rewrite (A45 x HnE), (A34 x Hx), (A23 x HnE), (A12 x Hx). exact (A01 x HnE).
Qed.

Lemma ecl_loop_ind : forall (n k : nat), (k + n = 15)%nat -> ecl_loop_stmt k.
Proof.
  induction n as [|n IH]; intros k Hkn.
  - (* [comment removed for export] *)
    assert (Hk : k = 15%nat) by lia. subst k. clear Hkn.
    intros Σ PMc sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 F fc m lo outer lb canary E rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c
      FDO MST HK E8 INE ART0 MI0 CALL LOW1 SPT0 CTX UWC CGH ENV FR ES.
    intros T c HA Hk.
    apply (ecl_iter 15 Σ PMc sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 F fc m lo outer lb canary E rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c
             FDO MST HK E8 INE ART0 MI0 CALL LOW1 SPT0 CTX UWC CGH ENV FR ES T c HA).
    intros c1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1 & CG1). apply Hk. exists Σ1. split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 CG1))))].
    eapply ASTA_conseq; [exact Hc1|].
    intros ms (r' & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x9 & x10 & u3 & u4 & u5 & u6 & F' & fc' & m' & -> & RA & PRES & ENV' & FR' & _ & ES').
    exists r', u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, x3, x9, x10, u3, u4, u5, u6, F', fc', m'.
    split; [reflexivity|]. exact (conj RA (conj PRES (conj ENV' (conj FR' ES')))).
  - (* [comment removed for export] *)
    assert (HK15 : (k < 15)%nat) by lia.
    intros Σ PMc sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 F fc m lo outer lb canary E rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c
      FDO MST HK E8 INE ART0 MI0 CALL LOW1 SPT0 CTX UWC CGH ENV FR ES.
    intros T c HA Hk.
    apply (ecl_iter k Σ PMc sp gp s11 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s9 s10 t3 t4 t5 t6 F fc m lo outer lb canary E rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c
             FDO MST HK E8 INE ART0 MI0 CALL LOW1 SPT0 CTX UWC CGH ENV FR ES T c HA).
    intros c1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1 & CG1).
    destruct (ASTA_unpack RT Σ1 _ _ c1 Hc1) as (ms1 & (r1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x3 & x9 & x10 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & -> & RA1 & PRES1 & ENV1 & FR1 & UWC1 & ES1) & Hc1'). clear Hc1.
    destruct RA1 as (ART1 & MI1 & WM1 & ST1).
    pose proof CALL as (ST & LOW & LOR & SPT & SPA).
    unfold clr_next in Hc1'. replace (Z.of_nat k =? 15) with false in Hc1' by (symmetry; apply Z.eqb_neq; clear - HK15; lia).
    replace (Z.of_nat k + 1) with (Z.of_nat (S k)) in Hc1' by (clear; lia).
    rewrite <- CG1 in CTX, CGH. rewrite <- LV1 in INE. rewrite <- SP1 in LOW, LOW1.
    apply (IH (S k) ltac:(clear - Hkn; lia) Σ1 PMc sp gp s11 r1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 x3 x9 x10 u3 u4 u5 u6 F1 fc1 m1 lo outer lb canary E
             rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c FDO MST ltac:(clear - HK15; lia) E8 INE ART1 MI1
             (conj ST1 (conj LOW (conj LOR (conj SPT SPA)))) LOW1 SPT0 CTX UWC1 CGH ENV1 FR1 ES1 T c1 Hc1').
    intros c2 (Σ2 & Hc2 & LV2 & FRS2 & SP2 & CR2 & CG2). apply Hk. exists Σ2.
    split; [| rewrite LV2, FRS2, SP2, CR2, CG2; exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 CG1))))].
    eapply ASTA_conseq; [exact Hc2|].
    intros ms (r' & v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y9 & y10 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & RA2 & PRES2 & ENV2 & FR2 & ES2).
    exists r', v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, y3, y9, y10, v3, v4, v5, v6, F2, fc2, m2. split; [reflexivity|].
    destruct RA2 as (ART2 & MI2 & WM2 & ST2).
    split; [exact (conj ART2 (conj MI2 (conj (wmono_trans asegs _ _ _ WM1 WM2) ST2)))|].
    split; [| exact (conj ENV2 (conj FR2 ES2))].
    rewrite LV1, FRS1 in PRES2. exact (pres_fp_trans _ _ _ _ m m1 m2 PRES1 PRES2).
Qed.

Theorem eclear_first_cps : eclear_first_stmt RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary k kd MK SA P pad top jm1 jm2 jp u r0 g0 oldcb
    FDO MST -> ART0 MI0 CALL HSTK CTX UWC CGH Hfr Hlen Hcr CLE STP OD ONCE BRET OC KC HK TSK INMK INSA INP MK16 SA16 P16 DISJ MKS MKP MKC SAC PC DK HKD KKD TSL UC TVO TVR TVG CBC.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in *.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 0x3c0 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ SEGTOP_A <= lo /\ usp <= 2^47) by (unfold RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  set (usp1 := usp + -96). cl_eu usp (-96) EU1. fold usp1 in EU1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  pose proof (af_live_range RT AF Σ m MK 72 ART0 INMK) as (MK0 & MKLO & _). pose proof (af_live_range RT AF Σ m SA 32 ART0 INSA) as (SA0 & SALO & _).
  pose proof (af_live_range RT AF Σ m P 128 ART0 INP) as (P0 & PLO & _).
  (* [comment removed for export] *)
  pose proof (clr_w0_walk ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(clear - NUM; lia) ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(clear - NUM; lia) UT SHC MI0) as W0.
  change e_eclear with e_ERR_clear_error in HA. cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 96, usp)]) m m1) by exact MU1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 96 [] ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 96 [] ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) MU1') as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= lo -> rw_cells asegs m1 a cs).
  { intros a cs H R. apply (wg_keep_seg _ m m1 _ _ H MU1 WM1). intros x Hx. cbn [app outside]. clear - Hx R NUM HSTK. unfold RT_STACK in *. lia. }
  pose proof (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(first [solve [clear - NUM HSTK; unfold RT_STACK in *; cl_fp_lia] | cl_fp_lia])) as CLE1.
  destruct (cl_chain_call (rt_cg RT Σ) e_eclear e_get_state SITE_clr_gsi m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWC AG1
              ltac:(fold usp; replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (unfold usp1; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 usp1 [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_EGSI Σ PMc (Z_to_bv 64 SITE_clr_gsi) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 lo (bv_unsigned ra :: outer) lb canary k kd MK SA P pad top jm1 jm2 jp u r0 g0 oldcb FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 6. }
  { rewrite EU1. clear - HSTK. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_clr_gsi) by (unfold SITE_clr_gsi; clear; lia). exact CTXc1. }
  { exact UWCc1. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact Hfr. } { exact Hlen. } { exact Hcr. } { exact CLE1. }
  { exact (STAT1 _ _ STP ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). } { exact (STAT1 _ _ OD ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). }
  { exact (STAT1 _ _ ONCE ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). } { exact (STAT1 _ _ BRET ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). }
  { exact (STAT1 _ _ OC ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). } { exact (STAT1 _ _ KC ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). } { exact HK. }
  { exact (STAT1 _ _ TSK ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM HK; unfold SEGTOP_A in *; lia)). } { exact INMK. } { exact INSA. } { exact INP. }
  { exact MK16. } { exact SA16. } { exact P16. } { exact DISJ. } { exact MKS. } { exact MKP. }
  { exact (STAT1 _ _ MKC ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - MKLO LOW; lia)). } { exact (STAT1 _ _ SAC ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - SALO LOW; lia)). } { exact (STAT1 _ _ PC ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - PLO LOW; lia)). }
  { exact (STAT1 _ _ DK ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). } { exact HKD. } { exact KKD. }
  { exact (STAT1 _ _ TSL ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM HKD; unfold SEGTOP_A in *; lia)). } { exact (STAT1 _ _ UC ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). }
  { exact (STAT1 _ _ TVO ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). } { exact (STAT1 _ _ TVR ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). }
  { exact (STAT1 _ _ TVG ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). } { exact (STAT1 _ _ CBC ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - NUM; unfold SEGTOP_A in *; lia)). }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & E & N & H & G & SK & LK & D & u' & top' & Hc2 & LV1 & FRS1 & SP1 & CR1 & CG1 & E0 & E16 & EUP).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & CLE2 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & BA & ACC & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  unfold G_IC_STOPPED, G_IC_OPTSDONE, G_IC_BASE_ONCE, G_IC_BASE_RET in D1, D2, D3, D4.
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_clr_gsi) in Hc2' by (unfold SITE_clr_gsi; lia).
  assert (INE : In (E, 904) (rt_live RT Σ1)) by (rewrite LV1; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 E 904 ART2 INE) as (_ & ELO & _). rewrite SP1 in ELO. pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 E 904 ART2 INE ltac:(clear; lia)) as EH.
  assert (E8 : E mod 8 = 0) by (clear - E16; Z.div_mod_to_equations; lia).
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  (* [comment removed for export] *)
  assert (EGWS : forall x, usp1 <= x -> outside (EG_W kd SA P) x).
  { intros x Hx. unfold EG_W, MTL_W. cbn [outside app]. unfold G_ALLOW_CUST. clear - Hx SALO PLO LOW HSTK HKD NUM. unfold usp1, RT_STACK in *. repeat split; lia. }
  assert (AG2 : agree_on (fun x => usp1 <= x < USTACK_TOP) m1 m2) by (intros a Ha; cbv beta in Ha; apply PRES2; [left; exact Ha | apply EGWS; clear - Ha; lia]).
  assert (FR2 : rw_cells asegs m2 usp1 (clr_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10)).
  { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. unfold clr_frame. cbn [cells_size csize Nat.add]. intros x Hx. apply AG2. cbv beta. clear - Hx NUM. unfold usp1, USTACK_TOP in *. lia. }
  assert (UWC2 : uw_chain m2 sp s0 outer).
  { apply (uw_chain_agree outer m1 m2 sp s0 (uw_chain_agree outer m m1 sp s0 UWC AG1)). intros a Ha. apply AG2. cbv beta in Ha |- *. fold usp in Ha. clear - Ha. unfold usp1. lia. }
  pose proof (es_rep_of_arrs0 m2 E (ecl_arrs_of_zeros m2 E BA (proj1 (af_acc_live RT AF Σ1 m2 E 904 ART2 INE)))) as ES0.
  (* [comment removed for export] *)
  pose proof (clr_w1_walk sp gp (Z_to_bv 64 TP_A) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1 s2 s3 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 E
                EH ltac:(clear - ELO LOW NUM; lia) UT2) as W1.
  fold usp usp1 in W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (a0' & ->) & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  rewrite <- CG1 in CTX, CGH.
  apply (ecl_loop_ind 15 0 eq_refl Σ1 PMc sp gp s11 (Z_to_bv 64 SITE_clr_gsi) u0 u1 u2 a0' b1 b2 b3 b4 b5 b6 b7 s3 s9 s10 u3 u4 u5 u6 F2 fc2 m2 lo outer (Z_to_bv 8 1) canary E
           ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 FDO MST ltac:(clear; lia) E8 INE ART2 MI2).
  { fold usp usp1. rewrite <- SP1 in LOW. unfold call_ok. rewrite EU1. split; [exact ST2|]. split; [exact LOW|]. split; [clear - HSTK; unfold usp1, RT_STACK in *; lia|].
    split; [clear - NUM; unfold usp1, USTACK_TOP in *; lia|]. fold usp in SPA. clear - SPA. unfold usp1. Z.div_mod_to_equations. lia. }
  { fold usp. rewrite SP1. clear - NUM. lia. }
  { exact SPT. }
  { exact CTX. }
  { exact UWC2. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact CLE2. }
  { exact FR2. }
  { exact ES0. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (r4 & v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & x3 & x9 & x10 & v3 & v4 & v5 & v6 & F4 & fc4 & m4 & -> & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & FR4 & ES4) & Hc4'). clear Hc4.
  fold usp in ST4, PRES4, FR4. fold usp1 in ST4, PRES4, FR4. rewrite EU1 in ST4, PRES4.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & _ & _ & _ & UT4).
  pose proof (arrs16_of_es_rep m4 E 0 0 ES4) as ARR4. pose proof ARR4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TB4).
  assert (INE2 : In (E, 904) (rt_live RT Σ2)) by (rewrite LV2; exact INE).
  (* [comment removed for export] *)
  pose proof (clr_wz_walk sp gp (Z_to_bv 64 TP_A) v0 v1 v2 d0 d1 d2 d3 d4 d5 d6 d7 x3 (Z_to_bv 64 128) (Z_to_bv 64 64) x9 x10 s11 v3 v4 v5 v6
                r4 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 F4 fc4 m4 lo E (Z_to_bv 64 0) (Z_to_bv 64 0)
                EH ltac:(rewrite <- SP1 in LOW; clear - ELO LOW SP1; lia) E8) as WZ.
  fold usp in WZ. fold usp1 in WZ.
  specialize (WZ ST4 ltac:(clear - NUM; lia) ltac:(clear - HSTK; unfold usp1, RT_STACK in *; lia) ltac:(clear - NUM; lia) UT4 (proj2 (af_acc_live RT AF Σ2 m4 E 904 ART4 INE2)) FR4 TB4 MI4).
  cl_lift WZ Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (a1' & m5 & -> & MU5 & WM5 & MI5 & TB5 & ST5) & Hc5'). clear Hc5.
  fold usp in ST5.
  (* [comment removed for export] *)
  assert (MU5' : munch ([(E + 896, E + 904)] ++ [(usp - 0, usp)]) m4 m5) by (eapply munch_weaken; [| exact MU5]; unfold sub_fp; cbn [outside app]; intros; tauto).
  assert (ART5 : ART RT Σ2 m5).
  { apply (wg_seg_ART RT AF Σ2 m4 m5 usp 0 _ ART4 ltac:(rewrite SP2, SP1; clear - NUM; lia) ltac:(clear - NUM; lia) MU5'); [| exact WM5]. intros x Hx. right. exists E, 904. split; [exact INE2|]. cbn [outside] in Hx. clear - Hx. lia. }
  assert (APART : forall p n, In (p, n) ([(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ rt_live RT Σ) -> E + 904 <= p \/ p + n <= E)
    by (intros p n Hin; exact (wg_live_apart RT AF Σ1 m2 _ E 904 _ p n ART2 LV1 Hin)).
  assert (K25 : forall a cs, rw_cells asegs m2 a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x) ->
            (a + Z.of_nat (cells_size cs) <= E \/ E + 904 <= a) -> rw_cells asegs m5 a cs).
  { intros a cs Hc HAc HD. apply (rw_cells_agree asegs m2 m5 _ _ Hc); [| exact (wmono_trans asegs _ _ _ WM4 WM5)]. intros x Hx.
    rewrite (MU5 x ltac:(cbn [outside]; clear - Hx HD; lia)). apply PRES4; [exact (HAc _ Hx)|]. cbn [outside]. clear - Hx HD. lia. }
  assert (K25s : forall a cs, rw_cells asegs m2 a cs ->
            (0xb8f190 <= a /\ a + Z.of_nat (cells_size cs) <= 0xba3e98) \/ (0xbc52a0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbc57d0) -> rw_cells asegs m5 a cs).
  { intros a cs Hc Hn. apply (K25 a cs Hc); [| clear - Hn EH; lia]. intros x Hx. right; left. apply client_static_intro. clear - Hn Hx. lia. }
  apply Hk. exists Σ2, E, N, H, G, SK, LK, D, u', top'.
  split; [| rewrite LV2, FRS2, SP2, CR2, CG2; exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 (conj CG1 (conj E0 (conj E16 EUP)))))))].
  eapply ASTA_conseq; [exact Hc5'|]. intros ms <-. exists m5.
  split; [exists v0, v1, v2, a1', d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F4, fc4; reflexivity|].
  split; [exact (conj ART5 (conj MI5 (conj (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM4 WM5))) ST5)))|].
  split.
  { (* [comment removed for export] *)
    intros a Ha Ho.
    pose proof (wg_newchunk_apart RT AF Σ Σ1 m2 [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8); (E, 904)] E 904 usp (bv_unsigned a) ART2
                  ltac:(rewrite LV1; reflexivity) ltac:(cbn [In]; do 6 right; left; reflexivity) FRS1 SP1 ltac:(clear - NUM; lia) ltac:(clear; lia) Ha) as NE.
    pose proof (cl_split RT AF Σ m usp 96 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Ha) as SPL.
    rewrite (MU5 a ltac:(cbn [outside]; clear - NE SPL; lia)).
    assert (A1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 (bv_unsigned a)).
    { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV1; apply in_or_app; right; right; exact He | rewrite FRS1; intros e He; exact He | clear; unfold usp1; lia]. }
    rewrite (PRES4 a A1 ltac:(cbn [outside]; clear - NE; lia)).
    assert (A2 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | clear; unfold usp1; lia]).
    rewrite (PRES2 a A2 Ho). exact (PR1 a Ha I). }
  split; [exact (cl_env_seg _ m4 m5 _ canary CLE4 MU5 ltac:(first [solve [clear - EH; cl_fp_lia] | cl_fp_lia]))|].
  split; [exact (K25s _ _ D1 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear; lia))|].
  split; [exact (K25s _ _ D2 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear; lia))|].
  split; [exact (K25s _ _ D3 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear; lia))|].
  split; [exact (K25s _ _ D4 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear; lia))|].
  split; [exact (K25 _ _ D5 ltac:(unfold sa_hdr; cbn [cells_size csize Nat.add]; intros x Hx; right; right; left; exists SA, 32; split; [rewrite LV1; apply in_or_app; right; right; exact INSA | clear - Hx; lia])
                     ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; apply or_comm; apply (APART SA 32); apply in_or_app; right; exact INSA))|].
  split; [exact D6|].
  split; [exact (K25 _ _ D7 ltac:(cbn [cells_size csize Nat.add]; intros x Hx; right; right; left; exists P, 128; split; [rewrite LV1; apply in_or_app; right; right; exact INP | clear - Hx; lia])
                     ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; apply or_comm; apply (APART P 128); apply in_or_app; right; exact INP))|].
  split.
  { destruct ARR4 as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _). unfold ecl_arrs. cbn [Nat.sub repeat app] in R0, R1, R2, R3, R4, R5, R6, R7, R8 |- *.
    assert (K45 : forall a cs, rw_cells asegs m4 a cs -> a + Z.of_nat (cells_size cs) <= E + 896 -> rw_cells asegs m5 a cs)
      by (intros a cs Hc Hb; apply (wg_keep_seg _ m4 m5 _ _ Hc MU5 WM5); intros x Hx; cbn [outside]; clear - Hx Hb; lia).
    cbn [Nat.sub repeat app] in R0, R1, R2, R3, R4, R5, R6, R7, R8 |- *. unfold ecl_arrs. cbn [Nat.sub repeat app].
    Ltac k45 K R := exact (K _ _ R ltac:(cbn [cells_size csize Nat.add repeat app]; clear; lia)).
    split; [k45 K45 R0|]. split; [k45 K45 R1|]. split; [k45 K45 R2|]. split; [k45 K45 R3|]. split; [k45 K45 R4|].
    split; [k45 K45 R5|]. split; [k45 K45 R6|]. split; [k45 K45 R7|]. split; [k45 K45 R8|]. exact TB5. }
  split; [exact (K25s _ _ D10 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear - HKD; lia))|].
  split; [exact (K25s _ _ D11 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear; lia))|].
  split; [exact (K25s _ _ D12 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear; lia))|].
  split; [exact (K25s _ _ D13 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear; lia))|].
  split; [exact (K25s _ _ D14 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear; lia))|].
  split; [exact (K25s _ _ D15 ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; clear; lia))|].
  split; [exact (K25 _ _ D16 ltac:(cbn [cells_size csize Nat.add]; intros x Hx; right; right; left; exists H, 8; split; [rewrite LV1; cbn [In app]; tauto | clear - Hx; lia])
                     ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; apply or_comm; apply (APART H 8); cbn [In app]; tauto))|].
  split; [exact (K25 _ _ D17 ltac:(cbn [cells_size csize Nat.add]; intros x Hx; right; right; left; exists N, 32; split; [rewrite LV1; cbn [In app]; tauto | clear - Hx; lia])
                     ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; apply or_comm; apply (APART N 32); cbn [In app]; tauto))|].
  split; [exact (K25 _ _ D18 ltac:(cbn [cells_size csize Nat.add]; intros x Hx; right; right; left; exists G, 16; split; [rewrite LV1; cbn [In app]; tauto | clear - Hx; lia])
                     ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; apply or_comm; apply (APART G 16); cbn [In app]; tauto))|].
  split; [exact (K25 _ _ D19 ltac:(unfold mutex_cells; cbn [cells_size csize Nat.add]; intros x Hx; right; right; left; exists LK, 40; split; [rewrite LV1; cbn [In app]; tauto | clear - Hx; lia])
                     ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; apply or_comm; apply (APART LK 40); cbn [In app]; tauto))|].
  exact (K25 _ _ D20 ltac:(cbn [cells_size csize Nat.add]; intros x Hx; right; right; left; exists D, 32; split; [rewrite LV1; cbn [In app]; tauto | clear - Hx; lia])
              ltac:(cbn [cells_size csize Nat.add sa_hdr mutex_cells app]; apply or_comm; apply (APART D 32); cbn [In app]; tauto)).
Qed.
End Eclear.
