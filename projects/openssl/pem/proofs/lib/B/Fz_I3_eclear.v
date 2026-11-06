(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OSSVerify.Proofs.openssl.pem.lib.B Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Fz_M_zalloc Fz_M_free Th_tsd Th_key Th_once Th_mutex Fz_T_once Fz_T_local Fz_T_sa Fz_T_sa_set Fz_T_master Fz_T_sk Fz_T_mtl Fz_T_its Fz_W5_glx Fz_W5_icb Fz_W5_gsi Fz_W5_gsi0 Fz_I3_glx0 Fz_G_OSSL_ERR_STATE_new Fz_I3_icfast Fz_I3_egsiw Fz_I3_egsi Fz_I3_eclw Fz_W5_rep Fz_W5_agr Fz_W5_eclr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Notation TP_A := (0xbd66f0)%Z (only parsing).

(* [comment removed for export] *)
Lemma cells_size_repeat : forall c k, cells_size (repeat c k) = (k * csize c)%nat.
Proof. intros c k. induction k as [|k IH]; cbn [repeat cells_size]; [reflexivity|]. cbn [cells_size] in IH. rewrite IH. lia. Qed.

Lemma cells_size_pre : forall c c' k, csize c' = csize c -> cells_size (repeat c' k) = (k * csize c)%nat.
Proof. intros c c' k E. rewrite cells_size_repeat, E. reflexivity. Qed.

Lemma repeat_snoc : forall {X} (c : X) k, repeat c (S k) = repeat c k ++ [c].
Proof. intros X c k. induction k as [|k IH]; [reflexivity|]. cbn [repeat app]. cbn [repeat] in IH. rewrite IH at 1. reflexivity. Qed.

(* [comment removed for export] *)
Lemma arr_get : forall (m : mem) A c c' (k n : nat), rw_cells bsegs m A (repeat c' k ++ repeat c (n - k)) -> (k < n)%nat -> csize c' = csize c ->
  rw_cells bsegs m (A + Z.of_nat (k * csize c)) [c].
Proof.
  intros m A c c' k n H Hk E. apply (proj1 (rw_cells_app m A _ _)) in H as [_ H2]. rewrite (cells_size_pre c c' k E) in H2.
  replace (n - k)%nat with (S (n - S k)) in H2 by lia. cbn [repeat] in H2. exact (rw_cells_head m _ c _ H2).
Qed.

(* [comment removed for export] *)
Lemma arr_step : forall (m m' : mem) A c c' (k n : nat), rw_cells bsegs m A (repeat c' k ++ repeat c (n - k)) -> (k < n)%nat -> csize c' = csize c ->
  wmono bsegs m m' ->
  (forall x : word, A <= bv_unsigned x < A + Z.of_nat (n * csize c) ->
     ~ (A + Z.of_nat (k * csize c) <= bv_unsigned x < A + Z.of_nat (k * csize c) + Z.of_nat (csize c)) -> m' x = m x) ->
  rw_cells bsegs m' (A + Z.of_nat (k * csize c)) [c'] ->
  rw_cells bsegs m' A (repeat c' (S k) ++ repeat c (n - S k)).
Proof.
  intros m m' A c c' k n H Hk E WM AG NEWc.
  apply (proj1 (rw_cells_app m A _ _)) in H as [H1 H2]. rewrite (cells_size_pre c c' k E) in H2.
  replace (n - k)%nat with (S (n - S k)) in H2 by lia. cbn [repeat] in H2. apply rw_cells_tail in H2.
  pose proof (rw_cells_bound _ _ _ _ H2) as B2. rewrite cells_size_repeat in B2.
  rewrite repeat_snoc, <- app_assoc. cbn [app].
  apply (proj2 (rw_cells_app m' A _ _)). rewrite (cells_size_pre c c' k E). split.
  - apply (rw_cells_agree bsegs m m' _ _ H1); [| exact WM]. rewrite (cells_size_pre c c' k E). intros x Hx. apply AG; nia.
  - apply (proj2 (rw_cells_app m' _ [c'] _)). split; [exact NEWc|]. cbn [cells_size Nat.add]. rewrite Nat.add_0_r, E.
    apply (rw_cells_agree bsegs m m' _ _ H2); [| exact WM]. rewrite cells_size_repeat. intros x Hx. apply AG; nia.
Qed.

(* [comment removed for export] *)
Definition zb4 : cell := CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Definition ecl_arrs (m : mem) (E : Z) (k : nat) : Prop :=
  rw_cells bsegs m E (repeat (C4 z64) k ++ repeat (C4 z64) (16 - k))
  /\ rw_cells bsegs m (E + 64) (repeat (C4 z64) k ++ repeat (C4 z64) (16 - k))
  /\ rw_cells bsegs m (E + 128) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells bsegs m (E + 256) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells bsegs m (E + 384) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells bsegs m (E + 512) (repeat (C4 z64) k ++ repeat zb4 (16 - k))
  /\ rw_cells bsegs m (E + 576) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells bsegs m (E + 704) (repeat (C4 ECL_LNW) k ++ repeat (C4 z64) (16 - k))
  /\ rw_cells bsegs m (E + 768) (repeat (C8 z64) k ++ repeat (C8 z64) (16 - k))
  /\ rw_cells bsegs m (E + 896) [C4 z64; C4 z64].

Lemma rw_CB_of_bytes_ec : forall (m : mem) a bs, bytes_at bsegs m a bs -> wr_at bsegs m a (Z.of_nat (length bs)) -> rw_cells bsegs m a [CB (length bs) bs].
Proof.
  intros m a bs BA WR. split.
  - split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA].
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact WR.
Qed.

(* [comment removed for export] *)
Lemma ecl_arrs_of_zeros : forall (m : mem) E, bytes_at bsegs m E (repeat (Z_to_bv 8 0) (Z.to_nat 904)) -> wr_at bsegs m E 904 -> ecl_arrs m E 0.
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
  rw_cells bsegs m (E + 4 * Z.of_nat k) [C4 z64] /\ rw_cells bsegs m (E + 4 * Z.of_nat k + 64) [C4 z64] /\ rw_cells bsegs m (E + 8 * Z.of_nat k + 128) [C8 z64]
  /\ rw_cells bsegs m (E + 8 * Z.of_nat k + 256) [C8 z64] /\ rw_cells bsegs m (E + 8 * Z.of_nat k + 384) [C8 z64] /\ rw_cells bsegs m (E + 4 * Z.of_nat k + 512) [zb4]
  /\ rw_cells bsegs m (E + 8 * Z.of_nat k + 576) [C8 z64] /\ rw_cells bsegs m (E + 4 * Z.of_nat k + 704) [C4 z64] /\ rw_cells bsegs m (E + 8 * Z.of_nat k + 768) [C8 z64].
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
Lemma ecl_arrs_step : forall (m m' : mem) E (k : nat), (k < 16)%nat -> ecl_arrs m E k -> wmono bsegs m m' ->
  (forall x : word, E <= bv_unsigned x < E + 904 -> outside (ecl_W E (Z.of_nat k)) (bv_unsigned x) -> m' x = m x) ->
  rw_cells bsegs m' (E + 4 * Z.of_nat k) [C4 z64] -> rw_cells bsegs m' (E + 4 * Z.of_nat k + 64) [C4 z64] -> rw_cells bsegs m' (E + 8 * Z.of_nat k + 128) [C8 z64] ->
  rw_cells bsegs m' (E + 8 * Z.of_nat k + 256) [C8 z64] -> rw_cells bsegs m' (E + 8 * Z.of_nat k + 384) [C8 z64] -> rw_cells bsegs m' (E + 4 * Z.of_nat k + 512) [C4 z64] ->
  rw_cells bsegs m' (E + 8 * Z.of_nat k + 576) [C8 z64] -> rw_cells bsegs m' (E + 4 * Z.of_nat k + 704) [C4 ECL_LNW] -> rw_cells bsegs m' (E + 8 * Z.of_nat k + 768) [C8 z64] ->
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
  apply (rw_cells_agree bsegs m m' _ _ A9); [| exact WM]. cbn [cells_size csize Nat.add]. intros x Hx. apply AG; [lia|]. unfold ecl_W. cbn [outside]. repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition ECLR_SITES : list (Z * Z) := [(SITE_ecl_egsi, e_eclear)] ++ ECL_SITES ++ EG_SITES.
Definition ECLR_CALLS : list (Z * Z) := [(SITE_ecl_egsi, e_get_state)] ++ ECL_CALLS ++ EG_CALLS.

Definition eclear_first_stmt (RT : rt_sig) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (k kd MK SA P : Z) (pad top : word) (jm1 jm2 jp : list byte) (u : byte) (r0 g0 oldcb : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x3c0 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_eclear (bv_unsigned ra :: outer) -> uw_chain m sp s0 outer -> cg_has (rt_cg RT Σ) ECLR_SITES ECLR_CALLS ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 7 <= LIVE_MAX -> 3 + mcost 904 <= rt_credit RT Σ -> cl_env m lb canary ->
  (* [comment removed for export] *)
  rw_cells bsegs m G_IC_STOPPED [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m G_IC_OPTSDONE [C8 (Z_to_bv 64 2)] ->
  rw_cells bsegs m G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells bsegs m G_IC_BASE_RET [C4 (Z_to_bv 64 1)] ->
  (* [comment removed for export] *)
  rw_cells bsegs m MK_ONCE [C4 (Z_to_bv 64 2)] -> rw_cells bsegs m MK_KEY [C4 (Z_to_bv 64 k)] -> 1 <= k < 128 ->
  rw_cells bsegs m (TSD_MAIN + 8 * k) [C8 (Z_to_bv 64 MK)] -> In (MK, 72) (rt_live RT Σ) -> In (SA, 32) (rt_live RT Σ) -> In (P, 128) (rt_live RT Σ) ->
  MK mod 16 = 0 -> SA mod 16 = 0 -> P mod 16 = 0 -> (SA + 32 <= P \/ P + 128 <= SA) -> (SA + 32 <= MK \/ MK + 72 <= SA) -> (P + 128 <= MK \/ MK + 72 <= P) ->
  rw_cells bsegs m MK [CB 24 jm1; C8 (Z_to_bv 64 SA); CB 40 jm2] ->
  rw_cells bsegs m SA (sa_hdr (Z_to_bv 64 1) pad top (Z_to_bv 64 0) (Z_to_bv 64 P)) -> rw_cells bsegs m P [C8 (Z_to_bv 64 0); CB 120 jp] ->
  (* [comment removed for export] *)
  rw_cells bsegs m DTOR_KEY [C4 (Z_to_bv 64 kd); C4 (Z_to_bv 64 0xffffffff)] -> 1 <= kd < 128 -> k <> kd -> rw_cells bsegs m (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (TP_A + -150) [C1 u] -> rw_cells bsegs m TEV_ONCE [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m TEV_RET [C4 r0] -> rw_cells bsegs m TEV_REG [C8 g0] ->
  rw_cells bsegs m (TP_A + -96) [C8 oldcb] ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_eclear m)))
    (fun c => exists (Σ' : rts RT) (E N H G SK LK D : Z) (u' : byte) (top' : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (E + 896)) m' ms
           /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (EG_W kd SA P) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells bsegs m' G_IC_STOPPED [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m' G_IC_OPTSDONE [C8 (Z_to_bv 64 2)]
           /\ rw_cells bsegs m' G_IC_BASE_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells bsegs m' G_IC_BASE_RET [C4 (Z_to_bv 64 1)]
           /\ rw_cells bsegs m' SA (sa_hdr (Z_to_bv 64 1) pad top' (Z_to_bv 64 1) (Z_to_bv 64 P)) /\ bv_unsigned top' = Z.max (bv_unsigned top) 0
           /\ rw_cells bsegs m' P [C8 (Z_to_bv 64 E); CB 120 jp]
           /\ ecl_arrs m' E 16
           /\ rw_cells bsegs m' (TSD_MAIN + 8 * kd) [C8 (Z_to_bv 64 H)] /\ rw_cells bsegs m' (TP_A + -150) [C1 u']
           /\ rw_cells bsegs m' TEV_ONCE [C4 (Z_to_bv 64 2)] /\ rw_cells bsegs m' TEV_RET [C4 (Z_to_bv 64 1)] /\ rw_cells bsegs m' TEV_REG [C8 (Z_to_bv 64 G)]
           /\ rw_cells bsegs m' (TP_A + -96) [C8 oldcb]
           /\ rw_cells bsegs m' H [C8 (Z_to_bv 64 N)] /\ rw_cells bsegs m' N [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 ERR_DEL_THREAD_STATE); C8 (Z_to_bv 64 0)]
           /\ rw_cells bsegs m' G [C8 (Z_to_bv 64 SK); C8 (Z_to_bv 64 LK)] /\ rw_cells bsegs m' LK (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells bsegs m' D [C8 (Z_to_bv 64 H); CB 24 (repeat (Z_to_bv 8 0) 24)]) c
       /\ rt_live RT Σ' = [(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ (E, 904) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - 3 - mcost 904 <= rt_credit RT Σ' /\ rt_cg RT Σ' = rt_cg RT Σ
       /\ 0 < E /\ E mod 16 = 0 /\ E + 904 < USTACK_TOP).

(* [comment removed for export] *)
Definition EZ16 : list word := repeat z64 16.
Definition ecl_ls (k : nat) : list word := repeat ECL_LNW k ++ repeat z64 (16 - k).

Lemma ec_rw_u32 : forall (m : mem) A cs ws, rw_cells bsegs m A cs -> cells_bytes cs = u32s ws -> cells_size cs = (4 * length ws)%nat -> u32arr bsegs m A ws.
Proof. intros m A cs ws [[WF B] W] E1 E2. split; [rewrite <- E1; exact B | rewrite E2 in W; rewrite Nat2Z.inj_mul in W; exact W]. Qed.
Lemma ec_rw_u64 : forall (m : mem) A cs ws, rw_cells bsegs m A cs -> cells_bytes cs = u64s ws -> cells_size cs = (8 * length ws)%nat -> u64arr bsegs m A ws.
Proof. intros m A cs ws [[WF B] W] E1 E2. split; [rewrite <- E1; exact B | rewrite E2 in W; rewrite Nat2Z.inj_mul in W; exact W]. Qed.
Lemma ec_rw_u8 : forall (m : mem) A cs bs, rw_cells bsegs m A cs -> cells_bytes cs = bs -> cells_size cs = length bs -> u8arr bsegs m A bs.
Proof. intros m A cs bs [[WF B] W] E1 E2. split; [rewrite <- E1; exact B | rewrite E2 in W; exact W]. Qed.
Lemma ec_u32_rw : forall (m : mem) A ws cs, u32arr bsegs m A ws -> cells_wf cs -> cells_bytes cs = u32s ws -> cells_size cs = (4 * length ws)%nat -> rw_cells bsegs m A cs.
Proof. intros m A ws cs [B W] WF E1 E2. split; [split; [exact WF | rewrite E1; exact B]|]. rewrite E2, Nat2Z.inj_mul. exact W. Qed.
Lemma ec_u64_rw : forall (m : mem) A ws cs, u64arr bsegs m A ws -> cells_wf cs -> cells_bytes cs = u64s ws -> cells_size cs = (8 * length ws)%nat -> rw_cells bsegs m A cs.
Proof. intros m A ws cs [B W] WF E1 E2. split; [split; [exact WF | rewrite E1; exact B]|]. rewrite E2, Nat2Z.inj_mul. exact W. Qed.
Lemma ec_u8_rw : forall (m : mem) A bs cs, u8arr bsegs m A bs -> cells_wf cs -> cells_bytes cs = bs -> cells_size cs = length bs -> rw_cells bsegs m A cs.
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
  rw_cells bsegs m E (repeat (C4 z64) 16) /\ rw_cells bsegs m (E + 64) (repeat (C4 z64) 16) /\ rw_cells bsegs m (E + 128) (repeat (C8 z64) 16)
  /\ rw_cells bsegs m (E + 256) (repeat (C8 z64) 16) /\ rw_cells bsegs m (E + 384) (repeat (C8 z64) 16) /\ rw_cells bsegs m (E + 512) (repeat (C4 z64) 16)
  /\ rw_cells bsegs m (E + 576) (repeat (C8 z64) 16) /\ rw_cells bsegs m (E + 704) (repeat (C4 ECL_LNW) 16) /\ rw_cells bsegs m (E + 768) (repeat (C8 z64) 16)
  /\ rw_cells bsegs m (E + 896) [C4 (Z_to_bv 64 top); C4 (Z_to_bv 64 bot)].
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

(* [comment removed for export] *)
Definition ecl_frame (s4e s3e s2e s1e s0e rae : word) : list cell := [C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae].

Section Eclear.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_ECR : err_clear_stmt RT.
Hypothesis C_EGSI : egsi_first_stmt RT.

(* [comment removed for export] *)
Definition ecl_loop_stmt (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (sp spi gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (E : Z) (s4e s3e s2e s1e s0e rae : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  (k < 16)%nat -> E mod 8 = 0 -> In (E, 904) (rt_live RT Σ) ->
  bv_unsigned spi = bv_unsigned sp - 48 -> bv_unsigned sp + 16 <= USTACK_TOP ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m spi lo -> lo + RT_STACK + 96 <= bv_unsigned spi ->
  cg_ctx (rt_cg RT Σ) e_eclear (bv_unsigned rae :: outer) -> uw_chain m sp s0e outer -> cg_has (rt_cg RT Σ) ECL_SITES ECL_CALLS ->
  cl_env m lb canary ->
  rw_cells bsegs m (bv_unsigned spi) (ecl_frame s4e s3e s2e s1e s0e rae) ->
  es_rep m E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls k) EZ16 ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra spi gp tp t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 SHB) (Z_to_bv 64 16)
                                        s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 ECL_LOOP) fc None m (seg_rom bsegs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
         ms = MS (mkR ra' spi gp tp t0' t1' t2' sp (Z_to_bv 64 E) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 16) (Z_to_bv 64 SHB) (Z_to_bv 64 16)
                      s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F' (Z_to_bv 64 ECL_DONE) fc' None m' (seg_rom bsegs)
         /\ rt_after RT Σ' (bv_unsigned spi) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned spi) [(E, E + 904)] m m'
         /\ cl_env m' lb canary
         /\ rw_cells bsegs m' (bv_unsigned spi) (ecl_frame s4e s3e s2e s1e s0e rae)
         /\ es_rep m' E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls 16) EZ16) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).

(* [comment removed for export] *)
Lemma ecl_iter : forall (k : nat) (Σ : rts RT) PMc (sp spi gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (E : Z) (s4e s3e s2e s1e s0e rae : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  (k < 16)%nat -> E mod 8 = 0 -> In (E, 904) (rt_live RT Σ) ->
  bv_unsigned spi = bv_unsigned sp - 48 -> bv_unsigned sp + 16 <= USTACK_TOP ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m spi lo -> lo + RT_STACK + 96 <= bv_unsigned spi ->
  cg_ctx (rt_cg RT Σ) e_eclear (bv_unsigned rae :: outer) -> uw_chain m sp s0e outer -> cg_has (rt_cg RT Σ) ECL_SITES ECL_CALLS ->
  cl_env m lb canary ->
  rw_cells bsegs m (bv_unsigned spi) (ecl_frame s4e s3e s2e s1e s0e rae) ->
  es_rep m E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls k) EZ16 ->
  cps bsegs (ASTA RT Σ PMc (eq (MS (mkR ra spi gp tp t0 t1 t2 sp (Z_to_bv 64 E) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 SHB) (Z_to_bv 64 16)
                                        s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 ECL_LOOP) fc None m (seg_rom bsegs))))
    (fun c => exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
         ms = MS (mkR (Z_to_bv 64 SITE_ecl_call) spi gp tp t0' t1' t2' sp (Z_to_bv 64 E) a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (Z.of_nat k + 1)) (Z_to_bv 64 SHB) (Z_to_bv 64 16)
                      s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F' (Z_to_bv 64 (ecl_next (Z.of_nat k))) fc' None m' (seg_rom bsegs)
         /\ rt_after RT Σ' (bv_unsigned spi) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned spi) [(E, E + 904)] m m'
         /\ cl_env m' lb canary
         /\ es_rep m' E 0 0 EZ16 EZ16 EZ16 EZ16 (ecl_ls (S k)) EZ16) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_cg RT Σ' = rt_cg RT Σ).
Proof.
  intros k Σ PMc sp spi gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m lo outer lb canary E s4e s3e s2e s1e s0e rae
    FDO MST -> HK E8 INE HU SPT0 ART0 MI0 CALL HSTK CTX UWC CGH ENV FR ES.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *. set (uspi := bv_unsigned spi) in *.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & _ & _ & _ & UT).
  (* [comment removed for export] *)
  pose proof (ecl_wcall spi gp (Z_to_bv 64 TP_A) t0 t1 t2 sp a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m E (Z.of_nat k) UT) as W.
  cl_lift W HA c1 Hc1. destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & <- & Hc1'). clear Hc1.
  destruct (cl_chain_call (rt_cg RT Σ) e_eclear e_err_clear SITE_ecl_call m m rae s0e sp spi outer CTX
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWC ltac:(intros a Ha; reflexivity)
              ltac:(fold usp; replace (usp - 16) with (uspi + Z.of_nat (cells_size [C8 s4e; C8 s3e; C8 s2e; C8 s1e])) by (cbn [cells_size csize Nat.add]; clear - HU; unfold uspi, usp in *; lia);
                    exact (rw_cells_skip m uspi [C8 s4e; C8 s3e; C8 s2e; C8 s1e] [C8 s0e; C8 rae] FR))
              ltac:(fold usp uspi; clear - HU; unfold usp, uspi in *; lia) SPT0) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_ECR Σ PMc (Z_to_bv 64 SITE_ecl_call) spi gp (Z_to_bv 64 TP_A) t0 t1 t2 sp (Z_to_bv 64 E) (Z_to_bv 64 E) (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
           (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 SHB) (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo (bv_unsigned rae :: outer) [E] E (Z.of_nat k) 0 0
           EZ16 EZ16 EZ16 EZ16 (ecl_ls k) EZ16 (Z_to_bv 64 0) (Z_to_bv 64 0) lb canary FDO MST eq_refl eq_refl eq_refl ART0 MI0 CALL HSTK).
  { rewrite (unsigned_lit SITE_ecl_call) by (unfold SITE_ecl_call; clear; lia). exact CTXc1. }
  { exact UWCc1. }
  { apply (cg_has_sub _ _ _ _ _ CGH); unfold ECR_SITES, ECR_CALLS, ECL_SITES, ECL_CALLS; intros e He; cbn [In] in He |- *; tauto. }
  { exact INE. } { exact E8. } { left; reflexivity. } { exact ES. } { clear - HK; lia. }
  { rewrite Nat2Z.id. unfold EZ16. apply nth_error_repeat. exact HK. }
  { rewrite Nat2Z.id. unfold EZ16. apply nth_error_repeat. exact HK. }
  { left. apply unsigned_lit. clear; lia. } { left. apply unsigned_lit. clear; lia. }
  { intros X. exfalso. apply X. apply unsigned_lit. clear; lia. }
  { exact ENV. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ2 & v & Hc2 & LV2 & FRS2 & SP2 & CR2 & CG2).
  assert (Z0 : bv_unsigned (Z_to_bv 64 0) = 0) by (apply unsigned_lit; clear; lia).
  unfold rmw in LV2. rewrite Z0 in LV2. cbn [Z.eqb] in LV2.
  destruct (ASTA_unpack RT Σ2 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & WMI & PRES2 & ES2 & ENV2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  pose proof (WMI Z0 Z0) as WM2. fold uspi in ST2, PRES2.
  rewrite (ret_pc_even SITE_ecl_call) in Hc2' by (unfold SITE_ecl_call; lia).
  destruct (af_client_consts RT AF Σ2 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  pose proof (ecl_wnext spi gp (Z_to_bv 64 TP_A) u0 u1 u2 sp v b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 (Z_to_bv 64 SITE_ecl_call) F2 fc2 m2 E (Z.of_nat k)
                ltac:(clear - HK; lia) UT2) as W.
  cl_lift W Hc2' c3 Hc3. destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.
  apply Hk. exists Σ2. split; [| rewrite LV2; exact (conj eq_refl (conj FRS2 (conj SP2 (conj CR2 CG2))))].
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-.
  exists u0, u1, u2, v, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F2, fc2, m2.
  split; [reflexivity|]. split; [exact (conj ART2 (conj MI2 (conj WM2 ST2)))|].
  split; [rewrite LV2 in PRES2; exact PRES2|]. split; [exact ENV2|].
  rewrite Nat2Z.id in ES2. rewrite !upd_repeat_same in ES2. unfold ECR_LNW in ES2. change (Z_to_bv 64 (-1)) with ECL_LNW in ES2. rewrite (upd_ecl_ls k HK) in ES2. exact ES2.
Qed.

Lemma ecl_loop_ind : forall (n k : nat), (k + n = 15)%nat -> ecl_loop_stmt k.
Proof.
  induction n as [|n IH]; intros k Hkn.
  - (* [comment removed for export] *)
    assert (Hk : k = 15%nat) by lia. subst k. clear Hkn.
    intros Σ PMc sp spi gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m lo outer lb canary E s4e s3e s2e s1e s0e rae
      FDO MST TP HK E8 INE HU SPT0 ART0 MI0 CALL HSTK CTX UWC CGH ENV FR ES.
    intros T c HA Hk.
    apply (ecl_iter 15 Σ PMc sp spi gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m lo outer lb canary E s4e s3e s2e s1e s0e rae
             FDO MST TP HK E8 INE HU SPT0 ART0 MI0 CALL HSTK CTX UWC CGH ENV FR ES T c HA).
    intros c1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1 & CG1). apply Hk. exists Σ1. split; [| exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 CG1))))].
    eapply ASTA_conseq; [exact Hc1|].
    intros ms (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & -> & RA & PRES & ENV' & ES').
    exists (Z_to_bv 64 SITE_ecl_call), u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F', fc', m'.
    split; [reflexivity|]. split; [exact RA|]. split; [exact PRES|]. split; [exact ENV'|]. split; [| exact ES'].
    destruct RA as (ART1 & MI1 & WM1 & ST1). pose proof CALL as (ST & LOW & LOR & SPT & SPA).
    pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as (_ & ELO & _).
    apply (rw_cells_agree bsegs m m' _ _ FR); [| exact WM1]. unfold ecl_frame. cbn [cells_size csize Nat.add]. intros x Hx. apply PRES; [left|].
    { clear - Hx HU SPT SPT0. unfold USTACK_TOP in *. lia. }
    cbn [outside]. clear - Hx ELO LOW LOR. unfold RT_STACK in *. repeat split; lia.
  - (* [comment removed for export] *)
    assert (HK15 : (k < 15)%nat) by lia.
    intros Σ PMc sp spi gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m lo outer lb canary E s4e s3e s2e s1e s0e rae
      FDO MST TP HK E8 INE HU SPT0 ART0 MI0 CALL HSTK CTX UWC CGH ENV FR ES.
    intros T c HA Hk.
    apply (ecl_iter k Σ PMc sp spi gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m lo outer lb canary E s4e s3e s2e s1e s0e rae
             FDO MST TP HK E8 INE HU SPT0 ART0 MI0 CALL HSTK CTX UWC CGH ENV FR ES T c HA).
    intros c1 (Σ1 & Hc1 & LV1 & FRS1 & SP1 & CR1 & CG1).
    destruct (ASTA_unpack RT Σ1 _ _ c1 Hc1) as (ms1 & (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & -> & RA1 & PRES1 & ENV1 & ES1) & Hc1'). clear Hc1.
    destruct RA1 as (ART1 & MI1 & WM1 & ST1).
    pose proof CALL as (ST & LOW & LOR & SPT & SPA). pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as (_ & ELO & _).
    assert (AGS : agree_on (fun x => bv_unsigned spi <= x < USTACK_TOP) m m1).
    { intros x Hx. cbv beta in Hx. apply PRES1; [left; exact Hx|]. cbn [outside]. clear - Hx ELO LOW LOR. unfold RT_STACK in *. repeat split; lia. }
    assert (FR1 : rw_cells bsegs m1 (bv_unsigned spi) (ecl_frame s4e s3e s2e s1e s0e rae)).
    { apply (rw_cells_agree bsegs m m1 _ _ FR); [| exact WM1]. unfold ecl_frame. cbn [cells_size csize Nat.add]. intros x Hx. apply AGS. cbv beta. clear - Hx HU SPT SPT0. unfold USTACK_TOP in *. lia. }
    unfold ecl_next in Hc1'. replace (Z.of_nat k =? 15) with false in Hc1' by (symmetry; apply Z.eqb_neq; clear - HK15; lia).
    replace (Z.of_nat k + 1) with (Z.of_nat (S k)) in Hc1' by (clear; lia).
    rewrite <- CG1 in CTX, CGH. rewrite <- LV1 in INE.
    apply (IH (S k) ltac:(clear - Hkn; lia) Σ1 PMc sp spi gp tp u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 (Z_to_bv 64 SITE_ecl_call) F1 fc1 m1 lo outer lb canary E
             s4e s3e s2e s1e s0e rae FDO MST TP ltac:(clear - HK15; lia) E8 INE HU SPT0 ART1 MI1
             ltac:(rewrite <- SP1 in LOW; exact (conj ST1 (conj LOW (conj LOR (conj SPT SPA))))) HSTK CTX
             (uw_chain_agree outer m m1 sp s0e UWC ltac:(intros x Hx; apply AGS; cbv beta in Hx |- *; clear - Hx HU; lia)) CGH ENV1 FR1 ES1 T c1 Hc1').
    intros c2 (Σ2 & Hc2 & LV2 & FRS2 & SP2 & CR2 & CG2). apply Hk. exists Σ2.
    split; [| rewrite LV2, FRS2, SP2, CR2, CG2; exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 CG1))))].
    eapply ASTA_conseq; [exact Hc2|].
    intros ms (r' & v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F2 & fc2 & m2 & -> & RA2 & PRES2 & ENV2 & FR2 & ES2).
    exists r', v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, F2, fc2, m2. split; [reflexivity|].
    destruct RA2 as (ART2 & MI2 & WM2 & ST2).
    split; [exact (conj ART2 (conj MI2 (conj (wmono_trans bsegs _ _ _ WM1 WM2) ST2)))|].
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
  set (usp1 := usp + -48). cl_eu usp (-48) EU1. fold usp1 in EU1.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  pose proof (af_live_range RT AF Σ m MK 72 ART0 INMK) as (MK0 & MKLO & _). pose proof (af_live_range RT AF Σ m SA 32 ART0 INSA) as (SA0 & SALO & _).
  pose proof (af_live_range RT AF Σ m P 128 ART0 INP) as (P0 & PLO & _).
  (* [comment removed for export] *)
  pose proof (ecl_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(clear - NUM; lia) ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(clear - NUM; lia) UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, ST1, Hc1'. fold usp1 in FR1, ST1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 48, usp)]) m m1) by exact MU1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 48 [] ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 48 [] ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) MU1') as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (STAT1 : forall a cs, rw_cells bsegs m a cs -> a + Z.of_nat (cells_size cs) <= lo -> rw_cells bsegs m1 a cs).
  { intros a cs H R. apply (wg_keep_seg _ m m1 _ _ H MU1 WM1). intros x Hx. cbn [app outside]. clear - Hx R NUM HSTK. unfold RT_STACK in *. lia. }
  pose proof (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(first [solve [clear - NUM HSTK; unfold RT_STACK in *; cl_fp_lia] | cl_fp_lia])) as CLE1.
  destruct (cl_chain_call (rt_cg RT Σ) e_eclear e_get_state SITE_ecl_egsi m m1 ra s0 sp (Z_to_bv 64 usp1) outer CTX
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWC AG1
              ltac:(fold usp; replace (usp - 16) with (usp1 + Z.of_nat (cells_size [C8 s4; C8 s3; C8 s2; C8 s1])) by (unfold usp1; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 usp1 [C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1))
              ltac:(rewrite EU1; fold usp; unfold usp1; lia) SPT) as (CTXc1 & UWCc1).
  (* [comment removed for export] *)
  apply (C_EGSI Σ PMc (Z_to_bv 64 SITE_ecl_egsi) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 sp s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 lo (bv_unsigned ra :: outer) lb canary k kd MK SA P pad top jm1 jm2 jp u r0 g0 oldcb FDO MST eq_refl eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 3. }
  { rewrite EU1. clear - HSTK. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_ecl_egsi) by (unfold SITE_ecl_egsi; clear; lia). exact CTXc1. }
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
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_ecl_egsi) in Hc2' by (unfold SITE_ecl_egsi; lia).
  assert (INE : In (E, 904) (rt_live RT Σ1)) by (rewrite LV1; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ1 m2 E 904 ART2 INE) as (_ & ELO & _). rewrite SP1 in ELO. pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 E 904 ART2 INE ltac:(clear; lia)) as EH.
  assert (E8 : E mod 8 = 0) by (clear - E16; Z.div_mod_to_equations; lia).
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  (* [comment removed for export] *)
  assert (EGWS : forall x, usp1 <= x -> outside (EG_W kd SA P) x).
  { intros x Hx. unfold EG_W, MTL_W. cbn [outside app]. unfold G_ALLOW_CUST. clear - Hx SALO PLO LOW HSTK HKD NUM. unfold usp1, RT_STACK in *. repeat split; lia. }
  assert (AG2 : agree_on (fun x => usp1 <= x < USTACK_TOP) m1 m2) by (intros a Ha; cbv beta in Ha; apply PRES2; [left; exact Ha | apply EGWS; clear - Ha; lia]).
  assert (FR2 : rw_cells bsegs m2 usp1 (ecl_frame s4 s3 s2 s1 s0 ra)).
  { apply (rw_cells_agree bsegs m1 m2 _ _ FR1); [| exact WM2]. cbn [cells_size csize Nat.add]. intros x Hx. apply AG2. cbv beta. clear - Hx NUM. unfold usp1, USTACK_TOP in *. lia. }
  assert (UWC2 : uw_chain m2 sp s0 outer).
  { apply (uw_chain_agree outer m1 m2 sp s0 (uw_chain_agree outer m m1 sp s0 UWC AG1)). intros a Ha. apply AG2. cbv beta in Ha |- *. fold usp in Ha. clear - Ha. unfold usp1. lia. }
  pose proof (es_rep_of_arrs0 m2 E (ecl_arrs_of_zeros m2 E BA (proj1 (af_acc_live RT AF Σ1 m2 E 904 ART2 INE)))) as ES0.
  (* [comment removed for export] *)
  pose proof (ecl_w1 (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 sp b1 b2 b3 b4 b5 b6 b7 s1 s2 (Z_to_bv 64 SHB) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 E
                EH ltac:(clear - ELO LOW NUM; lia) UT2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & <- & Hc3'). clear Hc3.
  (* [comment removed for export] *)
  rewrite <- CG1 in CTX, CGH.
  apply (ecl_loop_ind 15 0 eq_refl Σ1 PMc sp (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) u0 u1 u2 (Z_to_bv 64 E) b1 b2 b3 b4 b5 b6 b7
           s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 (Z_to_bv 64 SITE_ecl_egsi) F2 fc2 m2 lo outer (Z_to_bv 8 1) canary E
           s4 s3 s2 s1 s0 ra FDO MST eq_refl ltac:(clear; lia) E8 INE
           ltac:(rewrite EU1; fold usp; unfold usp1; clear; lia) SPT ART2 MI2).
  { rewrite <- SP1 in LOW. unfold call_ok. rewrite EU1. split; [exact ST2|]. split; [exact LOW|]. split; [clear - HSTK; unfold usp1, RT_STACK in *; lia|].
    split; [clear - NUM; unfold usp1, USTACK_TOP in *; lia|]. fold usp in SPA. clear - SPA. unfold usp1. Z.div_mod_to_equations. lia. }
  { rewrite EU1. clear - HSTK. unfold usp1, RT_STACK in *. lia. }
  { exact CTX. }
  { exact UWC2. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact CLE2. }
  { rewrite EU1. exact FR2. }
  { exact ES0. }
  { exact Hc3'. }
  clear Hc3'. intros c4 (Σ2 & Hc4 & LV2 & FRS2 & SP2 & CR2 & CG2).
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (r4 & v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F4 & fc4 & m4 & -> & (ART4 & MI4 & WM4 & ST4) & PRES4 & CLE4 & FR4 & ES4) & Hc4'). clear Hc4.
  rewrite EU1 in ST4, PRES4, FR4.
  destruct (af_client_consts RT AF Σ2 m4 ART4) as (_ & _ & _ & _ & UT4).
  pose proof (arrs16_of_es_rep m4 E 0 0 ES4) as ARR4. pose proof ARR4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TB4).
  assert (INE2 : In (E, 904) (rt_live RT Σ2)) by (rewrite LV2; exact INE).
  (* [comment removed for export] *)
  pose proof (ecl_wz sp gp (Z_to_bv 64 TP_A) v0 v1 v2 d0 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 16) s5 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
                r4 ra s0 s1 s2 s3 s4 F4 fc4 m4 lo E (Z_to_bv 64 0) (Z_to_bv 64 0)
                EH ltac:(rewrite <- SP1 in LOW; clear - ELO LOW SP1; lia) E8) as WZ.
  fold usp in WZ. fold usp1 in WZ.
  specialize (WZ ST4 ltac:(clear - NUM; lia) ltac:(clear - HSTK; unfold usp1, RT_STACK in *; lia) ltac:(clear - NUM; lia) UT4 (proj2 (af_acc_live RT AF Σ2 m4 E 904 ART4 INE2)) FR4 TB4 MI4).
  cl_lift WZ Hc4' c5 Hc5.
  destruct (ASTA_unpack RT Σ2 _ _ c5 Hc5) as (ms5 & (a1' & a2' & m5 & -> & MU5 & WM5 & MI5 & TB5 & ST5) & Hc5'). clear Hc5.
  fold usp in ST5.
  (* [comment removed for export] *)
  assert (MU5' : munch ([(E + 896, E + 904)] ++ [(usp - 0, usp)]) m4 m5) by (eapply munch_weaken; [| exact MU5]; unfold sub_fp; cbn [outside app]; intros; tauto).
  assert (ART5 : ART RT Σ2 m5).
  { apply (wg_seg_ART RT AF Σ2 m4 m5 usp 0 _ ART4 ltac:(rewrite SP2, SP1; clear - NUM; lia) ltac:(clear - NUM; lia) MU5'); [| exact WM5]. intros x Hx. right. exists E, 904. split; [exact INE2|]. cbn [outside] in Hx. clear - Hx. lia. }
  assert (APART : forall p n, In (p, n) ([(N, 32); (D, 32); (LK, 40); (SK, 56); (G, 16); (H, 8)] ++ rt_live RT Σ) -> E + 904 <= p \/ p + n <= E)
    by (intros p n Hin; exact (wg_live_apart RT AF Σ1 m2 _ E 904 _ p n ART2 LV1 Hin)).
  assert (K25 : forall a cs, rw_cells bsegs m2 a cs -> (forall x, a <= x < a + Z.of_nat (cells_size cs) -> aclient (rt_live RT Σ1) (rt_frames RT Σ1) usp1 x) ->
            (a + Z.of_nat (cells_size cs) <= E \/ E + 904 <= a) -> rw_cells bsegs m5 a cs).
  { intros a cs Hc HAc HD. apply (rw_cells_agree bsegs m2 m5 _ _ Hc); [| exact (wmono_trans bsegs _ _ _ WM4 WM5)]. intros x Hx.
    rewrite (MU5 x ltac:(cbn [outside]; clear - Hx HD; lia)). apply PRES4; [exact (HAc _ Hx)|]. cbn [outside]. clear - Hx HD. lia. }
  assert (K25s : forall a cs, rw_cells bsegs m2 a cs ->
            (0xbc1990 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbd6698) \/ (0xbf7aa0 <= a /\ a + Z.of_nat (cells_size cs) <= 0xbf7fd0) -> rw_cells bsegs m5 a cs).
  { intros a cs Hc Hn. apply (K25 a cs Hc); [| clear - Hn EH; lia]. intros x Hx. right; left. apply client_static_intro. clear - Hn Hx. lia. }
  apply Hk. exists Σ2, E, N, H, G, SK, LK, D, u', top'.
  split; [| rewrite LV2, FRS2, SP2, CR2, CG2; exact (conj LV1 (conj FRS1 (conj SP1 (conj CR1 (conj CG1 (conj E0 (conj E16 EUP)))))))].
  eapply ASTA_conseq; [exact Hc5'|]. intros ms <-. exists m5.
  split; [exists v0, v1, v2, a1', a2', d3, d4, d5, d6, d7, v3, v4, v5, v6, F4, fc4; reflexivity|].
  split; [exact (conj ART5 (conj MI5 (conj (wmono_trans bsegs _ _ _ WM1 (wmono_trans bsegs _ _ _ WM2 (wmono_trans bsegs _ _ _ WM4 WM5))) ST5)))|].
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
    assert (K45 : forall a cs, rw_cells bsegs m4 a cs -> a + Z.of_nat (cells_size cs) <= E + 896 -> rw_cells bsegs m5 a cs)
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
