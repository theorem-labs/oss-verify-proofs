(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA. Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_read.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_liveprim.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2B Require Import L2Kit L2Act L2Stmt L2StmtS L2StmtD B0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzInv CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0 B0_b2c_hcV B0_b2c_wrV B0F_b2d_wrV B0F_b2d_wrE.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

(* [comment removed for export] *)
Lemma rm0_in : forall p (l : list (Z * Z)) e, In e (rm0 p l) -> In e l /\ (p <> 0 -> fst e <> p).
Proof.
  intros p l e H. unfold rm0 in H. destruct (Z.eqb_spec p 0) as [E|NE]; [split; [exact H| intros C; exact (False_ind _ (C E))]|].
  apply live_remove_in in H as [H1 H2]. split; [exact H1| intros _; exact H2].
Qed.
Lemma rm0_keep : forall p (l : list (Z * Z)) e, In e l -> (p <> 0 -> fst e <> p) -> In e (rm0 p l).
Proof. intros p l e H N. unfold rm0. destruct (Z.eqb_spec p 0) as [E|NE]; [exact H| exact (live_remove_keep l p e H (N NE))]. Qed.
Lemma rm0_0 : forall (l : list (Z * Z)), rm0 0 l = l. Proof. reflexivity. Qed.
Lemma rm0_nz : forall p (l : list (Z * Z)), p <> 0 -> rm0 p l = live_remove p l.
Proof. intros p l NE. unfold rm0. destruct (Z.eqb_spec p 0) as [E|_]; [exact (False_ind _ (NE E))| reflexivity]. Qed.

Section DENDL2.
Context {ACEIL__ : ACeil}.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_PRIM : af_live_primary RT.
Hypothesis FRE : free_contract RT.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stages.
Variables (lo P usp sp0 : Z) (fr : list (Z * nat)) (L0 : list (Z * Z)) (mi : mem).
Variables (STRM S SHS n : Z) (dm : dsm).
Notation Wc := [(STRM + 48, STRM + 56)].
Hypothesis G : act_geom RT lo P usp sp0 false 0 8 2147450881 0 0 fr L0 Wc.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc. Hypothesis MST : mat_stable PMc.
Variables (sp gp tp : word).
Hypothesis TP : tp = Z_to_bv 64 0x6094d8.
Hypothesis USP : usp = bv_unsigned sp. Hypothesis PE : P = usp - 64.
Hypothesis AS : sanchor STRM SHS.
Hypothesis SLO : 0x62b000 <= STRM. Hypothesis SHI : STRM + 80 <= alloc_ceiling.
Hypothesis SSLO : 0x62b000 <= S. Hypothesis SSHI : S + 64144 <= alloc_ceiling.
Hypothesis LLO : alloc_ceiling <= lo. Hypothesis PLO : lo <= P.
Hypothesis S16 : S mod 16 = 0.
Hypothesis S0R : 0 <= STRM + 48 < P /\ P < 2^64.
Hypothesis S47 : 0 <= STRM /\ STRM + 80 <= 2^47.
Hypothesis SCL : forall x, STRM <= x < STRM + 80 -> aclient L0 fr usp x.
Hypothesis SHCL : forall x, SHS <= x < SHS + 10 -> aclient L0 fr usp x.
Hypothesis SHSH : SHS + 10 <= 17594333495296.
Hypothesis FSHI : STRM + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= STRM.
(* [comment removed for export] *)
Hypothesis L0NS : forall e, In e L0 -> fst e <> S.
Hypothesis L0N16 : sm_ll16 dm <> 0 -> forall e, In e L0 -> fst e <> sm_ll16 dm.
Hypothesis L0N4 : sm_ll4 dm <> 0 -> forall e, In e L0 -> fst e <> sm_ll4 dm.
Hypothesis NES16 : sm_ll16 dm <> 0 -> S <> sm_ll16 dm.
Hypothesis NES4 : sm_ll4 dm <> 0 -> S <> sm_ll4 dm.
Hypothesis NE164 : sm_ll16 dm <> 0 -> sm_ll4 dm <> 0 -> sm_ll4 dm <> sm_ll16 dm.
Hypothesis R16 : 0 <= sm_ll16 dm < 18446744073709551616. Hypothesis R4 : 0 <= sm_ll4 dm < 18446744073709551616.

Notation DENDR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
  (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (Z_to_bv 64 (STRM + 48)) (Z_to_bv 64 (STRM + 64)) a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 (STRM + 72)) (Z_to_bv 64 (S + 3152)) (Z_to_bv 64 (SHS + 6)) (Z_to_bv 64 2147450880) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Notation DSTRM w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 st w56 w72 := (STRMD w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 st w56 (Z_to_bv 64 B0_b2c_wrV.DBZF) w72).

(* [comment removed for export] *)
Definition dend_final (T : _) (Lfin : list (Z * Z)) (Σ0 : rts RT) (c6 c5 c4 c3 c2 c1 c0 cra : word) (s6 s7 s8 s9 s10 s11 : word)
    (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w56 w72 : word) : Prop :=
  forall c' (Σ' : rts RT) (m' : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc',
    ASTA RT Σ' PMc (eq (MS (mkR cra sp gp tp t0 t1 t2 c0 c1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F' (ret_pc cra) fc' None m' (seg_rom b0segs))) c' ->
    ART RT Σ' m' -> KMem.mem_inv bsegs m' -> stk bsegs m' lo usp ->
    rw_cells b0segs m' STRM (DSTRM w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 (Z_to_bv 64 0) w56 w72) ->
    PRESI usp fr L0 Wc mi m' ->
    rt_live RT Σ' = Lfin -> rt_frames RT Σ' = rt_frames RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 -> rt_credit RT Σ' = rt_credit RT Σ0 ->
    realizes bsegs c' T.

(* [comment removed for export] *)
Lemma dend_from4 : forall T (Σ : rts RT) (m : mem) c (c6 c5 c4 c3 c2 c1 c0 cra : word)
    (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w56 w72 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  sig_ok RT sp0 false 0 8 fr L0 Σ -> ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI usp fr L0 Wc mi m ->
  In (S, 64144) (rt_live RT Σ) ->
  rw_cells b0segs m P (ESAVED c6 c5 c4 c3 c2 c1 c0 cra) ->
  rw_cells b0segs m STRM (DSTRM w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 (Z_to_bv 64 S) w56 w72) ->
  bytes_at b0segs m SHS (repeat z8 10) ->
  ASTA RT Σ PMc (eq (MS (DENDR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x88754) fc None m (seg_rom b0segs))) c ->
  dend_final T (live_remove S (rt_live RT Σ)) Σ c6 c5 c4 c3 c2 c1 c0 cra s6 s7 s8 s9 s10 s11 w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72 ->
  realizes bsegs c T.
Proof.
  intros T Σ m c c6 c5 c4 c3 c2 c1 c0 cra w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
         SOK ART0 MI0 ST0 PR0 SLIV SAV SM ZSHn Hc Hk.
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU.
  pose proof (ck_intro STRM CCaller) as KS. pose proof (ck_intro SHS CCaller) as KSH.
  (* [comment removed for export] *)
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0_dend_X4 _ SHS P STRM S gp tp F fc AS SLO SHI SSLO SSHI m);
    [exact SM| exact (strm_reader m STRM SHS [] AS (proj1 S47) (proj2 S47) ZSHn I)|].
  apply evt_done. clear Hc. intros c1' Hc1.
  eapply (free_call G PMc FDO MST Σ S 64144 m); [exact FRE| exact SOK| exact SLIV| exact L0NS| exact TP| exact ART0| exact MI0| exact ST0| exact PR0| | exact Hc1|];
    [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 S0R)| exact (proj2 S0R)]|].
  clear Hc1. intros c2' Σ2 m2 u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 SOK2 LV2 FR2 CR2 ART2 MI2 ST2 PR2 STEP2.
  rewrite (KMState.ret_pc_even 0x8878c ltac:(lia) eq_refl) in Hc2.
  clear ST0. xfer_rtf G SOK2 STEP2 m m2.
  (* [comment removed for export] *)
  assert (AFW5 : app_fp [(STRM + 48, STRM + 56)]) by (cbn [app_fp]; unfold SH_LO, SH_HI; split; [clear - FSHI; lia| exact I]).
  eapply (l1_realizes RT AF Σ2 PMc _ T c2' MST Hc2).
  eapply (B0_dend_X5 _ SHS P STRM S lo gp tp F2 fc2 AS SHI SSLO LLO PLO m2 sp);
    [rewrite PE, USP; reflexivity| exact SM| exact SAV| exact ST2| exact (kmem_inv_N _ _ MI2)| exact (strm_reader m2 STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW5)|].
  clear Hc2 SM SAV. intros m3 SM ST3 NMI3 MU3 WM3. apply evt_done. intros c3' Hc3.
  unfold dend5_W in MU3.
  destruct (after_l1 AF G Σ2 _ m2 m3 SOK2 ART2 MI2 ST2 PR2 NMI3 MU3 WM3 ltac:(per_interval; right; right; right; cbn [outside]; lia)) as (ART3 & MI3 & _ & PR3 & _).
  rewrite <- USP in ST3.
  refine (Hk c3' Σ2 m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc3 ART3 MI3 ST3 SM PR3 LV2 FR2 (eq_trans (proj1 (proj2 SOK2)) (eq_sym (proj1 (proj2 SOK)))) CR2).
Qed.

(* [comment removed for export] *)
Lemma dend_from3 : forall T (Σ : rts RT) (m : mem) c (c6 c5 c4 c3 c2 c1 c0 cra : word)
    (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w56 w72 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  sig_ok RT sp0 false 0 8 fr L0 Σ -> ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI usp fr L0 Wc mi m ->
  In (S, 64144) (rt_live RT Σ) -> (sm_ll4 dm <> 0 -> In (sm_ll4 dm, 50000 * n) (rt_live RT Σ)) ->
  rw_cells b0segs m P (ESAVED c6 c5 c4 c3 c2 c1 c0 cra) ->
  rw_cells b0segs m (S + 3152) (MID_CELLS dm) ->
  rw_cells b0segs m STRM (DSTRM w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 (Z_to_bv 64 S) w56 w72) ->
  bytes_at b0segs m SHS (repeat z8 10) ->
  ASTA RT Σ PMc (eq (MS (DENDR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x8870c) fc None m (seg_rom b0segs))) c ->
  dend_final T (live_remove S (rm0 (sm_ll4 dm) (rt_live RT Σ))) Σ c6 c5 c4 c3 c2 c1 c0 cra s6 s7 s8 s9 s10 s11 w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72 ->
  realizes bsegs c T.
Proof.
  intros T Σ m c c6 c5 c4 c3 c2 c1 c0 cra w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
         SOK ART0 MI0 ST0 PR0 SLIV L4LIV SAV MID SM ZSHn Hc Hk.
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU. pose proof (ck_intro S (CLive S 64144)) as KSS.
  pose proof (ck_intro STRM CCaller) as KS. pose proof (ck_intro SHS CCaller) as KSH.
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0_dend_X3 _ SHS P STRM S gp tp F fc SLO SHI SSLO SSHI dm m);
    [exact MID| exact R4| exact SM| exact (live_reader RT AF Σ m _ _ [] ART0 SLIV ltac:(clear - S16; Z.div_mod_to_equations; lia) eq_refl I)
     | exact (strm_reader m STRM SHS [] AS (proj1 S47) (proj2 S47) ZSHn I)| |].
  - (* [comment removed for export] *)
    intros a3' NZ. apply evt_done. clear Hc. intros c1' Hc1.
    eapply (free_call G PMc FDO MST Σ (sm_ll4 dm) (50000 * n) m); [exact FRE| exact SOK| exact (L4LIV NZ)| exact (L0N4 NZ)| exact TP| exact ART0| exact MI0| exact ST0| exact PR0| | exact Hc1|];
      [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 S0R)| exact (proj2 S0R)]|].
    clear Hc1. intros c2' Σ2 m2 u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 SOK2 LV2 FR2 CR2 ART2 MI2 ST2 PR2 STEP2.
    rewrite (KMState.ret_pc_even 0x88754 ltac:(lia) eq_refl) in Hc2.
    assert (SLIV2 : In (S, 64144) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact SLIV| exact (NES4 NZ)]).
    clear ST0. xfer_rtf G SOK2 STEP2 m m2.
    eapply (dend_from4 T Σ2 m2 c2' c6 c5 c4 c3 c2 c1 c0 cra w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72); [exact SOK2| exact ART2| exact MI2| exact ST2| exact PR2| exact SLIV2| exact SAV| exact SM| exact ZSHn| exact Hc2|].
    intros c9 Σ9 m9 x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 F9 fc9 Hc9 ART9 MI9 ST9 SM9 PR9 LV9 FR9 SP9 CR9.
    refine (Hk c9 Σ9 m9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc9 ART9 MI9 ST9 SM9 PR9 _ _ _ _).
    + rewrite LV9, LV2, (rm0_nz _ _ NZ). reflexivity.
    + rewrite FR9. exact FR2.
    + rewrite SP9. exact (eq_trans (proj1 (proj2 SOK2)) (eq_sym (proj1 (proj2 SOK)))).
    + rewrite CR9. exact CR2.
  - (* [comment removed for export] *)
    intros a0' a1' a2' a3' EZ. apply evt_done. clear Hc. intros c1' Hc1.
    eapply (dend_from4 T Σ m c1' c6 c5 c4 c3 c2 c1 c0 cra w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72); [exact SOK| exact ART0| exact MI0| exact ST0| exact PR0| exact SLIV| exact SAV| exact SM| exact ZSHn| exact Hc1|].
    rewrite EZ, rm0_0 in Hk. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma dend_from2 : forall T (Σ : rts RT) (m : mem) c (c6 c5 c4 c3 c2 c1 c0 cra : word)
    (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w56 w72 : word)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  sig_ok RT sp0 false 0 8 fr L0 Σ -> ART RT Σ m -> KMem.mem_inv bsegs m -> stk bsegs m lo P -> PRESI usp fr L0 Wc mi m ->
  In (S, 64144) (rt_live RT Σ) -> (sm_ll16 dm <> 0 -> In (sm_ll16 dm, 200000 * n) (rt_live RT Σ)) -> (sm_ll4 dm <> 0 -> In (sm_ll4 dm, 50000 * n) (rt_live RT Σ)) ->
  rw_cells b0segs m P (ESAVED c6 c5 c4 c3 c2 c1 c0 cra) ->
  rw_cells b0segs m (S + 3152) (MID_CELLS dm) ->
  rw_cells b0segs m STRM (DSTRM w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 (Z_to_bv 64 S) w56 w72) ->
  bytes_at b0segs m SHS (repeat z8 10) ->
  ASTA RT Σ PMc (eq (MS (DENDR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x886c4) fc None m (seg_rom b0segs))) c ->
  dend_final T (live_remove S (rm0 (sm_ll4 dm) (rm0 (sm_ll16 dm) (rt_live RT Σ)))) Σ c6 c5 c4 c3 c2 c1 c0 cra s6 s7 s8 s9 s10 s11 w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72 ->
  realizes bsegs c T.
Proof.
  intros T Σ m c c6 c5 c4 c3 c2 c1 c0 cra w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
         SOK ART0 MI0 ST0 PR0 SLIV L16LIV L4LIV SAV MID SM ZSHn Hc Hk.
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU. pose proof (ck_intro S (CLive S 64144)) as KSS.
  pose proof (ck_intro STRM CCaller) as KS. pose proof (ck_intro SHS CCaller) as KSH.
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0_dend_X2 _ SHS P STRM S gp tp F fc SLO SHI SSLO SSHI dm m);
    [exact MID| exact R16| exact SM| exact (live_reader RT AF Σ m _ _ [] ART0 SLIV ltac:(clear - S16; Z.div_mod_to_equations; lia) eq_refl I)
     | exact (strm_reader m STRM SHS [] AS (proj1 S47) (proj2 S47) ZSHn I)| |].
  - (* [comment removed for export] *)
    intros a3' NZ. apply evt_done. clear Hc. intros c1' Hc1.
    eapply (free_call G PMc FDO MST Σ (sm_ll16 dm) (200000 * n) m); [exact FRE| exact SOK| exact (L16LIV NZ)| exact (L0N16 NZ)| exact TP| exact ART0| exact MI0| exact ST0| exact PR0| | exact Hc1|];
      [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 S0R)| exact (proj2 S0R)]|].
    clear Hc1. intros c2' Σ2 m2 u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 SOK2 LV2 FR2 CR2 ART2 MI2 ST2 PR2 STEP2.
    rewrite (KMState.ret_pc_even 0x8870c ltac:(lia) eq_refl) in Hc2.
    assert (SLIV2 : In (S, 64144) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact SLIV| exact (NES16 NZ)]).
    assert (L4LIV2 : sm_ll4 dm <> 0 -> In (sm_ll4 dm, 50000 * n) (rt_live RT Σ2)) by (intros N4; rewrite LV2; apply live_remove_keep; [exact (L4LIV N4)| exact (NE164 NZ N4)]).
    clear ST0. xfer_rtf G SOK2 STEP2 m m2.
    eapply (dend_from3 T Σ2 m2 c2' c6 c5 c4 c3 c2 c1 c0 cra w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72);
      [exact SOK2| exact ART2| exact MI2| exact ST2| exact PR2| exact SLIV2| exact L4LIV2| exact SAV| exact MID| exact SM| exact ZSHn| exact Hc2|].
    intros c9 Σ9 m9 x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 F9 fc9 Hc9 ART9 MI9 ST9 SM9 PR9 LV9 FR9 SP9 CR9.
    refine (Hk c9 Σ9 m9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc9 ART9 MI9 ST9 SM9 PR9 _ _ _ _).
    + rewrite LV9, LV2, (rm0_nz _ _ NZ). reflexivity.
    + rewrite FR9. exact FR2.
    + rewrite SP9. exact (eq_trans (proj1 (proj2 SOK2)) (eq_sym (proj1 (proj2 SOK)))).
    + rewrite CR9. exact CR2.
  - (* [comment removed for export] *)
    intros a0' a1' a2' a3' EZ. apply evt_done. clear Hc. intros c1' Hc1.
    eapply (dend_from3 T Σ m c1' c6 c5 c4 c3 c2 c1 c0 cra w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w56 w72);
      [exact SOK| exact ART0| exact MI0| exact ST0| exact PR0| exact SLIV| exact L4LIV| exact SAV| exact MID| exact SM| exact ZSHn| exact Hc1|].
    rewrite EZ, rm0_0 in Hk. exact Hk.
Qed.
End Stages.

(* [comment removed for export] *)
Theorem bzDecompressEnd_cps : bzDecompressEnd_contract RT.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m STRM S n tt l16 l4 h dm b lo usp W
         FDO MST A0E TP CEQ HD HSTRM MID ETT E16 E4 SM BS BF BO Q1L Q2L SOKA SLIV BLIV RN BLKN S16 RTT0 R160 R40 ART0 MI0 ST0 LOW LOR SPT SPA.
  intros T c Hc Hk. subst a0 tt l16 l4.
  set (P := usp - 64). assert (PE : P = usp - 64) by reflexivity.
  pose proof alloc_ceiling_range as ACR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. fold usp in SPR.
  pose proof LOR as LOR'. unfold RT_STACK in LOR'.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. unfold USTACK_TOP, STACK_WIN, SEGTOP_A in SP0R.
  (* [comment removed for export] *)
  assert (TTLIV : sm_tt dm <> 0 -> In (sm_tt dm, 400000 * n) (rt_live RT Σ)).
  { intros NZ. apply BLIV. unfold dblocks. destruct (Z.eqb_spec (sm_tt dm) 0) as [E|_]; [exact (False_ind _ (NZ E))|]. apply in_or_app; right. apply in_or_app; right. left; reflexivity. }
  assert (L16LIV : sm_ll16 dm <> 0 -> In (sm_ll16 dm, 200000 * n) (rt_live RT Σ)).
  { intros NZ. apply BLIV. unfold dblocks. destruct (Z.eqb_spec (sm_ll16 dm) 0) as [E|_]; [exact (False_ind _ (NZ E))|]. apply in_or_app; right. apply in_or_app; left. left; reflexivity. }
  assert (L4LIV : sm_ll4 dm <> 0 -> In (sm_ll4 dm, 50000 * n) (rt_live RT Σ)).
  { intros NZ. apply BLIV. unfold dblocks. destruct (Z.eqb_spec (sm_ll4 dm) 0) as [E|_]; [exact (False_ind _ (NZ E))|]. apply in_or_app; left. left; reflexivity. }
  assert (NESTT : sm_tt dm <> 0 -> S <> sm_tt dm).
  { intros NZ. pose proof (BLKN (or_introl NZ)) as N1.
    pose proof (live_disj_in RT AF Σ m S 64144 _ _ ART0 SLIV (TTLIV NZ) ltac:(intros E; injection E; clear - N1; lia)) as D. clear - D N1. lia. }
  assert (NES16 : sm_ll16 dm <> 0 -> S <> sm_ll16 dm).
  { intros NZ. pose proof (BLKN (or_intror (or_introl NZ))) as N1.
    pose proof (live_disj_in RT AF Σ m S 64144 _ _ ART0 SLIV (L16LIV NZ) ltac:(intros E; injection E; clear - N1; lia)) as D. clear - D N1. lia. }
  assert (NES4 : sm_ll4 dm <> 0 -> S <> sm_ll4 dm).
  { intros NZ. pose proof (BLKN (or_intror (or_intror NZ))) as N1.
    pose proof (live_disj_in RT AF Σ m S 64144 _ _ ART0 SLIV (L4LIV NZ) ltac:(intros E; injection E; clear - N1; lia)) as D. clear - D N1. lia. }
  assert (NETT16 : sm_tt dm <> 0 -> sm_ll16 dm <> 0 -> sm_ll16 dm <> sm_tt dm).
  { intros NZ NZ'. pose proof (BLKN (or_introl NZ)) as N1.
    pose proof (live_disj_in RT AF Σ m _ _ _ _ ART0 (TTLIV NZ) (L16LIV NZ') ltac:(intros E; injection E; clear - N1; lia)) as D. clear - D N1. lia. }
  assert (NETT4 : sm_tt dm <> 0 -> sm_ll4 dm <> 0 -> sm_ll4 dm <> sm_tt dm).
  { intros NZ NZ'. pose proof (BLKN (or_introl NZ)) as N1.
    pose proof (live_disj_in RT AF Σ m _ _ _ _ ART0 (TTLIV NZ) (L4LIV NZ') ltac:(intros E; injection E; clear - N1; lia)) as D. clear - D N1. lia. }
  assert (NE164 : sm_ll16 dm <> 0 -> sm_ll4 dm <> 0 -> sm_ll4 dm <> sm_ll16 dm).
  { intros NZ NZ'. pose proof (BLKN (or_intror (or_introl NZ))) as N1.
    pose proof (live_disj_in RT AF Σ m _ _ _ _ ART0 (L16LIV NZ) (L4LIV NZ') ltac:(intros E; injection E; clear - N1; lia)) as D. clear - D N1. lia. }
  assert (RTT : 0 <= sm_tt dm < 18446744073709551616).
  { destruct (Z.eq_dec (sm_tt dm) 0) as [E|NZ]; [rewrite E; lia|]. pose proof (af_live_range RT AF Σ m _ _ ART0 (TTLIV NZ)) as (X0 & X1 & _).
    pose proof (BLKN (or_introl NZ)) as N1. unfold STACK_WIN in X1. clear - X0 X1 N1 SP0R. lia. }
  assert (R16 : 0 <= sm_ll16 dm < 18446744073709551616).
  { destruct (Z.eq_dec (sm_ll16 dm) 0) as [E|NZ]; [rewrite E; lia|]. pose proof (af_live_range RT AF Σ m _ _ ART0 (L16LIV NZ)) as (X0 & X1 & _).
    pose proof (BLKN (or_intror (or_introl NZ))) as N1. unfold STACK_WIN in X1. clear - X0 X1 N1 SP0R. lia. }
  assert (R4 : 0 <= sm_ll4 dm < 18446744073709551616).
  { destruct (Z.eq_dec (sm_ll4 dm) 0) as [E|NZ]; [rewrite E; lia|]. pose proof (af_live_range RT AF Σ m _ _ ART0 (L4LIV NZ)) as (X0 & X1 & _).
    pose proof (BLKN (or_intror (or_intror NZ))) as N1. unfold STACK_WIN in X1. clear - X0 X1 N1 SP0R. lia. }
  (* [comment removed for export] *)
  pose proof (AF_PRIM Σ m S 64144 ART0 SLIV ltac:(lia)) as SSLO. unfold SEGTOP_A in SSLO.
  pose proof (af_live_range RT AF Σ m S 64144 ART0 SLIV) as (_ & SSHI0 & _).
  assert (SSHI : S + 64144 <= alloc_ceiling) by (clear - SSHI0 CEQ; lia).
  (* [comment removed for export] *)
  destruct SOKA as ((fS & kS & FIN & FLO & FHI) & S8 & ZSH).
  pose proof (af_frames_range RT AF Σ m fS kS ART0 FIN) as (FS0 & FS1 & _ & FSL).
  pose proof (af_frames_align RT AF Σ m fS kS ART0 FIN) as (_ & FSEG). unfold SEGTOP_A in FSEG.
  pose proof (af_frames_hi RT AF Σ m fS kS ART0 FIN) as FSHI0.
  assert (FSHI : STRM + 80 <= 0x7fff7000 \/ 0x10007fff8000 <= STRM) by (clear - FSHI0 FLO FHI; lia).
  assert (SLO : 0x62b000 <= STRM) by (clear - FSEG FLO; lia).
  assert (SHI : STRM + 80 <= alloc_ceiling) by (clear - FS1 FHI CEQ; lia).
  assert (LLO : alloc_ceiling <= lo) by (clear - CEQ LOW; lia).
  assert (PLO : lo <= P) by (clear - PE LOR'; lia).
  set (SHS := STRM / 8 + 2147450880).
  assert (AS : sanchor STRM SHS) by (apply sanchor_intro; exact S8).
  assert (ZSHn : bytes_at b0segs m SHS (repeat z8 10)) by exact ZSH.
  clearbody SHS.
  (* [comment removed for export] *)
  set (L0 := live_remove S (rm0 (sm_ll4 dm) (rm0 (sm_ll16 dm) (rm0 (sm_tt dm) (rt_live RT Σ))))).
  assert (L0SUB : forall e0, In e0 L0 -> In e0 (rt_live RT Σ)).
  { intros e0 H. apply live_remove_in in H as [H _]. apply rm0_in in H as [H _]. apply rm0_in in H as [H _]. apply rm0_in in H as [H _]. exact H. }
  assert (L0NS : forall e0, In e0 L0 -> fst e0 <> S).
  { intros e0 H. apply live_remove_in in H as [_ H]. exact H. }
  assert (L0N4 : sm_ll4 dm <> 0 -> forall e0, In e0 L0 -> fst e0 <> sm_ll4 dm).
  { intros NZ e0 H. apply live_remove_in in H as [H _]. apply rm0_in in H as [_ H]. exact (H NZ). }
  assert (L0N16 : sm_ll16 dm <> 0 -> forall e0, In e0 L0 -> fst e0 <> sm_ll16 dm).
  { intros NZ e0 H. apply live_remove_in in H as [H _]. apply rm0_in in H as [H _]. apply rm0_in in H as [_ H]. exact (H NZ). }
  assert (L0NTT : sm_tt dm <> 0 -> forall e0, In e0 L0 -> fst e0 <> sm_tt dm).
  { intros NZ e0 H. apply live_remove_in in H as [H _]. apply rm0_in in H as [H _]. apply rm0_in in H as [H _]. apply rm0_in in H as [_ H]. exact (H NZ). }
  assert (L0IN : forall e0, In e0 (rt_live RT Σ) -> fst e0 <> S -> (sm_tt dm <> 0 -> fst e0 <> sm_tt dm) -> (sm_ll16 dm <> 0 -> fst e0 <> sm_ll16 dm) ->
                            (sm_ll4 dm <> 0 -> fst e0 <> sm_ll4 dm) -> In e0 L0).
  { intros e0 H NS NT N16 N4. unfold L0. apply live_remove_keep; [| exact NS]. apply rm0_keep; [| exact N4]. apply rm0_keep; [| exact N16]. apply rm0_keep; [exact H| exact NT]. }
  assert (L0EQ : L0 = live_remove S (rm0 (sm_ll4 dm) (rm0 (sm_ll16 dm) (rm0 (sm_tt dm) (rt_live RT Σ))))) by reflexivity.
  clearbody L0.
  set (Wc := [(STRM + 48, STRM + 56)]).
  assert (SCL : forall x, STRM <= x < STRM + 80 -> aclient L0 (rt_frames RT Σ) usp x).
  { intros x Hx. right; right; right; left. exists fS, kS. split; [exact FIN| clear - Hx FLO FHI; lia]. }
  assert (WCL0 : forall x, ~ outside Wc x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x).
  { intros x Hx. unfold Wc in Hx. cbn [outside] in Hx. right; right; right; left. exists fS, kS. split; [exact FIN| clear - Hx FLO FHI; lia]. }
  destruct (act_setup_nf RT AF Σ m lo P usp Wc ART0 LOW ltac:(clear - PE LOR'; unfold RT_STACK; lia) ltac:(clear - PE; lia) SPT
              ltac:(clear - PE SPA; Z.div_mod_to_equations; lia) WCL0) as (G0 & SOK0).
  assert (G : act_geom RT lo P usp (rt_sp0 RT Σ) false 0 8 2147450881 0 0 (rt_frames RT Σ) L0 Wc).
  { apply (act_geom_sub _ _ _ _ _ _ _ _ _ _ _ _ _ L0 _ Wc G0 L0SUB). intros x Hx. apply SCL. unfold Wc in Hx. cbn [outside] in Hx. clear - Hx. lia. }
  pose proof (sig_ok_sub _ _ _ _ _ _ _ L0 _ SOK0 L0SUB) as SOK. clear G0 SOK0 WCL0.
  (* [comment removed for export] *)
  assert (AFW : app_fp [(P, P + 64)]).
  { cbn [app_fp]. unfold SH_LO, SH_HI. split; [right; clear - PE LOW LOR' CEQ ACR; lia| exact I]. }
  assert (S47 : 0 <= STRM /\ STRM + 80 <= 2^47) by (clear - SLO SHI ACR; lia).
  pose proof (live_reader RT AF Σ m S 64144 _ ART0 SLIV ltac:(clear - S16; Z.div_mod_to_equations; lia) eq_refl AFW) as SHd.
  pose proof (strm_reader m STRM SHS _ AS (proj1 S47) (proj2 S47) ZSHn AFW) as SHs.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _ & _).
  assert (AC : aconsts B0C m) by (split; [exact (ro_C8_KN m _ _ G1)| exact (ro_C8_KN m _ _ G2)]). clear G1 G2.
  rewrite BS, BF in SM.
  (* [comment removed for export] *)
  assert (SHSR : shad fS <= SHS /\ SHS + 10 <= shad (fS + fs_size kS)).
  { destruct AS as [_ ->]. unfold shad, SHB. clear - FLO FHI. Z.div_mod_to_equations. lia. }
  assert (SHCL : forall x, SHS <= x < SHS + 10 -> aclient L0 (rt_frames RT Σ) usp x).
  { intros x Hx. right; right; right; right. exists fS, kS. split; [exact FIN| clear - Hx SHSR; lia]. }
  assert (SHSH : SHS + 10 <= 17594333495296) by (destruct AS as [_ ->]; clear - SHI ACR; Z.div_mod_to_equations; lia).
  assert (S0R : 0 <= STRM + 48 < P /\ P < 2^64) by (clear - SLO SHI LLO PE LOR' SPR; lia).
  destruct (stk_split b0segs m lo P usp ST0 ltac:(clear - PE LOR'; lia)) as [ST0P _].
  (* [comment removed for export] *)
  assert (FIN0 : dend_final lo usp (rt_frames RT Σ) L0 m STRM PMc sp gp tp T L0 Σ s6 s5 s4 s3 s2 s1 s0 ra s6 s7 s8 s9 s10 s11
                   (Z_to_bv 64 (bs_src b + (bs_len b - bs_ai b))) (Z_to_bv 64 (bs_ai b)) (bs_til b) (bs_tih b) (bs_q1 b)
                   (Z_to_bv 64 (bs_dst b + (bs_dlen b - bs_av b))) (Z_to_bv 64 (bs_av b)) (bs_tol b) (bs_toh b) (bs_q2 b) (bs_bzalloc b) (bs_opaque b)).
  {
    intros c9 Σ9 m9 x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 F9 fc9 Hc9 ART9 MI9 ST9 SM9 PR9 LV9 FR9 SP9 CR9.
    apply Hk. exists Σ9.
    split; [| split; [rewrite LV9; exact L0EQ| split; [exact FR9| split; [exact SP9| exact CR9]]]].
    eapply ASTA_conseq; [exact Hc9|]. intros ms <-.
    exists m9, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, F9, fc9.
    split; [reflexivity|]. split; [exact ART9|]. split; [exact MI9|]. split; [exact ST9|].
    split.
    { cbn [bs_src bs_len bs_ai bs_til bs_tih bs_q1 bs_dst bs_dlen bs_av bs_tol bs_toh bs_q2 bs_S bs_bzalloc bs_bzfree bs_opaque].
      rewrite BF. exact SM9. }
    intros a Ha Ho. apply PR9. unfold W in Ho.
    assert (OB : ~ (S <= bv_unsigned a < S + 64144) /\ ~ (STRM + 48 <= bv_unsigned a < STRM + 56) /\
                 (sm_tt dm <> 0 -> ~ (sm_tt dm <= bv_unsigned a < sm_tt dm + 400000 * n)) /\
                 (sm_ll16 dm <> 0 -> ~ (sm_ll16 dm <= bv_unsigned a < sm_ll16 dm + 200000 * n)) /\
                 (sm_ll4 dm <> 0 -> ~ (sm_ll4 dm <= bv_unsigned a < sm_ll4 dm + 50000 * n))).
    { clear - Ho. unfold dblocks in Ho.
      destruct (Z.eqb_spec (sm_ll4 dm) 0) as [E4|N4]; destruct (Z.eqb_spec (sm_ll16 dm) 0) as [E16|N16]; destruct (Z.eqb_spec (sm_tt dm) 0) as [ETT|NTT];
        cbn [app map fst snd KFrame.outside] in Ho; repeat split; intros; lia. }
    destruct OB as (O1 & O2 & O3 & O4 & O5).
    split; [| unfold Wc; cbn [outside]; split; [clear - O2; lia| exact I]].
    destruct Ha as [H|[H|[H|H]]]; [left; exact H| right; left; exact H| | right; right; right; exact H].
    destruct H as (p & n0 & IN & R). right; right; left. exists p, n0. split; [| exact R].
    apply L0IN; [exact IN| | | |]; cbn [fst].
    - apply (live_other_base RT AF Σ m S 64144 p n0 _ ART0 SLIV IN ltac:(clear; lia) R). exact O1.
    - intros NZ. pose proof (BLKN (or_introl NZ)) as N1. apply (live_other_base RT AF Σ m _ _ p n0 _ ART0 (TTLIV NZ) IN ltac:(clear - N1; lia) R). exact (O3 NZ).
    - intros NZ. pose proof (BLKN (or_intror (or_introl NZ))) as N1. apply (live_other_base RT AF Σ m _ _ p n0 _ ART0 (L16LIV NZ) IN ltac:(clear - N1; lia) R). exact (O4 NZ).
    - intros NZ. pose proof (BLKN (or_intror (or_intror NZ))) as N1. apply (live_other_base RT AF Σ m _ _ p n0 _ ART0 (L4LIV NZ) IN ltac:(clear - N1; lia) R). exact (O5 NZ). }
  clear Hk.
  pose proof (ck_intro P CStack) as KP. pose proof (ck_intro usp CStack) as KU. pose proof (ck_intro S (CLive S 64144)) as KSS.
  pose proof (ck_intro STRM CCaller) as KS. pose proof (ck_intro SHS CCaller) as KSH.
  eapply (l1_realizes RT AF Σ PMc _ T c MST Hc).
  eapply (B0_dend_X1 _ SHS P STRM S lo gp tp F fc AS SLO SHI SSLO SSHI LLO PLO ltac:(clear - S16; Z.div_mod_to_equations; lia) h dm m);
    [reflexivity| exact ST0| exact HD| exact HSTRM| exact MID| exact RTT| exact SM| exact (kmem_inv_N _ _ MI0)| exact AC| exact SHd| exact SHs| |].
  - (* [comment removed for export] *)
    intros m1 vj0 a3' NZ SAV ST1n HD1 MID1 SM1 NMI1 MU1 WM1. apply evt_done. clear Hc. intros c1 Hc1.
    unfold dend_W in MU1.
    destruct (after_l1 AF G Σ _ m m1 SOK ART0 MI0 ST0P (presi_refl _ _ _ _ m) NMI1 MU1 WM1 ltac:(per_interval; unfold P; lia)) as (ART1 & MI1 & ST1 & PR1 & _).
    clear ST0 ST0P ZSH HD MID SM SHd SHs AC AFW HD1 ST1n.
    xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
    eapply (free_call G PMc FDO MST Σ (sm_tt dm) (400000 * n) m1); [exact FRE| exact SOK| exact (TTLIV NZ)| exact (L0NTT NZ)| exact TP| exact ART1| exact MI1| exact ST1| exact PR1| | exact Hc1|];
      [apply unwind_site1; [apply in_alloc_ras; reflexivity| exact (proj1 S0R)| exact (proj2 S0R)]|].
    clear Hc1. intros c2 Σ2 m2 u0 u1 u2 v0 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 Hc2 SOK2 LV2 FR2 CR2 ART2 MI2 ST2 PR2 STEP2.
    rewrite (KMState.ret_pc_even 0x886c4 ltac:(lia) eq_refl) in Hc2.
    assert (SLIV2 : In (S, 64144) (rt_live RT Σ2)) by (rewrite LV2; apply live_remove_keep; [exact SLIV| exact (NESTT NZ)]).
    assert (L16LIV2 : sm_ll16 dm <> 0 -> In (sm_ll16 dm, 200000 * n) (rt_live RT Σ2)) by (intros N16; rewrite LV2; apply live_remove_keep; [exact (L16LIV N16)| exact (NETT16 NZ N16)]).
    assert (L4LIV2 : sm_ll4 dm <> 0 -> In (sm_ll4 dm, 50000 * n) (rt_live RT Σ2)) by (intros N4; rewrite LV2; apply live_remove_keep; [exact (L4LIV N4)| exact (NETT4 NZ N4)]).
    clear ST1. xfer_rtf G SOK2 STEP2 m1 m2.
    eapply (dend_from2 lo P usp (rt_sp0 RT Σ) (rt_frames RT Σ) L0 m STRM S SHS n dm G PMc FDO MST sp gp tp TP eq_refl PE AS SLO SHI SSLO SSHI LLO PLO S16 S0R S47 SCL SHCL FSHI
              L0NS L0N16 L0N4 NES16 NES4 NE164 R16 R4 T Σ2 m2 c2 vj0 s5 s4 s3 s2 s1 s0 ra);
      [exact SOK2| exact ART2| exact MI2| exact ST2| exact PR2| exact SLIV2| exact L16LIV2| exact L4LIV2| exact SAV| exact MID1| exact SM1| exact ZSHn| exact Hc2|].
    intros c9 Σ9 m9 x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 F9 fc9 Hc9 ART9 MI9 ST9 SM9 PR9 LV9 FR9 SP9 CR9.
    refine (FIN0 c9 Σ9 m9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc9 ART9 MI9 ST9 SM9 PR9 _ _ _ _).
    + rewrite LV9, LV2, L0EQ, (rm0_nz _ _ NZ). reflexivity.
    + rewrite FR9. exact FR2.
    + rewrite SP9. exact (proj1 (proj2 SOK2)).
    + rewrite CR9. exact CR2.
  - (* [comment removed for export] *)
    intros m1 vj0 a0' a1' a2' a3' EZ SAV ST1n HD1 MID1 SM1 NMI1 MU1 WM1. apply evt_done. clear Hc. intros c1 Hc1.
    unfold dend_W in MU1.
    destruct (after_l1 AF G Σ _ m m1 SOK ART0 MI0 ST0P (presi_refl _ _ _ _ m) NMI1 MU1 WM1 ltac:(per_interval; unfold P; lia)) as (ART1 & MI1 & ST1 & PR1 & _).
    clear ST0 ST0P ZSH HD MID SM SHd SHs AC AFW HD1 ST1n.
    xfer_l1 m m1 MU1 WM1. clear NMI1 MU1 WM1.
    eapply (dend_from2 lo P usp (rt_sp0 RT Σ) (rt_frames RT Σ) L0 m STRM S SHS n dm G PMc FDO MST sp gp tp TP eq_refl PE AS SLO SHI SSLO SSHI LLO PLO S16 S0R S47 SCL SHCL FSHI
              L0NS L0N16 L0N4 NES16 NES4 NE164 R16 R4 T Σ m1 c1 vj0 s5 s4 s3 s2 s1 s0 ra);
      [exact SOK| exact ART1| exact MI1| exact ST1| exact PR1| exact SLIV| exact L16LIV| exact L4LIV| exact SAV| exact MID1| exact SM1| exact ZSHn| exact Hc1|].
    intros c9 Σ9 m9 x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 F9 fc9 Hc9 ART9 MI9 ST9 SM9 PR9 LV9 FR9 SP9 CR9.
    refine (FIN0 c9 Σ9 m9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc9 ART9 MI9 ST9 SM9 PR9 _ FR9 SP9 CR9).
    rewrite LV9, L0EQ, EZ, rm0_0. reflexivity.
Qed.
End DENDL2.
