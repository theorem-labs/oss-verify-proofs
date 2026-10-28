(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS Arr.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx PLayout RT_iface_pem Fz_kit Fz_ckit Fz_env Fz_W1_defs Fz_W1_misc Fz_W1_sync Fz_W1_ctrl Fz_W2_ctrl Fz_W3_iface Fz_W3_lems.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CBctrlF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
Hypothesis GO_memmeth : GOBJ MEM_METHOD 112.
Hypothesis GO_secmeth : GOBJ M_SECMEM_A 112.

(* [comment removed for export] *)
Lemma static_not_live : forall (Σ : rts RT) (m : mem) p k x, ART RT Σ m -> In (p, k) (rt_live RT Σ) -> client_static x -> ~ (p <= x < p + k).
Proof using AF.
  intros Σ m p k x ART0 Hin Hs. pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (_ & _ & SG). pose proof (client_static_range x Hs) as R.
  unfold SEGTOP_A in *. clear - SG R. lia.
Qed.

(* [comment removed for export] *)
Lemma pp_above_image : forall (Σ : rts RT) (m : mem) usp lo PP, ART RT Σ m -> pp_loc (rt_frames RT Σ) m usp PP ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK <= usp -> SEGTOP_A <= PP.
Proof using AF.
  intros Σ m usp lo PP ART0 LOC LOW LOR.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  destruct LOC as [(H1 & _) | (f & k & Hin & H1 & _)].
  - unfold SEGTOP_A, RT_STACK, STACK_WIN in *. clear - H1 LOW LOR SP0W SP0R. lia.
  - pose proof (proj2 (af_frames_align RT AF Σ m f k ART0 Hin)) as FLOI. clear - FLOI H1. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bio_ctrl_info_proof : Fz_W3_iface.bio_ctrl_info_stmt RT.
Proof using AF AFP GO_memmeth GO_secmeth.
  unfold Fz_W3_iface.bio_ctrl_info_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary K BI meth len max off
    FDO MST -> -> -> -> -> MB ART0 MI0 CALL HSTK ENV.
  pose proof MB as (BM & fl & rrw & numw & padw & nr & nw & EBI & EBM & INBI & BIAL & ND & HM & BH & BW & FLOK & BT & INNER).
  destruct INNER as (rmaxw & INBB & BBAL & BBC & INBM & BMAL & INR & RAL & OFF0 & LEN & MAXB & KD).
  assert (RC : exists D, rw_cells asegs m (k_rp K) (readp_cells len D off rmaxw (Z_to_bv 64 (msec meth)))).
  { destruct (k_d K) as [d|].
    - destruct KD as (junk & _ & _ & _ & RC & _). exists d. exact RC.
    - destruct KD as (MAX0 & _ & RC). exists 0.
      assert (E1 : len = 0) by (clear - MAX0 LEN OFF0; lia). assert (E2 : off = 0) by (clear - MAX0 LEN OFF0; lia). rewrite E1, E2. exact RC. }
  destruct RC as (D & RC).
  intros T c HA Hk. unfold BCTRL_STACK in HSTK.
  apply (bio_ctrl_info_cps RT AF GOBJ AFP GO_memmeth GO_secmeth Σ PMc ra sp gp _ t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m lo BI (k_bb K) (k_bm K) (k_rp K) D len off fl 0 meth (Z_to_bv 64 1) (Z_to_bv 64 1) rrw numw padw rmaxw (Z_to_bv 64 (msec meth))
           FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl INBI BIAL HM BH BW FLOK INBB BBAL BBC INBM BMAL INR RAL RC ltac:(clear; lia) ART0 MI0 CALL
           ltac:(clear - HSTK; lia) T c HA).
  intros c' HAS. apply Hk. unfold apost.
  eapply ASTA_conseq; [exact HAS|]. cbv beta. intros ms (m' & RS & AFT & PRm).
  pose proof AFT as (ART7 & MI7 & WM7 & ST7).
  exists (Z_to_bv 64 (len - off)), m'. split; [exact RS|]. split; [exact (conj ART7 (conj MI7 ST7))|].
  split; [intros x Hx _; exact (PRm x Hx)|].
  split; [apply (cl_env_agree m m' _ _ ENV); intros a Ha; apply PRm; apply acl_static; exact (cl_cell_static _ Ha)|].
  split; [reflexivity|]. split; [exact WM7|].
  eapply mbio_rep_agree; [exact MB|]. intros a (e & He & Ha). destruct e as [p n]. cbn [fst snd] in Ha.
  apply PRm. exact (acl_live _ _ _ p n _ (mbio_rep_ents _ _ _ _ _ _ _ _ _ MB He) Ha).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bio_ctrl_ptr_proof : Fz_W3_iface.bio_ctrl_ptr_stmt RT.
Proof using AF AFP MMV GO_memmeth GO_secmeth.
  unfold Fz_W3_iface.bio_ctrl_ptr_stmt.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary K BI meth len max off PP old
    FDO MST -> -> -> -> -> MB PPAL PPC LOC PPAP ART0 MI0 CALL HSTK ENV.
  pose proof MB as (BM & MBX). pose proof MBX as (fl & rrw & numw & padw & nr & nw & EBI & EBM & INBI & BIAL & ND & HM & BH & BW & FLOK & BT & INNER).
  destruct INNER as (rmaxw & INBB & BBAL & BBC & INBM & BMAL & INR & RAL & OFF0 & LEN & MAXB & KD).
  intros T c HA Hk. unfold BCTRL_STACK in HSTK. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (pp_above_image Σ m (bv_unsigned sp) lo PP ART0 LOC LOW LOR) as PPIMG.
  assert (E1 : In (k_bi K, 128) (mbio_ent K max)) by (unfold mbio_ent; left; reflexivity).
  assert (E2 : In (k_bb K, 16) (mbio_ent K max)) by (unfold mbio_ent; right; left; reflexivity).
  assert (E3 : In (k_bm K, 32) (mbio_ent K max)) by (unfold mbio_ent; right; right; left; reflexivity).
  assert (E4 : In (k_rp K, 32) (mbio_ent K max)) by (unfold mbio_ent; right; right; right; left; reflexivity).
  pose proof (PPAP _ E1) as PA1. pose proof (PPAP _ E2) as PA2. pose proof (PPAP _ E3) as PA3. pose proof (PPAP _ E4) as PA4. cbn [fst snd] in PA1, PA2, PA3, PA4.
  (* [comment removed for export] *)
  assert (STO : forall x, client_static x -> ~ (PP <= x < PP + 8)) by (intros x Hs; pose proof (client_static_range x Hs) as R; clear - R PPIMG; lia).
  destruct (k_d K) as [d|] eqn:EKD.
  - (* [comment removed for export] *)
    destruct KD as (junk & IND & MAXP & BMC & RC & LJ & DC).
    assert (E5 : In (d, max) (mbio_ent K max)) by (unfold mbio_ent; rewrite EKD; do 4 right; left; reflexivity).
    pose proof (PPAP _ E5) as PA5. cbn [fst snd] in PA5.
    pose proof ND as ND'. unfold mbio_blocks in ND'. rewrite EKD in ND'. cbn [app] in ND'.
    apply NoDup_cons_iff in ND' as [NBI ND2]. apply NoDup_cons_iff in ND2 as [NBB ND3]. apply NoDup_cons_iff in ND3 as [NBM ND4]. apply NoDup_cons_iff in ND4 as [NR _].
    cbn [In] in NBI, NBB, NBM, NR. rewrite <- EBI in NBI.
    assert (NDBI : d <> BI) by (clear - NBI; intros E; apply NBI; do 3 right; left; exact E).
    assert (NDBB : d <> k_bb K) by (clear - NBB; intros E; apply NBB; do 2 right; left; exact E).
    assert (NDBM : d <> k_bm K) by (clear - NBM; intros E; apply NBM; right; left; exact E).
    assert (NDR : d <> k_rp K) by (clear - NR; intros E; apply NR; left; exact E).
    assert (NMR : k_bm K <> k_rp K) by (clear - NBM; intros E; apply NBM; left; exact (eq_sym E)).
    apply (bio_ctrl_ptr_cps RT AF GOBJ AFP MMV GO_memmeth GO_secmeth Σ PMc ra sp gp _ t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo BI (k_bb K) (k_bm K) (k_rp K) d len max off fl 1 PP 0 meth (Z_to_bv 64 1) rrw numw padw rmaxw (Z_to_bv 64 (msec meth)) old junk
             FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl INBI BIAL HM BH BW FLOK ltac:(clear; lia) INBB BBAL BBC INBM BMAL BMC INR RAL RC NMR IND NDBI NDBB NDBM NDR
             OFF0 LEN ltac:(clear - MAXP MAXB; lia) LJ DC PPAL PPC LOC ltac:(clear; lia) ART0 MI0 CALL ltac:(clear - HSTK; lia) T c HA).
    intros c' HAS. apply Hk. unfold apost.
    eapply ASTA_conseq; [exact HAS|]. cbv beta. intros ms (rmaxw' & m' & RS & AFT & PRm & BMC7 & RC7 & DC7 & PPC7).
    pose proof AFT as (ART7 & MI7 & WM7 & ST7).
    exists (Z_to_bv 64 1), m'. split; [exact RS|]. split; [exact (conj ART7 (conj MI7 ST7))|].
    assert (WsubW : forall x, outside ((PP, PP + 8) :: mbio_W K max) x -> outside (CP_W (k_bm K) (k_rp K) d max PP) x).
    { intros x Ho. unfold mbio_W, mbio_ent in Ho. rewrite EKD in Ho. unfold CP_W. cbn [outside app map fst snd] in Ho |- *. clear - Ho. lia. }
    split; [intros x Hx Ho; exact (PRm x Hx (WsubW _ Ho))|].
    split.
    { apply (cl_env_agree m m' _ _ ENV). intros a Ha. pose proof (cl_cell_static _ Ha) as Hs. apply PRm; [apply acl_static; exact Hs|].
      pose proof (static_not_live Σ m _ _ _ ART0 INBM Hs) as S1. pose proof (static_not_live Σ m _ _ _ ART0 INR Hs) as S2.
      pose proof (static_not_live Σ m _ _ _ ART0 IND Hs) as S3. pose proof (STO _ Hs) as S4. unfold CP_W. cbn [outside]. clear - S1 S2 S3 S4. lia. }
    exists (k_bm K). split; [reflexivity|]. split; [exact WM7|]. split; [exact PPC7|].
    (* [comment removed for export] *)
    assert (AGK : forall p q a k, In (p, q) (rt_live RT Σ) -> p <> k_bm K -> p <> k_rp K -> p <> d -> (PP + 8 <= p \/ p + q <= PP) -> p <= a -> a + k <= p + q ->
              agree_on (fun x => a <= x < a + k) m m').
    { intros p q a k Hp N1 N2 N3 PA H1 H2 x Hx. cbv beta in Hx. apply PRm; [apply (acl_live _ _ _ p q); [exact Hp| clear - Hx H1 H2; lia]|].
      pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hp INBM ltac:(intros E; injection E; intros; apply N1; assumption)) as A1.
      pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hp INR ltac:(intros E; injection E; intros; apply N2; assumption)) as A2.
      pose proof (live_ne_apart RT AF Σ m _ _ _ _ ART0 Hp IND ltac:(intros E; injection E; intros; apply N3; assumption)) as A3.
      unfold CP_W. cbn [outside]. clear - Hx H1 H2 A1 A2 A3 PA MAXP. lia. }
    assert (NBIM : BI <> k_bm K) by (clear - NBI; intros E; apply NBI; right; left; exact (eq_sym E)).
    assert (NBIR : BI <> k_rp K) by (clear - NBI; intros E; apply NBI; right; right; left; exact (eq_sym E)).
    assert (NBBM : k_bb K <> k_bm K) by (clear - NBB; intros E; apply NBB; left; exact (eq_sym E)).
    assert (NBBR : k_bb K <> k_rp K) by (clear - NBB; intros E; apply NBB; right; left; exact (eq_sym E)).
    rewrite <- EBI in PA1.
    exists fl, rrw, numw, padw, nr, nw.
    split; [exact EBI|]. split; [reflexivity|]. split; [exact INBI|]. split; [exact BIAL|]. split; [exact ND|]. split; [exact HM|].
    split; [apply (rw_cells_agree_nw asegs m m' _ _ BH); unfold bio_head; cbn [cells_size csize Nat.add];
            apply (AGK BI 128); [exact INBI| exact NBIM| exact NBIR| exact (fun E => NDBI (eq_sym E))| exact PA1| clear; lia| clear; lia]|].
    split; [apply (rw_cells_agree_nw asegs m m' _ _ BW); unfold bio_w1_cells; cbn [cells_size csize Nat.add];
            apply (AGK BI 128); [exact INBI| exact NBIM| exact NBIR| exact (fun E => NDBI (eq_sym E))| exact PA1| clear; lia| clear; lia]|].
    split; [exact FLOK|].
    split; [apply (rw_cells_agree_nw asegs m m' _ _ BT); unfold bio_tail; cbn [cells_size csize Nat.add];
            apply (AGK BI 128); [exact INBI| exact NBIM| exact NBIR| exact (fun E => NDBI (eq_sym E))| exact PA1| clear; lia| clear; lia]|].
    exists rmaxw'. split; [exact INBB|]. split; [exact BBAL|].
    split; [apply (rw_cells_agree_nw asegs m m' _ _ BBC); cbn [cells_size csize Nat.add];
            apply (AGK (k_bb K) 16); [exact INBB| exact NBBM| exact NBBR| exact (fun E => NDBB (eq_sym E))| exact PA2| clear; lia| clear; lia]|].
    split; [exact INBM|]. split; [exact BMAL|]. split; [exact INR|]. split; [exact RAL|].
    split; [clear - OFF0; lia|]. split; [clear - OFF0 LEN; lia|]. split; [exact MAXB|].
    rewrite EKD. exists (mv_cur (Z.to_nat off) junk (Z.to_nat (len - off))).
    split; [exact IND|]. split; [exact MAXP|]. split; [exact BMC7|]. split; [exact RC7|].
    split; [rewrite mv_cur_length; [exact LJ| rewrite LJ; clear - OFF0 LEN; lia]| exact DC7].
  - (* [comment removed for export] *)
    destruct KD as (MAX0 & BMC & RC).
    assert (EL : len = 0) by (clear - MAX0 LEN OFF0; lia). assert (EO : off = 0) by (clear - MAX0 LEN OFF0; lia).
    apply (bio_ctrl_ptr_same_cps RT AF GOBJ AFP GO_memmeth GO_secmeth Σ PMc ra sp gp _ t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo BI (k_bb K) (k_bm K) (k_rp K) fl 1 PP 0 meth (Z_to_bv 64 1) rrw numw padw (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (msec meth))
             (Z_to_bv 64 (0 - 0)) rmaxw (Z_to_bv 64 (msec meth)) old
             FDO MST eq_refl eq_refl eq_refl eq_refl eq_refl INBI BIAL HM BH BW FLOK ltac:(clear; lia) INBB BBAL BBC INBM BMAL BMC INR RAL RC PPAL PPC LOC ltac:(clear; lia)
             ART0 MI0 CALL ltac:(clear - HSTK; lia) T c HA).
    intros c' HAS. apply Hk. unfold apost.
    eapply ASTA_conseq; [exact HAS|]. cbv beta. intros ms (m' & RS & AFT & PRm & PPC7).
    pose proof AFT as (ART7 & MI7 & WM7 & ST7).
    exists (Z_to_bv 64 1), m'. split; [exact RS|]. split; [exact (conj ART7 (conj MI7 ST7))|].
    split; [intros x Hx Ho; apply (PRm x Hx); cbn [outside] in Ho |- *; clear - Ho; tauto|].
    split; [apply (cl_env_agree m m' _ _ ENV); intros a Ha; pose proof (cl_cell_static _ Ha) as Hs; apply PRm; [apply acl_static; exact Hs|];
            pose proof (STO _ Hs) as S4; cbn [outside]; clear - S4; lia|].
    exists (k_bm K). split; [reflexivity|]. split; [exact WM7|]. split; [exact PPC7|].
    rewrite <- EBM. replace (len - off) with len by (clear - EO; lia).
    assert (MBX0 : mbio_repx (rt_live RT Σ) m K BI BM (Z_to_bv 64 len) meth len max 0) by (rewrite <- EO; exact MBX).
    eapply mbio_repx_agree; [exact MBX0|]. intros a (e & He & Ha). destruct e as [p n]. cbn [fst snd] in Ha.
    apply PRm; [exact (acl_live _ _ _ p n _ (mbio_rep_ents _ _ _ _ _ _ _ _ _ MB He) Ha)|].
    pose proof (PPAP _ He) as PA. cbn [fst snd] in PA. cbn [outside]. clear - Ha PA. lia.
Qed.
End CBctrlF.
