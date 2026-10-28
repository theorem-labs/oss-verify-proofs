(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_setcapA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_setmd. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_deldtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_pdtorA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_hkit3A Atp_createwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition CREATE_STACK : Z := 160 + RT_STACK.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat z8 8.
Proof. reflexivity. Qed.
Lemma le4_zero : le4 (Z_to_bv 64 0) = repeat z8 4.
Proof. reflexivity. Qed.

Section CreateCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis NEW1 : new_cps RT e_new_nt.
Hypothesis MSET : memset_icontract_f RT e_asan_memset.
Hypothesis SETCAP : setcap_cps RT.
Hypothesis SETMD : setmd_cps RT.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.

Local Ltac ul := unfold CREATE_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition create_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (DST cap md : Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a1 = Z_to_bv 64 cap -> a2 = Z_to_bv 64 md -> a3 = Z_to_bv 64 DST -> tp = Z_to_bv 64 0x6a7e68 ->
  32 <= cap <= 2^26 -> 1 <= md <= 4096 ->
  fobj RT Σ m DST 8 -> rw_cells asegs m DST [C8 (Z_to_bv 64 0)] ->
  Z.of_nat (length (rt_live RT Σ)) + 4 <= LIVE_MAX ->
  mcost 96 + mcost (sc_idx cap) + mcost (8 * md) + mcost md <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + CREATE_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                       t3 t4 t5 t6 F fc e_create m)))
    (fun c => exists (Σ' : rts RT) (impl idx oc ia : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(DST, DST + 8)] m m'
         /\ rw_cells asegs m' DST [C8 (Z_to_bv 64 impl)] /\ fobj RT Σ' m' DST 8
         /\ (exists p12 p28 p50, rw_cells asegs m' impl
               (impl16 (Z_to_bv 64 0x164ad0) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 md)
                       (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)))) c
       /\ rt_live RT Σ' = (ia, md) :: (oc, 8 * md) :: (idx, sc_idx cap) :: (impl, 96) :: rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost 96 - mcost (sc_idx cap) - mcost (8 * md) - mcost md
       /\ (0 < impl /\ impl mod 16 = 0) /\ (0 < idx /\ idx mod 16 = 0) /\ (0 < oc /\ oc mod 16 = 0) /\ (0 < ia /\ ia mod 16 = 0)).

Theorem create_ok : create_cps.
Proof using AF NEW1 MSET SETCAP SETMD AFC AFV.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m DST cap md lo
    FDO MST -> -> -> -> CAP MD FOBJ0 DC0 LVB CR0 ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (sc_idx_bounds cap ltac:(lia)) as IXB.
  assert (MC : 0 <= mcost 96 /\ 0 <= mcost (sc_idx cap) /\ 0 <= mcost (8 * md) /\ 0 <= mcost md) by (repeat split; apply mcost_nonneg; lia).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof FOBJ0 as (D8 & _ & (f & k & INF & FLO & FHI) & _). change ((8 + 7) / 8) with 1 in FHI.
  pose proof (fframe_ranges RT AF Σ m f k ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_align RT AF Σ m f k ART0 INF) as (_ & FSEG).
  assert (FP1 : fp_client RT Σ lo [(usp - 64, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).

  pose proof (cr_walk1 usp lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a0 (Z_to_bv 64 cap) (Z_to_bv 64 md) (Z_to_bv 64 DST) a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST0 ltac:(ul) ltac:(ul) ltac:(ul) (conj G1 G2) (AFC Σ m ART0) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FP1 MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ DST 8 ART0 LOW FP1 MU1 FOBJ0) as FOBJ1.
  assert (DC1 : rw_cells asegs m1 DST [C8 (Z_to_bv 64 0)]).
  { apply (rw_cells_agree asegs m m1 _ _ DC0); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1).
    intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbn [outside]. split; [ul| exact I]. }
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -64)) = usp + -64) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -64) mod 16 = 0) by (replace (usp + -64) with (usp + (-4) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).

  apply (NEW1 Σ PMc (Z_to_bv 64 0xba110) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 md) (Z_to_bv 64 DST)
           (Z_to_bv 64 96) (Z_to_bv 64 0x2eae8) (Z_to_bv 64 md) (Z_to_bv 64 DST) a4 a5 a6 a7 (Z_to_bv 64 cap) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
           t3 t4 t5 t6 F fc m1 96 lo FDO MST); try reflexivity; try assumption;
    [.. | split; [exact Hc1'| apply (cfrm0_of_asta RT Σ PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  - lia.
  - lia.
  - lia.
  - rewrite EU2. exact ST1.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact SPA2.
  - intros c2 ((Σ1 & p & Hc2 & LV1 & FRS1 & SP1 & CR1 & P0 & P16 & PTOP) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRP & _) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xba110) in Hc2' by lia.
    assert (INP1 : In (p, 96) (rt_live RT Σ1)) by (rewrite LV1; left; reflexivity).
    assert (P8 : p mod 8 = 0) by (clear - P16; Z.div_mod_to_equations; lia).
    pose proof (af_live_range RT AF Σ1 m2 p _ ART2 INP1) as (_ & PR1 & PSEG). rewrite SP1 in PR1.
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (INF1 : In (f, k) (rt_frames RT Σ1)) by (rewrite FRS1; exact INF).
    assert (FR2 : rw_cells asegs m2 (usp + -64) (cr_frame ra s0 s1 s2 s3 s4 s5 j)).
    { apply (rw_cells_agree asegs m1 m2 _ _ FR1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). unfold cr_frame. pres_tac. }
    assert (DC2 : rw_cells asegs m2 DST [C8 (Z_to_bv 64 0)]).
    { apply (rw_cells_agree asegs m1 m2 _ _ DC1); [| exact WM2]. apply (agree_of_pres _ _ _ _ _ _ PRES2). pres_tac. }
    pose proof (fobj_pres RT AF Σ Σ1 _ _ m1 m2 DST 8 ART1 FOBJ1 PRES2 FRS1) as FOBJ2.
    destruct (wr_at_rw_CB m2 p 96 WRP ltac:(lia)) as (jp & PC2). change (Z.to_nat 96) with 96%nat in PC2.
    apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 4; 4; 8; 4; 4; 18; 6; 40]%nat) in PC2; [| reflexivity].
    cbn [mk_CB_cells app] in PC2.
    repeat match type of PC2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jj" in set (j := t) in PC2; clearbody j end.
    pose proof PC2 as ((WF2 & _) & _). cbn [cells_wf cell_wf] in WF2. destruct WF2 as (_ & _ & LJ1 & _ & _ & LJ4 & _ & LJ6 & _).
    assert (FPP : fp_client RT Σ1 lo [(p, p + 96)]).
    { constructor; [| constructor]. right; left. exists p, 96. cbn [fst snd]. split; [exact INP1| lia]. }
    assert (SHZP : forall mx, ART RT Σ1 mx -> cr_shz [(p, p + 96)] mx p).
    { intros mx ARTx m' MU WM. exact (shz_live RT AF Σ1 m' p 96 (art_fp_client RT AF Σ1 mx m' lo _ ARTx LOW1 FPP MU WM) INP1 P8). }

    pose proof (cr_walk2 p jj jj0 jj1 jj2 jj3 jj4 jj5 jj6 jj7 (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 md) (Z_to_bv 64 DST)
                  b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 cap) s3 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc2 m2 P0 ltac:(ul) PSEG (SHZP m2 ART2) PC2 MI2) as W2.
    lazymatch type of W2 with evt asegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.
    destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (m3 & a3' & -> & MU3 & WM3 & MI3 & PC3) & Hc3'). clear Hc3.
    pose proof (art_fp_client RT AF Σ1 m2 m3 lo _ ART2 LOW1 FPP MU3 WM3) as ART3.
    assert (AG23 : agree_on (fun x => ~ (p <= x < p + 96)) m2 m3).
    { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
    assert (ST3 : stk asegs m3 lo (usp + -64)).
    { apply (stk_agree asegs m2 m3 _ _ ST2); [| exact WM3]. eapply agree_sub; [exact AG23|]. intros x Hx. cbv beta in *. ul. }
    destruct (af_acc_live RT AF Σ1 m3 p 96 ART3 INP1) as (WRP3 & ACP3).

    apply (MSET Σ1 PMc (Z_to_bv 64 0xba170) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 md) (Z_to_bv 64 DST)
             (Z_to_bv 64 (p + 32)) (Z_to_bv 64 0) (Z_to_bv 64 18) a3' b4 b5 b6 b7 (Z_to_bv 64 cap) (Z_to_bv 64 p) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6 F2 fc2 m3 (p + 32) 18 (Z_to_bv 8 0) lo FDO MST); try reflexivity; try assumption;
      [.. | split; [exact Hc3'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3'); intros ms0 <-; exact FRM2] |].
    + ul.
    + lia.
    + unfold checked_dst. split; [| split].
      * intros _. split; [exact (acc_sub asegs m3 p 96 (p + 32) 18 ACP3 ltac:(lia) ltac:(lia))|]. left. exists p, 96. split; [exact INP1| lia].
      * intros i Hi. right; right; left. exists p, 96. split; [exact INP1| lia].
      * exact (wr_at_sub m3 p 96 (p + 32) 18 WRP3 ltac:(lia) ltac:(lia) ltac:(lia)).
    + unfold call_ok. rewrite EU2. split; [exact ST3|]. split; [exact LOW1|]. split; [ul|]. split; [ul| exact SPA2].
    + intros c4 (Hc4 & FC4). unfold icpt_post in Hc4.
      destruct (ASTA_unpack_f RT Σ1 _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & BS4) & FRM4 & Hc4'). clear Hc4.
      destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
      cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even 0xba170) in Hc4' by lia.
      assert (PC4 : rw_cells asegs m4 p (cr_cells1 (CB 8 jj) jj1 jj4 (CB 18 (repeat z8 18)) jj6 (CB 40 jj7))).
      { unfold cr_cells1 in *.
        apply (cells_mid_update m3 m4 p [CB 8 jj; C4 (Z_to_bv 64 0); CB 4 jj1; C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 jj4] 18 jj5 (repeat z8 18)
                 [CB 6 jj6; CB 40 jj7] PC3); [| exact WM4| exact BS4| reflexivity].
        apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES4). intros x Hx. cbn [cells_size csize Nat.add app] in Hx. cbv beta in Hx.
        split; [right; right; left; exists p, 96; split; [exact INP1| lia]| lia]. }

      pose proof (cr_walk3 p jj jj1 jj4 (repeat z8 18) jj6 jj7 (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6a7e68) w0 w1 w2 (Z_to_bv 64 md) (Z_to_bv 64 DST)
                    (Z_to_bv 64 (p + 32)) g1 g2 g3 g4 g5 g6 g7 (Z_to_bv 64 cap) s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6 F4 fc4 m4 P0 ltac:(ul) PSEG (SHZP m4 ART4) PC4 MI4) as W3.
      lazymatch type of W3 with evt asegs _ ?X =>
        assert (W3' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W3) end.
      clear W3.
      apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc4'). clear W3'. intros c5 Hc5.
      destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & PC5) & Hc5'). clear Hc5.
      pose proof (art_fp_client RT AF Σ1 m4 m5 lo _ ART4 LOW1 FPP MU5 WM5) as ART5.
      assert (AG45 : agree_on (fun x => ~ (p <= x < p + 96)) m4 m5).
      { apply (agree_of_munch _ _ _ _ MU5). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
      assert (ST5 : stk asegs m5 lo (usp + -64)).
      { apply (stk_agree asegs m4 m5 _ _ ST4); [| exact WM5]. eapply agree_sub; [exact AG45|]. intros x Hx. cbv beta in *. ul. }
      destruct (af_acc_live RT AF Σ1 m5 p 96 ART5 INP1) as (WRP5 & ACP5).

      apply (MSET Σ1 PMc (Z_to_bv 64 0xba19c) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6a7e68) w0 w1 w2 (Z_to_bv 64 md) (Z_to_bv 64 DST)
               (Z_to_bv 64 (p + 56)) (Z_to_bv 64 0) (Z_to_bv 64 40) g3 g4 g5 g6 g7 (Z_to_bv 64 cap) (Z_to_bv 64 p) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11
               w3 w4 w5 w6 F4 fc4 m5 (p + 56) 40 (Z_to_bv 8 0) lo FDO MST); try reflexivity; try assumption;
        [.. | split; [exact Hc5'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c5 Hc5'); intros ms0 <-; exact FRM4] |].
      * ul.
      * lia.
      * unfold checked_dst. split; [| split].
        -- intros _. split; [exact (acc_sub asegs m5 p 96 (p + 56) 40 ACP5 ltac:(lia) ltac:(lia))|]. left. exists p, 96. split; [exact INP1| lia].
        -- intros i Hi. right; right; left. exists p, 96. split; [exact INP1| lia].
        -- exact (wr_at_sub m5 p 96 (p + 56) 40 WRP5 ltac:(lia) ltac:(lia) ltac:(lia)).
      * unfold call_ok. rewrite EU2. split; [exact ST5|]. split; [exact LOW1|]. split; [ul|]. split; [ul| exact SPA2].
      * intros c6 (Hc6 & FC6). unfold icpt_post in Hc6.
        destruct (ASTA_unpack_f RT Σ1 _ _ c6 Hc6 FC6) as (ms6 & (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & BS6) & FRM6 & Hc6'). clear Hc6.
        destruct RS6 as (x0 & x1 & x2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
        cbn [ms_fcsr] in FRM6. rewrite EU2 in ST6, PRES6. rewrite (ret_pc_even 0xba19c) in Hc6' by lia.
        assert (PC6 : rw_cells asegs m6 p (cr_cells1 (C8 (Z_to_bv 64 0x164ad0)) jj1 jj4 (CB 18 (repeat z8 18)) jj6 (CB 40 (repeat z8 40)))).
        { unfold cr_cells1 in *.
          apply (cells_mid_update m5 m6 p [C8 (Z_to_bv 64 0x164ad0); C4 (Z_to_bv 64 0); CB 4 jj1; C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 jj4; CB 18 (repeat z8 18); CB 6 jj6]
                   40 jj7 (repeat z8 40) [] PC5); [| exact WM6| exact BS6| reflexivity].
          apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES6). intros x Hx. cbn [cells_size csize Nat.add app] in Hx. cbv beta in Hx.
          split; [right; right; left; exists p, 96; split; [exact INP1| lia]| lia]. }

        assert (AG26 : agree_on (fun x => aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -64) x /\ ~ (p <= x < p + 96)) m2 m6).
        { intros a (Ha & Hn). rewrite (PRES6 a Ha ltac:(lia)), (AG45 a Hn), (PRES4 a Ha ltac:(lia)), (AG23 a Hn). reflexivity. }
        pose proof (af_frames_range RT AF Σ1 m2 f k ART2 INF1) as (_ & _ & _ & FLV). specialize (FLV p 96 INP1).
        assert (FR6 : rw_cells asegs m6 (usp + -64) (cr_frame ra s0 s1 s2 s3 s4 s5 j)).
        { apply (rw_cells_agree_nw asegs m2 m6 _ _ FR2). eapply agree_sub; [exact AG26|]. intros x Hx. unfold cr_frame in Hx.
          cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [left; ul| clear - Hx PR1 LOW LOR; ul]. }
        assert (DC6 : rw_cells asegs m6 DST [C8 (Z_to_bv 64 0)]).
        { apply (rw_cells_agree_nw asegs m2 m6 _ _ DC2). eapply agree_sub; [exact AG26|]. intros x Hx.
          cbn [cells_size csize Nat.add] in Hx. cbv beta. split; [right; right; right; left; exists f, k; split; [exact INF1| lia]| clear - Hx FLV FLO FHI; lia]. }
        assert (FOBJ6 : fobj RT Σ1 m6 DST 8).
        { apply (fobj_agree RT AF Σ1 Σ1 m2 m6 DST 8 ART2 FOBJ2 eq_refl).
          destruct (fobj_shadow_range RT AF Σ1 m2 DST 8 ART2 FOBJ2) as (f' & k' & INF' & S1' & S2' & _).
          pose proof (af_fshadow_apart RT AF Σ1 m2 f' k' ART2 INF') as (SL & _). specialize (SL p 96 INP1).
          eapply agree_sub; [exact AG26|]. intros x Hx. cbv beta in Hx. change ((8 + 7) / 8) with 1 in *.
          split; [right; right; right; right; exists f', k'; split; [exact INF'| lia]| clear - Hx SL S1' S2'; lia]. }

        assert (PC6' : rw_cells asegs m6 p (impl_cells (Z_to_bv 64 0x164ad0) (Z_to_bv 64 0) jj1 (Z_to_bv 64 0) (le4 (Z_to_bv 64 0) ++ jj4) (Z_to_bv 64 0)
                                                       (repeat z8 10 ++ jj6 ++ repeat z8 40))).
        { pose proof PC6 as ((W6 & _) & _). unfold cr_cells1 in W6. cbn [cells_wf cell_wf] in W6. destruct W6 as (_ & _ & L1 & _ & _ & L4 & _ & L6 & _).
          apply (rw_cells_relayout m6 p _ _ PC6).
          - unfold impl_cells. cbn [cells_wf cell_wf]. rewrite !length_app, !repeat_length, length_le4, L4, L6. repeat split; [exact L1].
          - unfold impl_cells, cr_cells1. cbn [cells_bytes cbytes]. rewrite le8_zero. rewrite <- ?app_assoc. reflexivity.
          - reflexivity. }

        assert (FPD : forall Σx, rt_frames RT Σx = rt_frames RT Σ -> fp_client RT Σx lo [(DST, DST + 8)]).
        { intros Σx E. constructor; [| constructor]. right; right. exists f, k. cbn [fst snd]. split; [rewrite E; exact INF| lia]. }
        assert (SHZ6 : cr_shz4 [(DST, DST + 8)] m6 DST p).
        { intros m' MU WM. pose proof (art_fp_client RT AF Σ1 m6 m' lo _ ART6 LOW1 (FPD Σ1 FRS1) MU WM) as ART'.
          split; [exact (fobj_shz RT AF Σ1 m' DST 8 ART' (fobj_munch RT AF Σ1 m6 m' lo _ DST 8 ART6 LOW1 (FPD Σ1 FRS1) MU FOBJ6))|].
          split; [exact (shz_live RT AF Σ1 m' p 96 ART' INP1 P8)|].
          change 96 with (8 * (96 / 8)). apply shz_of_acc; [| reflexivity| lia].
          apply (acc_lit RT AF Σ1 m' _ _ ART'). unfold ACC_LITS. repeat (first [left; reflexivity | right]). }
        pose proof (cr_walk4 p DST cap (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) jj1 (le4 (Z_to_bv 64 0) ++ jj4) (repeat z8 10 ++ jj6 ++ repeat z8 40)
                      (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6a7e68) x0 x1 x2 (Z_to_bv 64 md) (Z_to_bv 64 (p + 56)) h1 h2 h3 h4 h5 h6 h7
                      s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 F6 fc6 m6 P0 ltac:(ul) PSEG ltac:(ul) ltac:(ul) ltac:(clear - FLV FLO FHI; lia)
                      SHZ6 (AFV Σ1 m6 ART6) DC6 PC6' MI6) as W4.
        lazymatch type of W4 with evt asegs _ ?X =>
          assert (W4' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
        clear W4.
        apply (cps_realizes asegs _ _ _ c6 (asta_evt_c RT AF Σ1 PMc _ _ MST W4') Hc6'). clear W4'. intros c7 Hc7.
        destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & DC7 & PC7) & Hc7'). clear Hc7.
        pose proof (art_fp_client RT AF Σ1 m6 m7 lo _ ART6 LOW1 (FPD Σ1 FRS1) MU7 WM7) as ART7.
        pose proof (fobj_munch RT AF Σ1 m6 m7 lo _ DST 8 ART6 LOW1 (FPD Σ1 FRS1) MU7 FOBJ6) as FOBJ7.
        assert (AG67 : agree_on (fun x => ~ (DST <= x < DST + 8)) m6 m7).
        { apply (agree_of_munch _ _ _ _ MU7). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
        assert (ST7 : stk asegs m7 lo (usp + -64)).
        { apply (stk_agree asegs m6 m7 _ _ ST6); [| exact WM7]. eapply agree_sub; [exact AG67|]. intros x Hx. cbv beta in *. ul. }
        assert (FR7 : rw_cells asegs m7 (usp + -64) (cr_frame ra s0 s1 s2 s3 s4 s5 j)).
        { apply (rw_cells_agree_nw asegs m6 m7 _ _ FR6). eapply agree_sub; [exact AG67|]. intros x Hx. unfold cr_frame in Hx.
          cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }

        apply (SETCAP Σ1 PMc (Z_to_bv 64 0xba230) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6a7e68) x0 x1 x2 (Z_to_bv 64 md) (Z_to_bv 64 DST)
                 (Z_to_bv 64 p) (Z_to_bv 64 cap) (Z_to_bv 64 0xe3090) h3 h4 h5 h6 h7 (Z_to_bv 64 cap) (Z_to_bv 64 p) (Z_to_bv 64 2147450880)
                 (Z_to_bv 64 (DST / 8 + 2147450880)) s6 s7 s8 s9 s10 s11 x3 x4 x5 x6 F6 fc6 m7 p cap (Z_to_bv 64 0x164ad0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 jj1 (le4 (Z_to_bv 64 0) ++ jj4) (repeat z8 10 ++ jj6 ++ repeat z8 40) lo FDO MST); try reflexivity; try assumption;
          [.. | split; [exact Hc7'| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c7 Hc7'); intros ms0 <-; exact FRM6] |].
        -- lia.
        -- rewrite LV1. cbn [length]. lia.
        -- rewrite CR1. lia.
        -- rewrite EU2. exact ST7.
        -- rewrite EU2. ul.
        -- rewrite EU2. ul.
        -- rewrite EU2. exact SPA2.
        -- intros c8 ((Σ2 & idx & Hc8 & LV2 & FRS2 & SP2 & CR2 & IX0 & IX16) & FC8).
           destruct (ASTA_unpack_f RT Σ2 _ _ c8 Hc8 FC8) as (ms8 & (m8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & PC8 & _) & FRM8 & Hc8'). clear Hc8.
           destruct RS8 as (y0 & y1 & y2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & y3 & y4 & y5 & y6 & F8 & fc8 & ->).
           cbn [ms_fcsr] in FRM8. rewrite EU2 in ST8, PRES8. rewrite (ret_pc_even 0xba230) in Hc8' by lia.
           assert (INP2 : In (p, 96) (rt_live RT Σ2)) by (rewrite LV2; right; exact INP1).
           assert (INX2 : In (idx, sc_idx cap) (rt_live RT Σ2)) by (rewrite LV2; left; reflexivity).
           assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW1).
           assert (FRS2' : rt_frames RT Σ2 = rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
           assert (FR8 : rw_cells asegs m8 (usp + -64) (cr_frame ra s0 s1 s2 s3 s4 s5 j)).
           { apply (rw_cells_agree_nw asegs m7 m8 _ _ FR7). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES8). intros x Hx. unfold cr_frame in Hx.
             cbn [cells_size csize Nat.add] in Hx. split; [left; ul|]. cbn [outside]. split; [clear - Hx PR1 LOW LOR; ul| exact I]. }
           assert (DC8 : rw_cells asegs m8 DST [C8 (Z_to_bv 64 p)]).
           { apply (rw_cells_agree_nw asegs m7 m8 _ _ DC7). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES8). intros x Hx.
             cbn [cells_size csize Nat.add] in Hx. split; [right; right; right; left; exists f, k; split; [exact INF1| lia]|].
             cbn [outside]. split; [clear - Hx FLV FLO FHI; lia| exact I]. }
           assert (FOBJ8 : fobj RT Σ2 m8 DST 8).
           { apply (fobj_agree RT AF Σ1 Σ2 m7 m8 DST 8 ART7 FOBJ7 FRS2).
             destruct (fobj_shadow_range RT AF Σ1 m7 DST 8 ART7 FOBJ7) as (f' & k' & INF' & S1' & S2' & _).
             pose proof (af_fshadow_apart RT AF Σ1 m7 f' k' ART7 INF') as (SL & _). specialize (SL p 96 INP1).
             apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES8). intros x Hx. cbv beta in Hx. change ((8 + 7) / 8) with 1 in *.
             split; [right; right; right; right; exists f', k'; split; [exact INF'| lia]|]. cbn [outside]. split; [clear - Hx SL S1' S2'; lia| exact I]. }

           assert (SHV8 : shz m8 0x164ac0 96).
           { change 96 with (8 * (96 / 8)). apply shz_of_acc; [| reflexivity| lia].
             apply (acc_lit RT AF Σ2 m8 _ _ ART8). unfold ACC_LITS. repeat (first [left; reflexivity | right]). }
           pose proof (cr_walk5 usp lo p DST md (Z_to_bv 64 0) (Z_to_bv 64 idx) (Z_to_bv 64 cap) jj1 (le4 (Z_to_bv 64 0) ++ jj4) (repeat z8 10 ++ jj6 ++ repeat z8 40) j
                         gp (Z_to_bv 64 0x6a7e68) y0 y1 y2 k1 k2 k3 k4 k5 k6 k7 (Z_to_bv 64 cap) s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 ra s0 s1 s2 s3 s4 s5 F8 fc8 m8
                         ST8 ltac:(ul) ltac:(ul) ltac:(ul) P0 ltac:(ul) PSEG ltac:(ul) ltac:(ul)
                         (fobj_shz RT AF Σ2 m8 DST 8 ART8 FOBJ8) (shz_live RT AF Σ2 m8 p 96 ART8 INP2 P8) SHV8 (AFV Σ2 m8 ART8) FR8 DC8 PC8 MI8) as W5.
           lazymatch type of W5 with evt asegs _ ?X =>
             assert (W5' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W5) end.
           clear W5.
           apply (cps_realizes asegs _ _ _ c8 (asta_evt_c RT AF Σ2 PMc _ _ MST W5') Hc8'). clear W5'. intros c9 Hc9.
           destruct (ASTA_unpack RT Σ2 _ _ c9 Hc9) as (ms9 & (m9 & -> & MU9 & WM9 & MI9 & ST9) & Hc9'). clear Hc9.
           assert (E89 : forall a : word, m9 a = m8 a) by (intros a; apply MU9; exact I).
           assert (AG89 : forall P : Z -> Prop, agree_on P m8 m9) by (intros P a _; exact (E89 a)).
           assert (ART9 : ART RT Σ2 m9) by (apply (art_fp_client RT AF Σ2 m8 m9 lo [] ART8 LOW2 ltac:(constructor) MU9 WM9)).

           assert (PC9 : rw_cells asegs m9 p (impl_cells2 (le8 (Z_to_bv 64 0x164ad0) ++ le4 (Z_to_bv 64 0) ++ jj1 ++ le8 (Z_to_bv 64 idx) ++ (le4 (Z_to_bv 64 0) ++ jj4)
                                                             ++ le8 (Z_to_bv 64 cap)) (Z_to_bv 64 0) (repeat z8 2 ++ jj6) (Z_to_bv 64 0) (Z_to_bv 64 0) (repeat z8 24))).
           { apply (rw_cells_agree_nw asegs m8 m9 _ _) in PC8; [| apply AG89].
             pose proof PC8 as ((W8 & _) & _). unfold impl_cells in W8. cbn [cells_wf cell_wf] in W8. destruct W8 as (_ & _ & L1 & _ & L24 & _ & L56 & _).
             rewrite !length_app, !repeat_length in L56. rewrite length_app, length_le4 in L24.
             apply (rw_cells_relayout m9 p _ _ PC8).
             - unfold impl_cells2. cbn [cells_wf cell_wf]. rewrite !length_app, !repeat_length, !length_le8, !length_le4, L1.
               repeat split; lia.
             - unfold impl_cells, impl_cells2. cbn [cells_bytes cbytes]. rewrite le8_zero. rewrite <- ?app_assoc. reflexivity.
             - reflexivity. }
           rewrite <- ESP in Hc9'.

           apply (SETMD Σ2 PMc ra sp gp (Z_to_bv 64 0x6a7e68) y0 (Z_to_bv 64 0xe31f0) y2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 md) (Z_to_bv 64 0) k3 k4 k5 k6 k7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6 F8 fc8 m9 p md (Z_to_bv 64 0)
                    (le8 (Z_to_bv 64 0x164ad0) ++ le4 (Z_to_bv 64 0) ++ jj1 ++ le8 (Z_to_bv 64 idx) ++ (le4 (Z_to_bv 64 0) ++ jj4) ++ le8 (Z_to_bv 64 cap))
                    (repeat z8 2 ++ jj6) (repeat z8 24) lo FDO MST); try reflexivity; try assumption;
             [.. | split; [exact Hc9'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c9 Hc9'); intros ms0 <-; exact FRM8] |].
           ++ rewrite LV2, LV1. cbn [length]. lia.
           ++ rewrite CR2, CR1. lia.
           ++ fold usp. ul.
           ++ intros c10 ((Σ3 & oc & ia & Hc10 & LV3 & FRS3 & SP3 & CR3 & OC0 & OC16 & IA0 & IA16) & FC10).
              apply Hk. split; [| exact FC10]. exists Σ3, p, idx, oc, ia.
              split; [| split; [rewrite LV3, LV2, LV1; reflexivity| split; [rewrite FRS3; exact FRS2'| split; [rewrite SP3, SP2, SP1; reflexivity|
                          split; [rewrite CR3, CR2, CR1; lia| repeat split; assumption]]]]].
              eapply ASTA_conseq; [exact Hc10|]. intros ms (m10 & RS10 & AFT10 & PRES10 & PC10 & _). fold usp in AFT10, PRES10. exists m10.
              split; [exact RS10|].
              destruct AFT10 as (ART10 & MI10 & WM10 & ST10).
              split; [split; [exact ART10| split; [exact MI10| split; [| exact ST10]]]|].
              { exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM3 (wmono_trans _ _ _ _ WM4 (wmono_trans _ _ _ _ WM5
                        (wmono_trans _ _ _ _ WM6 (wmono_trans _ _ _ _ WM7 (wmono_trans _ _ _ _ WM8 (wmono_trans _ _ _ _ WM9 WM10))))))))). }
              assert (INF2 : In (f, k) (rt_frames RT Σ2)) by (rewrite FRS2; exact INF1).
              split; [| split; [| split]].
              **
                 intros a Ha Hout. cbn [outside] in Hout. destruct Hout as (HO & _).
                 pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
                 pose proof (fresh_apart RT AF Σ Σ1 m2 [(p, 96)] p 96 usp (bv_unsigned a) ART2 LV1 ltac:(left; reflexivity) FRS1 SP1 ltac:(ul) Ha) as NP.
                 assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -64) (bv_unsigned a)).
                 { apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; intros e He; right; exact He| rewrite FRS1; auto| lia]. }
                 assert (Ha2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp (bv_unsigned a)).
                 { apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV2, LV1; intros e He; right; right; exact He| rewrite FRS2'; auto| lia]. }
                 rewrite (PRES10 a Ha2), (E89 a), (PRES8 a Ha1), (AG67 _ HO), (AG26 _ (conj Ha1 NP)), (PRES2 a), (MU1 a); [reflexivity| | | |].
                 --- cbn [outside]. split; [clear - SPL LOW LOR; ul| exact I].
                 --- apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia].
                 --- cbn [outside]. split; [exact NP| exact I].
                 --- cbn [outside]. split; [exact NP| exact I].
              **
                 apply (rw_cells_agree_nw asegs m8 m10 _ _ DC8). eapply agree_trans; [apply AG89|].
                 apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES10). intros x Hx.
                 cbn [cells_size csize Nat.add] in Hx. split; [right; right; right; left; exists f, k; split; [exact INF2| lia]|].
                 cbn [outside]. split; [clear - Hx FLV FLO FHI; lia| exact I].
              ** apply (fobj_agree RT AF Σ2 Σ3 m8 m10 DST 8 ART8 FOBJ8 FRS3).
                 destruct (fobj_shadow_range RT AF Σ2 m8 DST 8 ART8 FOBJ8) as (f' & k' & INF' & S1' & S2' & _).
                 pose proof (af_fshadow_apart RT AF Σ2 m8 f' k' ART8 INF') as (SL & _). specialize (SL p 96 INP2).
                 eapply agree_trans; [apply AG89|].
                 apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES10). intros x Hx. cbv beta in Hx. change ((8 + 7) / 8) with 1 in *.
                 split; [right; right; right; right; exists f', k'; split; [exact INF'| lia]|]. cbn [outside]. split; [clear - Hx SL S1' S2'; lia| exact I].
              **
                 pose proof PC10 as ((W10 & _) & _). unfold impl_cells2 in W10. cbn [cells_wf cell_wf] in W10. destruct W10 as (L40 & _ & L48 & _).
                 rewrite !length_app, !length_le8, !length_le4 in L40. rewrite length_app, repeat_length in L48.
                 exists jj1, jj4, jj6.
                 apply (rw_cells_relayout m10 p _ _ PC10).
                 --- unfold impl16. cbn [cells_wf cell_wf]. repeat split; assumption.
                 --- unfold impl16, impl_cells2. cbn [cells_bytes cbytes]. rewrite le8_zero. rewrite <- ?app_assoc. reflexivity.
                 --- reflexivity.
Qed.

End CreateCPS.
