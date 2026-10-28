(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit X_aexdefs Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_h_alloc Sj_stage2_iface Atp_hkit4A Atp_fzwA Atp_setcapA Atp_defsA Atp_activewA Atp_pid1A Atp_pidiA Pj_rtkA Pj_cpsA Pj_defsA Pj_hdefsA Imp_hdefsA Imp_ifaceA Imp_libifaceA Imp_ios_defsA Imp_lftoi1A Imp_lftoi2A Imp_lftoi3A Imp_lftoi4A Imp_segdefsA Imp_segA3a Imp_segA3 Imp_segA2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma cells_wf_map_C1 : forall l : list byte, cells_wf (map C1 l).
Proof. induction l as [|b l IH]; [exact I|]. split; [exact I| exact IH]. Qed.

Lemma rw_cells_of_bytes_C1 : forall (m : mem) a (l : list byte), bytes_at bsegs m a l -> wr_at bsegs m a (Z.of_nat (length l)) -> rw_cells bsegs m a (map C1 l).
Proof.
  intros m a l BY WR. split; [split|].
  - exact (cells_wf_map_C1 l).
  - rewrite cells_bytes_map_C1'. exact BY.
  - rewrite cells_size_map_C1'. exact WR.
Qed.

Lemma outside_dec' : forall (W : list (Z * Z)) a, outside W a \/ ~ outside W a.
Proof.
  intros W a. induction W as [|[lo hi] W IH]; [left; exact I|]. cbn [outside].
  destruct IH as [IH|IH]; [| right; intros [_ H]; exact (IH H)].
  destruct (Z_lt_dec a lo) as [H|H]; [left; split; [lia| exact IH]|].
  destruct (Z_lt_dec a hi) as [H'|H']; [right; intros [H0 _]; lia| left; split; [lia| exact IH]].
Qed.

Lemma imp_sh_pro_pieces : imp_sh20 ++ repeat z8 68 ++ imp_sh88 = imp_sh_pro.
Proof. vm_compute. reflexivity. Qed.

Lemma imp_sh_assemble : forall (m : mem) f,
  rw_cells bsegs m (shad f) (map C1 imp_sh20) -> rw_cells bsegs m (shad f + 20) (map C1 (repeat z8 68)) -> rw_cells bsegs m (shad f + 88) (map C1 imp_sh88) ->
  rw_cells bsegs m (shad f) (map C1 imp_sh_pro).
Proof.
  intros m f H1 H2 H3. rewrite <- imp_sh_pro_pieces, !map_app.
  apply rw_cells_app. split; [exact H1|]. rewrite cells_size_map_C1'. change (Z.of_nat (length imp_sh20)) with 20.
  apply rw_cells_app. split; [exact H2|]. rewrite cells_size_map_C1', repeat_length. replace (shad f + 20 + Z.of_nat 68) with (shad f + 88) by lia. exact H3.
Qed.

Section Setup2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PDONE : rts RT -> mem -> Z -> list (Z * Z) -> Prop.
Hypothesis PDT : pdtor_cps RT PDONE.
Hypothesis PDFP : pdone_fpA RT PDONE.
Hypothesis PID : pj_pid_cpsA RT (pj_libA sj_lib) PDONE.
Hypothesis OKARM : forall PMc, imp_okarm_cpsA RT PMc.
Local Ltac ul := unfold FUZZ_STACK, PID_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Definition setupB (m : mem) (usp sp' f n d A8 : Z) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop :=
  (exists (j0 j8 j48 j128 j152 j192 : list byte), rw_cells bsegs m sp' (imp_locals2 j0 j8 f j48 (wz d) j128 j152 j192))
  /\ stk bsegs m (sp' + 216) (usp - 104) /\ rw_cells bsegs m (usp - 104) (imp_savedA cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11)
  /\ (exists h3, rw_cells bsegs m f (fz_hdr (C8 (wz IMP_MAGIC0)) (C8 (wz IMP_HDR_DESC_A)) (C8 (wz e_fuzz)) h3))
  /\ (rw_cells bsegs m (shad f) (map C1 imp_sh20) /\ (exists jx, rw_cells bsegs m (shad f + 20) [CB 68 jx]) /\ rw_cells bsegs m (shad f + 88) (map C1 imp_sh88))
  /\ ((libm m \/ sj_lib m) /\ imp_restA A8 m /\ LOCBA m /\ locx3 m /\ imp_tplocA m /\ lockwA m) /\ aex6A m.

Definition setupF (m : mem) (f : Z) : Prop :=
  (exists jsb, rw_cells bsegs m (f + 32) [CB 88 jsb])
  /\ (exists i0 i1 i2 i3, rw_cells bsegs m (f + 160) [CB 136 i0; CB 136 i1; CB 136 i2; CB 136 i3])
  /\ (exists jos, rw_cells bsegs m (f + 832) [CB 264 jos]) /\ (exists jtmp, rw_cells bsegs m (f + 1168) [CB 24 jtmp]).

Lemma setupF_agree : forall m m' f, setupF m f -> agree_on (fun x => f + 32 <= x < f + 1192) m m' -> setupF m' f.
Proof.
  intros m m' f ((jsb & FB) & (i0 & i1 & i2 & i3 & FI) & (jos & FO) & (jtmp & FT)) AG.
  split; [exists jsb; apply (rw_cells_agree_nw bsegs m m' _ _ FB); intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia|].
  split; [exists i0, i1, i2, i3; apply (rw_cells_agree_nw bsegs m m' _ _ FI); intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia|].
  split; [exists jos; apply (rw_cells_agree_nw bsegs m m' _ _ FO); intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia|].
  exists jtmp; apply (rw_cells_agree_nw bsegs m m' _ _ FT); intros a Ha; apply AG; cbn [cells_size csize Nat.add] in Ha; lia.
Qed.

Section WithPM.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Lemma imp_ctor_iterA : forall (Σ : rts RT) (K : config -> Prop) (usp sp' f lo A8 i : Z)
    (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x t3 t4 t5 t6 : word) Fr fc (m mw : mem) (j : list byte),
  impG (rt_sp0 RT Σ) usp sp' f lo -> 0 <= i <= 3 ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo sp' -> rt_frames RT Σ = [(f, 5%nat)] ->
  rw_cells bsegs m (f + 160 + 136 * i) [CB 136 j] ->
  bytes_at bsegs m (shad f + 20) (repeat z8 68) ->
  wr_at bsegs mw (f + 160) 544 -> wmono bsegs mw m ->
  (forall (x1' a0' a1' a2' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Fr' (m' : mem) (j9 j25 j65 j108 : list byte),
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo sp' -> wmono bsegs m m' ->
     (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> ~ (f + 160 + 136 * i <= bv_unsigned a < f + 160 + 136 * i + 136) -> m' a = m a) ->
     rw_cells bsegs m' (f + 160 + 136 * i) (impl0A (wz 0) j9 j25 j65 j108) ->
     bytes_at bsegs m' (shad f + 20) (repeat z8 68) ->
     aevt Σ K (ctor_st (if Z.ltb i 3 then IMP_CTORS_A else IMP_CTORS_END_A) x1' sp' gp t0' t1' t2' usp a0' a1' a2' a3' a4' a5' a6' a7'
                 f A8 (wz (f + 160 + 136 * i + 72)) (wz (f + 160 + 136 * i)) (136 * (i + 1)) t3' t4' t5' t6' Fr' fc m')) ->
  aevt Σ K (ctor_st IMP_CTORS_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f A8 s2x s7x (136 * i) t3 t4 t5 t6 Fr fc m).
Proof using AF RC FDO MST.
  intros until j. intros G IR ARTx MIx STx FRSx FI SHZ WRF WM0 HK.
  pose proof (impG_facts _ _ _ _ _ G) as (F0 & FLO & SH0 & SLO & SLO' & GLO & GLO' & LO64 & LSP & LUSP & SPH & SPH' & SP6 & F8).
  pose proof G as (FSEG & F64 & FTOP & SHB0 & SHT & SEP & LOW & LOR & UT & SPR & SPA & SPW & SPT).
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (INF : In (f, 5%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity. unfold SHB in SHF0.
  assert (FH : f + 2048 < 2^63) by ul.
  assert (COK : forall mx, stk bsegs mx lo sp' -> call_ok RT Σ mx (Z_to_bv 64 sp') lo).
  { intros mx STm. unfold call_ok. rewrite EU. split; [exact STm|]. split; [lia|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia]. }

  assert (MSTEP : forall (mx : mem) (dd nn : Z), ART RT Σ mx -> bytes_at bsegs mx (shad f + 20) (repeat z8 68) -> wmono bsegs mw mx ->
            f + 160 <= dd -> dd + nn <= f + 704 -> 0 < nn -> checked_dst RT Σ mx (Z_to_bv 64 sp') dd nn).
  { intros mx dd nn HAx SHx WMx D1 D2 NP. unfold checked_dst. rewrite EU. split; [| split].
    - intros _. split.
      + apply (acc_sub bsegs mx (f + 160) 544); [| lia| lia].
        replace (shad f + 20) with (shad (f + 160)) in SHx by (unfold shad; Z.div_mod_to_equations; lia).
        exact (acc_zero_run bsegs mx (f + 160) 68 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) SHx).
      + right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia].
    - intros i0 Hi. right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia].
    - apply (wr_at_sub _ (f + 160) 544); [exact (wr_at_transport bsegs mw mx (f + 160) 544 WRF WMx)| lia| lia| lia]. }

  assert (RTW : forall (mx my : mem) dd nn, rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) sp' dd nn mx my -> f + 160 <= dd -> dd + nn <= f + 704 ->
            forall P : Z -> Prop, (forall x, P x -> ((f <= x < f + 2040 /\ ~ (dd <= x < dd + nn)) \/ (shad f <= x < shad f + 256) \/ (sp' <= x < usp))) -> agree_on P mx my).
  { intros mx my dd nn PR D1 D2 P HP a Ha. apply PR; destruct (HP _ Ha) as [[H1 H2]|[H|H]].
    - right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia].
    - right; right; right; right. exists f, 5%nat. split; [exact INF| rewrite SHF0 in H |- *; unfold shad, SHB; change (fs_size 5) with 2048; Z.div_mod_to_equations; lia].
    - left. ul.
    - exact H2.
    - rewrite SHF0 in H. clear - H SEP F0 FLO LO64 SHF0 D1 D2. rewrite SHF0 in SEP. lia.
    - clear - H FLO LO64 D1 D2. lia. }

  assert (CLW : forall (mx my : mem) W, ART RT Σ mx -> munch W mx my -> wmono bsegs mx my -> (forall a, ~ outside W a -> f + 160 <= a < f + 704) ->
            ART RT Σ my /\ (stk bsegs mx lo sp' -> stk bsegs my lo sp') /\ (bytes_at bsegs mx (shad f + 20) (repeat z8 68) -> bytes_at bsegs my (shad f + 20) (repeat z8 68))).
  { intros mx my W HAx MU WM HW. split; [| split].
    - apply (art_client_write RT AF Σ mx my sp' HAx ltac:(lia)); [| exact WM]. intros a Ha. apply MU.
      destruct (outside_dec' W (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. exfalso. apply Ha. pose proof (HW _ Ho).
      right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia].
    - intros STm. apply (stk_agree_nw bsegs mx my _ _ STm). intros a Ha. apply MU. destruct (outside_dec' W (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. pose proof (HW _ Ho). exfalso. lia.
    - intros SHm. apply (bytes_at_agree bsegs mx my _ _ SHm). intros a Ha. apply MU. destruct (outside_dec' W (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. pose proof (HW _ Ho). exfalso.
      rewrite repeat_length in Ha. rewrite SHF0 in Ha. clear - Ha H SEP F0 SHF0. rewrite SHF0 in SEP. lia. }
  set (I := f + 160 + 136 * i) in *.
  assert (IR' : f + 160 <= I /\ I + 136 <= f + 704) by lia.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk4a usp sp' f A8 i x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x t3 t4 t5 t6 j Fr fc m F0 FH IR FI MIx)|].
  cbv beta. intros ms1 (m1 & j9 & j25 & j32 & j56 & j64 & j65 & j72 & j108 & j112 & -> & MU1 & WM1 & MI1 & FI1). apply evt_done. fold I in MU1, FI1 |- *.
  destruct (CLW m m1 _ ARTx MU1 WM1 ltac:(intros a Ha; cbn [outside] in Ha; lia)) as (ART1 & ST1 & SHZ1). specialize (ST1 STx). specialize (SHZ1 SHZ).

  unfold ctor_st.
  eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m1 (I + 32) 24 z8 lo eq_refl eq_refl eq_refl
            ltac:(ul) ltac:(lia) (MSTEP m1 (I + 32) 24 ART1 SHZ1 (wmono_trans _ _ _ _ WM0 WM1) ltac:(lia) ltac:(lia) ltac:(lia)) ART1 MI1 (COK m1 ST1)).
  intros w0 w1 w2 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2. rewrite EU in ST2, PR2.
  rewrite (ret_pc_even IMP_MS1RET_A) by (unfold IMP_MS1RET_A; lia). change (Z.to_nat 24) with 24%nat in BY2.
  assert (FI2 : rw_cells bsegs m2 I (implA_cells (C8 (Z_to_bv 64 0)) (CB 24 z24) (CB 8 j56) (CB 1 j64) j9 j25 j65 (CB 36 j72) j108 (CB 24 j112))).
  { unfold implA_cells in *.
    apply (cells_mid_update m1 m2 I [C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j9; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 j25; C4 (Z_to_bv 64 12)] 24 j32 z24
             [CB 8 j56; CB 1 j64; CB 7 j65; CB 36 j72; CB 4 j108; CB 24 j112] FI1); [| exact WM2| | reflexivity].
    - apply (RTW m1 m2 _ _ PR2 ltac:(lia) ltac:(lia)). intros x (Hx & Hn). cbn [app cells_size csize Nat.add] in Hx, Hn. left. lia.
    - cbn [cells_size csize Nat.add]. replace (I + Z.of_nat 32) with (I + 32) by lia. exact BY2. }
  assert (SHZ2 : bytes_at bsegs m2 (shad f + 20) (repeat z8 68)).
  { apply (bytes_at_agree bsegs m1 m2 _ _ SHZ1). apply (RTW m1 m2 _ _ PR2 ltac:(lia) ltac:(lia)). intros x Hx. rewrite repeat_length in Hx. right; left. lia. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk4b usp sp' f A8 i _ gp w0 w1 w2 _ g1 g2 g3 g4 g5 g6 g7 s2x w3 w4 w5 w6 (CB 24 z24) (CB 36 j72) (CB 24 j112) j9 j25 j56 j64 j65 j108 F2 fc m2
                             F0 FH IR eq_refl eq_refl eq_refl FI2 MI2)|].
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & FI3). apply evt_done. fold I in MU3, FI3 |- *.
  destruct (CLW m2 m3 _ ART2 MU3 WM3 ltac:(intros a Ha; cbn [outside] in Ha; lia)) as (ART3 & ST3 & SHZ3). specialize (ST3 ST2). specialize (SHZ3 SHZ2).

  unfold ctor_st.
  eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc m3 (I + 112) 24 z8 lo eq_refl eq_refl eq_refl
            ltac:(ul) ltac:(lia) (MSTEP m3 (I + 112) 24 ART3 SHZ3 (wmono_trans _ _ _ _ WM0 (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))) ltac:(lia) ltac:(lia) ltac:(lia))
            ART3 MI3 (COK m3 ST3)).
  intros v0 v1 v2 h1 h2 h3' h4 h5 h6 h7 v3 v4 v5 v6 F4 m4 (ART4 & MI4 & WM4 & ST4) PR4 BY4. rewrite EU in ST4, PR4.
  rewrite (ret_pc_even IMP_MS2RET_A) by (unfold IMP_MS2RET_A; lia). change (Z.to_nat 24) with 24%nat in BY4.
  assert (FI4 : rw_cells bsegs m4 I (implA_cells (C8 (Z_to_bv 64 0)) (CB 24 z24) (C8 (Z_to_bv 64 4294967295)) (C1 (Z_to_bv 8 0)) j9 j25 j65 (CB 36 j72) j108 (CB 24 z24))).
  { unfold implA_cells in *.
    apply (cells_mid_update m3 m4 I [C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j9; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 j25; C4 (Z_to_bv 64 12); CB 24 z24;
                                      C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0); CB 7 j65; CB 36 j72; CB 4 j108] 24 j112 z24 [] FI3); [| exact WM4| | reflexivity].
    - apply (RTW m3 m4 _ _ PR4 ltac:(lia) ltac:(lia)). intros x (Hx & Hn). cbn [app cells_size csize Nat.add] in Hx, Hn. left. lia.
    - cbn [cells_size csize Nat.add]. replace (I + Z.of_nat 112) with (I + 112) by lia. exact BY4. }
  assert (SHZ4 : bytes_at bsegs m4 (shad f + 20) (repeat z8 68)).
  { apply (bytes_at_agree bsegs m3 m4 _ _ SHZ3). apply (RTW m3 m4 _ _ PR4 ltac:(lia) ltac:(lia)). intros x Hx. rewrite repeat_length in Hx. right; left. lia. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [apply (imp_walk4c usp sp' f A8 i _ gp v0 v1 v2 _ h1 h2 h3' h4 h5 h6 h7 v3 v4 v5 v6 F4 fc m4)|].
  cbv beta. intros ms5 <-. apply evt_done.

  unfold ctor_st.
  eapply (aevt_memsetP RT RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc m4 (I + 72) 36 z8 lo eq_refl eq_refl eq_refl
            ltac:(ul) ltac:(lia) (MSTEP m4 (I + 72) 36 ART4 SHZ4 (wmono_trans _ _ _ _ WM0 (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM3 WM4))))
                     ltac:(lia) ltac:(lia) ltac:(lia)) ART4 MI4 (COK m4 ST4)).
  intros u0 u1 u2 k1 k2 k3 k4 k5 k6 k7 u3 u4 u5 u6 F6 m6 (ART6 & MI6 & WM6 & ST6) PR6 BY6. rewrite EU in ST6, PR6.
  rewrite (ret_pc_even IMP_MS3RET_A) by (unfold IMP_MS3RET_A; lia). change (Z.to_nat 36) with 36%nat in BY6.
  assert (FI6 : rw_cells bsegs m6 I (impl0A (Z_to_bv 64 0) j9 j25 j65 j108)).
  { unfold impl0A, implA_cells in *.
    apply (cells_mid_update m4 m6 I [C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 j9; C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 3 j25; C4 (Z_to_bv 64 12); CB 24 z24;
                                      C8 (Z_to_bv 64 4294967295); C1 (Z_to_bv 8 0); CB 7 j65] 36 j72 z36 [CB 4 j108; CB 24 z24] FI4); [| exact WM6| | reflexivity].
    - apply (RTW m4 m6 _ _ PR6 ltac:(lia) ltac:(lia)). intros x (Hx & Hn). cbn [app cells_size csize Nat.add] in Hx, Hn. left. lia.
    - cbn [cells_size csize Nat.add]. replace (I + Z.of_nat 72) with (I + 72) by lia. exact BY6. }
  assert (SHZ6 : bytes_at bsegs m6 (shad f + 20) (repeat z8 68)).
  { apply (bytes_at_agree bsegs m4 m6 _ _ SHZ4). apply (RTW m4 m6 _ _ PR6 ltac:(lia) ltac:(lia)). intros x Hx. rewrite repeat_length in Hx. right; left. lia. }

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [apply (imp_walk4d usp sp' f A8 i _ gp u0 u1 u2 _ k1 k2 k3 k4 k5 k6 k7 _ _ u3 u4 u5 u6 F6 fc m6 IR)|].
  cbv beta. intros ms7 <-. apply evt_done.
  apply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 m6 j9 j25 j65 j108 ART6 MI6 ST6); [| | exact FI6| exact SHZ6].
  - exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM3 (wmono_trans _ _ _ _ WM4 WM6)))).
  - intros a Ha Hn. rewrite (PR6 a Ha ltac:(lia)), (PR4 a Ha ltac:(lia)). rewrite (MU3 a ltac:(cbn [outside]; lia)). rewrite (PR2 a Ha ltac:(lia)).
    apply MU1. cbn [outside]. lia.
Qed.

Lemma imp_ctorsA : forall (Σ : rts RT) (K : config -> Prop) (usp sp' f lo A8 : Z)
    (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x t3 t4 t5 t6 : word) Fr fc (m : mem) (i0 i1 i2 i3 : list byte),
  impG (rt_sp0 RT Σ) usp sp' f lo ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo sp' -> rt_frames RT Σ = [(f, 5%nat)] ->
  rw_cells bsegs m (f + 160) [CB 136 i0; CB 136 i1; CB 136 i2; CB 136 i3] ->
  bytes_at bsegs m (shad f + 20) (repeat z8 68) ->
  (forall (x1' a0' a1' a2' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) Fr' (m' : mem),
     ART RT Σ m' -> mem_inv bsegs m' -> stk bsegs m' lo sp' -> wmono bsegs m m' ->
     (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> ~ (f + 160 <= bv_unsigned a < f + 704) -> m' a = m a) ->
     (exists j9 j25 j65 j108, rw_cells bsegs m' (f + 160) (impl0A (wz 0) j9 j25 j65 j108)) ->
     slot0A m' (f + 296) -> slot0A m' (f + 432) -> slot0A m' (f + 568) ->
     bytes_at bsegs m' (shad f + 20) (repeat z8 68) ->
     aevt Σ K (ctor_st IMP_CTORS_END_A x1' sp' gp t0' t1' t2' usp a0' a1' a2' a3' a4' a5' a6' a7'
                 f A8 (wz (f + 160 + 136 * 3 + 72)) (wz (f + 160 + 136 * 3)) (136 * (3 + 1)) t3' t4' t5' t6' Fr' fc m')) ->
  aevt Σ K (ctor_st IMP_CTORS_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f A8 s2x s7x (136 * 0) t3 t4 t5 t6 Fr fc m).
Proof using AF RC FDO MST.
  intros until i3. intros G ARTx MIx STx FRSx FI SHZ HK.
  pose proof FI as [_ WRF]. cbn [cells_size csize Nat.add] in WRF. change (Z.of_nat 544) with 544 in WRF.
  assert (INF : In (f, 5%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).

  lazymatch type of FI with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: nil) => change (c0 :: c1 :: c2 :: c3 :: nil) with ([c0] ++ [c1] ++ [c2] ++ [c3]) in FI end.
  apply rw_cells_app in FI. destruct FI as [B0 FI]. apply rw_cells_app in FI. destruct FI as [B1 FI]. apply rw_cells_app in FI. destruct FI as [B2 B3].
  cbn [cells_size csize Nat.add] in B1, B2, B3.
  replace (f + 160 + Z.of_nat 136) with (f + 160 + 136 * 1) in B1 by lia. replace (f + 160 + Z.of_nat 136 + Z.of_nat 136) with (f + 160 + 136 * 2) in B2 by lia.
  replace (f + 160 + Z.of_nat 136 + Z.of_nat 136 + Z.of_nat 136) with (f + 160 + 136 * 3) in B3 by lia. replace (f + 160) with (f + 160 + 136 * 0) in B0 by lia.

  assert (KEEP : forall (mx my : mem) k a (cs : list cell), rw_cells bsegs mx (f + 160 + 136 * k) cs -> cells_size cs = 136%nat -> 0 <= k <= 3 ->
            (forall b : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned b) -> ~ (a <= bv_unsigned b < a + 136) -> my b = mx b) ->
            (a + 136 <= f + 160 + 136 * k \/ f + 160 + 136 * k + 136 <= a) -> f + 160 <= a -> rw_cells bsegs my (f + 160 + 136 * k) cs).
  { intros mx my k a cs H SZ KR PR D A0. apply (rw_cells_agree_nw bsegs mx my _ _ H). intros b Hb. rewrite SZ in Hb. apply PR; [| lia].
    right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia]. }
  apply (imp_ctor_iterA Σ K usp sp' f lo A8 0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s7x t3 t4 t5 t6 Fr fc m m i0 G ltac:(lia) ARTx MIx STx FRSx B0 SHZ WRF (wmono_refl bsegs m)).
  intros x1a a0a a1a a2a t0a t1a t2a a3a a4a a5a a6a a7a t3a t4a t5a t6a Fa ma j9a j25a j65a j108a ARTa MIa STa WMa PRa FIa SHZa. cbn [Z.ltb].
  apply (imp_ctor_iterA Σ K usp sp' f lo A8 1 _ gp t0a t1a t2a a0a a1a a2a a3a a4a a5a a6a a7a _ _ t3a t4a t5a t6a Fa fc ma m i1 G ltac:(lia) ARTa MIa STa FRSx
           (KEEP m ma 1 _ _ B1 eq_refl ltac:(lia) PRa ltac:(lia) ltac:(lia)) SHZa WRF WMa).
  intros x1b a0b a1b a2b t0b t1b t2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fb mb j9b j25b j65b j108b ARTb MIb STb WMb PRb FIb SHZb. cbn [Z.ltb].
  apply (imp_ctor_iterA Σ K usp sp' f lo A8 2 _ gp t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b _ _ t3b t4b t5b t6b Fb fc mb m i2 G ltac:(lia) ARTb MIb STb FRSx
           (KEEP ma mb 2 _ _ (KEEP m ma 2 _ _ B2 eq_refl ltac:(lia) PRa ltac:(lia) ltac:(lia)) eq_refl ltac:(lia) PRb ltac:(lia) ltac:(lia)) SHZb WRF (wmono_trans _ _ _ _ WMa WMb)).
  intros x1c a0c a1c a2c t0c t1c t2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fc mc j9c j25c j65c j108c ARTc MIc STc WMc PRc FIc SHZc. cbn [Z.ltb].
  apply (imp_ctor_iterA Σ K usp sp' f lo A8 3 _ gp t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c _ _ t3c t4c t5c t6c Fc fc mc m i3 G ltac:(lia) ARTc MIc STc FRSx
           (KEEP mb mc 3 _ _ (KEEP ma mb 3 _ _ (KEEP m ma 3 _ _ B3 eq_refl ltac:(lia) PRa ltac:(lia) ltac:(lia)) eq_refl ltac:(lia) PRb ltac:(lia) ltac:(lia)) eq_refl ltac:(lia) PRc ltac:(lia) ltac:(lia))
           SHZc WRF (wmono_trans _ _ _ _ WMa (wmono_trans _ _ _ _ WMb WMc))).
  intros x1d a0d a1d a2d t0d t1d t2d a3d a4d a5d a6d a7d t3d t4d t5d t6d Fd md j9d j25d j65d j108d ARTd MId STd WMd PRd FId SHZd. cbn [Z.ltb].
  assert (PR : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) sp' (bv_unsigned a) -> ~ (f + 160 <= bv_unsigned a < f + 704) -> md a = m a).
  { intros a Ha Hn. rewrite (PRd a Ha ltac:(lia)), (PRc a Ha ltac:(lia)), (PRb a Ha ltac:(lia)). exact (PRa a Ha ltac:(lia)). }
  apply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fd md ARTd MId STd (wmono_trans _ _ _ _ WMa (wmono_trans _ _ _ _ WMb (wmono_trans _ _ _ _ WMc WMd))) PR); [| | | | exact SHZd].
  - exists j9a, j25a, j65a, j108a. replace (f + 160) with (f + 160 + 136 * 0) by lia.
    exact (KEEP mc md 0 _ _ (KEEP mb mc 0 _ _ (KEEP ma mb 0 _ _ FIa eq_refl ltac:(lia) PRb ltac:(lia) ltac:(lia)) eq_refl ltac:(lia) PRc ltac:(lia) ltac:(lia)) eq_refl ltac:(lia) PRd ltac:(lia) ltac:(lia)).
  - replace (f + 296) with (f + 160 + 136 * 1) by lia. apply (impl0A_slot0A md _ (wz 0) j9b j25b j65b j108b).
    exact (KEEP mc md 1 _ _ (KEEP mb mc 1 _ _ FIb eq_refl ltac:(lia) PRc ltac:(lia) ltac:(lia)) eq_refl ltac:(lia) PRd ltac:(lia) ltac:(lia)).
  - replace (f + 432) with (f + 160 + 136 * 2) by lia. apply (impl0A_slot0A md _ (wz 0) j9c j25c j65c j108c).
    exact (KEEP mc md 2 _ _ FIc eq_refl ltac:(lia) PRd ltac:(lia) ltac:(lia)).
  - replace (f + 568) with (f + 160 + 136 * 3) by lia. exact (impl0A_slot0A md _ (wz 0) j9d j25d j65d j108d FId).
Qed.

Lemma imp_setup2A : forall (Σ0 Σ : rts RT) (K : config -> Prop) (v : option Z) (A8 usp sp' f lo d : Z) (bs : list byte)
    (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x s8x s9x s10x s11x t3 t4 t5 t6 : word) (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    Fr fc (m0 m : mem) (cb : Z),
  let n := Z.of_nat (length bs) in
  impG (rt_sp0 RT Σ0) usp sp' f lo ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo sp' ->
  rt_frames RT Σ = [(f, 5%nat)] -> rt_live RT Σ = xnewA v A8 ++ rt_live RT Σ0 -> rt_sp0 RT Σ = rt_sp0 RT Σ0 -> cb + imp_body_costA n <= rt_credit RT Σ -> 0 <= cb ->
  In (A8, 8) (rt_live RT Σ) -> (forall B, v = Some B -> A8 = B) -> (forall q k, In (q, k) (rt_live RT Σ) -> 0 < k) ->
  Z.of_nat (length (rt_live RT Σ)) + 13 <= LIVE_MAX ->
  0 < d -> n < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p k, In (p, k) (rt_live RT Σ0) /\ p <= d /\ d + n <= p + k) \/ (bs = [] /\ d < SEGTOP_A)) ->
  setupB m usp sp' f n d A8 cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 -> setupF m f ->
  libc_nl m0 -> io_ssp m0 ->
  (forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m a = m0 a) ->
  frm0 fc ->
  imp_fin_k RT PMc K Σ0 v usp lo cra gp (wz TPV_A) cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 cb ->
  aevt Σ K (setup_st IMP_BODY_A x1 sp' gp t0 t1 t2 usp a0 a1 a2 a3 a4 a5 a6 a7 f s4x n s8x s9x s10x s11x t3 t4 t5 t6 Fr fc m).
Proof using AF RC PDT PDFP PID OKARM FDO MST.
  intros until cb. intros n G ARTx MIx STx FRSx LVx SPx CRx CB0 A8IN VA LVP LVB D0 NB BS INLV SB SF NL0 IOS0 PRES FRM KFIN.
  pose proof (impG_facts _ _ _ _ _ G) as (F0 & FLO & SH0 & SLO & SLO' & GLO & GLO' & LO64 & LSP & LUSP & SPH & SPH' & SP6 & F8).
  pose proof G as (FSEG & F64 & FTOP & SHB0 & SHT & SEP & LOW & LOR & UT & SPR & SPA & SPW & SPT).
  assert (EU : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (INF : In (f, 5%nat) (rt_frames RT Σ)) by (rewrite FRSx; left; reflexivity).
  assert (LV0x : forall e, In e (rt_live RT Σ0) -> In e (rt_live RT Σ)) by (intros e He; rewrite LVx; apply in_or_app; right; exact He).
  pose proof (imp_csep RT AF Σ0 Σ m usp sp' f lo ARTx INF LV0x SPx G) as CSEP.
  assert (SHF0 : shad f = f / 8 + SHB) by reflexivity. unfold SHB in SHF0.
  pose proof (af_frames_range RT AF Σ m f 5%nat ARTx INF) as (_ & _ & _ & FLV). change (fs_size 5) with 2048 in FLV.
  pose proof (proj1 (af_fshadow_apart RT AF Σ m f 5%nat ARTx INF)) as FSL. change (fs_size 5) with 2048 in FSL.
  assert (SHF : shad (f + 2048) = shad f + 256) by (unfold shad; Z.div_mod_to_equations; lia). rewrite SHF in FSL.
  pose proof (af_live_range RT AF Σ m A8 8 ARTx A8IN) as (A80 & A8LO & A8SG). rewrite SPx in A8LO.
  destruct SB as ((j0 & j8 & j48 & j128 & j152 & j192 & L2) & STp & SV & (h3 & HD) & (SH20 & (jx & SHX) & SH88) & ((L4 & RS & LB & LX & TP & LK) & AX)).
  destruct SF as ((jsb & FB) & (i0 & i1 & i2 & i3 & FI) & (jos & FO) & (jtmp & FT)).
  assert (N0 : 0 <= n < 2^26) by (subst n; lia).
  assert (DR : 0 <= d < 2^64).
  { destruct INLV as [(p & k & Hin & P1 & P2)|(E & DL)]; [| clear - D0 DL; ul].
    pose proof (af_live_range RT AF Σ m p k ARTx (LV0x _ Hin)) as (R0 & R1 & R2). pose proof (af_sp0_range RT AF Σ m ARTx). clear - D0 P1 P2 R1 N0 H. ul. }
  assert (COK : forall mx, stk bsegs mx lo sp' -> call_ok RT Σ mx (Z_to_bv 64 sp') lo).
  { intros mx STm. unfold call_ok. rewrite EU, SPx. split; [exact STm|]. split; [lia|]. split; [ul|]. split; [ul| clear - SPA; Z.div_mod_to_equations; lia]. }
  pose proof RS as (_ & _ & _ & _ & VEC & _ & VW & _ & A16).

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk3 usp sp' f lo d n A8 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4x s8x s9x s10x s11x t3 t4 t5 t6 j0 j8 j48 j128 j152 j192 Fr fc m
                             F0 FLO SLO' SH0 GLO' LSP LUSP SPH DR ltac:(lia) A80 ltac:(ul) L2 (proj1 VEC) MIx)|].
  cbv beta. intros ms1 (m1 & j8a & j64 & j112 & j128a & -> & MU1 & WM1 & MI1 & L3). apply evt_done.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 sp' ARTx ltac:(rewrite SPx; lia)); [| exact WM1]. intros a Ha. apply MU1. unfold imp_W3. cbn [outside].
    assert (C1 : ~ (sp' <= bv_unsigned a < USTACK_TOP)) by (intros Hc; apply Ha; left; exact Hc). unfold USTACK_TOP in *. repeat split; try exact I; lia. }
  assert (ST1 : stk bsegs m1 lo sp') by (apply (stk_agree_nw bsegs m m1 _ _ STx); intros a Ha; apply MU1; unfold imp_W3; cbn [outside]; repeat split; try exact I; lia).

  eapply (aevt_setshadow RT RC PMc FDO MST Σ K 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m1 (shad f + 20) 68 lo);
    [cbn; tauto| reflexivity| reflexivity| lia| | | exact ART1| exact MI1| exact (COK m1 ST1)|].
  { intros i Hi. exists f, 5%nat. rewrite FRSx. split; [left; reflexivity|]. change (fs_size 5) with 2048. rewrite SHF. lia. }
  { pose proof SHX as [_ W]. cbn [cells_size csize Nat.add] in W. change (Z.of_nat 68) with 68 in W.
    apply (wr_at_agree_nw bsegs m m1 _ _ W). intros a Ha. apply MU1. unfold imp_W3. cbn [outside]. rewrite SHF0 in Ha. clear - Ha SEP F0 SLO LO64 SHF0. rewrite SHF0 in SEP, SLO. repeat split; try exact I; lia. }
  intros v0 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2. rewrite EU in ST2, PR2.
  rewrite (ret_pc_even IMP_SS00RET_A) by (unfold IMP_SS00RET_A; lia). change (Z.to_nat 68) with 68%nat in BY2. change (Z_to_bv 8 0) with z8 in BY2.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [apply (imp_walk4pre usp sp' f A8 _ gp w0 w1 w2 v0 e1 e2 e3 e4 e5 e6 e7 s8x s9x s10x w3 w4 w5 w6 F2 fc m2)|].
  cbv beta. intros ms3 <-. apply evt_done.

  assert (FI2 : rw_cells bsegs m2 (f + 160) [CB 136 i0; CB 136 i1; CB 136 i2; CB 136 i3]).
  { apply (rw_cells_agree_nw bsegs m1 m2 _ _); [apply (rw_cells_agree_nw bsegs m m1 _ _ FI); intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply MU1; unfold imp_W3; cbn [outside]; repeat split; try exact I; lia|].
    intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PR2; [| rewrite SHF0; clear - Ha SEP F0 SHF0; rewrite SHF0 in SEP; lia].
    right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia]. }
  pose proof G as G'. rewrite <- SPx in G'.
  apply (imp_ctorsA Σ K usp sp' f lo A8 _ gp w0 w1 w2 _ e1 e2 e3 e4 e5 e6 e7 _ _ w3 w4 w5 w6 F2 fc m2 i0 i1 i2 i3 G' ART2 MI2 ST2 FRSx FI2 BY2).
  intros x1d a0d a1d a2d t0d t1d t2d a3d a4d a5d a6d a7d t3d t4d t5d t6d Fd m3 ART3 MI3 ST3 WM23 PR3 (j9 & j25 & j65 & j108 & FI3) S13 S23 S33 SHZ3.

  assert (AG03 : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' + 24 <= x < sp' + 144) /\ ~ (f + 160 <= x < f + 704) /\ ~ (shad f + 20 <= x < shad f + 88)) ->
            agree_on P m m3).
  { intros P HP a Ha. destruct (HP _ Ha) as (C0 & C1 & C2 & C3).
    rewrite (PR3 a C0 C2), (PR2 a C0 ltac:(lia)). apply MU1. unfold imp_W3. cbn [outside]. repeat split; try exact I; lia. }
  assert (L33 : rw_cells bsegs m3 sp' (imp_locals3 j0 j8a f (Z_to_bv 64 n) j64 j112 (Z_to_bv 64 d) j128a j152 j192)).
  { apply (rw_cells_agree_nw bsegs m1 m3 _ _ L3). intros a Ha. unfold imp_locals3 in Ha. cbn [cells_size csize Nat.add] in Ha. rewrite (PR3 a), (PR2 a); [reflexivity| | | |]; try (left; ul).
    - rewrite SHF0. clear - Ha SLO LO64 SHF0. lia.
    - clear - Ha FLO LO64. lia. }

  assert (WRX3 : wr_at bsegs m3 (shad f + 20) 68).
  { pose proof SHX as [_ W]. cbn [cells_size csize Nat.add] in W. change (Z.of_nat 68) with 68 in W. exact (wr_at_transport bsegs m m3 _ _ W (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM23))). }
  pose proof (rw_cells_of_bytes_C1 m3 _ _ SHZ3 ltac:(rewrite repeat_length; exact WRX3)) as SHR3.
  pose proof (sh68_pick m3 (shad f + 20) 0 SHR3 ltac:(lia) ltac:(lia) ltac:(ul)) as FS20. rewrite Z.add_0_r in FS20.
  assert (VS3 : ro_cells bsegs m3 (shad A8) [C1 z8]).
  { apply shz_ro1; [| clear - A16; Z.div_mod_to_equations; lia| clear - A80 A8LO LOW LOR UT; ul].
    pose proof (shz_live RT AF Σ m3 A8 8 ART3 A8IN ltac:(clear - A16; Z.div_mod_to_equations; lia)) as SZ. exact SZ. }
  assert (VW3 : rw_cells bsegs m3 A8 [C8 (Z_to_bv 64 SJ_SINGLETON)]).
  { apply (rw_cells_agree_nw bsegs m m3 _ _ VW). apply AG03. intros x Hx. cbn [cells_size csize Nat.add] in Hx. pose proof (FLV A8 8 A8IN) as Y1. pose proof (FSL A8 8 A8IN) as Y2.
    split; [right; right; left; exists A8, 8; split; [exact A8IN| lia]|]. clear - Hx Y1 Y2 A8LO LOW LOR SPR. repeat split; ul. }
  pose proof FI3 as FI3'. unfold impl0A, implA_cells in FI3'.
  lazymatch type of FI3' with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FI3' end.
  apply rw_cells_app in FI3'. destruct FI3' as [FW3 FR3]. cbn [cells_size csize Nat.add] in FR3.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (imp_walk5 usp sp' f lo d n A8 _ gp t0d t1d t2d a0d a1d a2d a3d a4d a5d a6d a7d _ t3d t4d t5d t6d _ j0 j8a j64 j112 j128a j152 j192 Fd fc m3
                             F0 F8 FLO SLO' SH0 GLO' LSP LUSP SPH DR ltac:(lia) A80 ltac:(clear - A8LO LOW; lia) ltac:(clear - A16; Z.div_mod_to_equations; lia)
                             ltac:(unfold shad; clear - A8LO A8SG A80 LOW SPW SPT SHT SHB0 FSEG FTOP; unfold shad, SHB in *; ul) L33 (proj1 VW3) VS3 FS20 FW3 MI3)|].
  cbv beta. intros ms4 (m4 & j160 & -> & MU4 & WM4 & MI4 & LL4 & FW4). apply evt_done.
  assert (W5 : forall a, ~ outside (imp_W5 sp' f) a -> (sp' <= a < sp' + 160) \/ (f + 160 <= a < f + 168)) by (intros a Ha; unfold imp_W5 in Ha; cbn [outside] in Ha; lia).
  assert (AG34 : forall P : Z -> Prop, (forall x, P x -> ~ (sp' <= x < sp' + 160) /\ ~ (f + 160 <= x < f + 168)) -> agree_on P m3 m4).
  { intros P HP a Ha. apply MU4. destruct (outside_dec' (imp_W5 sp' f) (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. pose proof (W5 _ Ho). pose proof (HP _ Ha). exfalso. lia. }
  assert (ART4 : ART RT Σ m4).
  { apply (art_client_write RT AF Σ m3 m4 sp' ART3 ltac:(rewrite SPx; lia)); [| exact WM4]. intros a Ha. apply MU4.
    destruct (outside_dec' (imp_W5 sp' f) (bv_unsigned a)) as [Ho|Ho]; [exact Ho|]. exfalso. apply Ha. destruct (W5 _ Ho) as [H|H]; [left; ul|].
    right; right; right; left. exists f, 5%nat. change (fs_size 5) with 2048. split; [exact INF| lia]. }
  assert (ST4 : stk bsegs m4 lo sp') by (apply (stk_agree_nw bsegs m3 m4 _ _ ST3); apply AG34; intros x Hx; lia).
  assert (AG04 : forall P : Z -> Prop,
            (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' <= x < sp' + 160) /\ ~ (f + 160 <= x < f + 704) /\ ~ (shad f + 20 <= x < shad f + 88)) ->
            agree_on P m m4).
  { intros P HP. eapply agree_trans; [apply AG03; intros x Hx; destruct (HP _ Hx) as (C0 & C1 & C2 & C3); repeat split; try assumption; lia|].
    apply AG34. intros x Hx. destruct (HP _ Hx) as (C0 & C1 & C2 & C3). split; [exact C1| lia]. }

  assert (ZST : forall x, sp' + 160 <= x < usp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' <= x < sp' + 160) /\ ~ (f + 160 <= x < f + 704) /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [left; ul|]. rewrite SHF0. clear - Hx FLO LO64 SLO SHF0. rewrite SHF0 in SLO. lia. }
  assert (ZFR : forall x, (f <= x < f + 160 \/ f + 704 <= x < f + 2040) -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' <= x < sp' + 160) /\ ~ (f + 160 <= x < f + 704) /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [right; right; right; left; exists f, 5%nat; change (fs_size 5) with 2048; split; [exact INF| lia]|].
    rewrite SHF0. clear - Hx FLO LO64 SEP F0 SHF0. rewrite SHF0 in SEP. lia. }
  assert (ZSH : forall x, (shad f <= x < shad f + 20 \/ shad f + 88 <= x < shad f + 156) -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' <= x < sp' + 160) /\ ~ (f + 160 <= x < f + 704) /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [right; right; right; right; exists f, 5%nat; split; [exact INF| change (fs_size 5) with 2048; rewrite SHF; lia]|].
    rewrite SHF0 in Hx |- *. clear - Hx FLO LO64 SEP F0 SLO SHF0. rewrite SHF0 in SEP, SLO. lia. }
  assert (ZCS : forall x, client_static x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' <= x < sp' + 160) /\ ~ (f + 160 <= x < f + 704) /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [right; left; exact Hx|]. pose proof (client_static_range _ Hx) as R. clear - R FSEG SHB0 GLO LOR SPR. ul. }
  assert (ZLV : forall x, in_live (rt_live RT Σ) x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' <= x < sp' + 160) /\ ~ (f + 160 <= x < f + 704) /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. split; [right; right; left; exact Hx|]. destruct Hx as (p & k & Hin & R). pose proof (FLV p k Hin) as Y1. pose proof (FSL p k Hin) as Y2.
    pose proof (af_live_range RT AF Σ m p k ARTx Hin) as (_ & Y3 & _). rewrite SPx in Y3. clear - R Y1 Y2 Y3 LOW LOR SPR. ul. }
  assert (ZRS : forall x, imp_rest_rng A8 x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' <= x < sp' + 160) /\ ~ (f + 160 <= x < f + 704) /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x Hx. unfold imp_rest_rng in Hx. destruct Hx as [H|[H|[H|[H|[H|[H|H]]]]]]; [apply ZCS; apply client_static_intro; lia ..|]. apply ZLV. exists A8, 8. split; [exact A8IN| lia]. }
  assert (ZAX : forall x, in_ranges IMP_AEX_W x -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x /\ ~ (sp' <= x < sp' + 160) /\ ~ (f + 160 <= x < f + 704) /\ ~ (shad f + 20 <= x < shad f + 88)).
  { intros x (l & h & Hin & R). apply ZCS. unfold IMP_AEX_W in Hin. revert R. aex_lits. cbn [In] in Hin. intros R. destruct Hin as [E|[E|[]]]; injection E as <- <-; apply client_static_intro; lia. }

  assert (SH4 : rw_cells bsegs m4 (shad f) (map C1 imp_sh_pro)).
  { apply imp_sh_assemble.
    - apply (rw_cells_agree_nw bsegs m m4 _ _ SH20). apply AG04. intros x Hx. rewrite cells_size_map_C1' in Hx. change (Z.of_nat (length imp_sh20)) with 20 in Hx. apply ZSH. lia.
    - apply rw_cells_of_bytes_C1; [| rewrite repeat_length; exact (wr_at_transport bsegs m3 m4 _ _ WRX3 WM4)].
      apply (bytes_at_agree bsegs m3 m4 _ _ SHZ3). apply AG34. intros x Hx. rewrite repeat_length in Hx. rewrite SHF0 in Hx. clear - Hx SEP F0 SLO LO64 SHF0. rewrite SHF0 in SEP, SLO. lia.
    - apply (rw_cells_agree_nw bsegs m m4 _ _ SH88). apply AG04. intros x Hx. rewrite cells_size_map_C1' in Hx. change (Z.of_nat (length imp_sh88)) with 68 in Hx. apply ZSH. lia. }
  assert (PRES4 : forall a : word, aclient (rt_live RT Σ0) [] usp (bv_unsigned a) -> outside IMP_XFP_A (bv_unsigned a) -> m4 a = m0 a).
  { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply (AG04 (fun x => x = bv_unsigned a)); [| reflexivity]. intros x ->. pose proof (CSEP _ Ha) as (C1 & C2 & C3).
    split; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact LV0x| intros e []| lia]|]. clear - C1 C2 C3 LO64 LUSP. lia. }
  apply (imp_bodyA RT AF RC PDONE PDT PDFP PID OKARM PMc FDO MST Σ0 Σ K v A8 usp sp' f lo d bs gp _ _ _ _ _ _ _ _ _ _ _ t3d t4d t5d t6d
           cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 Fd fc m0 m4 cb G ART4 MI4 ST4 FRSx LVx SPx CRx CB0 A8IN VA LVP LVB D0 NB);
    [| exact INLV| | | exact NL0| exact IOS0| exact PRES4| exact FRM| exact KFIN].
  - apply (bytes_at_agree bsegs m m4 _ _ BS). apply AG04. intros x Hx. cbv beta in Hx. apply ZLV.
    destruct INLV as [(p & k & Hin & P1 & P2)| (E0 & DL)]; [| rewrite E0 in Hx; cbn [length] in Hx; lia]. exists p, k. split; [exact (LV0x _ Hin)| subst n; lia].
  -
    split; [| split; [| split; [| split; [| split; [exact SH4| split; [split; [| split; [| split; [| split; [| split]]]]|]]]]]].
    + exists j0, j8a, j160, j192. exact LL4.
    + apply (stk_agree_nw bsegs m m4 _ _ STp). apply AG04. intros x Hx. cbv beta in Hx. apply ZST. lia.
    + apply (rw_cells_agree_nw bsegs m m4 _ _ SV). apply AG04. intros x Hx. rewrite imp_savedA_size in Hx. apply ZST. lia.
    + exists h3. apply (rw_cells_agree_nw bsegs m m4 _ _ HD). apply AG04. intros x Hx. unfold fz_hdr in Hx. cbn [cells_size csize Nat.add] in Hx. apply ZFR. lia.
    + destruct L4 as [L4|L4]; [left; apply (libm_agree m m4 L4)| right; apply (sj_lib_agree m m4 L4)]; apply AG04; intros x Hx; apply ZCS; apply client_static_intro; unfold sj4_rng in *; lia.
    + apply (imp_restA_agree A8 m m4 RS). apply AG04. intros x Hx. exact (ZRS x Hx).
    + apply (LOCBA_agree m m4 LB). apply AG04. intros x Hx. apply ZCS. apply client_static_intro. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. lia.
    + destruct LX as (X1 & X2 & X3). unfold locx3, LOC_CVC, LOC_CVW in *. split; [| split];
        [apply (rw_cells_agree_nw bsegs m m4 _ _ X1)| apply (rw_cells_agree_nw bsegs m m4 _ _ X2)| apply (rw_cells_agree_nw bsegs m m4 _ _ X3)];
        apply AG04; intros x Hx; cbn [cells_size csize Nat.add] in Hx; apply ZCS; apply client_static_intro; lia.
    + unfold imp_tplocA in *. apply (rw_cells_agree_nw bsegs m m4 _ _ TP). apply AG04. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply ZCS. apply client_static_intro. unfold TPV_A in Hx. lia.
    + apply (lockwA_agree m m4 LK). apply AG04. intros x Hx. apply ZCS. apply client_static_intro. unfold PJ_LOCKW_A in Hx. lia.
    + apply (aex6A_agree m m4 AX). apply AG04. intros x Hx. exact (ZAX x Hx).
  -
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    + exists j9, j25, j65, j108. unfold impl0A, implA_cells. lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) end.
      apply rw_cells_app. split; [exact FW4|]. cbn [cells_size csize Nat.add].
      apply (rw_cells_agree_nw bsegs m3 m4 _ _ FR3). apply AG34. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx FLO LO64. lia.
    + apply (slot0A_agree m3 m4 _ S13). apply AG34. intros x Hx. clear - Hx FLO LO64. lia.
    + apply (slot0A_agree m3 m4 _ S23). apply AG34. intros x Hx. clear - Hx FLO LO64. lia.
    + apply (slot0A_agree m3 m4 _ S33). apply AG34. intros x Hx. clear - Hx FLO LO64. lia.
    + exists jsb. apply (rw_cells_agree_nw bsegs m m4 _ _ FB). apply AG04. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply ZFR. lia.
    + exists jos. apply (rw_cells_agree_nw bsegs m m4 _ _ FO). apply AG04. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply ZFR. lia.
    + exists jtmp. apply (rw_cells_agree_nw bsegs m m4 _ _ FT). apply AG04. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply ZFR. lia.
Qed.

End WithPM.
End Setup2.
