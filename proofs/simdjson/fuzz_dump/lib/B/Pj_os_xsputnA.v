(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem F_imemmove I_qck Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_os_defsA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Pj_os_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac br_is b tac := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b by (symmetry; tac) end; cbv_concl_iota.

Lemma acc_agree : forall (m m' : mem) a n, acc bsegs m a n -> agree_on (fun x => shad a <= x <= shad (a + n)) m m' -> acc bsegs m' a n.
Proof.
  intros m m' a n H AG i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  apply (bytes_at_agree bsegs m m' _ _ Hb). intros x Hx. cbn [length] in Hx. apply AG. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

Lemma lts_small : forall x y, 0 <= x < 2^63 -> 0 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. rewrite bv_lts_lxor, !unsigned_lit by lia. rewrite !zb_lxor_pow2_small by lia.
  destruct (Z.ltb_spec x y), (Z.ltb_spec (x + 2^63) (y + 2^63)); lia.
Qed.

Lemma rw_cells_CB_cut3 : forall (m : mem) A (n : nat) (bs : list byte) (a k : Z),
  0 <= a -> 0 <= k -> a + k <= Z.of_nat n -> rw_cells bsegs m A [CB n bs] ->
  rw_cells bsegs m A ([CB (Z.to_nat a) (firstn (Z.to_nat a) bs)] ++ [CB (Z.to_nat k) (firstn (Z.to_nat k) (skipn (Z.to_nat a) bs))]
                       ++ [CB (n - Z.to_nat a - Z.to_nat k) (firstn (n - Z.to_nat a - Z.to_nat k) (skipn (Z.to_nat k) (skipn (Z.to_nat a) bs)))]).
Proof.
  intros m A n bs a k Ha Hk Hn H.
  apply (rw_cells_split_CB bsegs _ _ [] n bs [] [Z.to_nat a; Z.to_nat k; (n - Z.to_nat a - Z.to_nat k)%nat]) in H; [| cbn; lia].
  cbn [mk_CB_cells app] in H. exact H.
Qed.

Lemma bytes_at_sub : forall (m : mem) A (bs : list byte) (i k : Z), bytes_at bsegs m A bs -> 0 <= i -> 0 <= k -> i + k <= Z.of_nat (length bs) ->
  bytes_at bsegs m (A + i) (firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)).
Proof.
  intros m A bs i k H Hi Hk Hl.
  rewrite <- (firstn_skipn (Z.to_nat i) bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite firstn_length_le in H by lia. rewrite Z2Nat.id in H by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) (skipn (Z.to_nat i) bs)) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Section Xsputn.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Hypothesis ROA : forall Σ m, ART RT Σ m -> pj_os_roA m.

Local Ltac ul := unfold PJ_OS_XSPUTN_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma overflow_walk : forall (OS spv lo : Z) (b : byte) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (pb pp ep : word) F fc (m : mem),
  0x6cd000 <= OS -> OS + 288 < 2^47 -> OS mod 8 = 0 ->
  (forall m', munch [(spv - 16, spv); (OS + 40, OS + 64)] m m' -> wmono bsegs m m' -> shz m' OS 288) -> client_consts m ->
  rw_cells bsegs m (OS + 40) [C8 pb; C8 pp; C8 ep] -> mem_inv bsegs m ->
  stk bsegs m lo spv -> lo + 16 <= spv -> 0x6cd000 <= lo -> spv < 2^47 -> (OS + 288 <= spv - 16 \/ spv <= OS) ->
  evt bsegs (fun ms => exists (a1' a2' a3' a4' a5' : word) (m' : mem),
      ms = MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned b)) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(spv - 16, spv); (OS + 40, OS + 64)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo spv
      /\ rw_cells bsegs m' (OS + 40) [C8 (Z_to_bv 64 (OS + 64)); C8 (Z_to_bv 64 (OS + 64)); C8 (Z_to_bv 64 (OS + 128))])
    (MS (mkR ra (Z_to_bv 64 spv) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 OS) (Z_to_bv 64 (bv_unsigned b)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_OVERFLOW_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OSLO OSHI OS8 SHZ (G1 & G2 & _) PUT MI ST LO GLO SPH SEP. unfold PJ_OVERFLOW_A.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, SHB in *.
  assert (ESP : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(spv - 16, spv); (OS + 40, OS + 64)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  assert (EO : bv_unsigned (Z_to_bv 64 OS) = OS) by (apply unsigned_lit; lia).
  assert (RB : 0 <= bv_unsigned b < 256) by (pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia).
  zstep. zstep.

  zstep. zstep. zstep. if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; lia|]. clear G.
  zstep. zstep. zstep.
  shz_pose SHZ (OS + 48).
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  shz_pose SHZ (OS + 40).
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep.
  shz_pose SHZ (OS + 56).
  zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. zstep.
  zstep. zstep.
  zstep. zstep. zstep.
  release_frame FR ST spv.
  zstep.
  apply evt_done.
  replace (bv_unsigned b + 1 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
  replace (Z.land 18446744073709551615 (bv_unsigned b)) with (bv_unsigned b)
    by (symmetry; rewrite Z.land_comm; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  do 6 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| eassumption]; intros x Hx; cbn [outside] in *; lia|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  replace (OS + 40 + 8 + 8) with (OS + 56) in * by lia. replace (OS + 40 + 8) with (OS + 48) in * by lia.
  eassumption.
Qed.

Definition PUTINVA (OS pp ep : Z) : Prop := (pp = 0 /\ ep = 0) \/ (ep = OS + 128 /\ OS + 64 <= pp <= OS + 128).

Theorem xsputn_okA : xsputn_cpsA RT PMc.
Proof using AF RC RC2 FDO MST ROA.
  unfold xsputn_cpsA. intros until m. intros FDO' MST' INF FLO FHI AL16 SBF HULL RO BUF NR SP0 SLO ACC BCL SEP ART0 MI ST LOW LOR SPT SP16 HK.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _ & FLIVE).
  pose proof (af_frames_align RT AF Σ m fO kO ART0 INF) as (_ & FSEG).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold PJ_OS_XSPUTN_STACK_A in *. unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *. remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (LO64 : lo <= q - 64) by lia. assert (Q0 : 0 <= q - 64) by (destruct ST; lia).
  assert (UQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  assert (UQ64 : bv_unsigned (wz (q + -64)) = q + -64) by (apply unsigned_lit; lia).
  assert (LBS : length bs = Z.to_nat CAP) by (destruct BUF as [[[L _] _] _]; exact L).
  assert (LBZ : Z.of_nat (length bs) = CAP) by (rewrite LBS; lia).
  assert (SRB : bytes_at bsegs m S bs) by (destruct BUF as [[_ B] _]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B; exact B).
  destruct HULL as [(bo & FO) SHB].

  apply (rw_cells_split_CB bsegs _ _ [] 288 _ [] [128; 160]%nat) in FO; [| reflexivity]. cbn [mk_CB_cells app] in FO.
  lazymatch type of FO with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FO end.
  apply Sj_stage1_kit.rw_cells_app in FO. destruct FO as [_ FO]. cbn [cells_size csize Nat.add] in FO. replace (OS + Z.of_nat 128) with (OS + 128) in FO by lia.
  lazymatch type of FO with rw_cells _ _ _ [CB 160 ?t] => set (bo2 := t) in FO; clearbody bo2 end.
  unfold sb_cellsA in SBF.
  takeZ SBF 8%nat (OS + 64)%Z SBH. rename SBF into DUM.

  assert (CL : forall sp' x, (q + -64 <= x < q /\ sp' <= q + -64) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ)) ->
            aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros sp' x [[H1 H2]|[H|H]]; [left; ul| right; right; right; left| do 4 right]; (exists fO, kO; rewrite <- EFSZ; split; [exact INF| exact H]). }
  assert (CLS : forall sp' x, S <= x < S + CAP -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp' x).
  { intros sp' x Hx. (destruct BCL as [(p & k & Hin & P1 & P2)|(B1 & B2)]; [| rewrite <- EFSZ in B2]); [right; right; left; exists p, k; split; [exact Hin| lia]|].
    right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (ACCX : forall mx, ART RT Σ mx ->
            (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> mx a = m a) ->
            acc bsegs mx S N).
  { intros mx ARTx EQ. (destruct BCL as [(p & k & Hin & P1 & P2)|(B1 & B2)]; [| rewrite <- EFSZ in B2]).
    - apply (acc_sub bsegs mx p k); [exact (proj2 (af_acc_live RT AF Σ mx p k ARTx Hin))| lia| lia].
    - apply (acc_agree m mx S N ACC). intros a Ha. apply EQ.
      + do 4 right. exists fO, kO. rewrite <- EFSZ. split; [exact INF|]. unfold shad in *. clear - Ha B1 B2 NR. Z.div_mod_to_equations. lia.
      + cbn [outside]. split; [| exact I]. unfold shad in *. clear - Ha B1 B2 NR FSELF FLO FHI F0. Z.div_mod_to_equations. lia. }
  assert (RNGX : forall s n, S <= s -> 0 <= n -> s + n <= S + CAP -> rng_class RT Σ s n).
  { intros s n H1 H2 H3. (destruct BCL as [(p & k & Hin & P1 & P2)|(B1 & B2)]; [| rewrite <- EFSZ in B2]); [left; exists p, k; split; [exact Hin| lia]|].
    right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }

  assert (EXIT : forall (pp ep : Z) (pb' : word) (dum' jf : list byte) (mx : mem) (x1 x5 x6 x7 x9 y0 y1 y2 y3 y4 y5 y6 y7 x18 x19 x20 x21 x28 x29 x30 x31 : word) (Fx : bvmap 5 word),
    ART RT Σ mx -> mem_inv bsegs mx -> stk bsegs mx lo (q + -64) ->
    rw_cells bsegs mx (q + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells bsegs mx OS [C8 (Z_to_bv 64 PJ_SB_VPTR_A); C8 (Z_to_bv 64 PJ_LOC_IMP_A); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 pb'; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep)] ->
    rw_cells bsegs mx (OS + 64) [CB 64 dum'] -> bytes_at bsegs mx (shad OS) (repeat z8 36) ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> mx a = m a) ->
    aevt RT PMc Σ K (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV_A) x5 x6 x7 (Z_to_bv 64 N) x9 y0 y1 y2 y3 y4 y5 y6 y7
                          x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) Fx (Z_to_bv 64 0x111790) fc None mx (seg_rom bsegs))).
  { intros pp ep pb' dum' jf mx x1 x5 x6 x7 x9 y0 y1 y2 y3 y4 y5 y6 y7 x18 x19 x20 x21 x28 x29 x30 x31 Fx ARTx MIx STx FRx SBx DUMx SHx PRESx.
    apply (aevt_evt RT AF PMc MST).
    do 10 lstep.
    release_frame FRx STx q.
    apply evt_done. eapply HK; [exact ARTx| exact MIx| exact STx| | | exact PRESx].
    - split; [| exact SHx].
      assert (FO' : rw_cells bsegs mx (OS + 128) [CB 160 bo2]).
      { eapply rw_cells_agree_nw; [exact FO|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply PRESx; [apply (CL q); right; left; lia| cbn [outside]; lia]. }
      pose proof SBx as X. glueZ X DUMx. glueZ X FO'. exact (rw_cells_forget bsegs mx OS _ X).
    - glueZ SBx DUMx. unfold sb_cellsA. exact SBx. }

  assert (LOOP : forall (k : nat) (done pp ep : Z) (pb' : word) (dum' jf : list byte) (mx : mem) (x1 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 x20 x28 x29 x30 x31 : word) (Fx : bvmap 5 word),
    N - done <= Z.of_nat k -> 0 <= done < N -> PUTINVA OS pp ep ->
    ART RT Σ mx -> mem_inv bsegs mx -> stk bsegs mx lo (q + -64) ->
    rw_cells bsegs mx (q + -64) [CB 8 jf; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells bsegs mx OS [C8 (Z_to_bv 64 PJ_SB_VPTR_A); C8 (Z_to_bv 64 PJ_LOC_IMP_A); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 pb'; C8 (Z_to_bv 64 pp); C8 (Z_to_bv 64 ep)] ->
    rw_cells bsegs mx (OS + 64) [CB 64 dum'] -> bytes_at bsegs mx S bs -> bytes_at bsegs mx (shad OS) (repeat z8 36) ->
    (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> mx a = m a) ->
    aevt RT PMc Σ K (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV_A) x5 x6 x7 (Z_to_bv 64 done) (Z_to_bv 64 N) y0 y1 y2 y3 y4 y5 y6 y7
                          (Z_to_bv 64 (S + done)) (Z_to_bv 64 OS) x20 (Z_to_bv 64 (-1)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       Fx (Z_to_bv 64 0x111730) fc None mx (seg_rom bsegs))).
  { induction k as [|k IH]; intros done pp ep pb' dum' jf mx x1 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 x20 x28 x29 x30 x31 Fx
      HKk HD PI ARTx MIx STx FRx SBx DUMx SRCx SHx PRESx; [lia|].
    assert (RPP : 0 <= pp < 2^62 /\ 0 <= ep < 2^62) by (destruct PI as [[-> ->]|[-> ?]]; lia).
    pose proof (ROA Σ mx ARTx) as (VT & _). unfold PJ_NULSB_VT_A, PJ_XSPUTN_A, PJ_OVERFLOW_A in VT. unfold PJ_SB_VPTR_A in SBx.
    pose proof (af_client_consts RT AF Σ mx ARTx) as CCx.
    assert (SHZx : forall m', munch [(q + -64 - 16, q + -64); (OS + 40, OS + 64)] mx m' -> wmono bsegs mx m' -> shz m' OS 288).
    { intros m' MU WM. change 288 with (8 * Z.of_nat 36). apply (shz_of_zero_run m' OS 36); [Z.div_mod_to_equations; lia| lia|].
      apply (bytes_at_agree bsegs mx m' _ _ SHx). apply (agree_of_munch _ _ _ _ MU). intros x Hx. rewrite repeat_length in Hx.
      pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT). rewrite <- EFSZ in SHT. unfold shad, STACK_WIN in *.
      cbn [outside]. clear - Hx FLO FHI FSELF F0 SHT LOW LOR. split; [| split; [| exact I]]; Z.div_mod_to_equations; lia. }
    apply (aevt_evt RT AF PMc MST).
    do 2 lstep.
    lstep.
    destruct (Z_lt_dec pp ep) as [LT|GE].
    2:{
      br_is true ltac:(rewrite bv_ltu_Z, !unsigned_lit by lia; apply negb_true_iff, Z.ltb_ge; lia).
      pose proof (ro_C1_of_bytes mx (S + done) _ (bytes_at_nth mx S bs done SRCx ltac:(lia))) as CB0.
      assert (EU1 : bv_unsigned (Z_to_bv 64 (S + done)) = S + done) by (apply unsigned_lit; lia).
      set (cs := S + done) in *. set (b := nth (Z.to_nat done) bs (Z_to_bv 8 0)) in *.
      do 5 lstep.
      takeZ SBx 5%nat (OS + 40)%Z SBlo. rename SBx into PUTx.
      eapply evt_cut.
      { eapply (overflow_walk OS (q + -64) lo b); [lia| lia| Z.div_mod_to_equations; lia| exact SHZx| exact CCx| exact PUTx| exact MIx| exact STx| lia| lia| lia| lia]. }
      cbv beta. intros ms1 (c1 & c2 & c3 & c4 & c5 & m1 & -> & MU1 & WM1 & MI1 & ST1 & PUT1).
      rewrite (ret_pc_even 0x111778) by lia.
      assert (RB : 0 <= bv_unsigned b < 256) by (pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia).
      assert (AG1 : forall P : Z -> Prop, (forall x, P x -> ~ (q + -64 - 16 <= x < q + -64) /\ ~ (OS + 40 <= x < OS + 64)) -> agree_on P mx m1).
      { intros P HP a Ha. apply MU1. cbn [outside]. destruct (HP _ Ha) as [H1 H2]. split; [exact H1| split; [exact H2| exact I]]. }
      assert (ART1 : ART RT Σ m1).
      { apply (art_client_write RT AF Σ mx m1 (q + -64 - 16) ARTx ltac:(ul)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
        split; [intros Hin; apply Ha; left; ul|]. split; [| exact I]. intros Hin. apply Ha. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
      lazymatch type of FRx with rw_cells _ _ _ ?cs0 => assert (FR1 : rw_cells bsegs m1 (q + -64) cs0)
          by (eapply rw_cells_agree_nw; [exact FRx|]; apply AG1; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
      lazymatch type of SBlo with rw_cells _ _ _ ?cs0 => assert (SBlo1 : rw_cells bsegs m1 OS cs0)
          by (eapply rw_cells_agree_nw; [exact SBlo|]; apply AG1; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia) end.
      assert (DUM1 : rw_cells bsegs m1 (OS + 64) [CB 64 dum']) by (eapply rw_cells_agree_nw; [exact DUMx|]; apply AG1; intros x Hx; cbn [cells_size csize Nat.add] in Hx; lia).
      assert (SRC1 : bytes_at bsegs m1 S bs) by (eapply bytes_at_agree; [exact SRCx|]; apply AG1; intros x Hx; rewrite LBS in Hx; lia).
      assert (SH1 : bytes_at bsegs m1 (shad OS) (repeat z8 36)).
      { eapply bytes_at_agree; [exact SHx|]. apply AG1. intros x Hx. rewrite repeat_length in Hx. pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
        rewrite <- EFSZ in SHT. unfold shad, STACK_WIN in *. clear - Hx FLO FHI FSELF F0 SHT LOW LOR. Z.div_mod_to_equations. lia. }
      assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> m1 a = m a).
      { intros a Ha Ho. rewrite <- (PRESx a Ha Ho). apply MU1. pose proof (aclient_split_c RT AF Σ m q (bv_unsigned a) ART0 Ha) as SPL. unfold STACK_WIN in SPL.
        cbn [outside] in Ho |- *. clear - Ho SPL LOW LOR. repeat split; try exact I; lia. }
      pose proof SBlo1 as SB1. glueZ SB1 PUT1.
      clear AG1 MU1 WM1 ARTx MIx STx FRx SBlo SBlo1 PUTx DUMx SRCx SHx PRESx SHZx CCx VT.
      lstep.
      br_is false ltac:(rewrite bv_eqb_Z, unsigned_lit by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615; apply Z.eqb_neq; lia).
      do 2 lstep.
      lstep.
      subst cs.
      destruct (Z_lt_dec (done + 1) N) as [MORE|LAST].
      + br_is true ltac:(rewrite lts_small by lia; apply Z.ltb_lt; lia).
        replace (S + done + 1) with (S + (done + 1)) by lia.
        apply evt_done. eapply (IH (done + 1) (OS + 64) (OS + 128)); try eassumption; [lia| lia| right; lia].
      + br_is false ltac:(rewrite lts_small by lia; apply Z.ltb_ge; lia).
        lstep.
        replace (done + 1) with N by lia.
        apply evt_done. eapply EXIT; eassumption. }

    br_is false ltac:(rewrite bv_ltu_Z, !unsigned_lit by lia; apply negb_false_iff, Z.ltb_lt; lia).
    destruct PI as [[-> ->]|[-> PPR]]; [lia|].
    do 2 lstep.
    lstep.
    assert (CONT : forall (kz : Z) (y11 : word) (mm : mem), 1 <= kz <= N - done -> kz <= OS + 128 - pp -> mm = mx ->
      evt bsegs (fun ms => aevt RT PMc Σ K ms)
        (MS (mkR x1 (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV_A) x5 x6 x7 (Z_to_bv 64 done) (Z_to_bv 64 N) (Z_to_bv 64 pp) y11 y2 y3 y4 y5 y6 y7
                 (Z_to_bv 64 (S + done)) (Z_to_bv 64 OS) (Z_to_bv 64 kz) (Z_to_bv 64 (-1)) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            Fx (Z_to_bv 64 0x11174c) fc None mm (seg_rom bsegs))).
    { intros kz y11 mm K1 K2 ->.
      lstep.
      br_is false ltac:(rewrite bv_eqb_Z, unsigned_lit by lia; change (bv_unsigned z64) with 0; apply Z.eqb_neq; lia).
      do 2 lstep.
      lstep.
      apply evt_done.
      pose proof (rw_cells_CB_cut3 mx (OS + 64) 64 dum' (pp - (OS + 64)) kz ltac:(lia) ltac:(lia) ltac:(lia) DUMx) as D3.
      pose proof (bytes_at_sub mx S bs done kz SRCx ltac:(lia) ltac:(lia) ltac:(rewrite LBS; lia)) as SUB.
      set (sub := firstn (Z.to_nat kz) (skipn (Z.to_nat done) bs)) in *.
      assert (LSUB : Z.of_nat (length sub) = kz) by (subst sub; rewrite firstn_length_le; [lia| rewrite skipn_length, LBS; lia]).
      rewrite <- LSUB.
      assert (CS : checked_src RT Σ mx (Z_to_bv 64 (q + -64)) lo (S + done) (Z.of_nat (length sub))).
      { unfold checked_src. rewrite UQ64, LSUB. split; [| left; lia]. intros _.
        split; [apply (acc_sub bsegs mx S N); [exact (ACCX mx ARTx PRESx)| lia| lia]| apply RNGX; lia]. }
      assert (CD : checked_dst RT Σ mx (Z_to_bv 64 (q + -64)) pp (Z.of_nat (length sub))).
      { unfold checked_dst. rewrite UQ64, LSUB. split; [| split].
        - intros _. split; [| right; left; exists fO, kO; rewrite <- EFSZ; split; [exact INF| lia]].
          apply (acc_sub bsegs mx OS 288); [| lia| lia]. change 288 with (8 * Z.of_nat 36). apply (acc_zero_run bsegs mx OS 36); [Z.div_mod_to_equations; lia| lia| exact SHx].
        - intros i Hi. apply (CL (q + -64)). right; left. lia.
        - apply (wr_at_sub mx (OS + 64) 64); [exact (rw_cells_wr_at bsegs mx _ _ 64 DUMx ltac:(cbn; lia))| lia| lia| lia]. }
      assert (COK : call_ok RT Σ mx (Z_to_bv 64 (q + -64)) lo).
      { unfold call_ok. rewrite UQ64. split; [exact STx|]. split; [exact LOW|]. split; [ul|]. split; [ul| clear - SP16; Z.div_mod_to_equations; lia]. }
      eapply (aevt_memmove2P RT PMc FDO MST RC2 Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fx fc mx pp (S + done) sub lo
                eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) SUB CS CD ARTx MIx COK).
      intros w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 BY2. rewrite UQ64 in ST2, PRES2.
      rewrite (ret_pc_even 0x11175c) by lia. rewrite ?LSUB in PRES2. rewrite ?LSUB in BY2. rewrite ?LSUB.
      assert (AG2 : forall P : Z -> Prop, (forall x, P x -> ((q + -64 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ)) \/ (S <= x < S + CAP))
                                                       /\ ~ (pp <= x < pp + kz)) -> agree_on P mx m2).
      { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply PRES2; [| exact H2].
        destruct H1 as [H|[H|[H|H]]]; [apply (CL (q + -64)); left; split; [exact H| lia]| apply (CL (q + -64)); right; left; exact H
                                       | apply (CL (q + -64)); right; right; exact H| apply CLS; exact H]. }
      lazymatch type of FRx with rw_cells _ _ _ ?cs0 => assert (FR2 : rw_cells bsegs m2 (q + -64) cs0)
          by (eapply rw_cells_agree_nw; [exact FRx|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| lia]) end.
      lazymatch type of SBx with rw_cells _ _ _ ?cs0 => assert (SB2 : rw_cells bsegs m2 OS cs0)
          by (eapply rw_cells_agree_nw; [exact SBx|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
      assert (SRC2 : bytes_at bsegs m2 S bs) by (eapply bytes_at_agree; [exact SRCx|]; apply AG2; intros x Hx; rewrite LBS in Hx; split; [right; right; right; lia| lia]).
      assert (SH2 : bytes_at bsegs m2 (shad OS) (repeat z8 36)).
      { eapply bytes_at_agree; [exact SHx|]. apply AG2. intros x Hx. rewrite repeat_length in Hx. unfold shad in *. clear - Hx FLO FHI FSELF F0 PPR K1 K2.
        split; [right; right; left|]; Z.div_mod_to_equations; lia. }
      assert (DUM2 : exists dum2, rw_cells bsegs m2 (OS + 64) [CB 64 dum2]).
      { lazymatch type of D3 with rw_cells _ _ _ ([CB ?n1 ?d1] ++ [CB ?n2 ?d2] ++ [CB ?n3 ?d3]) =>
          assert (D3' : rw_cells bsegs m2 (OS + 64) ([CB n1 d1] ++ [CB n2 sub] ++ [CB n3 d3]));
          [ apply (cells_mid_update mx m2 (OS + 64) [CB n1 d1] n2 d2 sub [CB n3 d3] D3); [| exact WM2| | subst sub; rewrite firstn_length_le; [reflexivity| rewrite skipn_length, LBS; lia]];
            [ apply AG2; intros x (Hx & Hn); cbn [app cells_size csize Nat.add] in Hx, Hn; split; [right; left; lia| lia]
            | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; replace (OS + 64 + (pp - (OS + 64))) with pp by lia; exact BY2 ]
          | pose proof (rw_cells_forget bsegs m2 (OS + 64) _ D3') as (dum2 & H);
            assert (E64 : cells_size ([CB n1 d1] ++ [CB n2 sub] ++ [CB n3 d3]) = 64%nat) by (cbn [app cells_size csize]; lia);
            rewrite E64 in H; exists dum2; exact H ]
        end. }
      destruct DUM2 as (dum2 & DUM2).
      assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> m2 a = m a).
      { intros a Ha Ho. rewrite <- (PRESx a Ha Ho). apply PRES2; [apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]|]. cbn [outside] in Ho. lia. }
      clear AG2 PRES2 BY2 D3 SUB CS CD COK ARTx MIx STx FRx SBx DUMx SRCx SHx PRESx WM2.

      pose proof (munch_refl [(OS + 48, OS + 56)] m2) as MU3. pose proof (wmono_refl bsegs m2) as WM3.
      change (id (bytes_at bsegs m2 (shad OS) (repeat z8 36))) in SH2.
      apply (aevt_evt RT AF PMc MST).
      do 2 lstep.
      do 4 lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      assert (ART3 : ART RT Σ m3).
      { apply (art_client_write RT AF Σ m2 m3 (q + -64) ART2 ltac:(ul)); [| exact WM3]. intros a Ha. apply MU3. cbn [outside].
        split; [| exact I]. intros Hin. apply Ha. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
      assert (SH3 : bytes_at bsegs m3 (shad OS) (repeat z8 36)).
      { unfold id in SH2. eapply bytes_at_agree; [exact SH2|]. apply (agree_of_munch _ _ _ _ MU3). intros x Hx. rewrite repeat_length in Hx. cbn [outside].
        split; [| exact I]. unfold shad in *. clear - Hx FLO FHI FSELF F0. Z.div_mod_to_equations. lia. }
      assert (PRES3' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> m3 a = m a).
      { intros a Ha Ho. rewrite <- (PRES2' a Ha Ho). apply MU3. cbn [outside] in Ho |- *. split; [lia| exact I]. }
      clear MU3 WM3 SH2 PRES2' ART2.
      lstep.
      destruct (Z_lt_dec (kz + done) N) as [MORE|LAST].
      * br_is false ltac:(rewrite lts_small by lia; apply negb_false_iff, Z.ltb_lt; lia).
        replace (kz + done) with (done + kz) by lia. replace (S + done + kz) with (S + (done + kz)) by lia.
        apply evt_done. eapply (IH (done + kz) (pp + kz) (OS + 128)); try eassumption; [lia| lia| right; lia].
      * br_is true ltac:(rewrite lts_small by lia; apply negb_true_iff, Z.ltb_ge; lia).
        replace (kz + done) with N by lia.
        apply evt_done. eapply EXIT; eassumption. }
    destruct (Z_lt_dec (N - done) (OS + 128 - pp)) as [SM|BG].
    - br_is true ltac:(rewrite lts_small by lia; apply Z.ltb_lt; lia).
      eapply (CONT (N - done)); [lia| lia| reflexivity].
    - br_is false ltac:(rewrite lts_small by lia; apply Z.ltb_ge; lia).
      lstep.
      eapply (CONT (OS + 128 - pp)); [lia| lia| reflexivity]. }

  assert (PRES0 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> m a = m a) by (intros; reflexivity).
  pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  change (id (rw_cells bsegs m (OS + 128) [CB 160 bo2])) in FO. change (id (bytes_at bsegs m (shad OS) (repeat z8 36))) in SHB.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 64%nat ST.
  do 8 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0 end.
  assert (ART1 : ART RT Σ m0).
  { apply (art_client_write RT AF Σ m m0 (q + -64) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
    split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (PRES0' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> outside [(OS + 40, OS + 128)] (bv_unsigned a) -> m0 a = m a).
  { intros a Ha Ho. apply MU. cbn [outside]. pose proof (aclient_split_c RT AF Σ m q (bv_unsigned a) ART0 Ha) as SPL. unfold STACK_WIN in SPL. split; [clear - SPL LOW LOR; lia| exact I]. }
  assert (SH0 : bytes_at bsegs m0 (shad OS) (repeat z8 36)).
  { unfold id in SHB. eapply bytes_at_agree; [exact SHB|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. rewrite repeat_length in Hx. cbn [outside]. split; [| exact I].
    pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT). rewrite <- EFSZ in SHT. unfold shad, STACK_WIN in *. clear - Hx FLO FHI SHT LOW LOR. Z.div_mod_to_equations. lia. }
  clear MU WM SHB.
  lstep.
  destruct (Z.eq_dec N 0) as [N0|N1].
  - subst N. if_true.
    lstep.
    apply evt_done. eapply (EXIT 0 0); eassumption.
  - br_is false ltac:(rewrite bv_lts_zero_l, unsigned_lit by lia; cbn [negb]; apply negb_false_iff, andb_true_iff; split; apply Z.ltb_lt; lia).
    do 6 lstep.
    replace S with (S + 0) at 2 by lia.
    apply evt_done. eapply (LOOP (Z.to_nat N) 0 0 0); try eassumption; [lia| lia| left; lia].
Qed.

End Xsputn.
