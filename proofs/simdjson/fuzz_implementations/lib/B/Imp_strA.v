(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel ImpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Sj_stage1_kit Pj_loc_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Atp_hkit4A Atp_hkit5A Pj_rtkA Pj_defsA Pj_os_defsA Imp_hdefsA Imp_oss_defsA Imp_str_growA Imp_sb_overflowA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac PROBEH := try (match goal with H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => idtac H ":" T | munch _ _ _ => idtac H ":" T | stk _ _ _ _ => idtac H ":" T | bytes_at _ _ _ _ => idtac H ":" T | _ => fail end; fail end).
Ltac PROBE := PROBEH; match goal with |- evt _ _ (MS ?r _ ?pc _ _ ?m _) => idtac "PC:" pc "MEM:" m; idtac "REGS:" r | |- ?G => idtac "GOAL" G end; fail "PROBE".

Section STR.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Local Ltac ul := unfold OSS_STR_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition str_kont (Σ : rts RT) (K : config -> Prop) (lo O q R D L : Z) (m0 : mem)
    (cra : word) (gp cs0 cs1 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) : Prop :=
  forall (Σ' : rts RT) (ocp : option (Z * Z)) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     strresA m' R L ocp -> (forall DATA SZ, ocp = Some (DATA, SZ) -> DATA + SZ <= rt_sp0 RT Σ - STACK_WIN) ->
     rw_cells bsegs m' (O + 96) [C8 (wz (D + L))] -> bytes_at bsegs m' (shad R) [z8; z8; z8] -> OSHADOWA m' O ->
     rt_live RT Σ' = ocp_chunks ocp ++ rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ - str_costA L <= rt_credit RT Σ' ->
     (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (R <= bv_unsigned a < R + 24) -> ~ (O + 96 <= bv_unsigned a < O + 104) -> m' a = m0 a) ->
     aevt RT PMc Σ' K (MS (mkR cra (wz q) gp (wz TPV_A) t0' t1' t2' cs0 cs1 a0' a1' a2' a3' a4' a5' a6' a7' cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F' (ret_pc cra) fc None m' (seg_rom bsegs)).

Lemma str_tailA : forall (Σ : rts RT) (K : config -> Prop) (len lo O q R D L fO : Z) (kO : nat) (dlen : nat) (dbs junk j8 : list byte) (m0 m : mem)
    (cra gp cs0 cs1 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32)
    (xra xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs0 xs1 xs2 xs3 xs5 xt3 xt4 xt5 xt6 : word) (F : bvmap 5 word),
  In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  fO <= R -> R + 24 <= fO + fs_size kO - 8 -> R mod 8 = 0 -> (R + 24 <= O \/ O + 264 <= R) ->
  0 <= L -> L <= PJ_OUTMAX len -> 0 <= len <= SJ_PADMAX -> 0 < D -> L <= Z.of_nat dlen -> D + Z.of_nat dlen <= lo -> (D + Z.of_nat dlen <= R \/ R + 24 <= D) ->
  ((exists p k, In (p, k) (rt_live RT Σ) /\ p <= D /\ D + Z.of_nat dlen <= p + k) \/ (fO <= D /\ D + Z.of_nat dlen <= fO + fs_size kO - 8)) ->
  acc bsegs m D L ->
  rw_cells bsegs m (O + 48) [C8 (wz D); C8 (wz (D + L))] -> rw_cells bsegs m (O + 96) [C8 (wz (D + L))] ->
  rw_cells bsegs m D [CB dlen dbs] -> rw_cells bsegs m R [CB 24 junk] -> bytes_at bsegs m (shad R) [z8; z8; z8] -> OSHADOWA m O ->
  rw_cells bsegs m (q + -64) [CB 8 j8; C8 cs5; C8 cs4; C8 cs3; C8 cs2; C8 cs1; C8 cs0; C8 cra] ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo (q + -64) -> lo + OSS_STR_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX -> str_costA L <= rt_credit RT Σ ->
  (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (R <= bv_unsigned a < R + 24) -> ~ (O + 96 <= bv_unsigned a < O + 104) -> m a = m0 a) ->
  str_kont Σ K lo O q R D L m0 cra gp cs0 cs1 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 fc ->
  aevt RT PMc Σ K (MS (mkR xra (wz (q + -64)) gp (wz TPV_A) xt0 xt1 xt2 xs0 xs1 (wz R) (wz (O + 8)) (wz (D + L)) xa3 xa4 xa5 xa6 xa7
                        xs2 xs3 (wz (D + L)) xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
               F (wz 0x12126c) fc None m (seg_rom bsegs)).
Proof using AF RC RC2 FDO MST.
  intros until F. intros INF (FLO & FHI & AL16) LOW LOR RLO RHI R8 RSEP L0 LMAX HL D0 LD DLO SEPRD DSRC ACC PB HMC DBUF RCL RSH SH FR ART0 MI ST LOQ QT Q16 LVB CR PRES0 KONT.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (PJ_CAPMAX_bound len HL) as CMB.
  unfold OSS_STR_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 80) by (destruct ST; ul).
  assert (UQ64 : bv_unsigned (wz (q + -64)) = q + -64) by (apply unsigned_lit; ul).
  assert (LDB : length dbs = dlen) by (destruct DBUF as [[[HLx _] _] _]; exact HLx).
  assert (L26 : L <= 67112960) by (unfold PJ_OUTMAX, SJ_PADMAX in *; lia).
  assert (CLF : forall Lx sp x, fO <= x < fO + FSZ - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CLS : forall Lx sp x, shad fO <= x < shad (fO + FSZ) -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; right. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (SHO : shad fO <= shad O /\ shad O + 33 <= shad (fO + FSZ)) by (unfold shad; clear - FLO FHI AL16; Z.div_mod_to_equations; lia).
  assert (SHR : shad fO <= shad R /\ shad R + 3 <= shad (fO + FSZ)) by (unfold shad; clear - RLO RHI R8; Z.div_mod_to_equations; lia).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF. rewrite <- EFSZ in FSELF.
  pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT). rewrite <- EFSZ in SHT.
  assert (CLD : forall sp x, D <= x < D + Z.of_nat dlen -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp x).
  { intros sp x Hx. destruct DSRC as [(p & k & Hin & Hp & Hk)|[H1 H2]]; [right; right; left; exists p, k; split; [exact Hin| lia]| apply CLF; lia]. }
  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0 Ha) as [H|H]; [left; exact H| right; lia]. }

  assert (ACCR : forall mx, bytes_at bsegs mx (shad R) [z8; z8; z8] -> acc bsegs mx R 24).
  { intros mx HB. apply (acc_zero_run bsegs mx R 3); [exact R8| lia| exact HB]. }
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q); (R, R + 24)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  lstep. lstep. replace (D + L + - D) with L by lia. try replace (D + L - D) with L by lia.
  lstep. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| try clear Kc].
  lstep. lstep.
  destruct (Z_lt_le_dec 22 L) as [LONG|SHORT].
  -
    if_cases Kc; zify_cond Kc; [try clear Kc| exfalso; rewrite ?unsigned_lit in Kc by lia; lia].
    pose proof (imp_S_range L ltac:(lia)) as (SR1 & SR2 & SR3).
    lstep. lstep. lstep.
    lazymatch goal with |- evt ?sg ?QQ (MS ?R0 ?FF _ ?fcc ?rv ?mm ?ro) =>
      lazymatch R0 with context C [Z_to_bv 64 (Z.lor L 7)] =>
        let R' := context C [Z_to_bv 64 (imp_S L)] in
        assert (JOIN : evt sg QQ (MS R' FF (Z_to_bv 64 0x1212d0) fcc rv mm ro))
      end end.
    {
      lstep. lstep.
      apply evt_done.
      assert (ART1 : ART RT Σ m) by exact ART0.
      assert (Z1 : 1 <= imp_S L <= 0x20001000) by lia.
      clear MU WM.
      eapply (aevt_opnew RT AF RC PMc FDO MST Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (q + -64) (imp_S L) lo Z1 eq_refl
                ltac:(lia) ltac:(unfold str_costA in CR; destruct (Z.leb_spec L 22); lia) ART0 MI ST LOW ltac:(ul) ltac:(ul) ltac:(clear - Q16; Z.div_mod_to_equations; lia)).
      intros Σ1 p v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F1 m2 ART2 MI2 WM2 ST2 PRES2 WR2 ACC2 LV1 FRS1 SP1 CR1 P0 P16 PTOP.
      rewrite (ret_pc_even 0x1212d8) by lia.
      pose proof (af_live_range RT AF Σ1 m2 p (imp_S L) ART2 ltac:(rewrite LV1; left; reflexivity)) as (_ & PZ & _). rewrite SP1 in PZ.
      assert (NB : p + imp_S L < 2^47) by (clear - PZ SP0R; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
      assert (FRESH : forall sp a, lo <= sp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> ~ (p <= a < p + imp_S L)).
      { intros sp a Hsp Ha. apply (fresh_apart_l RT AF Σ1 m2 [(p, imp_S L)] (rt_live RT Σ) p (imp_S L) sp a ART2 LV1 ltac:(left; reflexivity) ltac:(rewrite SP1; lia)).
        rewrite FRS1. exact Ha. }

      assert (AG2 : forall Q : Z -> Prop, (forall x, Q x -> (q + -64 <= x < q) \/ (D <= x < D + Z.of_nat dlen) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) -> agree_on Q m m2).
      { intros Q HP a Ha. apply PRES2. destruct (HP _ Ha) as [H|[H|[H|H]]]; [left; ul| apply CLD; exact H| apply CLF; exact H| apply CLS; exact H]. }
      lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR2 : rw_cells bsegs m2 (q + -64) cs)
        by (eapply rw_cells_agree_nw; [exact FR|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia) end.
      assert (PB2 : rw_cells bsegs m2 (O + 48) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (D + L))])
        by (eapply rw_cells_agree_nw; [exact PB|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; do 2 right; left; lia).
      assert (HMC2 : rw_cells bsegs m2 (O + 96) [C8 (Z_to_bv 64 (D + L))])
        by (eapply rw_cells_agree_nw; [exact HMC|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; do 2 right; left; lia).
      assert (DBUF2 : rw_cells bsegs m2 D [CB dlen dbs])
        by (eapply rw_cells_agree_nw; [exact DBUF|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia).
      assert (RC2' : rw_cells bsegs m2 R [CB 24 junk])
        by (eapply rw_cells_agree_nw; [exact RCL|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; do 2 right; left; lia).
      assert (RSH2 : bytes_at bsegs m2 (shad R) [z8; z8; z8])
        by (eapply bytes_at_agree; [exact RSH|]; apply AG2; intros x Hx; cbn [length] in Hx; do 3 right; lia).
      assert (SH2 : OSHADOWA m2 O) by (apply (OSHADOWA_agree m m2 O SH); apply AG2; intros x Hx; do 3 right; lia).
      assert (ACCD2 : acc bsegs m2 D L).
      { destruct DSRC as [(pp & k & Hin & Hp & Hk)|[H1 H2]].
        - apply (acc_sub bsegs m2 pp k); [| lia| lia]. apply (proj2 (af_acc_live RT AF Σ1 m2 pp k ART2 ltac:(rewrite LV1; right; exact Hin))).
        - apply (acc_agree_at m m2 D L ACC ltac:(lia)). apply AG2. intros x Hx. do 3 right. unfold shad in *. clear - Hx H1 H2 LD L0. Z.div_mod_to_equations. lia. }
      assert (PRES02 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (R <= bv_unsigned a < R + 24) -> ~ (O + 96 <= bv_unsigned a < O + 104) -> m2 a = m0 a).
      { intros a Ha H1 H2. rewrite <- (PRES0 a Ha H1 H2). apply PRES2. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]. }
      clear AG2 PRES2 FR PB HMC DBUF RCL RSH SH ACC PRES0 ST MI.

      apply (aevt_evt RT AF PMc MST).
      pose proof (munch_refl [(q - 64, q); (R, R + 24)]%Z m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
      apply (rw_cells_split_CB bsegs _ _ [] 24 junk [] [8; 8; 8]%nat) in RC2'; [|reflexivity]. cbn [mk_CB_cells app] in RC2'. forget_junk RC2'.
      pj_hide RSH2.
      lstep. lstep. lstep. lstep. lstep.
      lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| try clear Kc].

      lstep. lstep. lstep. lstep.
      apply evt_done.
      lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      assert (ART3 : ART RT Σ1 m3).
      { apply (art_client_write RT AF Σ1 m2 m3 (q + -64) ART2 ltac:(rewrite SP1; ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
        split; [intros Hin; apply Ha; left; ul|]. split; [| exact I]. intros Hin. apply Ha. rewrite FRS1. apply CLF. lia. }
      assert (AG3 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 64 <= x < q) /\ ~ (R <= x < R + 24)) -> agree_on Q m2 m3).
      { intros Q HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
      rename DBUF2 into DBUF3.
      destruct (rw_cells_CB_atA _ _ _ _ L DBUF3 ltac:(lia)) as [SRCL _].
      pose proof SRCL as SRCb. apply rw_cells_bytes_at in SRCb. cbn [cells_bytes cbytes] in SRCb. rewrite app_nil_r in SRCb. clear SRCL.
      assert (LSRC : Z.of_nat (length (firstn (Z.to_nat L) dbs)) = L) by (rewrite firstn_length_le; [lia| lia]).
      assert (CS : checked_src RT Σ1 m3 (Z_to_bv 64 (q + -64)) lo D L).
      { unfold checked_src. rewrite UQ64. split; [| left; lia]. intros _. split.
        - apply (acc_agree_at m2 m3 D L ACCD2 ltac:(lia)). apply AG3. intros x Hx. pose proof (af_frames_hi RT AF Σ m fO kO ART1 INF) as FRHI. rewrite <- EFSZ in FRHI.
          unfold shad, SHB in *. clear - Hx FRHI LOR LOQ QT DLO RLO RHI LD L0 D0. Z.div_mod_to_equations. lia.
        - destruct DSRC as [(pp & k & Hin & Hp & Hk)|[H1 H2]]; [left; exists pp, k; split; [rewrite LV1; right; exact Hin| lia]|].
          right; left. exists fO, kO. rewrite FRS1, <- EFSZ. split; [exact INF| lia]. }
      first [pose proof (wr_at_transport bsegs m2 m3 p (imp_S L) WR2 WM) as WR3 | rename WR2 into WR3].
      assert (CD : checked_dst RT Σ1 m3 (Z_to_bv 64 (q + -64)) p L).
      { unfold checked_dst. rewrite UQ64. split; [| split].
        - intros _. split; [| left; exists p, (imp_S L); split; [rewrite LV1; left; reflexivity| lia]].
          apply (acc_sub bsegs m3 p (imp_S L)); [| lia| lia].
          pose proof (proj2 (af_acc_live RT AF Σ1 m3 p (imp_S L) ART3 ltac:(rewrite LV1; left; reflexivity))) as X. exact X.
        - intros i Hi. right; right; left. exists p, (imp_S L). split; [rewrite LV1; left; reflexivity| lia].
        - apply (wr_at_sub m3 p (imp_S L)); [exact WR3| lia| lia| lia]. }
      assert (COK : call_ok RT Σ1 m3 (Z_to_bv 64 (q + -64)) lo).
      { unfold call_ok. rewrite UQ64, SP1. split; [assumption|]. split; [lia|]. split; [ul|]. split; [ul| clear - Q16; Z.div_mod_to_equations; lia]. }
      clear MU WM.
      replace (Z_to_bv 64 L) with (Z_to_bv 64 (Z.of_nat (length (firstn (Z.to_nat L) dbs)))) by (rewrite LSRC; reflexivity). rewrite <- LSRC in CS, CD.
      eapply (aevt_memmove2P RT PMc FDO MST RC2 Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m3 p D _ lo eq_refl eq_refl eq_refl ltac:(ul) ltac:(ul) ltac:(rewrite LSRC; lia) SRCb CS CD ART3 ltac:(assumption) COK).
      intros w0 w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m4 (ART4 & MI4 & WM4 & ST4) PRES4 BY4. rewrite UQ64 in ST4, PRES4. rewrite LSRC in PRES4.
      rewrite (ret_pc_even 0x121300) by lia.
      replace (Z_to_bv 64 (Z.of_nat (length (firstn (Z.to_nat L) dbs)))) with (Z_to_bv 64 L) by (rewrite LSRC; reflexivity).

      assert (AG4 : forall Q : Z -> Prop, (forall x, Q x -> (q + -64 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) -> agree_on Q m3 m4).
      { intros Q HP a Ha. pose proof (HP _ Ha) as HX. apply PRES4.
        - rewrite FRS1. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H].
        - destruct HX as [H|[H|H]]; [clear - H PZ LOW LOQ SR1; lia| |].
          + pose proof (FRESH (q + -64) (bv_unsigned a) ltac:(ul) (CLF (rt_live RT Σ) (q + -64) _ H)). lia.
          + pose proof (FRESH (q + -64) (bv_unsigned a) ltac:(ul) (CLS (rt_live RT Σ) (q + -64) _ H)). lia. }
      lazymatch type of FR2 with rw_cells _ ?mm _ ?cs => first [constr_eq mm m4 | assert (FR4 : rw_cells bsegs m4 (q + -64) cs)
        by (eapply rw_cells_agree_nw; [exact FR2|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; lia); clear FR2; rename FR4 into FR2] end.
      lazymatch type of RC2' with rw_cells _ ?mm _ ?cs => first [constr_eq mm m4 | assert (RC4 : rw_cells bsegs m4 R cs)
        by (eapply rw_cells_agree_nw; [exact RC2'|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia); clear RC2'; rename RC4 into RC2'] end.
      lazymatch type of HMC2 with rw_cells _ ?mm _ ?cs => first [constr_eq mm m4 | assert (HMC4 : rw_cells bsegs m4 (O + 96) cs)
        by (eapply rw_cells_agree_nw; [exact HMC2|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; right; left; lia); clear HMC2; rename HMC4 into HMC2] end.
      pj_unhide RSH2.
      assert (RSH4 : bytes_at bsegs m4 (shad R) [z8; z8; z8]).
      { eapply bytes_at_agree; [| apply AG4]; [eapply bytes_at_agree; [exact RSH2| apply AG3]|]; intros x Hx; cbn [length] in Hx.
        - clear - Hx SHR FSELF SHT LOW LOQ RLO RHI. split; lia.
        - do 2 right. lia. }
      assert (SH4 : OSHADOWA m4 O).
      { apply (OSHADOWA_agree m3 m4 O); [apply (OSHADOWA_agree m2 m3 O SH2); apply AG3| apply AG4]; intros x Hx.
        - clear - Hx SHO FSELF SHT LOW LOQ RLO RHI. split; lia.
        - do 2 right. lia. }
      assert (PRES04 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (R <= bv_unsigned a < R + 24) -> ~ (O + 96 <= bv_unsigned a < O + 104) -> m4 a = m0 a).
      { intros a Ha H1 H2. rewrite <- (PRES02 a Ha H1 H2). rewrite (PRES4 a).
        - apply AG3 with (Q := fun x => x = bv_unsigned a); [| reflexivity]. intros x ->. split; [destruct (CSEP _ Ha); lia| exact H1].
        - rewrite FRS1. apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LV1; intros e He; right; exact He| intros e He; exact He| lia].
        - pose proof (FRESH q (bv_unsigned a) ltac:(ul) Ha). lia. }
      destruct (wr_at_rw_CB m4 p (imp_S L) (wr_at_transport bsegs m3 m4 p (imp_S L) WR3 WM4) ltac:(lia)) as (bn & NEWC).
      clear AG4 AG3 PRES4 BY4 SRCb CS CD COK RSH2 SH2 PRES02 ART2 ART3 WM2 WR3 ACC2 ACCD2 DBUF3.

      pose proof (af_frames_range RT AF Σ1 m4 fO kO ART4 ltac:(rewrite FRS1; exact INF)) as (_ & _ & _ & FLV1).
      pose proof (FLV1 p (imp_S L) ltac:(rewrite LV1; left; reflexivity)) as PO. rewrite <- EFSZ in PO. clear FLV1.
      pose proof (proj1 (af_fshadow_apart RT AF Σ1 m4 fO kO ART4 ltac:(rewrite FRS1; exact INF)) p (imp_S L) ltac:(rewrite LV1; left; reflexivity)) as PSH. rewrite <- EFSZ in PSH.
      apply (aevt_evt RT AF PMc MST).
      pose proof (munch_refl [(q - 64, q); (p + L, p + L + 1)]%Z m4) as MU. pose proof (wmono_refl bsegs m4) as WM.
      lstep.
      destruct (rw_cells_CB_atA _ _ _ _ L NEWC ltac:(lia)) as [NPRE NREST].
      apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [1; (Z.to_nat (imp_S L) - Z.to_nat L - 1)]%nat) in NREST; [| cbn; lia]. cbn [mk_CB_cells app] in NREST.
      forget_junk NREST. forget_junk NPRE. clear NEWC.
      remember (Z.to_nat (imp_S L) - Z.to_nat L - 1)%nat as k3 eqn:EK3 in NREST.
      set (pn := p + L) in *.
      lstep.
      subst pn.
      pose proof (rw_cells_joinA _ _ _ _ _ NPRE NREST ltac:(cbn [cells_size csize]; lia)) as BA2. clear NPRE NREST.
      lazymatch type of BA2 with rw_cells _ _ _ (?cs1 ++ ?cs2) =>
        pose proof (rw_cells_merge bsegs _ _ [] (cs1 ++ cs2) [] ltac:(rewrite app_nil_l, app_nil_r; exact BA2)) as NEWC end.
      clear BA2. cbn [cells_size csize cells_bytes cbytes app] in NEWC.
      lazymatch type of NEWC with rw_cells _ _ _ [CB ?k ?bsx] => replace k with (Z.to_nat (imp_S L)) in NEWC by lia; set (bn' := bsx) in NEWC; clearbody bn' end.

      do 7 lstep. lstep. release_frame FR2 ST4 q. lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      apply evt_done. eapply (KONT Σ1 (Some (p, imp_S L))).
      + apply (art_client_write RT AF Σ1 m4 m9 (q + -64) ART4 ltac:(rewrite SP1; ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
        split; [intros Hin; apply Ha; left; ul|]. split; [| exact I]. intros Hin. apply Ha. right; right; left. exists p, (imp_S L). split; [rewrite LV1; left; reflexivity| lia].
      + assumption.
      + exact ST4.
      + unfold strresA. split; [lia|]. split; [reflexivity|]. split; [exact RC2'|]. split; [eexists; exact NEWC|]. split; [exact P0| exact P16].
      + intros DATA SZ [= <- <-]. exact PZ.
      + exact HMC2.
      + first [exact RSH4 | eapply bytes_at_agree; [exact RSH4|]; apply (agree_of_munch _ _ _ _ MU); intros x Hx; cbn [length] in Hx; cbn [outside];
               clear - Hx SHR FSELF SHT LOW LOQ PSH SR1 L0; split; [| split; [| exact I]]; lia].
      + apply (OSHADOWA_agree m4 m9 O SH4). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside].
        clear - Hx SHO FSELF SHT LOW LOQ PSH SR1 L0. split; [| split; [| exact I]]; lia.
      + exact LV1.
      + exact FRS1.
      + exact SP1.
      + rewrite CR1. unfold str_costA. destruct (Z.leb_spec L 22); lia.
      + intros a Ha H1 H2. rewrite <- (PRES04 a Ha H1 H2). apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [| exact I].
        pose proof (FRESH q (bv_unsigned a) ltac:(ul) Ha). lia. }

    lstep. if_cases Kc; zify_cond Kc; rewrite ?unsigned_lit in Kc by lia.
    + lstep. replace (Z_to_bv 64 (Z.lor L 7 + 1)) with (Z_to_bv 64 (imp_S L)) by (f_equal; unfold imp_S; destruct (Z.eqb_spec (Z.lor L 7) 23); lia). exact JOIN.
    + lstep. lstep. replace (Z_to_bv 64 26) with (Z_to_bv 64 (imp_S L)) by (f_equal; unfold imp_S; destruct (Z.eqb_spec (Z.lor L 7) 23); lia). exact JOIN.
  -
    if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| try clear Kc].
    apply (rw_cells_split_CB bsegs _ _ [] 24 junk [] [1; 23]%nat) in RCL; [|reflexivity]. cbn [mk_CB_cells app] in RCL. forget_junk RCL.
    pj_hide RSH.
    lstep. zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite ?(Z.mod_small (L * 2)) by lia. rewrite le1_smallZ by lia. mem_after_store.
    replace (L * 2) with (2 * L) in RCL by lia.
    lstep. lstep.
    assert (CR0 : rt_credit RT Σ - str_costA L <= rt_credit RT Σ) by (unfold str_costA; destruct (Z.leb_spec L 22); pose proof (mcost_le_growc (imp_S L)); lia).
    destruct (Z.eq_dec L 0) as [L00|L1].
    +
      subst L. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| try clear Kc].
      lstep. lstep. lstep.
      do 7 lstep. lstep. release_frame FR ST q. lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      lazymatch goal with H : rw_cells bsegs m9 R _ |- _ => rename H into RC9 end.
      merge_at RC9 1%nat 2%nat.
      pj_unhide RSH.
      apply evt_done. eapply (KONT Σ None).
      * apply (art_client_write RT AF Σ m m9 (q + -64) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
        split; [intros Hin; apply Ha; left; ul|]. split; [| exact I]. intros Hin. apply Ha. apply CLF. lia.
      * assumption.
      * exact ST.
      * unfold strresA. split; [lia|]. eexists. first [exact RC9 | rewrite Z.add_0_r in RC9; exact RC9 | change (2 * 0) with 0; exact RC9].
      * intros DATA SZ [=].
      * first [exact HMC | rewrite Z.add_0_r; exact HMC | rewrite Z.add_0_r in HMC; exact HMC].
      * eapply bytes_at_agree; [exact RSH|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [length] in Hx. cbn [outside]. clear - Hx SHR FSELF SHT LOW LOQ RLO RHI. split; [| split; [| exact I]]; lia.
      * apply (OSHADOWA_agree m m9 O SH). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. clear - Hx SHO FSELF SHT LOW LOQ RLO RHI. split; [| split; [| exact I]]; lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * exact CR0.
      * intros a Ha H1 H2. rewrite <- (PRES0 a Ha H1 H2). apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [exact H1| exact I].
    +
      if_cases Kc; zify_cond Kc; [try clear Kc| exfalso; rewrite ?unsigned_lit in Kc by lia; lia].
      lstep. lstep. lstep. lstep.
      apply evt_done.
      lazymatch goal with |- aevt _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
      pj_unhide RSH.
      assert (ART3 : ART RT Σ m3).
      { apply (art_client_write RT AF Σ m m3 (q + -64) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
        split; [intros Hin; apply Ha; left; ul|]. split; [| exact I]. intros Hin. apply Ha. apply CLF. lia. }
      assert (AG3 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 64 <= x < q) /\ ~ (R <= x < R + 24)) -> agree_on Q m m3).
      { intros Q HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
      assert (RSH3 : bytes_at bsegs m3 (shad R) [z8; z8; z8]).
      { eapply bytes_at_agree; [exact RSH|]. apply AG3. intros x Hx. cbn [length] in Hx. clear - Hx SHR FSELF SHT LOW LOQ RLO RHI. split; lia. }
      lazymatch type of DBUF with rw_cells _ ?mm _ _ => first [constr_eq mm m3; rename DBUF into DBUF3 | assert (DBUF3 : rw_cells bsegs m3 D [CB dlen dbs])
          by (eapply rw_cells_agree_nw; [exact DBUF|]; apply AG3; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx DLO LOQ SEPRD; split; lia); clear DBUF] end.
      destruct (rw_cells_CB_atA _ _ _ _ L DBUF3 ltac:(lia)) as [SRCL _].
      pose proof SRCL as SRCb. apply rw_cells_bytes_at in SRCb. cbn [cells_bytes cbytes] in SRCb. rewrite app_nil_r in SRCb. clear SRCL.
      assert (LSRC : Z.of_nat (length (firstn (Z.to_nat L) dbs)) = L) by (rewrite firstn_length_le; [lia| lia]).
      assert (CS : checked_src RT Σ m3 (Z_to_bv 64 (q + -64)) lo D L).
      { unfold checked_src. rewrite UQ64. split; [| left; lia]. intros _. split.
        - apply (acc_agree_at m m3 D L ACC ltac:(lia)). apply AG3. intros x Hx. pose proof (af_frames_hi RT AF Σ m fO kO ART0 INF) as FRHI. rewrite <- EFSZ in FRHI.
          unfold shad, SHB in *. clear - Hx FRHI LOR LOQ QT DLO RLO RHI LD L0 D0. Z.div_mod_to_equations. split; lia.
        - destruct DSRC as [(pp & k & Hin & Hp & Hk)|[H1 H2]]; [left; exists pp, k; split; [exact Hin| lia]|].
          right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
      lazymatch goal with H : rw_cells bsegs m3 R _ |- _ => rename H into RC3 end.
      assert (CD : checked_dst RT Σ m3 (Z_to_bv 64 (q + -64)) (R + 1) L).
      { unfold checked_dst. rewrite UQ64. split; [| split].
        - intros _. split; [apply (acc_sub bsegs m3 R 24); [exact (ACCR m3 RSH3)| lia| lia]|]. right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia].
        - intros i Hi. apply CLF. lia.
        - apply (wr_at_sub m3 R 24); [apply (rw_cells_wr_at bsegs m3 _ _ _ RC3); cbn; lia| lia| lia| lia]. }
      assert (COK : call_ok RT Σ m3 (Z_to_bv 64 (q + -64)) lo).
      { unfold call_ok. rewrite UQ64. split; [assumption|]. split; [lia|]. split; [ul|]. split; [ul| clear - Q16; Z.div_mod_to_equations; lia]. }
      clear MU WM.
      replace (Z_to_bv 64 L) with (Z_to_bv 64 (Z.of_nat (length (firstn (Z.to_nat L) dbs)))) by (rewrite LSRC; reflexivity). rewrite <- LSRC in CS, CD.
      eapply (aevt_memmove2P RT PMc FDO MST RC2 Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (R + 1) D _ lo eq_refl eq_refl eq_refl ltac:(ul) ltac:(ul) ltac:(rewrite LSRC; lia) SRCb CS CD ART3 ltac:(assumption) COK).
      intros w0 w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m4 (ART4 & MI4 & WM4 & ST4) PRES4 BY4. rewrite UQ64 in ST4, PRES4. rewrite LSRC in PRES4.
      rewrite (ret_pc_even 0x121300) by lia.
      replace (Z_to_bv 64 (Z.of_nat (length (firstn (Z.to_nat L) dbs)))) with (Z_to_bv 64 L) by (rewrite LSRC; reflexivity).
      assert (FRESH4 : forall x, fO <= x < fO + FSZ - 8 -> ~ (R + 1 <= x < R + 1 + L) -> m4 (Z_to_bv 64 x) = m3 (Z_to_bv 64 x)).
      { intros x Hx Hn. assert (XR : 0 <= x < 2^64) by (clear - Hx F0 FTOP SP0R; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
        apply PRES4; rewrite unsigned_lit by exact XR; [apply CLF; exact Hx| exact Hn]. }
      assert (AG4 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -64 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (R + 1 <= x < R + 1 + L)) -> agree_on Q m3 m4).
      { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES4; [| exact HN]. destruct HX as [H|[H|H]]; [left; ul| apply CLF; exact H| apply CLS; exact H]. }
      lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells bsegs m4 (q + -64) cs)
        by (eapply rw_cells_agree_nw; [exact FR|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| clear - Hx RLO RHI FHI FTOP LOW LOQ SHORT L0; lia]) end.
      assert (HMC4 : rw_cells bsegs m4 (O + 96) [C8 (Z_to_bv 64 (D + L))]).
      { eapply rw_cells_agree_nw; [exact HMC|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| clear - Hx RSEP SHORT L0; lia]. }
      assert (RSH4 : bytes_at bsegs m4 (shad R) [z8; z8; z8]).
      { eapply bytes_at_agree; [exact RSH3|]. apply AG4. intros x Hx. cbn [length] in Hx. clear - Hx SHR FSELF RLO RHI L0 SHORT. split; [do 2 right; lia| lia]. }
      assert (SH4 : OSHADOWA m4 O).
      { apply (OSHADOWA_agree m3 m4 O); [apply (OSHADOWA_agree m m3 O SH); apply AG3| apply AG4]; intros x Hx; [clear - Hx SHO FSELF SHT LOW LOQ RLO RHI; split; lia|].
        clear - Hx SHO FSELF RLO RHI L0 SHORT. split; [do 2 right; lia| lia]. }

      takeZ RC3 1%nat (R + 1) RB0.
      destruct (rw_cells_CB_atA _ _ _ _ L RC3 ltac:(lia)) as [_ RREST].
      assert (RB0' : rw_cells bsegs m4 R [C1 (Z_to_bv 8 (2 * L))]).
      { eapply rw_cells_agree_nw; [exact RB0|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [right; left; lia| lia]. }
      lazymatch type of RREST with rw_cells _ _ _ ?cs => assert (RREST' : rw_cells bsegs m4 (R + 1 + L) cs)
        by (eapply rw_cells_agree_nw; [exact RREST|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| lia]) end.
      assert (RCOPY : rw_cells bsegs m4 (R + 1) [CB (Z.to_nat L) (firstn (Z.to_nat L) dbs)]).
      { pose proof (rw_cells_CB_intro m4 (R + 1) _ BY4) as X. replace (length (firstn (Z.to_nat L) dbs)) with (Z.to_nat L) in X by lia. apply X.
        rewrite Z2Nat.id by lia. apply (wr_at_sub m4 R 24); [| lia| lia| lia].
        apply (wr_at_transport bsegs m3 m4 R 24); [| exact WM4]. pose proof (rw_cells_wr_at bsegs m3 _ _ 1 RB0 ltac:(cbn; lia)) as W1. pose proof (rw_cells_wr_at bsegs m3 _ _ 23 RC3 ltac:(cbn; lia)) as W2.
        destruct W1 as (W1a & W1b & W1). destruct W2 as (W2a & W2b & W2). split; [lia|]. split; [lia|].
        intros i Hi. destruct (Z_lt_dec i 1); [apply W1; lia| replace (R + i) with (R + 1 + (i - 1)) by lia; apply W2; lia]. }
      assert (PRES04 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> ~ (R <= bv_unsigned a < R + 24) -> ~ (O + 96 <= bv_unsigned a < O + 104) -> m4 a = m0 a).
      { intros a Ha H1 H2. rewrite <- (PRES0 a Ha H1 H2). rewrite (PRES4 a); [| apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]| lia].
        apply AG3 with (Q := fun x => x = bv_unsigned a); [| reflexivity]. intros x ->. split; [destruct (CSEP _ Ha); lia| exact H1]. }
      clear AG4 AG3 PRES4 BY4 SRCb CS CD COK RB0 RREST RC3 RSH3 RSH FR HMC SH PRES0 DBUF3 ST ART0 ART3 MI.

      apply (aevt_evt RT AF PMc MST).
      pose proof (munch_refl [(q - 64, q); (R, R + 24)]%Z m4) as MU. pose proof (wmono_refl bsegs m4) as WM.
      pj_hide RSH4.
      lstep.
      apply (rw_cells_split_CB bsegs _ _ [] _ _ [] [1; (23 - Z.to_nat L - 1)]%nat) in RREST'; [| cbn; lia]. cbn [mk_CB_cells app] in RREST'. forget_junk RREST'.
      remember (23 - Z.to_nat L - 1)%nat as k3 eqn:EK3 in RREST'.
      set (pn := R + 1 + L) in *.
      lstep.
      subst pn.
      pose proof (rw_cells_joinA _ _ _ _ _ RCOPY RREST' ltac:(cbn [cells_size csize]; lia)) as R2. clear RCOPY RREST'.
      lazymatch type of R2 with rw_cells _ _ _ (?cs1 ++ ?cs2) =>
        pose proof (rw_cells_merge bsegs _ _ [] (cs1 ++ cs2) [] ltac:(rewrite app_nil_l, app_nil_r; exact R2)) as R3 end.
      clear R2. cbn [cells_size csize cells_bytes cbytes app] in R3.
      lazymatch type of R3 with rw_cells _ _ _ [CB ?k ?bsx] => replace k with 23%nat in R3 by lia; set (j23 := bsx) in R3; clearbody j23 end.
      pose proof (rw_cells_joinA _ _ _ _ _ RB0' R3 ltac:(cbn [cells_size csize]; lia)) as RC9. cbn [app] in RC9. clear RB0' R3.

      do 7 lstep. lstep. release_frame FR4 ST4 q. lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
      pj_unhide RSH4.
      apply evt_done. eapply (KONT Σ None).
      * apply (art_client_write RT AF Σ m4 m9 (q + -64) ART4 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
        split; [intros Hin; apply Ha; left; ul|]. split; [| exact I]. intros Hin. apply Ha. apply CLF. lia.
      * assumption.
      * exact ST4.
      * unfold strresA. split; [lia|]. eexists. exact RC9.
      * intros DATA SZ [=].
      * exact HMC4.
      * eapply bytes_at_agree; [exact RSH4|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [length] in Hx. cbn [outside]. clear - Hx SHR FSELF SHT LOW LOQ RLO RHI. split; [| split; [| exact I]]; lia.
      * apply (OSHADOWA_agree m4 m9 O SH4). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [outside]. clear - Hx SHO FSELF SHT LOW LOQ RLO RHI. split; [| split; [| exact I]]; lia.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * exact CR0.
      * intros a Ha H1 H2. rewrite <- (PRES04 a Ha H1 H2). apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [exact H1| exact I].
Qed.

Theorem strA_proof : strA_cps RT PMc.
Proof using AF RC RC2 FDO MST.
  unfold strA_cps. intros until m. intros FDO' MST' LVE LPOS INF OIN LOW LOR INV SH HL WMAX RLO RHI R8 RSEP RCL RSH ART0 MI ST LOQ QT Q16 LVB CR HK.
  pose proof OIN as (FLO & FHI & AL16).
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold OSS_STR_A. pose proof LOQ as LOQ'. unfold OSS_STR_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT.
  assert (Q0 : 0 <= q - 80) by (destruct ST; ul).
  destruct INV as (PUTC & REP & NUM). destruct PUTC as (PUTC & (hm & HMC & HMR) & (j108 & MODE)). unfold sb_cellsA in PUTC.
  pose proof (OSNUMA_cap24 len st NUM) as CAP24. pose proof NUM as (WB & K0 & CAPB & HB).
  set (cap := oa_cap st) in *. set (D := oa_data st) in *. set (w := oa_w st) in *.

  assert (DBUF : exists dlen dbs, rw_cells bsegs m D [CB dlen dbs] /\ w <= Z.of_nat dlen /\ 0 < D /\ D + Z.of_nat dlen <= lo /\ (D + Z.of_nat dlen <= R \/ R + 24 <= D)
                 /\ ((exists p k, In (p, k) (rt_live RT Σ) /\ p <= D /\ D + Z.of_nat dlen <= p + k) \/ (fO <= D /\ D + Z.of_nat dlen <= fO + fs_size kO - 8))
                 /\ acc bsegs m D w /\ (D + Z.of_nat dlen <= O + 96 \/ O + 104 <= D)).
  { unfold STRREPA in REP. unfold oa_lim in WB. destruct (oa_heap st) eqn:HP.
    - destruct REP as (_ & (dbs & BLK) & D0 & D16 & M16).
      pose proof (af_live_range RT AF Σ m D cap ART0 ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)) as (_ & DTOP & _).
      pose proof (FLIVE D cap ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)) as DF.
      exists (Z.to_nat cap), dbs. rewrite Z2Nat.id by lia. split; [exact BLK|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [clear - DF RLO RHI; lia|]. split.
      + left. exists D, cap. split; [rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity| lia].
      + split; [| clear - DF FLO FHI; lia]. apply (acc_sub bsegs m D cap); [| lia| lia]. apply (proj2 (af_acc_live RT AF Σ m D cap ART0 ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity))).
    - destruct REP as (_ & (dbs & R23) & ED). destruct HB as [EC _]. change (oa_data st) with D in ED.
      exists 23%nat, dbs. rewrite <- ED in R23. rewrite ED. split; [rewrite <- ED; exact R23|]. split; [cbn; lia|]. split; [lia|]. split; [cbn; lia|]. split; [cbn; clear - RSEP; lia|]. split.
      + right. cbn. lia.
      + split; [| cbn; lia]. apply (acc_sub bsegs m O (8 * Z.of_nat 33)); [| lia| cbn; lia]. apply (acc_zero_run bsegs m O 33); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact SH]. }
  clear REP. destruct DBUF as (dlen & dbs & DBUF & LD & D0 & DLO & SEPRD & DSRC & ACC & SEPHM).
  assert (CLF : forall Lx sp x, fO <= x < fO + fs_size kO - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. split; [exact INF| lia]. }
  assert (CSEP : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0 Ha) as [H|H]; [left; exact H| right; lia]. }
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q); (O + 96, O + 104)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pj_hide RSH. pj_hide DBUF. pj_hide RCL.
  lstep. carve_frame 64%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

  do 7 lstep. lstep. lstep. lstep. if_true.
  takeZ PUTC 5%nat (O + 48) PA. takeZ PUTC 2%nat (O + 64) PB.

  lstep. lstep.

  assert (JOINT : forall m1, munch [(q - 64, q); (O + 96, O + 104)]%Z m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (q + -64) ->
      rw_cells bsegs m1 (O + 96) [C8 (Z_to_bv 64 (D + w))] ->
      rw_cells bsegs m1 (q + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells bsegs m1 (O + 48) [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 (D + w))] ->
      forall xa2 xa3,
      evt bsegs (fun ms' => aevt RT PMc Σ K ms')
        (MS (mkR ra (Z_to_bv 64 (q + -64)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 R) (Z_to_bv 64 (O + 8)) (Z_to_bv 64 (D + w)) xa2 xa3 a5 a6 a7
                 s2 s3 (Z_to_bv 64 (D + w)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x12126c) fc None m1 (seg_rom bsegs))).
  { intros m1 MU1 WM1 MI1 ST1 HMC1 FR1 PB1 xa2 xa3. pj_unhide RSH. pj_unhide DBUF. pj_unhide RCL.
    assert (ART1 : ART RT Σ m1).
    { apply (art_client_write RT AF Σ m m1 (q - 64) ART0 ltac:(ul)); [| exact WM1]. intros a Ha. apply MU1. cbn [outside].
      split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I]. }
    assert (AG1 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 64 <= x < q) /\ ~ (O + 96 <= x < O + 104)) -> agree_on Q m m1).
    { intros Q HP a Ha. apply MU1. cbn [outside]. destruct (HP _ Ha) as (X & W'). split; [exact X| split; [exact W'| exact I]]. }
    pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
    pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT).
    apply evt_done.
    eapply (str_tailA Σ K len lo O q R D w fO kO dlen dbs junk jk m m1);
      [exact INF| exact OIN| exact LOW| exact LOR| exact RLO| exact RHI| exact R8| exact RSEP| subst w; lia| subst w; exact WMAX| exact HL| exact D0| exact LD| exact DLO| exact SEPRD
      | exact DSRC| | exact PB1| exact HMC1| | | | | exact FR1| exact ART1| exact MI1| exact ST1| exact LOQ'| ul| exact Q16| exact LVB| subst w; exact CR| |].
    - apply (acc_agree_at m m1 D w ACC ltac:(lia)). apply AG1. intros x Hx. pose proof (af_frames_hi RT AF Σ m fO kO ART0 INF) as FRHI.
      unfold shad, SHB in *. clear - Hx FRHI LOR LOQ QT DLO FLO FHI LD WB D0 FTOP SP0R. unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *. Z.div_mod_to_equations. split; lia.
    - eapply rw_cells_agree_nw; [exact DBUF|]. apply AG1. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx DLO LOQ SEPHM. split; lia.
    - eapply rw_cells_agree_nw; [exact RCL|]. apply AG1. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx RLO RHI FHI FTOP LOW LOQ RSEP. split; lia.
    - eapply bytes_at_agree; [exact RSH|]. apply AG1. intros x Hx. cbn [length] in Hx.
      assert (SHR : shad fO <= shad R /\ shad R + 3 <= shad (fO + fs_size kO)) by (unfold shad; clear - RLO RHI R8; Z.div_mod_to_equations; lia).
      clear - Hx SHR FSELF SHT LOW LOQ RLO RHI FLO FHI. split; lia.
    - apply (OSHADOWA_agree m m1 O SH). apply AG1. intros x Hx.
      assert (SHO : shad fO <= shad O /\ shad O + 33 <= shad (fO + fs_size kO)) by (unfold shad; clear - FLO FHI AL16; Z.div_mod_to_equations; lia).
      clear - Hx SHO FSELF SHT LOW LOQ RLO RHI FLO FHI. split; lia.
    - intros a Ha H1 H2. apply MU1. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [exact H2| exact I].
    -
      intros Σ' ocp t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' ART' MI' ST' RES' OCP' HMC' RSH' SH' LV' FRS' SP' CR' PRES'.
      eapply (HK Σ' ocp); [exact ART'| exact MI'| exact ST'| exact RES'| exact OCP'| subst D w; exact HMC'| exact RSH'| exact SH'| exact LV'| exact FRS'| exact SP'| exact CR'|].
      intros a Ha Ho. cbn [outside] in Ho. apply PRES'; [exact Ha| lia| lia]. }
  destruct (Z.eq_dec hm (D + w)) as [->|NE].
  - lstep. if_cases Kc; zify_cond Kc; [try clear Kc| exfalso; rewrite ?unsigned_lit in Kc by ul; ul].
    apply (JOINT _ MU WM ltac:(assumption) ltac:(assumption) HMC FR PB).
  - lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by ul; ul| try clear Kc].

    lstep. lstep.
    apply (JOINT _ MU WM ltac:(assumption) ltac:(assumption) HMC FR PB).
Qed.
End STR.
