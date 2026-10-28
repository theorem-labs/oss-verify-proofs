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

Definition xsp_frameA (j8 : list byte) (ra s0 s1 s2 s3 s4 s5 : word) : list cell :=
  [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Section XS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis ROWS : forall Σ m, ART RT Σ m -> imp_rowsA m.
Hypothesis OVF : overflowA_cps RT PMc.

Local Ltac ul := unfold OSS_XSPUTN_STACK_A, OSS_OV_STACK_A, OSS_PB_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition xsp_kont (K : config -> Prop) (L : list (Z * Z)) (FR0 : list (Z * nat)) (SP0 c0 len lo O q w0 N : Z) (m0 : mem)
    (cra : word) (gp cs0 cs1 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) : Prop :=
  forall (Σ' : rts RT) (st' : ossA) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo q ->
     SBINVA' m' O len st' -> oa_w st' = w0 + N -> OSHADOWA m' O ->
     rt_live RT Σ' = oachunk st' ++ L -> rt_frames RT Σ' = FR0 -> rt_sp0 RT Σ' = SP0 ->
     c0 + os_psi len st' <= rt_credit RT Σ' ->
     (forall a : word, aclient L FR0 q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m' a = m0 a) ->
     aevt RT PMc Σ' K (MS (mkR cra (wz q) gp (wz TPV_A) t0' t1' t2' cs0 cs1 (wz N) a1' a2' a3' a4' a5' a6' a7' cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F' (ret_pc cra) fc None m' (seg_rom bsegs)).

Lemma xsputn_exitA : forall (Σ : rts RT) (K : config -> Prop) (L : list (Z * Z)) (st : ossA) (c0 len lo O q w0 N fO : Z) (kO : nat) (m0 m : mem)
    (cra gp cs0 cs1 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (j8 : list byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xt3 xt4 xt5 xt6 : word) (F : bvmap 5 word),
  rt_live RT Σ = oachunk st ++ L -> In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O -> rt_sp0 RT Σ - STACK_WIN <= lo ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo (q + -64) -> lo + 64 <= q -> q + 16 <= USTACK_TOP ->
  SBINVA' m O len st -> oa_w st = w0 + N -> OSHADOWA m O -> c0 + os_psi len st <= rt_credit RT Σ ->
  rw_cells bsegs m (q + -64) (xsp_frameA j8 cra cs0 cs1 cs2 cs3 cs4 cs5) ->
  (forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m a = m0 a) ->
  xsp_kont K L (rt_frames RT Σ) (rt_sp0 RT Σ) c0 len lo O q w0 N m0 cra gp cs0 cs1 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 fc ->
  aevt RT PMc Σ K (MS (mkR xra (wz (q + -64)) gp (wz TPV_A) xt0 xt1 xt2 (wz N) (wz N) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        xs2 (wz (O + 8)) xs4 (wz (-1)) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
               F (wz 0x1208cc) fc None m (seg_rom bsegs)).
Proof using AF MST.
  intros until F. intros LVE INF (FLO & FHI & AL16) LOW ART0 MI ST LOQ QT INV W SH CR FR PRES KONT.
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & _).
  assert (Q0 : 0 <= q - 64) by (destruct ST; ul).
  unfold xsp_frameA in FR.
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

  lstep. do 7 lstep. lstep. release_frame FR ST q. lstep.
  apply evt_done. eapply (KONT Σ st); [| assumption| exact ST| exact INV| exact W| exact SH| exact LVE| reflexivity| reflexivity| exact CR| exact PRES].
  apply (art_client_write RT AF Σ m _ (q + -64) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul.
Qed.

Lemma xsputn_loopA : forall (k : nat) (Σ : rts RT) (K : config -> Prop) (L : list (Z * Z)) (st : ossA) (c0 len lo O q w0 S N i CAP fO : Z) (kO : nat) (bs : list byte) (m0 m : mem)
    (cra gp cs0 cs1 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (j8 : list byte)
    (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 : word) (F : bvmap 5 word),
  N - i <= Z.of_nat k ->
  rt_live RT Σ = oachunk st ++ L -> (forall p n, In (p, n) L -> 0 < n) -> In (fO, kO) (rt_frames RT Σ) -> oss_inA fO kO O ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> 0x7fff7f800000 <= lo ->
  SBINVA' m O len st -> OSHADOWA m O -> 0 <= len <= SJ_PADMAX -> oa_w st = w0 + i -> 0 <= i < N -> N < 2^40 ->
  rw_cells bsegs m S [CB (Z.to_nat CAP) bs] -> N <= CAP -> 0 < S -> S + CAP <= lo -> acc bsegs m S N ->
  ((exists p n, In (p, n) L /\ p <= S /\ S + CAP <= p + n) \/ (fO <= S /\ S + CAP <= fO + fs_size kO - 8)) -> (S + CAP <= O \/ O + 264 <= S) ->
  oa_w st + (N - i) <= PJ_OUTMAX len ->
  ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo (q + -64) -> lo + OSS_XSPUTN_STACK_A <= q -> q + 16 <= USTACK_TOP -> q mod 16 = 0 ->
  Z.of_nat (length L) + 2 <= LIVE_MAX -> 0 <= c0 -> c0 + os_psi len st <= rt_credit RT Σ ->
  rw_cells bsegs m (q + -64) (xsp_frameA j8 cra cs0 cs1 cs2 cs3 cs4 cs5) ->
  (forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m a = m0 a) ->
  xsp_kont K L (rt_frames RT Σ) (rt_sp0 RT Σ) c0 len lo O q w0 N m0 cra gp cs0 cs1 cs2 cs3 cs4 cs5 s6 s7 s8 s9 s10 s11 fc ->
  aevt RT PMc Σ K (MS (mkR xra (wz (q + -64)) gp (wz TPV_A) xt0 xt1 xt2 (wz i) (wz N) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                        (wz (S + i)) (wz (O + 8)) xs4 (wz (-1)) s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
               F (wz 0x12086c) fc None m (seg_rom bsegs)).
Proof using AF RC RC2 FDO MST ROWS OVF.
  induction k as [|k IH]; intros until F;
    intros HK LVE LPOS INF OIN LOW LOR INV SH HL W IR NB BUFC NC S0 STOP ACC SRC SEPO OUT ART0 MI ST LOQ QT Q16 LVB C00 CR FR PRES KONT; [lia|].
  pose proof OIN as (FLO & FHI & AL16).
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold OSS_XSPUTN_STACK_A, OSS_OV_STACK_A, OSS_PB_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT.
  remember (fs_size kO) as FSZ eqn:EFSZ.
  assert (Q0 : 0 <= q - 96) by (destruct ST; ul).
  assert (UQ64 : bv_unsigned (wz (q + -64)) = q + -64) by (apply unsigned_lit; ul).
  assert (LBS : length bs = Z.to_nat CAP) by (destruct BUFC as [[[HLx _] _] _]; exact HLx).
  destruct INV as (PUTC & REP & NUM). destruct PUTC as (PUTC & (hm & HMC & HMR) & (j108 & MODE)). unfold sb_cellsA in PUTC.
  pose proof (OSNUMA_cap24 len st NUM) as CAP24. pose proof (PJ_CAPMAX_bound len HL) as CMB. pose proof (OSNUMA_k len st HL NUM) as KB.
  pose proof (os_psi_nonneg len st HL NUM) as PSI0.
  set (cap := oa_cap st) in *. set (D := oa_data st) in *. set (lim := oa_lim st) in *. set (w := oa_w st) in *.
  pose proof NUM as (WB & K0 & CAPB & HB). change (oa_lim st) with lim in WB. change (oa_w st) with w in WB.
  assert (LIMR : 22 <= lim < cap) by (subst lim cap; unfold oa_lim in *; destruct (oa_heap st); [lia| destruct HB as [EC _]; unfold IMP_SCAP0 in EC; lia]).
  assert (M16 : oa_heap st = true -> cap mod 16 = 0).
  { intros HP. unfold STRREPA in REP. rewrite HP in REP. destruct REP as (_ & _ & _ & _ & X). exact X. }
  assert (DR : 0 < D /\ D + cap <= lo).
  { unfold STRREPA in REP. destruct (oa_heap st) eqn:HP.
    - destruct REP as (_ & _ & D0 & _). pose proof (af_live_range RT AF Σ m D cap ART0 ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)) as (_ & R1 & _). lia.
    - destruct REP as (_ & _ & ED). destruct HB as [EC _]. subst D cap. rewrite ED. unfold IMP_SCAP0 in EC. lia. }
  assert (CLF : forall Lx sp x, fO <= x < fO + FSZ - 8 -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; left. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (CLS : forall Lx sp x, shad fO <= x < shad (fO + FSZ) -> aclient Lx (rt_frames RT Σ) sp x).
  { intros Lx sp x Hx. right; right; right; right. exists fO, kO. rewrite <- EFSZ. split; [exact INF| lia]. }
  assert (SHO : shad fO <= shad O /\ shad O + 33 <= shad (fO + FSZ)) by (unfold shad; clear - FLO FHI AL16; Z.div_mod_to_equations; lia).
  assert (CSEP : forall a, aclient L (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0) as [H|H]; [| left; exact H| right; lia].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }

  assert (CLSRC : forall sp x, S <= x < S + CAP -> aclient L (rt_frames RT Σ) sp x).
  { intros sp x Hx. destruct SRC as [(p & n & Hin & Hp & Hn)|[H1 H2]].
    - right; right; left. exists p, n. split; [exact Hin| lia].
    - rewrite EFSZ in *. apply CLF. lia. }
  unfold xsp_frameA in FR.
  destruct (Z.eq_dec w lim) as [FULL|ROOM].
  -
    assert (CM : 2 * cap <= PJ_CAPMAX len) by (apply (os_grow_okA len st (N - i) ltac:(lia) NUM); [subst w lim; exact FULL| lia| subst w; lia]).

    assert (LBS' : (Z.to_nat i < length bs)%nat) by lia.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hn; [| exfalso; apply nth_error_None in Hn; lia].
    pose proof (u8arr_read bsegs m S bs i b (Z_to_bv 64 (S + i)) (u8arr_of_rw_cells _ _ _ _ _ BUFC) Hn ltac:(lia) ltac:(reflexivity)) as RD.
    pose proof (bv_unsigned_in_range 8 b) as BR. unfold bv_modulus in BR. cbn in BR.
    pose proof (ROWS Σ m ART0) as (_ & _ & _ & V4 & _). unfold OSS_SBVT_A, OSS_XSPUTN_A, OSS_OVERFLOW_A in V4.
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

    lstep. lstep. lstep. if_cases Kc; zify_cond Kc; [clear Kc| exfalso; rewrite ?unsigned_lit in Kc by ul; ul].

    unfold OSS_SB_VPTR_A in PUTC.
    lstep. lstep. lstep. lstep. lstep.
    apply evt_done. clear MU WM RD V4. fold OSS_SB_VPTR_A in PUTC.
    assert (INV : SBINVA' m O len st).
    { split; [| split; [exact REP| exact NUM]]. split; [exact PUTC|]. split; [exists hm; split; [exact HMC| exact HMR]| exists j108; exact MODE]. }
    assert (LVB1 : Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX).
    { rewrite LVE, length_app. unfold oachunk. destruct (oa_heap st); cbn [length]; lia. }
    assert (PSI1 : forall NEW, mcost (2 * cap) + os_psi len (oa_grown st NEW) <= os_psi len st /\ 0 <= os_psi len (oa_grown st NEW)).
    { intros NEW. pose proof (os_psi_grow len st NEW KB CAP24 CM) as X. split; [subst cap; lia|].
      unfold os_psi, oa_grown. cbn [oa_cap oa_k]. rewrite PJ_GROWC_val. subst cap. lia. }
    pose proof (PSI1 0) as [MC0 PSIG0]. pose proof (mcost_le_growc (2 * cap) ltac:(lia)) as MCB. rewrite PJ_GROWC_val in MCB.
    eapply (OVF Σ K L st len lo O (q + -64) (bv_unsigned b) fO kO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m FDO MST LVE LPOS INF OIN LOW LOR INV SH ltac:(exact FULL) HL CM ltac:(lia) ART0 MI ST
              ltac:(unfold OSS_OV_STACK_A, OSS_PB_STACK_A, RT_STACK; lia) ltac:(ul) ltac:(clear - Q16; Z.div_mod_to_equations; lia) LVB1 ltac:(subst cap; lia)).
    intros Σ1 NEW u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 m2 ART2 MI2 ST2 INV2 SH2 NTOP LV1 FRS1 SP1 CR1 PRES2.
    rewrite (ret_pc_even 0x1208b4) by lia.
    change (oa_cap st) with cap in NTOP, LV1, CR1.
    destruct (PSI1 NEW) as [MC PSIG]. clear PSI1.

    assert (AG2 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -64 <= x < q) \/ (S <= x < S + CAP) \/ (shad fO <= x < shad (fO + FSZ))) /\ ~ (O + 8 <= x < O + 112)) -> agree_on Q m m2).
    { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES2; [| cbn [outside]; split; [exact HN| exact I]].
      destruct HX as [H|[H|H]]; [left; ul| apply CLSRC; exact H| apply CLS; exact H]. }
    lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR2 : rw_cells bsegs m2 (q + -64) cs)
      by (eapply rw_cells_agree_nw; [exact FR|]; apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| ul]) end.
    assert (BUFC2 : rw_cells bsegs m2 S [CB (Z.to_nat CAP) bs]).
    { eapply rw_cells_agree_nw; [exact BUFC|]. apply AG2. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite Nat.add_0_r, Z2Nat.id in Hx by lia. split; [right; left; lia| lia]. }
    assert (ACC2 : acc bsegs m2 S N).
    { destruct SRC as [(p & n & Hin & Hp & Hn')|[H1 H2]].
      - apply (acc_sub bsegs m2 p n); [| lia| lia]. apply (proj2 (af_acc_live RT AF Σ1 m2 p n ART2 ltac:(rewrite LV1; right; exact Hin))).
      - apply (acc_agree_at m m2 S N ACC ltac:(lia)). apply AG2. intros x Hx. rewrite EFSZ in *.
        pose proof (proj2 (af_fshadow_apart RT AF Σ m fO kO ART0 INF) fO kO INF) as FSELF.
        split; [do 2 right; unfold shad in *; clear - Hx H1 H2 NC IR; Z.div_mod_to_equations; lia|]. unfold shad in *. clear - Hx H1 H2 NC IR FSELF FLO FHI. Z.div_mod_to_equations. lia. }
    assert (PRES02 : forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m2 a = m0 a).
    { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply PRES2; [| cbn [outside]; split; [exact Ho| exact I]].
      apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact He| intros e He; exact He| lia]. }
    clear AG2 FR BUFC ACC PRES ST MI SH INV PUTC HMC HMR MODE REP.

    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl [(q - 64, q)]%Z m2) as MU. pose proof (wmono_refl bsegs m2) as WM.
    lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| try clear Kc].
    lstep. lstep. lstep. if_cases Kc; zify_cond Kc; rewrite ?signed_lit in Kc by lia.
    +
      replace (Z_to_bv 64 (S + i + 1)) with (Z_to_bv 64 (S + (i + 1))) by (f_equal; lia).
      apply evt_done. clear MU WM.
      eapply (IH Σ1 K L (oa_grown st NEW) c0 len lo O q w0 S N (i + 1) CAP fO kO bs m0 m2);
        [lia| exact LV1| exact LPOS| rewrite FRS1; exact INF| exact OIN| rewrite SP1; exact LOW| exact LOR| exact INV2| exact SH2| exact HL
        | unfold oa_grown; cbn [oa_w]; subst w; lia| lia| exact NB| exact BUFC2| exact NC| exact S0| exact STOP| exact ACC2| rewrite <- EFSZ; exact SRC| exact SEPO
        | unfold oa_grown; cbn [oa_w]; subst w; lia| exact ART2| exact MI2| exact ST2| unfold OSS_XSPUTN_STACK_A, OSS_OV_STACK_A, OSS_PB_STACK_A, RT_STACK; lia| ul| exact Q16
        | exact LVB| exact C00| lia| exact FR2| rewrite FRS1; exact PRES02| rewrite FRS1, SP1; exact KONT].
    +
      lstep.
      replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 N) by (f_equal; lia).
      apply evt_done. clear MU WM.
      eapply (xsputn_exitA Σ1 K L (oa_grown st NEW) c0 len lo O q w0 N fO kO m0 m2);
        [exact LV1| rewrite FRS1; exact INF| exact OIN| rewrite SP1; exact LOW| exact ART2| exact MI2| exact ST2| lia| ul| exact INV2
        | unfold oa_grown; cbn [oa_w]; subst w; lia| exact SH2| lia| exact FR2| rewrite FRS1; exact PRES02| rewrite FRS1, SP1; exact KONT].
  -

    assert (DBUF : exists dlen dbs, rw_cells bsegs m D [CB dlen dbs] /\ lim + 1 <= Z.of_nat dlen <= cap
                   /\ (if oa_heap st then dlen = Z.to_nat cap else dlen = 23%nat /\ D = O + 73)).
    { unfold STRREPA in REP. destruct (oa_heap st) eqn:HP.
      - destruct REP as (R3 & (dbs & BLK) & _). exists (Z.to_nat cap), dbs. split; [exact BLK|]. split; [subst lim cap; unfold oa_lim; rewrite HP; lia| reflexivity].
      - destruct REP as (R1 & (dbs & R23) & ED). exists 23%nat, dbs. change (oa_data st) with D in ED. rewrite <- ED in R23. split; [exact R23|].
        destruct HB as [EC _]. subst lim cap. unfold oa_lim, IMP_SCAP0 in *. rewrite HP. split; [lia| split; [reflexivity| exact ED]]. }
    destruct DBUF as (dlen & dbs & DBUF & DLEN & DCASE).

    assert (SEP2 : S + CAP <= D \/ D + cap <= S).
    { destruct (oa_heap st) eqn:HP.
      - destruct SRC as [(p & n & Hin & Hp & Hn')|[H1 H2]].
        + destruct (af_live_disj RT AF Σ m D cap p n [] L ART0 ltac:(rewrite LVE; unfold oachunk; rewrite HP; reflexivity) ltac:(exact Hin)); lia.
        + pose proof (FLIVE D cap ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)). lia.
      - destruct DCASE as [_ ED]. destruct HB as [EC _]. subst cap. unfold IMP_SCAP0 in EC. rewrite ED, EC. lia. }

    assert (DCL : forall sp x, D <= x < D + cap -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp x).
    { intros sp x Hx. destruct (oa_heap st) eqn:HP.
      - right; right; left. exists D, cap. split; [rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity| lia].
      - destruct DCASE as [_ ED]. destruct HB as [EC _]. apply CLF. subst cap. unfold IMP_SCAP0 in EC. lia. }
    apply (aevt_evt RT AF PMc MST).
    pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.

    lstep. lstep. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by ul; ul| try clear Kc].

    lstep. lstep.
    set (n := Z.min (N - i) (lim - w)).
    assert (NR : 1 <= n /\ n <= N - i /\ n <= lim - w) by (subst n; lia).
    lazymatch goal with |- evt ?sg ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
      lazymatch R with context C [Z_to_bv 64 (N - i)] =>
        let R' := context C [Z_to_bv 64 n] in
        assert (JOIN : evt sg Q (MS R' FF (Z_to_bv 64 0x120888) fcc rv mm ro))
      end end.
    {

      lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit in Kc by lia; lia| try clear Kc].
      lstep. lstep. lstep.
      apply evt_done.

      pose proof ART0 as ART1. pose proof BUFC as BUFC1. pose proof DBUF as DBUF1. pose proof ACC as ACC1. pose proof SH as SH1.
      rename m into m1.

      destruct (rw_cells_CB_atA _ _ _ _ i BUFC1 ltac:(lia)) as [SB1 SB2].
      destruct (rw_cells_CB_atA _ _ _ _ n SB2 ltac:(cbn; lia)) as [SRCn SB3].
      pose proof SRCn as SRCb. apply rw_cells_bytes_at in SRCb. cbn [cells_bytes cbytes] in SRCb. rewrite app_nil_r in SRCb.
      assert (LSRC : Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))) = n) by (rewrite firstn_length_le; [lia| rewrite length_skipn; lia]).
      clear SB1 SB2 SB3 SRCn.
      assert (CS : checked_src RT Σ m1 (Z_to_bv 64 (q + -64)) lo (S + i) n).
      { unfold checked_src. rewrite UQ64. split; [| left; lia]. intros _. split; [apply (acc_sub bsegs m1 S N); [exact ACC1| lia| lia]|].
        destruct SRC as [(p & n' & Hin & Hp & Hn')|[H1 H2]].
        - left. exists p, n'. split; [rewrite LVE; apply in_or_app; right; exact Hin| lia].
        - right; left. exists fO, kO. split; [exact INF| lia]. }
      assert (DACC : acc bsegs m1 D cap).
      { destruct (oa_heap st) eqn:HP.
        - apply (proj2 (af_acc_live RT AF Σ m1 D cap ART1 ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity))).
        - destruct DCASE as [_ ED]. destruct HB as [EC _]. apply (acc_sub bsegs m1 O (8 * Z.of_nat 33)); [| rewrite ED; lia| subst cap; unfold IMP_SCAP0 in EC; rewrite ED, EC; cbn; lia].
          apply (acc_zero_run bsegs m1 O 33); [clear - AL16; Z.div_mod_to_equations; lia| lia| exact SH1]. }
      assert (CD : checked_dst RT Σ m1 (Z_to_bv 64 (q + -64)) (D + w) n).
      { unfold checked_dst. rewrite UQ64. split; [| split].
        - intros _. split; [apply (acc_sub bsegs m1 D cap); [exact DACC| lia| lia]|].
          destruct (oa_heap st) eqn:HP; [left; exists D, cap; split; [rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity| lia]|].
          right; left. exists fO, kO. destruct DCASE as [_ ED]. destruct HB as [EC _]. split; [exact INF| subst cap; unfold IMP_SCAP0 in EC; rewrite <- EFSZ; lia].
        - intros j Hj. apply DCL. lia.
        - apply (wr_at_sub m1 D (Z.of_nat dlen)); [apply (rw_cells_wr_at bsegs m1 _ _ _ DBUF1); cbn; lia| lia| lia| lia]. }
      assert (COK : call_ok RT Σ m1 (Z_to_bv 64 (q + -64)) lo).
      { unfold call_ok. rewrite UQ64. split; [exact ST|]. split; [lia|]. split; [ul|]. split; [ul| clear - Q16; Z.div_mod_to_equations; lia]. }
      clear MU WM.
      replace (Z_to_bv 64 n) with (Z_to_bv 64 (Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))))) by (rewrite LSRC; reflexivity).
      rewrite <- LSRC in CS, CD.
      eapply (aevt_memmove2P RT PMc FDO MST RC2 Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (D + w) (S + i) _ lo eq_refl eq_refl eq_refl ltac:(ul) ltac:(ul) ltac:(rewrite LSRC; lia) SRCb CS CD ART1 ltac:(assumption) COK).
      intros w0' w1 w2 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F2 m4 (ART4 & MI4 & WM4 & ST4) PRES4 BY4. rewrite UQ64 in ST4, PRES4. rewrite LSRC in PRES4.
      rewrite (ret_pc_even 0x120898) by lia.
      replace (Z_to_bv 64 (Z.of_nat (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))))) with (Z_to_bv 64 n) by (rewrite LSRC; reflexivity).

      assert (AG4 : forall Q : Z -> Prop, (forall x, Q x -> ((q + -64 <= x < q) \/ (fO <= x < fO + FSZ - 8) \/ (shad fO <= x < shad (fO + FSZ)) \/ (S <= x < S + CAP) \/ (D <= x < D + cap))
                                                       /\ ~ (D + w <= x < D + w + n)) -> agree_on Q m1 m4).
      { intros Q HP a Ha. destruct (HP _ Ha) as [HX HN]. apply PRES4; [| exact HN].
        destruct HX as [H|[H|[H|[H|H]]]]; [left; ul| apply CLF; exact H| apply CLS; exact H| | apply DCL; exact H].
        apply (aclient_mono _ _ _ _ _ _ _ (CLSRC (q + -64) _ H)); [rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }
      lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells bsegs m4 (q + -64) cs)
        by (eapply rw_cells_agree_nw; [exact FR|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [left; lia| ul]) end.
      assert (DPOS : (D = O + 73 /\ cap = 24) \/ (fO + FSZ <= D \/ D + cap <= fO)).
      { destruct (oa_heap st) eqn:HP; [right| left].
        - exact (FLIVE D cap ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)).
        - destruct DCASE as [_ ED]. destruct HB as [EC _]. split; [exact ED| subst cap; exact EC]. }

      assert (NDST : forall x, fO <= x < fO + FSZ - 8 -> ~ (O + 73 <= x < O + 96) -> ~ (D + w <= x < D + w + n)).
      { intros x Hx Hn. clear - Hx Hn DPOS NR LIMR WB FLO FHI. destruct DPOS as [[ED EC]|HD]; lia. }
      lazymatch type of PUTC with rw_cells _ _ _ ?cs => assert (PUTC4 : rw_cells bsegs m4 (O + 8) cs)
        by (eapply rw_cells_agree_nw; [exact PUTC|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| apply NDST; lia]) end.
      assert (HMC4 : rw_cells bsegs m4 (O + 96) [C8 (Z_to_bv 64 hm)])
        by (eapply rw_cells_agree_nw; [exact HMC|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| apply NDST; lia]).
      assert (MODE4 : rw_cells bsegs m4 (O + 104) [CB 4 mode16; CB 4 j108])
        by (eapply rw_cells_agree_nw; [exact MODE|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [right; left; lia| apply NDST; lia]).
      assert (SH4 : OSHADOWA m4 O).
      { apply (OSHADOWA_agree m1 m4 O SH1). apply AG4. intros x Hx. pose proof (proj2 (af_fshadow_apart RT AF Σ m1 fO kO ART0 INF) fO kO INF) as FSELF. rewrite <- EFSZ in FSELF.
        split; [do 2 right; left; lia|]. destruct (oa_heap st) eqn:HP.
        - pose proof (proj1 (af_fshadow_apart RT AF Σ m1 fO kO ART0 INF) D cap ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)) as FSL. rewrite <- EFSZ in FSL.
          clear - Hx SHO FSL NR LIMR WB. lia.
        - destruct DCASE as [_ ED]. destruct HB as [EC _]. clear - Hx SHO FSELF ED EC NR LIMR WB FLO FHI. subst cap. unfold IMP_SCAP0 in EC. lia. }
      assert (BUFC4 : rw_cells bsegs m4 S [CB (Z.to_nat CAP) bs]).
      { eapply rw_cells_agree_nw; [exact BUFC1|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite Nat.add_0_r, Z2Nat.id in Hx by lia.
        split; [do 3 right; left; lia| clear - Hx SEP2 NR LIMR WB; lia]. }
      assert (ACC4 : acc bsegs m4 S N).
      { destruct SRC as [(p & n' & Hin & Hp & Hn')|[H1 H2]].
        - apply (acc_sub bsegs m4 p n'); [| lia| lia]. apply (proj2 (af_acc_live RT AF Σ m4 p n' ART4 ltac:(rewrite LVE; apply in_or_app; right; exact Hin))).
        - apply (acc_agree_at m1 m4 S N ACC1 ltac:(lia)). apply AG4. intros x Hx.
          pose proof (proj2 (af_fshadow_apart RT AF Σ m1 fO kO ART0 INF) fO kO INF) as FSELF. rewrite <- EFSZ in FSELF.
          split; [do 2 right; left; unfold shad in *; clear - Hx H1 H2 NC IR; Z.div_mod_to_equations; lia|].
          destruct (oa_heap st) eqn:HP.
          + pose proof (proj1 (af_fshadow_apart RT AF Σ m1 fO kO ART0 INF) D cap ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)) as FSL. rewrite <- EFSZ in FSL.
            unfold shad in *. clear - Hx H1 H2 NC IR FSL NR LIMR WB. Z.div_mod_to_equations. lia.
          + destruct DCASE as [_ ED]. destruct HB as [EC _]. unfold shad in *. clear - Hx H1 H2 NC IR FSELF ED EC NR LIMR WB FLO FHI. subst cap. unfold IMP_SCAP0 in EC. Z.div_mod_to_equations. lia. }
      assert (REP4 : STRREPA m4 O st).
      { unfold STRREPA in REP |- *. destruct (oa_heap st) eqn:HP.
        - destruct REP as (R3 & _ & RR). split; [| split; [| exact RR]].
          + eapply rw_cells_agree_nw; [exact R3|]. apply AG4. intros x Hx. cbn in Hx. pose proof (FLIVE D cap ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)) as FD.
            split; [right; left; lia| clear - Hx FD NR LIMR WB FLO FHI; lia].
          +
            destruct (rw_cells_CB_atA _ _ _ _ w DBUF1 ltac:(lia)) as [DB1 DB2]. destruct (rw_cells_CB_atA _ _ _ _ n DB2 ltac:(cbn; lia)) as [_ DB3]. clear DB2.
            assert (DB1' : rw_cells bsegs m4 D [CB (Z.to_nat w) (firstn (Z.to_nat w) dbs)]).
            { eapply rw_cells_agree_nw; [exact DB1|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [do 4 right; lia| lia]. }
            lazymatch type of DB3 with rw_cells _ _ _ ?cs => assert (DB3' : rw_cells bsegs m4 (D + w + n) cs)
              by (eapply rw_cells_agree_nw; [exact DB3|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [do 4 right; lia| lia]) end.
            assert (DB2' : rw_cells bsegs m4 (D + w) [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))]).
            { pose proof (rw_cells_CB_intro m4 (D + w) _ BY4) as X. replace (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))) with (Z.to_nat n) in X by lia. apply X.
              rewrite Z2Nat.id by lia. apply (wr_at_sub m4 D (Z.of_nat dlen)); [| lia| lia| lia].
              apply (wr_at_transport bsegs m1 m4 D (Z.of_nat dlen)); [| exact WM4]. apply (rw_cells_wr_at bsegs m1 _ _ _ DBUF1). cbn. lia. }
            pose proof (rw_cells_CB_join2A _ _ _ _ _ _ _ DB1' DB2' ltac:(lia)) as DB12.
            pose proof (rw_cells_CB_join2A _ _ _ _ _ _ _ DB12 DB3' ltac:(lia)) as DBUF4.
            replace (Z.to_nat w + Z.to_nat n + (dlen - Z.to_nat w - Z.to_nat n))%nat with dlen in DBUF4 by lia. rewrite DCASE in DBUF4. eexists. exact DBUF4.
        - destruct REP as (R1 & _ & ED). destruct DCASE as [EDL ED']. destruct HB as [EC _]. split; [| split; [| exact ED]].
          + eapply rw_cells_agree_nw; [exact R1|]. apply AG4. intros x Hx. cbn in Hx. split; [right; left; lia| clear - Hx ED' WB; lia].
          + destruct (rw_cells_CB_atA _ _ _ _ w DBUF1 ltac:(lia)) as [DB1 DB2]. destruct (rw_cells_CB_atA _ _ _ _ n DB2 ltac:(cbn; lia)) as [_ DB3]. clear DB2.
            assert (DB1' : rw_cells bsegs m4 D [CB (Z.to_nat w) (firstn (Z.to_nat w) dbs)]).
            { eapply rw_cells_agree_nw; [exact DB1|]. apply AG4. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [do 4 right; subst cap; unfold IMP_SCAP0 in EC; lia| lia]. }
            lazymatch type of DB3 with rw_cells _ _ _ ?cs => assert (DB3' : rw_cells bsegs m4 (D + w + n) cs)
              by (eapply rw_cells_agree_nw; [exact DB3|]; apply AG4; intros x Hx; cbn [cells_size csize Nat.add] in Hx; split; [do 4 right; subst cap; unfold IMP_SCAP0 in EC; lia| lia]) end.
            assert (DB2' : rw_cells bsegs m4 (D + w) [CB (Z.to_nat n) (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))]).
            { pose proof (rw_cells_CB_intro m4 (D + w) _ BY4) as X. replace (length (firstn (Z.to_nat n) (skipn (Z.to_nat i) bs))) with (Z.to_nat n) in X by lia. apply X.
              rewrite Z2Nat.id by lia. apply (wr_at_sub m4 D (Z.of_nat dlen)); [| lia| lia| lia].
              apply (wr_at_transport bsegs m1 m4 D (Z.of_nat dlen)); [| exact WM4]. apply (rw_cells_wr_at bsegs m1 _ _ _ DBUF1). cbn. lia. }
            pose proof (rw_cells_CB_join2A _ _ _ _ _ _ _ DB1' DB2' ltac:(lia)) as DB12.
            pose proof (rw_cells_CB_join2A _ _ _ _ _ _ _ DB12 DB3' ltac:(lia)) as DBUF4.
            replace (Z.to_nat w + Z.to_nat n + (dlen - Z.to_nat w - Z.to_nat n))%nat with dlen in DBUF4 by lia. rewrite EDL in DBUF4.
            eexists. rewrite ED' in DBUF4. exact DBUF4. }
      assert (PRES04 : forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m4 a = m0 a).
      { intros a Ha Ho. rewrite <- (PRES a Ha Ho). apply PRES4.
        - apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia].
        - destruct (oa_heap st) eqn:HP.
          + pose proof (fresh_apart_l RT AF Σ m1 [(D, cap)] L D cap q (bv_unsigned a) ART0 ltac:(rewrite LVE; unfold oachunk; rewrite HP; reflexivity) ltac:(left; reflexivity) ltac:(ul) Ha). lia.
          + destruct DCASE as [_ ED]. lia. }
      clear AG4 FR PUTC HMC MODE BUFC1 DBUF1 ACC1 SH1 REP PRES PRES4 BY4 SRCb CS CD COK DBUF.

      apply (aevt_evt RT AF PMc MST).
      pose proof (munch_refl [(q - 64, q); (O + 56, O + 64)]%Z m4) as MU. pose proof (wmono_refl bsegs m4) as WM.
      lstep. lstep. lstep. lstep. lstep. lstep. lstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      replace (D + w + n) with (D + (w + n)) in PUTC4 by lia.
      assert (ART5 : ART RT Σ m5).
      { apply (art_client_write RT AF Σ m4 m5 (q + -64) ART4 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside].
        split; [intros Hin; apply Ha; left; ul|]. split; [intros Hin; apply Ha; apply CLF; lia| exact I]. }
      assert (AG5 : forall Q : Z -> Prop, (forall x, Q x -> ~ (q - 64 <= x < q) /\ ~ (O + 56 <= x < O + 64)) -> agree_on Q m4 m5).
      { intros Q HP a Ha. apply MU. cbn [outside]. destruct (HP _ Ha) as [X Y]. split; [exact X| split; [exact Y| exact I]]. }
      assert (INV5 : SBINVA' m5 O len (oa_adv st n)).
      { unfold SBINVA', PUTCELLSA, sb_cellsA, oa_adv, oa_lim. cbn [oa_data oa_cap oa_heap oa_k oa_w].
        change (oa_data st) with D. change (oa_w st) with w. change (if oa_heap st then oa_cap st - 1 else 22) with lim.
        split; [| split].
        - split; [exact PUTC4|]. split; [exists hm; split; [exact HMC4| lia]| exists j108; exact MODE4].
        - apply (STRREPA_agree m4 m5 O _ ltac:(unfold STRREPA; cbn [oa_heap oa_cap oa_data]; exact REP4)); [cbn [oa_cap]; lia|].
          apply AG5. intros x Hx. unfold strrep_rng in Hx. cbn [oa_heap oa_data oa_cap] in Hx. change (oa_data st) with D in Hx. change (oa_cap st) with cap in Hx.
          clear - Hx DR LOQ FHI FLO Q0 FTOP LOW DPOS. lia.
        - pose proof (OSNUMA_adv len st n NUM ltac:(lia)) as X. unfold oa_adv in X. apply X. change (oa_w st) with w. change (oa_lim st) with lim. lia. }
      assert (SH5 : OSHADOWA m5 O).
      { apply (OSHADOWA_agree m4 m5 O SH4). apply AG5. intros x Hx. pose proof (proj2 (af_fshadow_apart RT AF Σ m4 fO kO ART4 INF) fO kO INF) as FSELF. rewrite <- EFSZ in FSELF.
        pose proof (fframe_ranges RT AF Σ m4 fO kO ART4 INF) as (_ & _ & _ & _ & SHT). rewrite <- EFSZ in SHT. clear - Hx SHO FSELF SHT LOW LOQ FLO FHI. lia. }
      assert (PRES05 : forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m5 a = m0 a).
      { intros a Ha Ho. rewrite <- (PRES04 a Ha Ho). apply MU. cbn [outside]. split; [destruct (CSEP _ Ha); lia|]. split; [lia| exact I]. }
      lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR5 : rw_cells bsegs m5 (q + -64) cs) by assumption end.
      assert (ACC5 : acc bsegs m5 S N).
      { apply (acc_agree_at m4 m5 S N ACC4 ltac:(lia)). apply AG5. intros x Hx.
        pose proof (af_frames_hi RT AF Σ m4 fO kO ART4 INF) as FRHI. rewrite <- EFSZ in FRHI.
        unfold shad, SHB in *. clear - Hx FRHI LOR LOQ QT STOP NC FLO FHI S0. Z.div_mod_to_equations. lia. }
      rename BUFC4 into BUFC5.
      clear AG5 PUTC4 HMC4 MODE4 REP4 SH4 PRES04 ACC4.
      if_cases Kc; zify_cond Kc; rewrite ?signed_lit in Kc by lia.
      +
        replace (Z_to_bv 64 (n + i)) with (Z_to_bv 64 N) by (f_equal; lia).
        apply evt_done. clear MU WM.
        eapply (xsputn_exitA Σ K L (oa_adv st n) c0 len lo O q w0 N fO kO m0 m5);
          [exact LVE| exact INF| exact OIN| exact LOW| exact ART5| assumption| exact ST4| lia| ul| exact INV5
          | unfold oa_adv; cbn [oa_w]; change (oa_w st) with w; lia| exact SH5| rewrite os_psi_adv; exact CR| exact FR5| exact PRES05| exact KONT].
      +
        replace (Z_to_bv 64 (S + i + n)) with (Z_to_bv 64 (S + (n + i))) by (f_equal; lia).
        apply evt_done. clear MU WM.
        eapply (IH Σ K L (oa_adv st n) c0 len lo O q w0 S N (n + i) CAP fO kO bs m0 m5);
          [lia| exact LVE| exact LPOS| exact INF| exact OIN| exact LOW| exact LOR| exact INV5| exact SH5| exact HL
          | unfold oa_adv; cbn [oa_w]; change (oa_w st) with w; lia| lia| exact NB| exact BUFC5| exact NC| exact S0| exact STOP| exact ACC5| rewrite <- EFSZ; exact SRC| exact SEPO
          | unfold oa_adv; cbn [oa_w]; change (oa_w st) with w; lia| exact ART5| assumption| exact ST4| unfold OSS_XSPUTN_STACK_A, OSS_OV_STACK_A, OSS_PB_STACK_A, RT_STACK; lia| ul| exact Q16
          | exact LVB| exact C00| rewrite os_psi_adv; exact CR| exact FR5| exact PRES05| exact KONT]. }

    lstep. if_cases Kc; zify_cond Kc; rewrite ?signed_lit in Kc by lia.
    + exact_evt JOIN.
    + lstep. exact_evt JOIN.
Qed.

Theorem xsputnA_proof : xsputnA_cps RT PMc.
Proof using AF RC RC2 FDO MST ROWS OVF.
  unfold xsputnA_cps. intros until m. intros FDO' MST' LVE LPOS INF OIN LOW LOR INV SH HL BUFC NR S0 STOP ACC SRC SEPO OUT ART0 MI ST LOQ QT Q16 LVB CR HK.
  pose proof OIN as (FLO & FHI & AL16).
  pose proof (af_frames_range RT AF Σ m fO kO ART0 INF) as (F0 & FTOP & FSEG & FLIVE).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  unfold OSS_XSPUTN_STACK_A, OSS_OV_STACK_A, OSS_PB_STACK_A, RT_STACK in LOQ. unfold OSS_XSPUTN_A. unfold USTACK_TOP in QT.
  assert (Q0 : 0 <= q - 96) by (destruct ST; ul).
  assert (NB : N < 2^40).
  { pose proof (PJ_CAPMAX_bound len HL). destruct INV as (_ & _ & (WB & _ & (_ & CM) & _)). unfold PJ_CAPMAX, PJ_OUTMAX in *. lia. }
  pose proof (os_psi_nonneg len st HL ltac:(destruct INV as (_ & _ & N'); exact N')) as PSI0.
  assert (CSEP : forall a, aclient L (rt_frames RT Σ) q a -> q <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split_c RT AF Σ m q a ART0) as [H|H]; [| left; exact H| right; lia].
    apply (aclient_mono _ _ _ _ _ _ _ Ha); [rewrite LVE; intros e He; apply in_or_app; right; exact He| intros e He; exact He| lia]. }
  destruct INV as (PUTC & REP & NUM).
  assert (DLO : forall x, sbinv_rngI O st x -> x < lo).
  { intros x [Hx|[HP Hx]]; [lia|]. pose proof (af_live_range RT AF Σ m (oa_data st) (oa_cap st) ART0 ltac:(rewrite LVE; unfold oachunk; rewrite HP; left; reflexivity)). lia. }
  apply (aevt_evt RT AF PMc MST).
  pose proof (munch_refl [(q - 64, q)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct PUTC as (PUTC & (hm & HMC & HMR) & (j108 & MODE)). pj_hide REP. pj_hide PUTC. pj_hide HMC. pj_hide MODE.
  lstep. carve_frame 64%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 64 _ [] [8;8;8;8;8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR. forget_junk FR.

  do 7 lstep. lstep. if_cases Kc; zify_cond Kc; [exfalso; rewrite ?unsigned_lit, ?signed_lit in Kc by lia; lia| try clear Kc].
  do 5 lstep. lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  pj_unhide REP. pj_unhide PUTC. pj_unhide HMC. pj_unhide MODE.
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (q - 64) ART0 ltac:(ul)); [| exact WM]. intros a Ha. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. ul. }
  assert (AGL : agree_on (fun x => x < lo) m m1) by (intros a Ha; apply MU; cbn [outside]; split; [lia| exact I]).
  assert (INV1 : SBINVA' m1 O len st).
  { apply (SBINVA'_agree m m1 O len st); [| intros a Ha; apply AGL; exact (DLO _ Ha)].
    split; [| split; [exact REP| exact NUM]]. split; [exact PUTC|]. split; [exists hm; split; [exact HMC| exact HMR]| exists j108; exact MODE]. }
  assert (SH1 : OSHADOWA m1 O).
  { apply (OSHADOWA_agree m m1 O SH). intros a Ha. apply AGL. pose proof (fframe_ranges RT AF Σ m fO kO ART0 INF) as (_ & _ & _ & _ & SHT). unfold shad in *. clear - Ha SHT LOW FLO FHI. Z.div_mod_to_equations. lia. }
  rename BUFC into BUFC1.
  assert (ACC1 : acc bsegs m1 S N).
  { apply (acc_agree_at m m1 S N ACC ltac:(lia)). intros a Ha. apply AGL. unfold shad, SHB in *. clear - Ha LOR LOQ QT STOP NR S0. Z.div_mod_to_equations. lia. }
  assert (PRES1 : forall a : word, aclient L (rt_frames RT Σ) q (bv_unsigned a) -> ~ (O + 8 <= bv_unsigned a < O + 112) -> m1 a = m a).
  { intros a Ha _. apply MU. cbn [outside]. split; [| exact I]. destruct (CSEP _ Ha); ul. }
  clear PUTC HMC HMR MODE REP MU WM.
  replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia).
  apply evt_done.
  eapply (xsputn_loopA (Z.to_nat N) Σ K L st (rt_credit RT Σ - os_psi len st) len lo O q (oa_w st) S N 0 CAP fO kO bs m m1);
    [lia| exact LVE| exact LPOS| exact INF| exact OIN| exact LOW| exact LOR| exact INV1| exact SH1| exact HL| lia| lia| exact NB| exact BUFC1| lia| exact S0| exact STOP| exact ACC1
    | exact SRC| exact SEPO| lia| exact ART1| assumption| exact ST| unfold OSS_XSPUTN_STACK_A, OSS_OV_STACK_A, OSS_PB_STACK_A, RT_STACK; lia| ul| exact Q16| exact LVB| lia| lia
    | exact FR| exact PRES1|].

  intros Σ' st' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' ART' MI' ST' INV' W' SH' LV' FRS' SP' CR' PRES'.
  eapply (HK Σ' st'); [exact ART'| exact MI'| exact ST'| exact INV'| exact W'| exact SH'| exact LV'| exact FRS'| exact SP'| lia|].
  intros a Ha Ho. cbn [outside] in Ho. apply PRES'; [exact Ha| lia].
Qed.
End XS.
