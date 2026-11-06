(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim Stdio SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Sj_num_kit Atp_h_defs Od_kit.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_cpsB Od_hkit0A Od_lkitB Od_bodyB Od_beginB Od_top_defsB
  Od_setup_defsB Od_setupkB Od_setupk2B Od_setupw2B Od_setupw3B.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma pres_fp_step : forall (L : list (Z * Z)) usp W (m0 m m' : mem),
  rt_pres_fp L [] usp W m0 m -> (forall a : word, aclient L [] usp (bv_unsigned a) -> m' a = m a) -> rt_pres_fp L [] usp W m0 m'.
Proof. intros L usp W m0 m m' H HS a Ha Ho. rewrite (HS a Ha). exact (H a Ha Ho). Qed.

Ltac xfer_all LIBp LIBx m m' AG WM side vside libside cpside :=
  repeat match goal with
  | H : stk bsegs m ?lo ?hi |- _ =>
      first [ let Q := fresh "AGQ" in
              assert (Q : agree_on (fun x => lo <= x < hi) m m') by (eapply agree_sub; [exact AG| side]);
              apply (fun X => stk_agree bsegs m m' lo hi X Q WM) in H; clear Q
            | clear H ]
  | H : vrepA m ?V ?A ?c ?sz ?e |- _ =>
      let Q := fresh "AGQ" in
      assert (Q : agree_on (fun x => V <= x < V + 24 \/ A <= x < A + 16 * sz) m m') by (eapply agree_sub; [exact AG| vside]);
      apply (fun X => oa_vrepA_agree m m' V A c sz e X Q) in H; clear Q
  | H : rt_pres_fp ?L [] ?u ?W ?m0 m |- _ =>
      let Q := fresh "AGQ" in
      assert (Q : forall a : word, aclient L [] u (bv_unsigned a) -> m' a = m a) by cpside;
      apply (fun X => pres_fp_step L u W m0 m m' X Q) in H; clear Q
  | H : LIBp m |- _ =>
      let Q := fresh "AGQ" in
      assert (Q : agree_on (in_ranges LIB_FP) m m') by libside;
      apply (fun X => LIBx m m' X Q) in H; clear Q
  end;
  lazymatch goal with
  | H : vrepA m _ _ _ _ _ |- _ => fail 1 "xfer_all: vrepA not transported"
  | H : rt_pres_fp _ _ _ _ _ m |- _ => fail 1 "xfer_all: rt_pres_fp not transported"
  | H : LIBp m |- _ => fail 1 "xfer_all: LIB not transported"
  | _ => idtac
  end;
  rt_transport_with m m' AG WM side.

Section PhaseB.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.

Notation aevt := (aevt RT PMc).
Local Ltac ul := unfold FUZZ_STACK, OD_NEED in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Lemma LIB_agreeB : forall m m', LIB m -> agree_on (in_ranges LIB_FP) m m' -> LIB m'.
Proof using LIB_loc. intros m m' H AG. apply (LIB_loc m m' H). intros a Ha. apply AG. exact Ha. Qed.

Lemma zero16_cells : forall (m : mem) a, bytes_at bsegs m a (repeat (Z_to_bv 8 0) 16) -> wr_at bsegs m a 16 ->
  rw_cells bsegs m a [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof using.
  intros m a B W. split; [split; [cbn; auto| exact B]| exact W].
Qed.

Lemma aevt_memcmp : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (p q : Z) (bp bq : list byte) (lo : Z),
  a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 q -> a2 = Z_to_bv 64 (Z.of_nat (length bp)) ->
  length bq = length bp -> 0 < p <= 2^47 -> 0 < q <= 2^47 -> (0 < length bp)%nat -> Z.of_nat (length bp) < 2^20 ->
  bytes_at bsegs m p bp -> bytes_at bsegs m q bq ->
  checked_src RT Σ m sp lo p (Z.of_nat (length bp)) -> checked_src RT Σ m sp lo q (Z.of_nat (length bp)) ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> frm0 fc ->
  (forall (r : word) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', frm0 fc' ->
     (r = Z_to_bv 64 0 <-> bp = bq) ->
     rt_after RT Σ (bv_unsigned sp) lo m m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) 0 0 m m' ->
     aevt Σ K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_memcmp) fc None m (seg_rom bsegs)).
Proof using RTF FDO MST.
  intros until lo. intros E0 E1 E2 LQ P0 Q0 LP LL BP BQ CP CQ ART0 MI0 COK F0 HK.
  eapply (aevt_rt RT PMc); [| exact F0 |].
  - exact (rf_memcmp RT RTF Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m p q bp bq lo FDO MST E0 E1 E2 LQ P0 Q0 LP LL BP BQ CP CQ ART0 MI0 COK).
  - intros c (r & RQ & HQ). unfold icpt_post in HQ. eexists Σ, _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & _) F0'. revert F0'.
    apply (ret_st_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => frm0 (ms_fcsr ms) -> aevt Σ K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' F0'. exact (HK r q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' fc' m' F0' RQ RA PR).
Qed.

Lemma od_cutB_intro : forall (Σ0 ΣB : rts RT) (m0 mB : mem) (usp S1 F lo : Z) (dz : list Z) (A cap size COPY BUF : Z) (els : list (Z * Z))
    (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word)
    (j0 j144 j176 j264 j288 j336 j376 j384 j432 h0 h8 jd jp : list byte),
  usp mod 16 = 0 -> usp + 16 <= USTACK_TOP -> S1 mod 32 = 0 -> usp - 560 <= S1 <= usp - 544 ->
  rt_sp0 RT Σ0 - STACK_WIN <= lo -> lo + FUZZ_STACK <= usp -> F mod 64 = 0 -> 0 < F ->
  rt_frames RT Σ0 = [] -> (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ0 ->
  ART RT ΣB mB -> mem_inv bsegs mB -> stk bsegs mB lo S1 -> rt_frames RT ΣB = [(F, 3%nat)] -> rt_sp0 RT ΣB = rt_sp0 RT Σ0 ->
  rw_cells bsegs mB (S1 + 384) [CB 48 j384; CB 8 j432] ->
  stk bsegs mB (S1 + 440) (usp - 104) -> rw_cells bsegs mB (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
  rw_cells bsegs mB F [CB 8 h0; CB 24 h8] ->
  vrepA mB (F + 32) A cap size els -> 1 <= size -> wr_at bsegs mB (F / 8 + 2147450880) 64 ->
  rw_cells bsegs mB (F + 192) [CB 64 jd] -> LIB mB -> rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 mB ->
  bytes_ok dz /\ zlength dz < 2^26 ->
  rt_live RT ΣB = (if od_copied dz then [(COPY, zlength (od_s0 dz) + 64)] else []) ++ vblockA A cap size ++ rt_live RT Σ0 ->
  (if od_copied dz
   then 0 < COPY /\ COPY mod 16 = 0 /\ COPY <= BUF <= COPY + 3 /\ BUF - COPY + zlength (od_doc dz) = zlength (od_s0 dz)
        /\ bytes_at bsegs mB BUF (padded_bytes (od_doc dz))
   else COPY = 0 /\ BUF = 0) ->
  rt_credit RT Σ0 - OD_VEC_COST - OD_PAD_COST <= rt_credit RT ΣB ->
  rw_cells bsegs mB S1 (od_lowB F (od_action dz) (if od_copied dz then 0 else 1) COPY j0 j144 j176 j264 j288 j336 j376) ->
  rw_cells bsegs mB (F + 96) [C1 (Z_to_bv 8 0); CB 7 jp] ->
  rw_cells bsegs mB (F + 104) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs mB (F + 120) [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 1024)] ->
  rw_cells bsegs mB (F + 136) [C8 (Z_to_bv 64 (zlength (od_doc dz))); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs mB (F / 8 + 2147450880) (map (fun z => C1 (Z_to_bv 8 z)) [0xf1; 0xf1; 0xf1; 0xf1; 0; 0; 0; 0xf2; 0xf2; 0xf2; 0xf2; 0xf2]) ->
  rw_cells bsegs mB (F / 8 + 2147450892) (map C1 (repeat (Z_to_bv 8 0) 7)) ->
  rw_cells bsegs mB (F / 8 + 2147450899) (map (fun z => C1 (Z_to_bv 8 z)) [0xf2; 0xf2; 0xf2; 0xf2; 0xf2]) ->
  rw_cells bsegs mB (F / 8 + 2147450904) (map C1 (repeat (Z_to_bv 8 0) 8)) ->
  rw_cells bsegs mB (F / 8 + 2147450912) (map (fun z => C1 (Z_to_bv 8 z)) [0xf3; 0xf3; 0xf3; 0xf3]) ->
  od_cutB RT LIB Σ0 ΣB m0 mB usp S1 F lo dz A cap size COPY BUF els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11.
Proof using.
  intros until jp.
  intros U16 UT S32 S1R LOW LOR F64 FPOS FRS0 LVPOS LVB CR0 ARTx MIx STx FRSx SPx HI STp FRs HDR VR SZ1 WRS FDoc LIBx CPx DZ LVx CPY CRx
    LOWx PA0 PA8 PA24 PA40 SHa SHp SHb SHd SHc.
  constructor.
  - constructor; try assumption.
    + split; assumption.
    + split; assumption.
    + split; assumption.
    + split; assumption.
    + eexists _, _. exact HI.
    + eexists _, _. exact HDR.
    + eexists. exact FDoc.
  - exact DZ.
  - exact LVx.
  - exact CPY.
  - exact CRx.
  - eexists _, _, _, _, _, _, _. exact LOWx.
  - exists jp. unfold od_parserB, wz.
    change [C1 (Z_to_bv 8 0); CB 7 jp; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 1024);
            C8 (Z_to_bv 64 (zlength (od_doc dz))); C8 (Z_to_bv 64 0)]
      with ([C1 (Z_to_bv 8 0); CB 7 jp] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 4294967295); C8 (Z_to_bv 64 1024)]
            ++ [C8 (Z_to_bv 64 (zlength (od_doc dz))); C8 (Z_to_bv 64 0)]).
    apply Sj_stage1_kit.rw_cells_app. split; [exact PA0|]. cbn [cells_size csize Nat.add]. replace (F + 96 + Z.of_nat 8) with (F + 104) by lia.
    apply Sj_stage1_kit.rw_cells_app. split; [exact PA8|]. cbn [cells_size csize Nat.add]. replace (F + 104 + Z.of_nat 16) with (F + 120) by lia.
    apply Sj_stage1_kit.rw_cells_app. split; [exact PA24|]. cbn [cells_size csize Nat.add]. replace (F + 120 + Z.of_nat 16) with (F + 136) by lia.
    exact PA40.
  - unfold od_shadow. cbn [map repeat] in *.
    lazymatch goal with |- rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 ::
                                            ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: ?c21 :: ?c22 :: ?c23 ::
                                            ?c24 :: ?c25 :: ?c26 :: ?c27 :: ?c28 :: ?c29 :: ?c30 :: ?c31 :: ?rest) =>
      change (rw_cells bsegs mB (F / 8 + 2147450880) ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [c12; c13; c14; c15; c16; c17; c18] ++ [c19; c20; c21; c22; c23]
                                     ++ [c24; c25; c26; c27; c28; c29; c30; c31] ++ rest)) end.
    apply Sj_stage1_kit.rw_cells_app. split; [exact SHa|]. cbn [cells_size csize Nat.add]. replace (F / 8 + 2147450880 + Z.of_nat 12) with (F / 8 + 2147450892) by lia.
    apply Sj_stage1_kit.rw_cells_app. split; [exact SHp|]. cbn [cells_size csize Nat.add]. replace (F / 8 + 2147450892 + Z.of_nat 7) with (F / 8 + 2147450899) by lia.
    apply Sj_stage1_kit.rw_cells_app. split; [exact SHb|]. cbn [cells_size csize Nat.add]. replace (F / 8 + 2147450899 + Z.of_nat 5) with (F / 8 + 2147450904) by lia.
    apply Sj_stage1_kit.rw_cells_app. split; [exact SHd|]. cbn [cells_size csize Nat.add]. replace (F / 8 + 2147450904 + Z.of_nat 8) with (F / 8 + 2147450912) by lia.
    exact SHc.
Qed.

Theorem od_phaseB : od_phaseB_stmt RT LIB PMc.
Proof using LIB_loc AF FDO MST RTF NEWA AFC.
  intros K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 _ _ KB.
  unfold od_cutA_k.
  intros ΣA S1 F A cap size p0 els xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc mA FRM CA.
  destruct CA as [C0 DZ LV CR (j0 & j136 & j176 & j264 & j288 & j336 & j376 & LOWF) (jp & PAR) SH (els' & EELS) P0R S0B S0L].
  destruct C0 as [(U16 & UT) (S32 & S1R) (LOW & LOR) (F64 & FPOS) FRS0 LVPOS LVB CR0 ART0 MI0 ST0 FRS SP0 (j384 & j432 & HI) STp SAVED (h0 & h8 & HDR)
                  VR SZ1 WRS (jd & DOC) LIB0 CP0].
  set (s0 := od_s0 dz) in *. set (len0 := zlength s0) in *.
  assert (LEN0 : 0 <= len0 < 2^26).
  { destruct (oa_els_shape 0 (tl dz)) as (_ & _ & _ & _ & PREF). subst len0 s0. unfold od_s0, od_parts, od_rest.
    rewrite PREF. unfold zlength in *. rewrite firstn_length. destruct DZ as (_ & DL). destruct dz as [|c l]; cbn [tl length] in *; lia. }
  pose proof (af_sp0_range RT AF ΣA mA ART0) as SP0R.
  assert (INF : In (F, 3%nat) (rt_frames RT ΣA)) by (rewrite FRS; left; reflexivity).
  pose proof (fframe_ranges RT AF ΣA mA F 3 ART0 INF) as (_ & FR1' & _ & SHB0 & SHT).
  pose proof (af_fshadow_apart RT AF ΣA mA F 3 ART0 INF) as (FSL & FSF). pose proof (FSF F 3%nat INF) as FSELF.
  pose proof (af_frames_align RT AF ΣA mA F 3 ART0 INF) as (_ & FSEG).
  pose proof (af_frames_range RT AF ΣA mA F 3%nat ART0 INF) as (_ & _ & _ & FLV).
  change (fs_size 3) with 512 in *. rewrite SP0 in FR1', SHT.
  assert (SHF : shad (F + 512) = shad F + 64) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  rewrite SHF in *. unfold shad, SHB in SHB0, SHT, FSELF, FSL.
  assert (FD0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  set (S := F / 8 + 2147450880) in *.
  assert (GF : F + 512 <= lo /\ S + 64 <= lo /\ (F + 512 <= S \/ S + 64 <= F) /\ SEGTOP_A <= F) by (clear - FR1' SHT LOW FSELF FSEG; ul).
  destruct GF as (FLO & SLO & FSEP & FSG).
  assert (LOWA : rt_sp0 RT ΣA - STACK_WIN <= lo) by (rewrite SP0; exact LOW).
  assert (EU1 : bv_unsigned (Z_to_bv 64 S1) = S1) by (apply unsigned_lit; ul).

  pose proof VR as (VSZ & VSC & VCAP & VA0 & VAT & VS & VB).
  destruct VB as [(B1 & B2)|(CAP1 & A16 & APOS & VEL)]; [lia|].
  assert (INV : In (A, 16 * size) (rt_live RT ΣA)).
  { rewrite LV. apply in_or_app. left. unfold vblockA. destruct (cap =? 0) eqn:CZ; [apply Z.eqb_eq in CZ; lia|]. apply ann_block_vis. }
  pose proof (af_live_range RT AF ΣA mA A (16 * size) ART0 INV) as (_ & AV1 & _).
  pose proof (FLV A (16 * size) INV) as FAV. pose proof (FSL A (16 * size) INV) as SAV.
  assert (SHZA : shz mA A 16).
  { eapply shz_sub; [exact (shz_live RT AF ΣA mA A (16 * size) ART0 INV ltac:(clear - A16; Z.div_mod_to_equations; lia))| lia|].
    replace (16 * size / 8) with (2 * size) by (clear; Z.div_mod_to_equations; lia). lia. }

  assert (S0C : len0 = 0 \/ exists p k, In (p, k) (rt_live RT ΣA) /\ p <= p0 /\ p0 + len0 <= p + k /\ (F + 512 <= p \/ p + k <= F) /\ (p + k <= S \/ S + 64 <= p) /\ p + k <= lo).
  { destruct S0L as [E|(p & k & Hin & P1 & P2)]; [left; subst len0; fold s0; rewrite E; reflexivity| right]. exists p, k.
    assert (Hin' : In (p, k) (rt_live RT ΣA)) by (rewrite LV; apply in_or_app; right; exact Hin).
    pose proof (af_live_range RT AF ΣA mA p k ART0 Hin') as (_ & R1 & _).
    split; [exact Hin'|]. split; [exact P1|]. split; [exact P2|]. split; [exact (FLV p k Hin')|]. split; [exact (FSL p k Hin')|]. clear - R1 LOWA. lia. }
  assert (S0BL : Z.of_nat (length (zbytes s0)) = len0) by (unfold zbytes; rewrite length_map; reflexivity).

  assert (ACL0 : forall x, (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (p0 <= x < p0 + len0) ->
                   aclient (rt_live RT ΣA) (rt_frames RT ΣA) S1 x).
  { intros x [H|[H|[H|[H|H]]]].
    - left. ul.
    - right; right; right; left. exists F, 3%nat. change (fs_size 3) with 512. split; [exact INF| lia].
    - right; right; right; right. exists F, 3%nat. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. split; [exact INF| lia].
    - right; right; left. exists A, (16 * size). split; [exact INV| lia].
    - destruct S0C as [E|(p & k & Hin & P1 & P2 & _)]; [lia|]. right; right; left. exists p, k. split; [exact Hin| lia]. }

  assert (CALLER : forall x, aclient (rt_live RT Σ0) [] usp x ->
            ~ (F <= x < F + 512) /\ ~ (S <= x < S + 64) /\ ~ (lo <= x < usp) /\ aclient (rt_live RT ΣA) (rt_frames RT ΣA) S1 x).
  { intros x [H|[H|[H|[H|H]]]].
    - split; [clear - H FLO LOR; ul|]. split; [clear - H SLO LOR; ul|]. split; [lia|]. left; clear - H S1R; lia.
    - pose proof (client_static_range x H) as CRr.
      split; [clear - CRr FSG; ul|]. split; [clear - CRr SHB0; ul|]. split; [clear - CRr SP0R LOWA; ul|]. right; left; exact H.
    - destruct H as (p & n & Hin & Hp).
      assert (HinL : In (p, n) (rt_live RT ΣA)) by (rewrite LV; apply in_or_app; right; exact Hin).
      pose proof (FLV p n HinL) as D1. pose proof (FSL p n HinL) as D2. pose proof (af_live_range RT AF ΣA mA p n ART0 HinL) as (_ & D3 & _).
      split; [clear - Hp D1; lia|]. split; [clear - Hp D2; lia|]. split; [clear - Hp D3 LOWA; lia|].
      right; right; left; exists p, n; split; [exact HinL| exact Hp].
    - destruct H as (f & k & [] & _).
    - destruct H as (f & k & [] & _). }

  unfold od_shadow in SH. cbn [map] in SH.
  lazymatch type of SH with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 ::
                                            ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: ?c21 :: ?c22 :: ?c23 ::
                                            ?c24 :: ?c25 :: ?c26 :: ?c27 :: ?c28 :: ?c29 :: ?c30 :: ?c31 :: ?rest) =>
    change (rw_cells bsegs mA S ([c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] ++ [c12; c13; c14; c15; c16; c17; c18] ++ [c19; c20; c21; c22; c23]
                                   ++ [c24; c25; c26; c27; c28; c29; c30; c31] ++ rest)) in SH end.
  apply Sj_stage1_kit.rw_cells_app in SH. destruct SH as [SHa X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [SHp X].
  apply Sj_stage1_kit.rw_cells_app in X. destruct X as [SHb X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [SHd SHc].
  cbn [cells_size csize Nat.add] in SHp, SHb, SHd, SHc.
  replace (S + Z.of_nat 12) with (F / 8 + 2147450892) in * by (subst S; lia).
  replace (F / 8 + 2147450892 + Z.of_nat 7) with (F / 8 + 2147450899) in * by lia.
  replace (F / 8 + 2147450899 + Z.of_nat 5) with (F / 8 + 2147450904) in * by lia.
  replace (F / 8 + 2147450904 + Z.of_nat 8) with (F / 8 + 2147450912) in * by lia.
  apply (rw_cells_split_CB bsegs _ _ [] 56 _ [] [1; 7; 16; 8; 8; 16]%nat) in PAR; [| reflexivity]. cbn [mk_CB_cells app] in PAR.
  repeat match type of PAR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jq" in set (j := t) in PAR; clearbody j end.
  lazymatch type of PAR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    change (rw_cells bsegs mA (F + 96) ([c0; c1] ++ [c2] ++ [c3; c4] ++ rest)) in PAR end.
  apply Sj_stage1_kit.rw_cells_app in PAR. destruct PAR as [PA0 X]. apply Sj_stage1_kit.rw_cells_app in X. destruct X as [PA8 X].
  apply Sj_stage1_kit.rw_cells_app in X. destruct X as [PA24 PA40].
  cbn [cells_size csize Nat.add] in PA8, PA24, PA40.
  replace (F + 96 + Z.of_nat 8) with (F + 104) in * by lia.
  replace (F + 104 + Z.of_nat 16) with (F + 120) in * by lia.
  replace (F + 120 + Z.of_nat 16) with (F + 136) in * by lia.
  clear VS VEL.

  unfold od_lowA in LOWF.
  apply (rw_cells_split_CB bsegs _ _ [] 120 _ _ [112; 8]%nat) in LOWF; [| reflexivity]. cbn [mk_CB_cells app] in LOWF.
  lazymatch type of LOWF with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: CB 32 ?j :: ?rest) =>
    apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3] 32 j rest [8; 24]%nat) in LOWF; [| reflexivity] end.
  cbn [mk_CB_cells app] in LOWF.
  repeat match type of LOWF with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac | skipn _ _ => idtac end; let j := fresh "jl" in set (j := t) in LOWF; clearbody j end.
  lazymatch type of LOWF with rw_cells _ _ _ [CB 112 ?a; CB 8 ?b; _; _; CB 8 ?c; CB 24 ?d; _; CB 72 ?e; _; _; CB 16 ?f; _; CB 40 ?g; _; CB 32 ?h; _; CB 8 ?i] =>
    change (rw_cells bsegs mA S1 (od_lowM F (od_action dz) a b c d e f g h i)) in LOWF end.
  unfold od_lowM in LOWF.

  unfold wz, OD_CUTA.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walkB1 xra usp S1 F lo (od_action dz) gp (Z_to_bv 64 0x656e70) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 (Z_to_bv 64 A) xs6 xs9 xt3 xt4 xt5 xt6
             _ _ _ _ _ _ _ jq jl jl0 jl1 jl2 j176 j264 j288 j336 j376 jq0 xF xfc mA
             FPOS FLO SLO FD0 FSEP ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) LOWF PA0 SHp MI0). }
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & PA01 & SHp1). cbn [map repeat] in SHp1.
  apply evt_done. unfold oa_WB1 in MU1.
  assert (FP1 : fp_ok RT ΣA lo [(F + 96, F + 97); (F / 8 + 2147450892, F / 8 + 2147450899)]).
  { repeat apply Forall_cons; [| | apply Forall_nil]; cbn [fst snd].
    - right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. lia.
    - right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. subst S. lia. }
  pose proof (art_of_munch RT AF ΣA mA m1 lo _ ART0 LOWA FP1 MU1 WM1) as ART1.
  assert (AG01 : agree_on (fun x => ~ (F + 96 <= x < F + 97) /\ ~ (F / 8 + 2147450892 <= x < F / 8 + 2147450899)) mA m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x (H2 & H3'). cbn [outside]. repeat split; assumption. }
  assert (ST1 : stk bsegs m1 lo S1).
  { apply (stk_agree bsegs mA m1 _ _ ST0); [| exact WM1]. eapply agree_sub; [exact AG01|]. intros x Hx. cbv beta in *. subst S. ul. }
  assert (STp1 : stk bsegs m1 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs mA m1 _ _ STp); [| exact WM1]. eapply agree_sub; [exact AG01|]. intros x Hx. cbv beta in *. subst S. ul. }
  assert (LIB1 : LIB m1).
  { apply (LIB_agreeB mA m1 LIB0). eapply agree_sub; [exact AG01|]. intros x Hx. pose proof (proj2 (oa_lib_fp_static x Hx)). cbv beta. subst S. ul. }
  assert (CP1 : rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 m1).
  { apply (pres_fp_step _ _ _ _ _ _ CP0). intros a Ha. apply MU1. cbn [outside]. pose proof (CALLER _ Ha) as (C1 & C2 & C3 & _).
    split; [clear - C1; lia|]. split; [subst S; clear - C2; lia| exact I]. }
  assert (VR1 : vrepA m1 (F + 32) A cap size els).
  { apply (oa_vrepA_agree mA m1 _ _ _ _ _ VR). eapply agree_sub; [exact AG01|]. intros x Hx. cbv beta.
    destruct Hx as [Hx|Hx]; [subst S; clear - Hx FLO S1R LOR FSEP; ul| subst S; clear - Hx AV1 FAV SAV LOWA S1R LOR; ul]. }
  assert (SHZ1 : shz m1 A 16).
  { eapply shz_sub; [exact (shz_live RT AF ΣA m1 A (16 * size) ART1 INV ltac:(clear - A16; Z.div_mod_to_equations; lia))| lia|].
    replace (16 * size / 8) with (2 * size) by (clear; Z.div_mod_to_equations; lia). lia. }
  clear ST0 STp LIB0 CP0 VR SHZA ART0 MI0 PA0 SHp FP1.
  unfold fa_saved in SAVED.
  rt_transport_with mA m1 AG01 WM1 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?S0BL in Hx; cbv beta;
      first [ subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
            | destruct S0C as [E|(p & k & _ & P1 & P2 & P3 & P4 & P5)]; [clear - Hx E; lia| subst S; clear - Hx P1 P2 P3 P4 P5 S1R LOR; ul] ]).
  clear AG01 MU1.

  pose proof (rw_cells_bytes_at bsegs m1 _ _ SHp1) as SHpB. cbn [cells_bytes cbytes app] in SHpB.
  assert (SHP13 : bytes_at bsegs m1 (shad (F + 104)) (repeat z8 2)).
  { replace (shad (F + 104)) with (F / 8 + 2147450892 + 1) by (unfold shad, SHB; clear - F64; Z.div_mod_to_equations; lia).
    change [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
      with ([Z_to_bv 8 0] ++ ([Z_to_bv 8 0; Z_to_bv 8 0] ++ [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0])) in SHpB.
    apply bytes_at_app in SHpB. destruct SHpB as [_ X]. apply bytes_at_app in X. exact (proj1 X). }
  clear SHpB.
  pose proof (rw_cells_wr_at bsegs m1 _ _ 16 PA8 ltac:(cbn; lia)) as PW8.
  unfold lh_regs.
  eapply (aevt_memset RT RTF PMc FDO MST ΣA K) with (d := F + 104) (n := 16) (cb := Z_to_bv 8 0) (lo := lo);
    [ reflexivity | reflexivity | reflexivity | clear - FLO FPOS LOR UT; ul | clear; lia
    | | exact ART1 | exact MI1
    | unfold call_ok; rewrite EU1; split; [exact ST1|]; split; [exact LOWA|]; split; [clear - LOR S1R; ul|]; split; [clear - S1R UT; ul| clear - S32; Z.div_mod_to_equations; lia]
    | exact FRM | ].
  { unfold checked_dst. rewrite EU1. split; [| split; [| exact PW8]].
    - intros _. split.
      + apply (acc_zero_run bsegs m1 (F + 104) 2); [clear - F64; Z.div_mod_to_equations; lia| clear - FPOS; lia| exact SHP13].
      + right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear. lia.
    - intros i Hi. apply ACL0. right; left. clear - Hi. lia. }
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 FRM2 (ART2 & MI2 & WM2 & ST2) PR2 PB8.
  rewrite EU1 in ST2, PR2. rewrite (ret_pc_even 0x96bfc) by lia.
  assert (AG12 : agree_on (fun x => ((S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (p0 <= x < p0 + len0))
                                     /\ ~ (F + 104 <= x < F + 104 + 16)) m1 m2)
    by (intros a [H1 H2]; exact (PR2 a (ACL0 _ H1) H2)).
  assert (STp2 : stk bsegs m2 (S1 + 440) (usp - 104)).
  { apply (stk_agree bsegs m1 m2 _ _ STp1); [| exact WM2]. eapply agree_sub; [exact AG12|]. intros x Hx. cbv beta in *. clear - Hx FLO S1R LOR. ul. }
  assert (LIB2 : LIB m2).
  { apply (LIB_agreeB m1 m2 LIB1). intros a Ha. destruct (oa_lib_fp_static _ Ha) as [CS R]. apply PR2; [right; left; exact CS|]. clear - R FSG. ul. }
  assert (CP2 : rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 m2).
  { apply (pres_fp_step _ _ _ _ _ _ CP1). intros a Ha. pose proof (CALLER _ Ha) as (C1 & _ & _ & C4). apply PR2; [exact C4| clear - C1; lia]. }
  assert (VR2 : vrepA m2 (F + 32) A cap size els).
  { apply (oa_vrepA_agree m1 m2 _ _ _ _ _ VR1). eapply agree_sub; [exact AG12|]. intros x Hx. cbv beta.
    destruct Hx as [Hx|Hx]; [split; [right; left; clear - Hx; lia| clear - Hx; lia]| split; [do 3 right; left; exact Hx| clear - Hx FAV; lia]]. }
  pose proof (wr_at_transport bsegs m1 m2 _ _ PW8 WM2) as PW82.
  pose proof (zero16_cells m2 (F + 104) PB8 PW82) as PA82.
  clear STp1 LIB1 CP1 VR1 ST1 ART1 MI1 PA8 PW8 PW82 PB8 SHZ1 SHP13.
  rt_transport_with m1 m2 AG12 WM2 ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?S0BL in Hx; cbv beta;
      split; [subst S; clear - Hx S1R; lia| first [clear - Hx; lia | subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
                                                   | destruct S0C as [E|(p & k & _ & P1 & P2 & P3 & P4 & P5)]; [clear - Hx E; lia| clear - Hx P1 P2 P3; lia] ]]).
  clear AG12 PR2.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walkB2 (Z_to_bv 64 0x96bfc) usp S1 F lo gp (Z_to_bv 64 0x656e70) t0' t1' t2' _ a1' a2' a3' a4' a5' a6' a7' xs3 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 A) xs6 xs9
             t3' t4' t5' t6' jq2 jq3 F2 fc2 m2 FPOS FLO ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) PA24 MI2). }
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3 & PA243).
  apply evt_done.
  assert (FP3 : fp_ok RT ΣA lo [(F + 120, F + 136)]).
  { apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]. right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. lia. }
  pose proof (art_of_munch RT AF ΣA m2 m3 lo _ ART2 LOWA FP3 MU3 WM3) as ART3.
  assert (AG23 : agree_on (fun x => ~ (F + 120 <= x < F + 136)) m2 m3)
    by (apply (agree_of_munch _ _ _ _ MU3); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
  clear ART2 MI2 PA24 FP3.
  xfer_all LIB LIB_agreeB m2 m3 AG23 WM3
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?S0BL in Hx; cbv beta;
          first [ subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
                | destruct S0C as [E|(p & k & _ & P1 & P2 & P3 & P4 & P5)]; [clear - Hx E; lia| subst S; clear - Hx P1 P2 P3 P4 P5 S1R LOR; ul] ])
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [clear - Hx; lia| clear - Hx FAV; lia])
    ltac:(intros a Ha; apply MU3; cbn [outside]; pose proof (proj2 (oa_lib_fp_static _ Ha)) as R; split; [clear - R FSG; ul| exact I])
    ltac:(intros a Ha; apply MU3; cbn [outside]; pose proof (CALLER _ Ha) as (C1 & _); split; [clear - C1; lia| exact I]).
  clear AG23 MU3.

  pose proof (rw_cells_bytes_at bsegs m3 _ _ SHp1) as SHpB. cbn [cells_bytes cbytes app] in SHpB.
  assert (SHP17 : bytes_at bsegs m3 (shad (F + 136)) (repeat z8 2)).
  { replace (shad (F + 136)) with (F / 8 + 2147450892 + 5) by (unfold shad, SHB; clear - F64; Z.div_mod_to_equations; lia).
    change [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
      with ([Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ++ ([Z_to_bv 8 0; Z_to_bv 8 0] ++ [])) in SHpB.
    apply bytes_at_app in SHpB. destruct SHpB as [_ X]. apply bytes_at_app in X. exact (proj1 X). }
  clear SHpB.
  pose proof (rw_cells_wr_at bsegs m3 _ _ 16 PA40 ltac:(cbn; lia)) as PW40.
  unfold lh_regs.
  eapply (aevt_memset RT RTF PMc FDO MST ΣA K) with (d := F + 136) (n := 16) (cb := Z_to_bv 8 0) (lo := lo);
    [ reflexivity | reflexivity | reflexivity | clear - FLO FPOS LOR UT; ul | clear; lia
    | | exact ART3 | exact MI3
    | unfold call_ok; rewrite EU1; split; [exact ST2|]; split; [exact LOWA|]; split; [clear - LOR S1R; ul|]; split; [clear - S1R UT; ul| clear - S32; Z.div_mod_to_equations; lia]
    | exact FRM2 | ].
  { unfold checked_dst. rewrite EU1. split; [| split; [| exact PW40]].
    - intros _. split.
      + apply (acc_zero_run bsegs m3 (F + 136) 2); [clear - F64; Z.div_mod_to_equations; lia| clear - FPOS; lia| exact SHP17].
      + right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. clear. lia.
    - intros i Hi. apply ACL0. right; left. clear - Hi. lia. }
  intros u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F4 fc4 m4 FRM4 (ART4 & MI4 & WM4 & ST4) PR4 PB40.
  rewrite EU1 in ST4, PR4. rewrite (ret_pc_even 0x96c24) by lia.
  assert (AG34 : agree_on (fun x => ((S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (p0 <= x < p0 + len0))
                                     /\ ~ (F + 136 <= x < F + 136 + 16)) m3 m4)
    by (intros a [H1 H2]; exact (PR4 a (ACL0 _ H1) H2)).
  pose proof (wr_at_transport bsegs m3 m4 _ _ PW40 WM4) as PW404.
  pose proof (zero16_cells m4 (F + 136) PB40 PW404) as PA404.
  clear ST2 ART3 MI3 PA40 PW40 PW404 PB40 SHP17.
  xfer_all LIB LIB_agreeB m3 m4 AG34 WM4
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?S0BL in Hx; cbv beta;
          split; [subst S; clear - Hx S1R; lia| first [clear - Hx; lia | subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
                                                       | destruct S0C as [E|(p & k & _ & P1 & P2 & P3 & P4 & P5)]; [clear - Hx E; lia| clear - Hx P1 P2 P3; lia] ]])
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [split; [right; left; clear - Hx; lia| clear - Hx; lia]| split; [do 3 right; left; exact Hx| clear - Hx FAV; lia]])
    ltac:(intros a Ha; destruct (oa_lib_fp_static _ Ha) as [CS R]; apply PR4; [right; left; exact CS| clear - R FSG; ul])
    ltac:(intros a Ha; pose proof (CALLER _ Ha) as (C1 & _ & _ & C4); apply PR4; [exact C4| clear - C1; lia]).
  clear AG34 PR4.

  assert (SHZ4 : shz m4 A 16).
  { eapply shz_sub; [exact (shz_live RT AF ΣA m4 A (16 * size) ART4 INV ltac:(clear - A16; Z.div_mod_to_equations; lia))| lia|].
    replace (16 * size / 8) with (2 * size) by (clear; Z.div_mod_to_equations; lia). lia. }
  assert (VE4 : rw_cells bsegs m4 A [C8 (Z_to_bv 64 p0); C8 (Z_to_bv 64 len0)]).
  { destruct VR2 as (_ & _ & _ & _ & _ & _ & [(B1 & _)|(_ & _ & _ & VEL)]); [lia|]. rewrite EELS in VEL. cbn [velts fst snd] in VEL.
    lazymatch type of VEL with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in VEL end.
    apply Sj_stage1_kit.rw_cells_app in VEL. exact (proj1 VEL). }
  assert (A8 : A mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
  assert (DZL : zlength (od_doc dz) = if od_copied dz then zlength (strip_bom s0) else 0).
  { unfold od_doc. fold s0. destruct (od_copied dz); reflexivity. }
  assert (CPD : od_copied dz = (len0 <=? SJ_PADMAX)) by reflexivity.
  unfold SJ_PADMAX in CPD.

  assert (FPU : fp_ok RT ΣA lo [(S1 + 112, S1 + 144); (F + 136, F + 144); (F / 8 + 2147450904, F / 8 + 2147450912)]).
  { repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd].
    - left. ul.
    - right; right; left. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. lia.
    - right; right; right. exists F, 3%nat. split; [exact INF|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. subst S. lia. }
  destruct (Z_le_gt_dec len0 0xfffc0) as [LLE|LGT].
  2:{
      apply (aevt_evt RT AF PMc MST).
      eapply evt_cut.
      { exact (od_walkB3n (Z_to_bv 64 0x96c24) usp S1 F A p0 len0 gp (Z_to_bv 64 0x656e70) u0 u1 u2 _ b1 b2 b3 b4 b5 b6 b7
                 (Z_to_bv 64 (F + 96)) xs3 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 (F + 136)) xs9 u3 u4 u5 u6 F4 fc4 m4
                 APOS ltac:(clear - VAT CAP1; lia) A8 ltac:(lia) SHZ4 VE4 MI4). }
      cbv beta. intros ms5 (k0 & k1 & ->).
      eapply evt_cut.
      { exact (od_walkBU (Z_to_bv 64 0x96c24) usp S1 F lo (od_action dz) gp (Z_to_bv 64 0x656e70) u0 u1 u2 k0 k1 b2 b3 b4 b5 b6 b7
                 (Z_to_bv 64 len0) xs3 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 A) xs9 u3 u4 u5 u6
                 _ _ _ _ _ _ _ _ jl jl0 jl1 jl2 j176 j264 j288 j336 j376 _ _ F4 fc4 m4 FPOS FLO SLO FD0 FSEP ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) LOWF PA404 SHd MI4). }
      cbv beta. intros ms6 (m6 & k2 & k3 & -> & MU6 & WM6 & MI6 & LOW6 & PA406 & SHd6).
      apply evt_done. unfold oa_WBU in MU6.
      pose proof (art_of_munch RT AF ΣA m4 m6 lo _ ART4 LOWA FPU MU6 WM6) as ART6.
      assert (AG46 : agree_on (fun x => ~ (S1 + 112 <= x < S1 + 144) /\ ~ (F + 136 <= x < F + 144) /\ ~ (F / 8 + 2147450904 <= x < F / 8 + 2147450912)) m4 m6).
      { apply (agree_of_munch _ _ _ _ MU6). intros x (H1 & H2 & H3'). cbn [outside]. repeat split; assumption. }
      clear ART4 MI4 SHd FPU SHZ4 VE4 LOWF PA404.
      xfer_all LIB LIB_agreeB m4 m6 AG46 WM6
        ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?S0BL in Hx; cbv beta;
              first [ subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul
                    | destruct S0C as [E|(p & k & _ & P1 & P2 & P3 & P4 & P5)]; [clear - Hx E; lia| subst S; clear - Hx P1 P2 P3 P4 P5 S1R LOR; ul] ])
        ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [subst S; clear - Hx FSEP FLO S1R LOR FPOS; ul| subst S; clear - Hx SAV FAV AV1 LOWA S1R LOR; ul])
        ltac:(intros a Ha; apply MU6; cbn [outside]; pose proof (proj2 (oa_lib_fp_static _ Ha)) as R;
              split; [clear - R S1R LOWA LOR SP0R; ul|]; split; [clear - R FSG; ul|]; split; [subst S; clear - R SHB0; ul| exact I])
        ltac:(intros a Ha; apply MU6; cbn [outside]; pose proof (CALLER _ Ha) as (C1 & C2 & C3 & _);
              split; [clear - C3 S1R LOR; ul|]; split; [clear - C1; lia|]; split; [subst S; clear - C2; lia| exact I]).
      assert (ECP : od_copied dz = false) by (rewrite CPD; apply Z.leb_gt; lia).
      assert (EL : 0 = zlength (od_doc dz)) by (rewrite DZL, ECP; reflexivity).
      unfold lh_regs.
      lazymatch goal with |- aevt _ _ (MS (mkR ?ra ?sp ?gp ?tp ?t0 ?t1 ?t2 ?s0 ?s1 ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 _ ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?t3 ?t4 ?t5 ?t6)
                                            ?FF ?pc ?fc ?e ?m ?r) =>
        cut (forall L, L = zlength (od_doc dz) ->
               aevt ΣA K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) FF pc fc e m r));
          [ intros G; exact (G 0 EL) | intros L -> ] end.
      apply (KB ΣA S1 F A cap size 0 0 els _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F4 fc4 m6 FRM4).
      apply (od_cutB_intro Σ0 ΣA m0 m6 usp S1 F lo dz A cap size 0 0 els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
               jl jl2 j176 j264 j288 j336 j376 j384 j432 h0 h8 jd jq0 U16 UT S32 S1R LOW LOR F64 FPOS FRS0 LVPOS LVB CR0 ART6 MI6 ST4 FRS SP0 HI STp2 SAVED HDR VR2 SZ1 WRS DOC LIB2 CP2 DZ);
        [ rewrite ECP; exact LV | rewrite ECP; split; reflexivity
        | pose proof (mcost_nonneg (2^20) ltac:(lia)) as X; unfold OD_PAD_COST; clear - CR X; lia
        | rewrite ECP; exact LOW6 | exact PA01 | exact PA82 | exact PA243 | rewrite <- EL; exact PA406 | exact SHa | exact SHp1 | exact SHb | exact SHd6 | exact SHc ]. }

  assert (ECP : od_copied dz = true) by (rewrite CPD; apply Z.leb_le; lia).
  pose proof (od_s0_ok dz (proj1 DZ)) as S0OK. fold s0 in S0OK.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walkB3c (Z_to_bv 64 0x96c24) usp S1 F A p0 len0 gp (Z_to_bv 64 0x656e70) u0 u1 u2 _ b1 b2 b3 b4 b5 b6 b7
             (Z_to_bv 64 (F + 96)) xs3 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 (F + 136)) xs9 u3 u4 u5 u6 F4 fc4 m4
             APOS ltac:(clear - VAT CAP1; lia) A8 ltac:(lia) SHZ4 VE4 (AFC ΣA m4 ART4) MI4). }
  cbv beta. intros ms5 <-. apply evt_done.
  assert (LVLEN : Z.of_nat (length (rt_live RT ΣA)) < LIVE_MAX).
  { rewrite LV, length_app. unfold vblockA. destruct (cap =? 0); [cbn [length]|]; [unfold FUZZ_LIVE in LVB; lia|].
    pose proof (ann_block_length A (16 * cap) (16 * size)). unfold FUZZ_LIVE in LVB. lia. }
  assert (MC : mcost (len0 + 64) <= OD_PAD_COST).
  { unfold OD_PAD_COST. pose proof (mcost_le (len0 + 64) ltac:(lia)) as X. assert (E : mcost (2^20) = 2 * 2^20 + 16384 + 2097152) by (vm_compute; reflexivity). rewrite E. lia. }
  assert (PADC : OD_VEC_COST + OD_PAD_COST <= FUZZ_COST) by (unfold OD_VEC_COST, OD_PAD_COST, FUZZ_COST; vm_compute; discriminate).
  unfold lh_regs.
  eapply (aevt_newarr RT PMc FDO MST NEWA ΣA K) with (n := len0 + 64) (lo := lo);
    rewrite ?EU1;
    [ clear - LEN0 LLE; lia | reflexivity | reflexivity | exact LVLEN | clear - MC PADC CR CR0; lia | exact ART4 | exact MI4 | exact ST4 | exact LOWA
    | clear - LOR S1R; ul | clear - S1R UT; ul | clear - S32; Z.div_mod_to_equations; lia | exact FRM4 | ].
  intros ΣN COPY v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F5 fc5 m5 FRM5 (ART5 & MI5 & WM5 & ST5) PR5 WRC ACC LVN FRSN SPN CRN CPOS C16 CTOP.
  rewrite ?EU1 in ST5, PR5. rewrite (ret_pc_even 0x96c84) by lia.
  assert (INFN : In (F, 3%nat) (rt_frames RT ΣN)) by (rewrite FRSN; exact INF).
  assert (INC : In (COPY, len0 + 64) (rt_live RT ΣN)) by (rewrite LVN; left; reflexivity).
  assert (INVN : In (A, 16 * size) (rt_live RT ΣN)) by (rewrite LVN; right; exact INV).
  assert (LOWN : rt_sp0 RT ΣN - STACK_WIN <= lo) by (rewrite SPN; exact LOWA).
  pose proof (af_frames_range RT AF ΣN m5 F 3%nat ART5 INFN) as (_ & _ & _ & FLVN). change (fs_size 3) with 512 in FLVN.
  pose proof (af_fshadow_apart RT AF ΣN m5 F 3 ART5 INFN) as (FSLN & _). change (fs_size 3) with 512 in FSLN. rewrite SHF in FSLN. unfold shad, SHB in FSLN. fold S in FSLN.
  pose proof (FLVN COPY (len0 + 64) INC) as CF. pose proof (FSLN COPY (len0 + 64) INC) as CS.
  pose proof (af_live_range RT AF ΣN m5 COPY (len0 + 64) ART5 INC) as (_ & CL & _).
  assert (CLO : COPY + (len0 + 64) <= lo) by (clear - CL LOWN; lia).
  pose proof (af_live_disj RT AF ΣN m5 COPY (len0 + 64) A (16 * size) [] (rt_live RT ΣA) ART5 LVN INV) as CA.
  assert (S0N : len0 = 0 \/ exists p k, In (p, k) (rt_live RT ΣN) /\ p <= p0 /\ p0 + len0 <= p + k /\ (F + 512 <= p \/ p + k <= F) /\ (p + k <= S \/ S + 64 <= p) /\ p + k <= lo
                                  /\ (COPY + (len0 + 64) <= p \/ p + k <= COPY)).
  { destruct S0C as [E|(p & k & Hin & P1 & P2 & P3 & P4 & P5)]; [left; exact E| right]. exists p, k.
    split; [rewrite LVN; right; exact Hin|]. repeat (split; [assumption|]).
    exact (af_live_disj RT AF ΣN m5 COPY (len0 + 64) p k [] (rt_live RT ΣA) ART5 LVN Hin). }
  assert (ACLN : forall x, (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (p0 <= x < p0 + len0) \/ (COPY <= x < COPY + (len0 + 64)) ->
                   aclient (rt_live RT ΣN) (rt_frames RT ΣN) S1 x).
  { intros x [H|[H|[H|[H|[H|H]]]]].
    - left. ul.
    - right; right; right; left. exists F, 3%nat. change (fs_size 3) with 512. split; [exact INFN| lia].
    - right; right; right; right. exists F, 3%nat. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. split; [exact INFN| lia].
    - right; right; left. exists A, (16 * size). split; [exact INVN| lia].
    - destruct S0N as [E|(p & k & Hin & P1 & P2 & _)]; [lia|]. right; right; left. exists p, k. split; [exact Hin| lia].
    - right; right; left. exists COPY, (len0 + 64). split; [exact INC| lia]. }
  assert (CALLN : forall x, aclient (rt_live RT Σ0) [] usp x -> aclient (rt_live RT ΣN) (rt_frames RT ΣN) S1 x /\ ~ (COPY <= x < COPY + (len0 + 64))).
  { intros x Hx. pose proof (CALLER _ Hx) as (_ & _ & _ & C4). split.
    - rewrite FRSN. apply (aclient_mono _ _ _ _ _ _ _ C4); [intros e He; rewrite LVN; right; exact He| auto| lia].
    - apply (fresh_apart_l RT AF ΣN m5 [(COPY, len0 + 64)] (rt_live RT ΣA) COPY (len0 + 64) S1 x ART5 LVN ltac:(left; reflexivity) ltac:(clear - LOWN LOR S1R; ul)).
      rewrite FRSN. exact C4. }
  assert (AG45 : agree_on (fun x => (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (p0 <= x < p0 + len0)) m4 m5)
    by (intros a Ha; exact (PR5 a (ACL0 _ Ha))).
  assert (FPN : fp_ok RT ΣN lo [(S1 + 112, S1 + 144); (F + 136, F + 144); (F / 8 + 2147450904, F / 8 + 2147450912)]).
  { repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd].
    - left. ul.
    - right; right; left. exists F, 3%nat. split; [exact INFN|]. change (fs_size 3) with 512. lia.
    - right; right; right. exists F, 3%nat. split; [exact INFN|]. change (fs_size 3) with 512. rewrite SHF. unfold shad, SHB. fold S. subst S. lia. }
  clear ST4 ART4 MI4 SHZ4 VE4 FPU.
  xfer_all LIB LIB_agreeB m4 m5 AG45 WM5
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?S0BL in Hx; cbv beta; subst S; clear - Hx S1R; lia)
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [right; left; clear - Hx; lia| do 3 right; left; exact Hx])
    ltac:(intros a Ha; destruct (oa_lib_fp_static _ Ha) as [CS' R]; apply PR5; right; left; exact CS')
    ltac:(intros a Ha; pose proof (CALLER _ Ha) as (_ & _ & _ & C4); apply PR5; exact C4).
  clear AG45 PR5 ACL0 S0C.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut.
  { exact (od_walkB4 (Z_to_bv 64 0x96c84) usp S1 F COPY len0 gp (Z_to_bv 64 0x656e70) v0 v1 v2 e1 e2 e3 e4 e5 e6 e7
             xs3 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 (len0 + 64)) (Z_to_bv 64 (F + 136)) (Z_to_bv 64 p0) v3 v4 v5 v6 F5 fc5 m5
             CPOS ltac:(clear - CLO LOR UT; ul) ltac:(lia)). }
  cbv beta. intros ms6 <-. apply evt_done. unfold lh_regs.
  eapply (aevt_memset RT RTF PMc FDO MST ΣN K) with (d := COPY + len0) (n := 64) (cb := Z_to_bv 8 0) (lo := lo);
    [ reflexivity | reflexivity | reflexivity | clear - CPOS CLO LOR UT LEN0; ul | clear; lia
    | apply (checked_dst_live RT AF ΣN m5 _ COPY (len0 + 64)); [exact ART5| exact INC| clear - LEN0; lia| clear; lia| clear; lia]
    | exact ART5 | exact MI5
    | unfold call_ok; rewrite EU1; split; [exact ST5|]; split; [exact LOWN|]; split; [clear - LOR S1R; ul|]; split; [clear - S1R UT; ul| clear - S32; Z.div_mod_to_equations; lia]
    | exact FRM5 | ].
  intros y0 y1 y2 k1 k2 k3 k4 k5 k6 k7 y3 y4 y5 y6 F6 fc6 m6 FRM6 (ART6 & MI6 & WM6 & ST6) PR6 PB6.
  rewrite EU1 in ST6, PR6. rewrite (ret_pc_even 0x96ca4) by lia. change (Z.to_nat 64) with 64%nat in PB6.
  assert (AG56 : agree_on (fun x => (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (p0 <= x < p0 + len0)) m5 m6).
  { intros a Ha. apply (PR6 a); [apply ACLN; clear - Ha; tauto|].
    destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H CLO LOR S1R LEN0; ul| clear - H CF LEN0; lia| clear - H CS LEN0; lia| clear - H CA LEN0; lia|].
    destruct S0N as [E|(p & k & _ & P1 & P2 & _ & _ & _ & P6)]; [clear - H E; lia| clear - H P1 P2 P6 LEN0; lia]. }
  clear ST5 ART5 MI5.
  xfer_all LIB LIB_agreeB m5 m6 AG56 WM6
    ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?S0BL in Hx; cbv beta; subst S; clear - Hx S1R; lia)
    ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [right; left; clear - Hx; lia| do 3 right; left; exact Hx])
    ltac:(intros a Ha; destruct (oa_lib_fp_static _ Ha) as [CS' R]; apply PR6; [right; left; exact CS'|];
          pose proof (af_live_range RT AF ΣN m6 COPY (len0 + 64) ART6 INC) as (_ & _ & [X|X]); [clear - R X LEN0 CPOS; lia| clear - R X LEN0; ul])
    ltac:(intros a Ha; destruct (CALLN _ Ha) as (C1 & C2); apply PR6; [exact C1| clear - C2 LEN0; lia]).
  clear AG56 PR6.

  assert (FINB : forall (mx : mem) (BUF L : Z) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 ys6 ys9 yt3 yt4 yt5 yt6 : word) yF yfc,
            frm0 yfc -> ART RT ΣN mx -> mem_inv bsegs mx -> stk bsegs mx lo S1 ->
            rw_cells bsegs mx (S1 + 384) [CB 48 j384; CB 8 j432] -> stk bsegs mx (S1 + 440) (usp - 104) ->
            rw_cells bsegs mx (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
            rw_cells bsegs mx F [CB 8 h0; CB 24 h8] -> vrepA mx (F + 32) A cap size els -> wr_at bsegs mx S 64 ->
            rw_cells bsegs mx (F + 192) [CB 64 jd] -> LIB mx -> rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 mx ->
            rw_cells bsegs mx S1 (od_lowB F (od_action dz) 0 COPY jl jl2 j176 j264 j288 j336 j376) ->
            rw_cells bsegs mx (F + 96) [C1 (Z_to_bv 8 0); CB 7 jq0] ->
            rw_cells bsegs mx (F + 104) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
            rw_cells bsegs mx (F + 120) [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 1024)] ->
            rw_cells bsegs mx (F + 136) [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 0)] ->
            rw_cells bsegs mx S (map (fun z => C1 (Z_to_bv 8 z)) [0xf1; 0xf1; 0xf1; 0xf1; 0; 0; 0; 0xf2; 0xf2; 0xf2; 0xf2; 0xf2]) ->
            rw_cells bsegs mx (F / 8 + 2147450892) (map C1 (repeat (Z_to_bv 8 0) 7)) ->
            rw_cells bsegs mx (F / 8 + 2147450899) (map (fun z => C1 (Z_to_bv 8 z)) [0xf2; 0xf2; 0xf2; 0xf2; 0xf2]) ->
            rw_cells bsegs mx (F / 8 + 2147450904) (map C1 (repeat (Z_to_bv 8 0) 8)) ->
            rw_cells bsegs mx (F / 8 + 2147450912) (map (fun z => C1 (Z_to_bv 8 z)) [0xf3; 0xf3; 0xf3; 0xf3]) ->
            COPY <= BUF <= COPY + 3 -> BUF - COPY + L = len0 -> L = zlength (strip_bom s0) -> bytes_at bsegs mx BUF (padded_bytes (strip_bom s0)) ->
            aevt ΣN K (lh_regs 0x96dac yra S1 gp (Z_to_bv 64 0x656e70) yt0 yt1 yt2 usp ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                         (Z_to_bv 64 L) ys3 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 BUF) ys6 F ys9 yt3 yt4 yt5 yt6 yF yfc mx)).
  { intros mx BUF L yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 ys6 ys9 yt3 yt4 yt5 yt6 yF yfc
      FRMx ARTx MIx STx HIx STpx SAVx HDRx VRx WRSx DOCx LIBx CPx LOWx P0x P8x P24x P40x SHax SHpx SHbx SHdx SHcx BR BL LE PADx.
    assert (EDOC : od_doc dz = strip_bom s0) by (unfold od_doc; fold s0; rewrite ECP; reflexivity).
    unfold lh_regs. rewrite LE in P40x |- *. rewrite <- EDOC in P40x |- *.
    apply (KB ΣN S1 F A cap size COPY BUF els _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yF yfc mx FRMx).
    apply (od_cutB_intro Σ0 ΣN m0 mx usp S1 F lo dz A cap size COPY BUF els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11
             jl jl2 j176 j264 j288 j336 j376 j384 j432 h0 h8 jd jq0 U16 UT S32 S1R LOW LOR F64 FPOS FRS0 LVPOS LVB CR0 ARTx MIx STx
             ltac:(rewrite FRSN; exact FRS) ltac:(rewrite SPN; exact SP0) HIx STpx SAVx HDRx VRx SZ1 WRSx DOCx LIBx CPx DZ);
      [ rewrite ECP, LVN, LV; reflexivity
      | rewrite ECP, EDOC; split; [exact CPOS|]; split; [exact C16|]; split; [exact BR|]; split; [rewrite <- LE; exact BL| exact PADx]
      | rewrite CRN; clear - MC CR; lia
      | rewrite ECP; exact LOWx | exact P0x | exact P8x | exact P24x | exact P40x | exact SHax | exact SHpx | exact SHbx | exact SHdx | exact SHcx ]. }
  clear KB.

  assert (SHORT : forall (m7 : mem) (zra za0 za1 za2 za3 za4 za5 za6 za7 z0 z1 z2 z3 z4 z5 z6 : word) F7 fc7,
            len0 < 3 -> frm0 fc7 -> ART RT ΣN m7 -> mem_inv bsegs m7 -> stk bsegs m7 lo S1 ->
            rw_cells bsegs m7 (S1 + 384) [CB 48 j384; CB 8 j432] -> stk bsegs m7 (S1 + 440) (usp - 104) ->
            rw_cells bsegs m7 (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11) ->
            rw_cells bsegs m7 F [CB 8 h0; CB 24 h8] -> vrepA m7 (F + 32) A cap size els -> wr_at bsegs m7 S 64 ->
            rw_cells bsegs m7 (F + 192) [CB 64 jd] -> LIB m7 -> rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 m7 ->
            rw_cells bsegs m7 S1 (od_lowM F (od_action dz) jl jl0 jl1 jl2 j176 j264 j288 j336 j376) ->
            rw_cells bsegs m7 (F + 96) [C1 (Z_to_bv 8 0); CB 7 jq0] ->
            rw_cells bsegs m7 (F + 104) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
            rw_cells bsegs m7 (F + 120) [C8 (Z_to_bv 64 0xffffffff); C8 (Z_to_bv 64 1024)] ->
            rw_cells bsegs m7 (F + 136) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
            rw_cells bsegs m7 S (map (fun z => C1 (Z_to_bv 8 z)) [0xf1; 0xf1; 0xf1; 0xf1; 0; 0; 0; 0xf2; 0xf2; 0xf2; 0xf2; 0xf2]) ->
            rw_cells bsegs m7 (F / 8 + 2147450892) (map C1 (repeat (Z_to_bv 8 0) 7)) ->
            rw_cells bsegs m7 (F / 8 + 2147450899) (map (fun z => C1 (Z_to_bv 8 z)) [0xf2; 0xf2; 0xf2; 0xf2; 0xf2]) ->
            rw_cells bsegs m7 (F / 8 + 2147450904) (map (fun z => C1 (Z_to_bv 8 z)) [0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8]) ->
            rw_cells bsegs m7 (F / 8 + 2147450912) (map (fun z => C1 (Z_to_bv 8 z)) [0xf3; 0xf3; 0xf3; 0xf3]) ->
            bytes_at bsegs m7 COPY (padded_bytes s0) ->
            aevt ΣN K (lh_regs 0x96cb8 zra S1 gp (Z_to_bv 64 0x656e70) z0 z1 z2 usp za0 za1 za2 za3 za4 za5 za6 za7
                         (Z_to_bv 64 len0) (Z_to_bv 64 COPY) (Z_to_bv 64 (F + 104)) (Z_to_bv 64 (len0 + 64)) (Z_to_bv 64 (F + 136)) F (Z_to_bv 64 p0)
                         z3 z4 z5 z6 F7 fc7 m7)).
  { intros m7 zra za0 za1 za2 za3 za4 za5 za6 za7 z0 z1 z2 z3 z4 z5 z6 F7 fc7
      L3 FRM7 ART7 MI7 ST7 HI7 STp7 SAV7 HDR7 VR7 WRS7 DOC7 LIB7 CP7 LOW7 P07 P87 P247 P407 SHa7 SHp7 SHb7 SHd7 SHc7 PAD7.
    cbn [map repeat] in SHa7, SHp7, SHb7, SHd7, SHc7.
    assert (PADL : Z.of_nat (length (padded_bytes s0)) = len0 + 64).
    { unfold padded_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, S0BL. reflexivity. }
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { exact (od_walkB6s zra usp S1 F lo (od_action dz) COPY len0 gp (Z_to_bv 64 0x656e70) z0 z1 z2 za0 za1 za2 za3 za4 za5 za6 za7 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 p0)
               z3 z4 z5 z6 _ _ _ _ _ _ _ _ jl jl0 jl1 jl2 j176 j264 j288 j336 j376 _ _ F7 fc7 m7
               FPOS FLO SLO FD0 FSEP ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(clear - LEN0 L3; lia) ltac:(clear - CPOS CLO LOR UT LEN0; ul) LOW7 P407 SHd7 MI7). }
    cbv beta. intros ms8 (m8 & g0 & g1 & -> & MU8 & WM8 & MI8 & LOW8 & P408 & SHd8).
    apply evt_done. unfold oa_WBU in MU8.
    pose proof (art_of_munch RT AF ΣN m7 m8 lo _ ART7 LOWN FPN MU8 WM8) as ART8.
    assert (AG78 : agree_on (fun x => ~ (S1 + 112 <= x < S1 + 144) /\ ~ (F + 136 <= x < F + 144) /\ ~ (F / 8 + 2147450904 <= x < F / 8 + 2147450912)) m7 m8).
    { apply (agree_of_munch _ _ _ _ MU8). intros x (H1 & H2 & H3'). cbn [outside]. repeat split; assumption. }
    clear ART7 MI7 SHd7 LOW7 P407.
    xfer_all LIB LIB_agreeB m7 m8 AG78 WM8
      ltac:(intros x Hx; cbn [cells_size csize Nat.add length repeat] in Hx; rewrite ?PADL in Hx; cbv beta;
            first [ subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul | subst S; clear - Hx CS CF CLO S1R LOR LEN0; ul ])
      ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [subst S; clear - Hx FSEP FLO S1R LOR FPOS; ul| subst S; clear - Hx SAV FAV AV1 LOWA S1R LOR; ul])
      ltac:(intros a Ha; apply MU8; cbn [outside]; pose proof (proj2 (oa_lib_fp_static _ Ha)) as R;
            split; [clear - R S1R LOWA LOR SP0R; ul|]; split; [clear - R FSG; ul|]; split; [subst S; clear - R SHB0; ul| exact I])
      ltac:(intros a Ha; apply MU8; cbn [outside]; pose proof (CALLER _ Ha) as (C1 & C2 & C3 & _);
            split; [clear - C3 S1R LOR; ul|]; split; [clear - C1; lia|]; split; [subst S; clear - C2; lia| exact I]).
    assert (ESB : strip_bom s0 = s0) by (apply strip_bom_short; unfold len0, zlength in L3; clear - L3; lia).
    apply (FINB m8 COPY len0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F7 fc7 FRM7 ART8 MI8 ST7 HI7 STp7 SAV7 HDR7 VR7 WRS7 DOC7 LIB7 CP7 LOW8 P07 P87 P247 P408 SHa7 SHp7 SHb7 SHd8 SHc7);
      [ clear; lia | clear; lia | rewrite ESB; reflexivity | rewrite ESB; exact PAD7 ]. }
  unfold od_shadow in *.
  destruct (Z.eq_dec len0 0) as [LZ|LNZ].
  -
    assert (S0E : s0 = []) by (subst len0; unfold zlength in LZ; destruct s0; [reflexivity| cbn [length] in LZ; lia]).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { exact (od_walkB5z (Z_to_bv 64 0x96ca4) usp S1 F len0 gp (Z_to_bv 64 0x656e70) y0 y1 y2 _ k1 k2 k3 k4 k5 k6 k7
               (Z_to_bv 64 COPY) (Z_to_bv 64 (F + 104)) (Z_to_bv 64 (len0 + 64)) (Z_to_bv 64 (F + 136)) (Z_to_bv 64 p0) y3 y4 y5 y6 F6 fc6 m6 LZ). }
    cbv beta. intros ms7 <-. apply evt_done.
    apply (SHORT m6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc6 ltac:(lia) FRM6 ART6 MI6 ST6 HI STp2 SAVED HDR VR2 WRS DOC LIB2 CP2 LOWF PA01 PA82 PA243 PA404 SHa SHp1 SHb SHd SHc).
    rewrite S0E. unfold padded_bytes, zbytes. cbn [map app length]. rewrite LZ, Z.add_0_r in PB6. exact PB6.
  -
    destruct S0N as [E|(p & k & INP & P1 & P2 & P3 & P4 & P5 & P6)]; [contradiction|].
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut.
    { exact (od_walkB5c (Z_to_bv 64 0x96ca4) usp S1 F COPY p0 len0 gp (Z_to_bv 64 0x656e70) y0 y1 y2 _ k1 k2 k3 k4 k5 k6 k7
               (Z_to_bv 64 (F + 104)) (Z_to_bv 64 (len0 + 64)) (Z_to_bv 64 (F + 136)) y3 y4 y5 y6 F6 fc6 m6 ltac:(lia)). }
    cbv beta. intros ms7 <-. apply evt_done. unfold lh_regs.
    pose proof (af_live_range RT AF ΣN m6 p k ART6 INP) as (PP0 & _ & _).
    eapply (aevt_memcpy RT RTF PMc FDO MST ΣN K) with (d := COPY) (s := p0) (bs := zbytes s0) (lo := lo);
      rewrite ?S0BL;
      [ reflexivity | reflexivity | reflexivity | clear - CPOS CLO LOR UT LEN0; ul | clear - PP0 P1 P2 P5 LOR UT LEN0; ul | clear - LEN0; lia | exact S0B
      | apply (checked_src_live RT AF ΣN m6 _ lo p k); [exact ART6| exact INP| exact P1| exact P2| exact LOWN]
      | apply (checked_dst_live RT AF ΣN m6 _ COPY (len0 + 64)); [exact ART6| exact INC| clear; lia| clear; lia| clear - LEN0; lia]
      | clear - P1 P2 P6 LEN0; lia
      | exact ART6 | exact MI6
      | unfold call_ok; rewrite EU1; split; [exact ST6|]; split; [exact LOWN|]; split; [clear - LOR S1R; ul|]; split; [clear - S1R UT; ul| clear - S32; Z.div_mod_to_equations; lia]
      | exact FRM6 | ].
    intros z0 z1 z2 c1 c2 c3 c4 c5 c6 c7 z3 z4 z5 z6 F7 fc7 m7 FRM7 (ART7 & MI7 & WM7 & ST7) PR7 PB7.
    rewrite ?EU1, ?S0BL in ST7, PR7. rewrite (ret_pc_even 0x96cb8) by lia.
    assert (AG67 : agree_on (fun x => (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (COPY + len0 <= x < COPY + len0 + 64)) m6 m7).
    { intros a Ha. apply (PR7 a); [apply ACLN; clear - Ha LEN0; lia|].
      destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H CLO LOR S1R LEN0; ul| clear - H CF LEN0; lia| clear - H CS LEN0; lia| clear - H CA LEN0; lia| clear - H; lia]. }
    clear ST6 ART6 MI6 S0B.
    xfer_all LIB LIB_agreeB m6 m7 AG67 WM7
      ltac:(intros x Hx; cbn [cells_size csize Nat.add length repeat] in Hx; cbv beta; subst S; clear - Hx S1R; lia)
      ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [right; left; clear - Hx; lia| do 3 right; left; exact Hx])
      ltac:(intros a Ha; destruct (oa_lib_fp_static _ Ha) as [CS' R]; apply PR7; [right; left; exact CS'|];
            pose proof (af_live_range RT AF ΣN m7 COPY (len0 + 64) ART7 INC) as (_ & _ & [X|X]); [clear - R X LEN0 CPOS; lia| clear - R X LEN0; ul])
      ltac:(intros a Ha; destruct (CALLN _ Ha) as (C1 & C2); apply PR7; [exact C1| clear - C2 LEN0; lia]).
    clear AG67 PR7.
    assert (PAD7 : forall mx, bytes_at bsegs mx COPY (zbytes s0) -> bytes_at bsegs mx (COPY + len0) (repeat (Z_to_bv 8 0) 64) -> bytes_at bsegs mx COPY (padded_bytes s0)).
    { intros mx B1 B2. unfold padded_bytes. apply bytes_at_app. split; [exact B1|]. rewrite S0BL. exact B2. }
    assert (LS0 : Z.of_nat (length s0) = len0) by reflexivity.
    destruct (Z_lt_ge_dec len0 3) as [L3|L3].
    +
      exact (SHORT m7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F7 fc7 L3 FRM7 ART7 MI7 ST7 HI STp2 SAVED HDR VR2 WRS DOC LIB2 CP2 LOWF PA01 PA82 PA243 PA404 SHa SHp1 SHb SHd SHc
               (PAD7 m7 PB7 PB6)).
    +
      clear SHORT.
      cbn [map] in SHd.
      assert (FPD : fp_ok RT ΣN lo [(S1 + 112, S1 + 144); (F / 8 + 2147450904, F / 8 + 2147450912)]).
      { inversion FPN as [|? ? X1 X2]. inversion X2 as [|? ? _ X3]. apply Forall_cons; [exact X1| exact X3]. }
      apply (aevt_evt RT AF PMc MST).
      eapply evt_cut.
      { exact (od_walkB6b (Z_to_bv 64 0x96cb8) usp S1 F lo (od_action dz) COPY len0 gp (Z_to_bv 64 0x656e70) z0 z1 z2 _ c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 p0)
                 z3 z4 z5 z6 _ _ _ _ _ _ _ _ jl jl0 jl1 jl2 j176 j264 j288 j336 j376 F7 fc7 m7
                 FPOS FLO SLO FD0 FSEP ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(clear - LEN0 L3; lia) ltac:(clear - CPOS CLO LOR UT LEN0; ul) LOWF SHd MI7). }
      cbv beta. intros ms8 (m8 & -> & MU8 & WM8 & MI8 & LOW8 & SHd8).
      apply evt_done. unfold oa_WB6 in MU8. unfold od_lowB in LOW8.
      pose proof (art_of_munch RT AF ΣN m7 m8 lo _ ART7 LOWN FPD MU8 WM8) as ART8.
      assert (AG78 : agree_on (fun x => ~ (S1 + 112 <= x < S1 + 144) /\ ~ (F / 8 + 2147450904 <= x < F / 8 + 2147450912)) m7 m8).
      { apply (agree_of_munch _ _ _ _ MU8). intros x (H1 & H3'). cbn [outside]. repeat split; assumption. }
      clear ART7 MI7 SHd LOWF.
      xfer_all LIB LIB_agreeB m7 m8 AG78 WM8
        ltac:(intros x Hx; cbn [cells_size csize Nat.add length repeat] in Hx; rewrite ?S0BL in Hx; cbv beta;
              first [ subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul | subst S; clear - Hx CS CF CLO S1R LOR LEN0; ul ])
        ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [subst S; clear - Hx FSEP FLO S1R LOR FPOS; ul| subst S; clear - Hx SAV FAV AV1 LOWA S1R LOR; ul])
        ltac:(intros a Ha; apply MU8; cbn [outside]; pose proof (proj2 (oa_lib_fp_static _ Ha)) as R;
              split; [clear - R S1R LOWA LOR SP0R; ul|]; split; [subst S; clear - R SHB0; ul| exact I])
        ltac:(intros a Ha; apply MU8; cbn [outside]; pose proof (CALLER _ Ha) as (C1 & C2 & C3 & _);
              split; [clear - C3 S1R LOR; ul|]; split; [subst S; clear - C2; lia| exact I]).
      clear AG78 MU8. cbn [map repeat] in SHd8.
      assert (LF3 : length (firstn 3 (zbytes s0)) = 3%nat).
      { apply firstn_length_le. unfold zbytes. rewrite length_map. clear - L3 LS0. lia. }
      assert (CPF : bytes_at bsegs m8 COPY (firstn 3 (zbytes s0))).
      { pose proof PB7 as X. rewrite <- (firstn_skipn 3 (zbytes s0)) in X. apply bytes_at_app in X. exact (proj1 X). }
      unfold lh_regs.
      eapply (aevt_memcmp ΣN K) with (p := COPY) (q := BOM_LIT) (bp := firstn 3 (zbytes s0)) (bq := BOM_BYTES) (lo := lo);
        rewrite ?LF3;
        [ reflexivity | reflexivity | reflexivity | reflexivity | clear - CPOS CLO LOR UT LEN0; ul | unfold BOM_LIT; clear; lia | clear; lia | clear; lia
        | exact CPF | exact (bom_at m8 MI8)
        | change (Z.of_nat 3) with 3; apply (checked_src_live RT AF ΣN m8 _ lo COPY (len0 + 64)); [exact ART8| exact INC| clear; lia| clear - L3; lia| exact LOWN]
        | change (Z.of_nat 3) with 3; unfold checked_src; split; [| left; unfold BOM_LIT; clear - LOW SP0R SP0; ul];
          intros _; split;
            [ apply (acc_sub bsegs m8 BOM_LIT 4 BOM_LIT 3); [| clear; lia| clear; lia]; apply (acc_lit RT AF ΣN m8 _ _ ART8); unfold ACC_LITS, BOM_LIT; repeat (first [left; reflexivity | right])
            | right; right; right; unfold BOM_LIT, SEGTOP_A; clear; lia ]
        | exact ART8 | exact MI8
        | unfold call_ok; rewrite EU1; split; [exact ST7|]; split; [exact LOWN|]; split; [clear - LOR S1R; ul|]; split; [clear - S1R UT; ul| clear - S32; Z.div_mod_to_equations; lia]
        | exact FRM7 | ].
      intros r q0 q1 q2 d1 d2 d3 d4 d5 d6 d7 q3 q4 q5 q6 F9 fc9 m9 FRM9 RQ (ART9 & MI9 & WM9 & ST9) PR9.
      rewrite ?EU1 in ST9, PR9. rewrite (ret_pc_even 0x96d88) by lia.
      assert (AG89 : agree_on (fun x => (S1 <= x < usp) \/ (F <= x < F + 504) \/ (S <= x < S + 64) \/ (A <= x < A + 16 * size) \/ (COPY <= x < COPY + (len0 + 64))) m8 m9).
      { intros a Ha. apply (PR9 a); [apply ACLN; clear - Ha; tauto| clear; lia]. }
      clear ST7 ART8 MI8 CPF.
      xfer_all LIB LIB_agreeB m8 m9 AG89 WM9
        ltac:(intros x Hx; cbn [cells_size csize Nat.add length repeat] in Hx; rewrite ?S0BL in Hx; cbv beta; subst S; clear - Hx S1R LEN0; lia)
        ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [right; left; clear - Hx; lia| do 3 right; left; exact Hx])
        ltac:(intros a Ha; destruct (oa_lib_fp_static _ Ha) as [CS' R]; apply PR9; [right; left; exact CS'| clear; lia])
        ltac:(intros a Ha; destruct (CALLN _ Ha) as (C1 & C2); apply PR9; [exact C1| clear; lia]).
      clear AG89 PR9.

      assert (FPL : fp_ok RT ΣN lo [(F + 136, F + 144)]).
      { inversion FPN as [|? ? _ X2]. inversion X2 as [|? ? X3 _]. apply Forall_cons; [exact X3| apply Forall_nil]. }
      assert (LAST : forall (mx : mem) (BUF L : Z) (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 ys9 yt3 yt4 yt5 yt6 : word) yF yfc,
                munch [(F + 136, F + 144)] m9 mx -> wmono bsegs m9 mx -> mem_inv bsegs mx ->
                rw_cells bsegs mx (F + 136) [C8 (Z_to_bv 64 L); C8 (Z_to_bv 64 0)] -> frm0 yfc ->
                COPY <= BUF <= COPY + 3 -> BUF - COPY + L = len0 -> L = zlength (strip_bom s0) ->
                (forall my, bytes_at bsegs my COPY (padded_bytes s0) -> bytes_at bsegs my BUF (padded_bytes (strip_bom s0))) ->
                aevt ΣN K (lh_regs 0x96dac yra S1 gp (Z_to_bv 64 0x656e70) yt0 yt1 yt2 usp ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                             (Z_to_bv 64 L) ys3 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 BUF) (Z_to_bv 64 (F + 136)) F ys9 yt3 yt4 yt5 yt6 yF yfc mx)).
      { intros mx BUF L yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 ys9 yt3 yt4 yt5 yt6 yF yfc MUx WMx MIx P40x FRMx BR BL LE PADx.
        pose proof (art_of_munch RT AF ΣN m9 mx lo _ ART9 LOWN FPL MUx WMx) as ARTx.
        assert (AG9x : agree_on (fun x => ~ (F + 136 <= x < F + 144)) m9 mx)
          by (apply (agree_of_munch _ _ _ _ MUx); intros x Hx; cbn [outside]; split; [exact Hx| exact I]).
        pose proof (PAD7 m9 PB7 PB6) as PADB.
        assert (PADL : Z.of_nat (length (padded_bytes s0)) = len0 + 64).
        { unfold padded_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, S0BL. reflexivity. }
        clear ART9 MI9 PA404 PB7 PB6.
        xfer_all LIB LIB_agreeB m9 mx AG9x WMx
          ltac:(intros x Hx; cbn [cells_size csize Nat.add length repeat] in Hx; rewrite ?PADL in Hx; cbv beta;
                first [ subst S; clear - Hx FLO SLO FSEP S1R LOR FPOS; ul | subst S; clear - Hx CS CF CLO S1R LOR LEN0; ul ])
          ltac:(intros x Hx; cbv beta; destruct Hx as [Hx|Hx]; [clear - Hx; lia| clear - Hx FAV; lia])
          ltac:(intros a Ha; apply MUx; cbn [outside]; pose proof (proj2 (oa_lib_fp_static _ Ha)) as R; split; [clear - R FSG; ul| exact I])
          ltac:(intros a Ha; apply MUx; cbn [outside]; pose proof (CALLER _ Ha) as (C1 & _); split; [clear - C1; lia| exact I]).
        exact (FINB mx BUF L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ yF yfc FRMx ARTx MIx ST9 HI STp2 SAVED HDR VR2 WRS DOC LIB2 CP2 LOW8 PA01 PA82 PA243 P40x SHa SHp1 SHb SHd8 SHc
                 BR BL LE (PADx mx PADB)). }
      destruct (strip_bom_cases s0 S0OK ltac:(clear - L3 LS0; lia)) as [(EB & ESB & ELB)|(NB & ESB)].
      *
        assert (R0 : r = Z_to_bv 64 0) by (apply RQ; exact EB). subst r.
        apply (aevt_evt RT AF PMc MST).
        eapply evt_cut.
        { exact (od_walkB7b (Z_to_bv 64 0x96d88) usp S1 F lo COPY len0 gp (Z_to_bv 64 0x656e70) q0 q1 q2 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 (F + 104)) (Z_to_bv 64 p0) q3 q4 q5 q6
                   _ _ F9 fc9 m9 CPOS ltac:(clear - CLO LOR UT LEN0; ul) ltac:(clear - LEN0 L3; lia) FPOS FLO ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) PA404 MI9). }
        cbv beta. intros ms10 (m10 & g0 & -> & MU10 & WM10 & MI10 & P4010). apply evt_done.
        apply (LAST m10 (COPY + 3) (len0 - 3) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F9 fc9 MU10 WM10 MI10 P4010 FRM9);
          [ clear; lia | clear; lia | rewrite ELB; reflexivity | ].
        intros my X. rewrite ESB. unfold padded_bytes in *.
        rewrite <- (firstn_skipn 3 s0) in X at 1. unfold zbytes in X. rewrite map_app, <- app_assoc in X. apply bytes_at_app in X. destruct X as [_ X].
        rewrite length_map, firstn_length_le in X by (clear - L3 LS0; lia). exact X.
      *
        assert (RNZ : r <> Z_to_bv 64 0) by (intros E; apply NB; apply RQ; exact E).
        apply (aevt_evt RT AF PMc MST).
        eapply evt_cut.
        { exact (od_walkB7n (Z_to_bv 64 0x96d88) r usp S1 F lo COPY len0 gp (Z_to_bv 64 0x656e70) q0 q1 q2 d1 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 3) (Z_to_bv 64 (F + 104)) (Z_to_bv 64 p0)
                   q3 q4 q5 q6 _ _ F9 fc9 m9 RNZ FPOS FLO ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(clear - LEN0; lia) PA404 MI9). }
        cbv beta. intros ms10 (m10 & g0 & -> & MU10 & WM10 & MI10 & P4010). apply evt_done.
        apply (LAST m10 COPY len0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F9 fc9 MU10 WM10 MI10 P4010 FRM9);
          [ clear; lia | clear; lia | rewrite ESB; reflexivity | ].
        intros my X. rewrite ESB. exact X.
Qed.
End PhaseB.
