(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_RtOwn LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmCall LbA_PmXp LbA_PmXv LbA_PmVup LbA_PmGlue LbA_PmVops LbA_PmHdr LbA_PmLH LbA_PmOL LbA_TablStmt LbA_DiagStmt LbA_ContStmt LbA_PmWKit LbA_PmU2K LbA_PmWT1 LbA_PmWT2 LbA_PmWT3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PmOLX.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma bud_set_v1 : forall n c b' n' cap', pm_bud n c -> 0 <= OPND_SZ * cap' <= 2 ^ 23 -> pm_bud n (set_v1A c (b', n', cap')).
Proof.
  intros n c b' n' cap' B Hc. unfold pm_bud, set_v1A in *. cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd] in *.
  repeat match goal with |- _ /\ _ => split end; try tauto; try lia.
Qed.
Lemma bsz_set_v1 : forall c b' n' cap',
  (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> OPND_SZ * cap' <= 2 ^ 40 ->
  forall q k, In (q, k) (c_blocks (set_v1A c (b', n', cap'))) -> k <= 2 ^ 40.
Proof.
  intros c b' n' cap' Hb Hc q k Hin. rewrite cblocks_set_v1 in Hin. rewrite (cblocks_v1 c) in Hb.
  apply in_app_iff in Hin as [Hin|Hin]; [exact (Hb q k ltac:(apply in_app_iff; left; exact Hin))|].
  apply in_app_iff in Hin as [Hin|Hin]; [| exact (Hb q k ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin))].
  unfold vec_opnd_blocks in Hin. destruct (b' =? 0); [destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-. exact Hc.
Qed.

Section TLD.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis HOWN : rt_own H.
  Hypothesis HVO : vopnd_slow_stmt H.
  Hypothesis HV4R : v4slow_stmt H V32_SLOW_RREF.
  Hypothesis HFW : fixword_stmtA.
  Hypothesis HEX : exhausted_stmtA H LINV.

  Lemma ictxA_keep : forall (w : pmwA H) m m1 m' I,
    ictxA H w m I -> ffkeep w m m1 -> ffkeepX w TL_FFX m1 m' -> ictxA H w m' I.
  Proof.
    intros w m m1 m' I (C1 & C2 & C3 & C4 & C5) FK FX.
    assert (T : forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
              forallb (fun on : Z * Z => (k + Z.of_nat (cells_size cs) <=? fst on) || (fst on + snd on <=? k))%bool TL_FFX = true ->
              rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m' (wa_ff w + k) cs).
    { intros k cs Hk Hn Hb C. apply (ffkeepX_cell w TL_FFX m1 m' k cs FX (FK k cs Hk Hn C) Hk Hn Hb). }
    unfold ictxA. refine (conj _ (conj _ (conj _ (conj _ _)))); (apply T; [cbn; lia | cbn; lia | reflexivity | assumption]).
  Qed.
  Lemma ifrA_keep : forall (w : pmwA H) m m1 m',
    ifrA H w m -> ffkeep w m m1 -> ffkeepX w TL_FFX m1 m' -> ifrA H w m'.
  Proof.
    intros w m m1 m' (ext & tid & rid & C1 & C2 & C3 & C4 & C5 & C6 & C7 & R1 & R2 & R3) FK FX.
    assert (T : forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
              forallb (fun on : Z * Z => (k + Z.of_nat (cells_size cs) <=? fst on) || (fst on + snd on <=? k))%bool TL_FFX = true ->
              rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m' (wa_ff w + k) cs).
    { intros k cs Hk Hn Hb C. apply (ffkeepX_cell w TL_FFX m1 m' k cs FX (FK k cs Hk Hn C) Hk Hn Hb). }
    exists ext, tid, rid. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj R1 (conj R2 R3)))))))));
      (apply T; [cbn; lia | cbn; lia | reflexivity | assumption]).
  Qed.

  Theorem pm_push_tailAX : forall (spal : Z) (w : pmwA H) (I : ictxR) s LB LBs m mo c msF R F fc tbl (t nw : Z) (Q : config -> Prop),
    pmw_okA H w -> OBAS H LINV w s LB LBs m mo c msF R F fc I OL_PUSHK RT_PUSHK S_OPER tbl spal -> 0 <= spal <= PM_STRK * nw -> incl TBL_EEF44 tbl ->
    PropExec.getr R 23%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R 24%bv = Z_to_bv 64 (i_io I) -> PropExec.getr R 26%bv = Z_to_bv 64 t ->
    0 <= t < 2 ^ 32 ->
    rw_cells asegs m (wa_ff w + 946) [C2 (Z_to_bv 64 nw)] -> 0 <= nw < 2 ^ 16 -> mdef m (wa_ff w + 944) 20 ->
    i_io I + 1 <= c_widx c -> c_widx c < i_io I + i_iwc I -> Zlen (t3b (c_v2 c)) <= c_widx c - i_io I ->
    (t3b (c_v1 c) = t3c (c_v1 c) -> 40 * t3c (c_v1 c) + 20 <= 2 ^ 23) ->
    CHECKKA H LINV w Q ->
    (forall s' LB' LBs' m' mo' msF' R' F' fc' (b1 cap1 : Z) (v2 : Z * list Z * Z),
       OBA H LINV w s' LB' LBs' m' mo' (set_scalA (set_v2A (set_v1A c (b1, t3b (c_v1 c) + 1, cap1)) v2) (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c))
           msF' R' F' fc' I OL_HEAD RT_EEF44 S_INSTR TBL_EEF44 ->
       Zlen (t3b v2) <= Zlen (t3b (c_v2 c)) + nw -> c_widx c + nw <= wa_n w ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros spal w I s LB LBs m mo c msF R F fc tbl t nw Q OK OB HSPAL INCL G23 G24 G26 Ht Cnw Hnw MD944 Hio1 Hio2 HL2 Hgrow KC HEADK.
    pose proof OB as [X00 KR0 VIS0 RF0 FZ0 HT00 G3_0 G4_0 Htr Hbsz BUD IP ICX IFR Hic Hend Hw MACC V3R].
    pose proof (pmw_bounds H w OK) as BND. pose proof (wk_n H w OK) as WN.
    pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop]. pose proof IP as (_ & _ & _ & _ & _ & _ & Rio).
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X00) as (_ & _ & _ & Hlen1 & _).

    eapply (tl_segA H HHbp LINV LINV_frame LINV_cl HOWN HVO spal w I s LB LBs m mo c msF R F fc tbl t Q OK OB INCL G23 G24 G26 MD944).
    { intros FULL b'' n''. apply (bud_set_v1 _ _ _ _ _ BUD). unfold OPND_SZ, vgrow. specialize (Hgrow FULL). lia. }
    intros s1 LB1 LBs1 msF1 mo1 m1 R1 b1 cap1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G23_1 G24_1 G26_1 G10_1 BUD1 Hcap1 FFK1.
    set (c1 := set_v1A c (b1, t3b (c_v1 c) + 1, cap1)) in *.
    assert (BC1 : 0 <= OPND_SZ * cap1 <= 2 ^ 23).
    { unfold pm_bud, c1, set_v1A in BUD1. cbn [c_v1 t3c snd] in BUD1. lia. }
    assert (Hbsz1 : forall q k, In (q, k) (c_blocks c1) -> k <= 2 ^ 40) by (apply (bsz_set_v1 _ _ _ _ Hbsz); lia).

    assert (HK : forall s' LB' LBs' (v2 : Z * list Z * Z),
              Zlen (t3b v2) <= Zlen (t3b (c_v2 c)) + nw -> c_widx c + nw <= wa_n w ->
              pm_bud (wa_n w) (set_v2A c1 v2) -> (forall q k, In (q, k) (c_blocks (set_v2A c1 v2)) -> k <= 2 ^ 40) ->
              tl_headK H LINV w s' LB' LBs' m1 (set_scalA (set_v2A c1 v2) (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c)) F fc Q).
    { intros s' LB' LBs' v2 HL FIT BUD2 Hbsz2 msF' mo' m' R' KR' VIS' RF' X' HT' G3' G4' FX'.
      eapply (HEADK s' LB' LBs' m' mo' msF' R' F fc b1 cap1 v2); [| exact HL | exact FIT].
      split.
      - exact X'. - exact KR'. - exact VIS'. - exact RF'. - exact FZ0. - exact HT'. - exact G3'. - exact G4'.
      - cbn. exact Htr.
      - intros q k Hin. apply (Hbsz2 q k). exact Hin.
      - unfold pm_bud in BUD2 |- *. cbn [set_scalA c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr] in BUD2 |- *. exact BUD2.
      - exact IP.
      - exact (ictxA_keep w m m1 m' I ICX FFK1 FX').
      - exact (ifrA_keep w m m1 m' IFR FFK1 FX').
      - cbn [set_scalA c_icount]. exact Hic.
      - cbn [set_scalA c_endian c_reqconv]. exact Hend.
      - exact Hw.
      - unfold macctA in MACC |- *. cbn [set_scalA set_v2A c1 set_v1A c_m1 c_m2 c_m3]. exact MACC.
      - cbn [set_scalA set_v2A c1 set_v1A c_v3]. exact V3R. }

    eapply (tl_segB H HHbp LINV LINV_frame HEX spal w I s1 LB1 LBs1 m1 mo1 c c1 msF1 R1 F fc t nw Q OK X1 HSPAL KR1 VIS1 RF1 FZ0 HT1
              G3_1 G4_1 G23_1 G24_1 G26_1 G10_1 eq_refl eq_refl eq_refl eq_refl);
      [cbn; exact Htr | exact BUD1 | exact Hbsz1 | exact (FFK1 946 [C2 (Z_to_bv 64 nw)] ltac:(lia) ltac:(cbn; lia) Cnw) | exact Hnw
      | exact IP | exact Hio1 | exact Ht | exact Hend | exact (proj1 Hw) | exact KC | | ].
    {
      intros FIT. change c1 with (set_v2A c1 (c_v2 c)) at 1.
      change (set_scalA c1) with (set_scalA (set_v2A c1 (c_v2 c))).
      apply (HK s1 LB1 LBs1 (c_v2 c)); [lia | exact FIT | exact BUD1 | exact Hbsz1]. }

    intros msF2 mo2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 G19 G21 G23_2 G24_2 G27 RC Hnw1 FIT.
    assert (Hk : Z.of_nat (Z.to_nat nw) = nw) by lia.
    eapply (tl_loop H HHbp LINV LINV_frame LINV_cl HOWN HV4R HFW (Z.to_nat nw) spal w s1 LB1 LBs1 m1 m1 mo2 c1 (c_v2 c) msF2 R2 F fc
              (c_widx c + nw) (c_endian c) Q OK ltac:(lia));
      [exact X2 | exact KR2 | exact VIS2 | exact RF2 | exact HT2 | exact G3_2 | exact G4_2
      | rewrite Hk; exact G19 | rewrite Hk; replace (c_widx c + nw - nw) with (c_widx c) by lia; exact G21
      | rewrite Hk; replace (c_widx c + nw - nw) with (c_widx c) by lia; exact G23_2
      | exact G24_2 | destruct Hend as [_ [-> | ->]]; lia | exact G27 | exact (proj1 Hw) | lia | lia | lia | exact BUD1 | exact Hbsz1
      | apply ffkeepX_refl | ].
    intros s' LB' LBs' m' mo' msF' R' v2' KR' VIS' RF' X' HT' G3' G4' G27' HL' BUD' Hbsz' FX'.
    eapply (tl_fin H HHbp LINV LINV_frame spal w s' LB' LBs' m1 m' mo' c (set_v2A c1 v2') msF' R' F fc nw Q OK X' HSPAL FX' KR' VIS' RF' HT' G3' G4' G27'
              eq_refl eq_refl eq_refl eq_refl ltac:(lia) FIT).
    apply (HK s' LB' LBs' v2'); [lia | exact FIT | exact BUD' | exact Hbsz'].
  Qed.

End TLD.
