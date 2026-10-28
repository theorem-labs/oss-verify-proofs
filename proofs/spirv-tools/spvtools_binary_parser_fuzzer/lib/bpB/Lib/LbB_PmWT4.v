(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVup LbB_PmGlue LbB_PmVops LbB_PmHdr LbB_PmLH LbB_PmOL LbB_TablStmt LbB_DiagStmt LbB_ContStmt LbB_PmWKit LbB_PmU2K LbB_PmWT1 LbB_PmWT2 LbB_PmWT3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmOLX LbB_BiW32S LbB_PiStmt.
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
  Hypothesis HFC : biw32_stmt H.
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
    PropExec.getr R 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R 25%bv = Z_to_bv 64 (i_io I) ->
    (exists ty, PropExec.getr R 18%bv = Z_to_bv 64 ty /\ 0 <= ty < 2 ^ 32) ->
    0 <= t < 2 ^ 32 ->
    rw_cells asegs m (wa_ff w + 114) [C2 (Z_to_bv 64 nw)] -> 0 <= nw < 2 ^ 16 -> mdef m (wa_ff w + 112) 20 ->
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
    intros spal w I s LB LBs m mo c msF R F fc tbl t nw Q OK OB HSPAL INCL G22 G25 (ty & G18 & Hty) Ht Cnw Hnw MD112 Hio1 Hio2 HL2 Hgrow KC HEADK.
    pose proof OB as [X00 KR0 VIS0 RF0 FZ0 HT00 G3_0 G4_0 Htr Hbsz BUD IP ICX IFR Hic Hend Hw MACC V3R].
    pose proof (pmw_bounds H w OK) as BND. pose proof (wk_n H w OK) as WN.
    pose proof (@PmODefsS1.ipure_ranges TG idescA I IP) as [Riwc Rop]. pose proof IP as (_ & _ & _ & _ & _ & _ & Rio).
    assert (WNZ : wa_words w <> 0).
    { destruct (wk_words H w OK) as [[W0 N0] | (pw & kk & _ & _ & Wp & _)]; lia. }

    assert (HK : forall s' LB' LBs' m1 b1 cap1 (v2 : Z * list Z * Z),
              ffkeep w m m1 ->
              Zlen (t3b v2) <= Zlen (t3b (c_v2 c)) + nw -> c_widx c + nw <= wa_n w ->
              pm_bud (wa_n w) (set_v2A (set_v1A c (b1, t3b (c_v1 c) + 1, cap1)) v2) ->
              (forall q k, In (q, k) (c_blocks (set_v2A (set_v1A c (b1, t3b (c_v1 c) + 1, cap1)) v2)) -> k <= 2 ^ 40) ->
              tl_headK H LINV w s' LB' LBs' m1 (set_scalA (set_v2A (set_v1A c (b1, t3b (c_v1 c) + 1, cap1)) v2) (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c)) F fc Q).
    { intros s' LB' LBs' m1 b1 cap1 v2 FFK1 HL FIT BUD2 Hbsz2 msF' mo' m' R' KR' VIS' RF' X' HT' G3' G4' FX'.
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
      - unfold pi_macct in MACC |- *. cbn [set_scalA set_v2A set_v1A c_m1 c_m2 c_m3]. exact MACC.
      - cbn [set_scalA set_v2A set_v1A c_v3]. exact V3R. }

    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X00) as (_ & _ & _ & Hlen0 & _).
    assert (BUDG : t3b (c_v1 c) = t3c (c_v1 c) -> forall b'' n'', pm_bud (wa_n w) (set_v1A c (b'', n'', vgrow (t3c (c_v1 c))))).
    { intros FULL b'' n''. apply (bud_set_v1 _ _ _ _ _ BUD). unfold OPND_SZ, vgrow. specialize (Hgrow FULL). lia. }
    eapply tl_segA with (spal := spal) (w := w) (I := I) (s := s) (LB := LB) (LBs := LBs) (m := m) (mo := mo) (c := c)
                        (msF := msF) (R := R) (F := F) (fc := fc) (tbl := tbl) (t := ty) (Q := Q).
    all: first [eassumption | idtac].
    intros s1 LB1 LBs1 msF1 mo1 m1 R1 b1 cap1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G22_1 G25_1 G18_1 G23_1 BUD1 Hcap1 FFK1.
    pose proof (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1) as (_ & _ & _ & Hlen1 & _).
    set (c1 := set_v1A c (b1, t3b (c_v1 c) + 1, cap1)) in *.
    assert (BC1 : 0 <= OPND_SZ * cap1 <= 2 ^ 23).
    { unfold pm_bud, c1, set_v1A in BUD1. cbn [c_v1 t3c snd] in BUD1. lia. }
    assert (Hbsz1 : forall q k, In (q, k) (c_blocks c1) -> k <= 2 ^ 40) by (apply (bsz_set_v1 _ _ _ _ Hbsz); lia).
    assert (G23' : PropExec.getr R1 23%bv = Z_to_bv 64 (t3a (c_v1 c1) + OPND_SZ * t3b (c_v1 c1))) by (subst c1; cbn [set_v1A c_v1 t3a t3b fst snd]; exact G23_1).
    assert (N1 : 1 <= t3b (c_v1 c1)).
    { subst c1. cbn [set_v1A c_v1 t3b fst snd]. lia. }
    assert (Htr1 : c_tr c1 = []) by (subst c1; cbn; exact Htr).
    assert (C114 : rw_cells asegs m1 (wa_ff w + 114) [C2 (Z_to_bv 64 nw)]) by exact (FFK1 114 [C2 (Z_to_bv 64 nw)] ltac:(lia) ltac:(cbn; lia) Cnw).
    assert (FINK : c_widx c + nw <= wa_n w ->
              tl_headK H LINV w s1 LB1 LBs1 m1 (set_scalA c1 (c_widx c + nw) (c_icount c) (c_endian c) (c_reqconv c)) F fc Q).
    { intros FIT. change c1 with (set_v2A c1 (c_v2 c)) at 1.
      change (set_scalA c1) with (set_scalA (set_v2A c1 (c_v2 c))).
      apply (HK s1 LB1 LBs1 m1 b1 cap1 (c_v2 c) FFK1); [lia | exact FIT | exact BUD1 | exact Hbsz1]. }
    eapply tl_segB with (spal := spal) (w := w) (I := I) (s := s1) (LB := LB1) (LBs := LBs1) (m := m1) (mo := mo1) (c := c) (c1 := c1)
                        (msF := msF1) (R := R1) (F := F) (fc := fc) (t := ty) (nw := nw) (Q := Q).
    all: first [eassumption | reflexivity | idtac].
    intros m2 msF2 mo2 R2 KR2 VIS2 RF2 X2 HT2 G3_2 G4_2 G18_2 G19 G21 G23_2 G22_2 FX2 C64 RC Hnw1 FIT.
    assert (Hk : Z.of_nat (Z.to_nat nw) = nw) by lia.
    assert (X2' : PMXAT H LINV w s1 LB1 LBs1 m2 mo2 (set_v2A c1 (c_v2 c)) S_WORD TBL_EEF44 [] [] spal) by exact X2.
    assert (BUD1' : pm_bud (wa_n w) (set_v2A c1 (c_v2 c))) by exact BUD1.
    assert (Hbsz1' : forall q kk, In (q, kk) (c_blocks (set_v2A c1 (c_v2 c))) -> kk <= 2 ^ 40) by exact Hbsz1.
    assert (G19' : PropExec.getr R2 19%bv = Z_to_bv 64 (c_widx c + nw)) by exact G19.
    assert (G21' : PropExec.getr R2 21%bv = Z_to_bv 64 (wa_words w + 4 * (c_widx c + nw - Z.of_nat (Z.to_nat nw))))
      by (rewrite Hk; replace (c_widx c + nw - nw) with (c_widx c) by lia; exact G21).
    assert (G23'' : PropExec.getr R2 23%bv = Z_to_bv 64 (wa_words w + 4 * (c_widx c + nw - Z.of_nat (Z.to_nat nw))))
      by (rewrite Hk; replace (c_widx c + nw - nw) with (c_widx c) by lia; exact G23_2).
    assert (Hen : 0 <= c_endian c < 2 ^ 32) by (destruct Hend as [_ [-> | ->]]; lia).
    assert (Hk0 : (0 < Z.to_nat nw)%nat) by lia.
    assert (Hkb : Z.of_nat (Z.to_nat nw) <= c_widx c + nw <= wa_n w) by lia.
    assert (Hk17 : Zlen (t3b (c_v2 c)) + Z.of_nat (Z.to_nat nw) <= 2 ^ 17) by lia.
    eapply tl_loop with (k := Z.to_nat nw) (spal := spal) (w := w) (s := s1) (LB := LB1) (LBs := LBs1) (m0 := m1) (m := m2) (mo := mo2)
                        (c1 := c1) (v2j := c_v2 c) (msF := msF2) (R := R2) (F := F) (fc := fc) (ia := c_widx c + nw) (en := c_endian c) (Q := Q).
    all: first [eassumption | idtac].
    intros s' LB' LBs' m' mo' msF' R' v2' KR' VIS' RF' X' HT' G3' G4' G19'' HL' BUD' Hbsz' FX'.
    eapply tl_fin with (spal := spal) (w := w) (s := s') (LB := LB') (LBs := LBs') (m0 := m1) (m := m') (mo := mo') (c := c) (cX := set_v2A c1 v2')
                       (msF := msF') (R := R') (F := F) (fc := fc) (nw := nw) (Q := Q).
    all: first [eassumption | reflexivity | lia | idtac].
    apply (HK s' LB' LBs' m1 b1 cap1 v2' FFK1); [lia | exact FIT | exact BUD' | exact Hbsz'].
  Qed.

End TLD.
