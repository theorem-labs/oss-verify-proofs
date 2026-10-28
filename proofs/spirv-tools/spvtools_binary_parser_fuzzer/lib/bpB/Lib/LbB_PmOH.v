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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase PrsGrammar PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablGrammar TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RtOwn LbB_DStat LbB_TablStmt LbB_ContStmt LbB_PmLeaf LbB_PmLeafW LbB_PmLH LbB_PmVops LbB_PmVup LbB_PmU2K LbB_PmOL LbB_PmWG LbB_PmWPT.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PiStmt LbB_PmOLX LbB_PmOHK LbB_PmOH1 LbB_PmOH2_F LbB_PmOH2_P LbB_PmOH3_A LbB_PmOH3_D LbB_PmOH3_Z LbB_PmOHD LbB_PmOHX.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section OH.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis TFS : take_first_stmtA H.

  Hypothesis ARMS : forall t, arm_stmtAX H LINV t (arm_pcA t).

  Hypothesis TAIL : push_tail_stmtAX H LINV.
  Hypothesis CHK : forall (w : pmwA H) (lw : Z) (Q : config -> Prop), pmw_okA H w -> EXITKA H LINV w lw Q -> CHECKKA H LINV w Q.
  Hypothesis OHZ : forall (w : pmwA H) (I : ictxR) s LB LBs m mo c msF R F fc (Q : config -> Prop) (lw : Z), pmw_okA H w ->
    OLIA H LINV w s LB LBs m mo c msF R F fc I -> c_widx c < i_io I + i_iwc I -> t3b (c_v3 c) = [] ->
    EXITKA H LINV w lw Q -> as_SR H Q (mkCfg msF mo).
  Hypothesis HEXH : exhausted_stmtA H LINV.

  Lemma HHm : asan_rt_hyps H.
Proof.
  exact (proj1 HHbp).
Qed.

  Lemma oh_ictx_keep : forall (w : pmwA H) X m m' I, ffkeepX w X m m' -> Forall (fun on : Z * Z => fst on + snd on <= 9040) X ->
    ictxA H w m I -> ictxA H w m' I.
  Proof.
    intros w X m m' I K HX (C1 & C2 & C3 & C4 & C5).
    assert (KC : forall k cs, 9040 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
              rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m' (wa_ff w + k) cs).
    { intros k cs Hk Hks C. apply K; [lia | exact Hks | | exact C].
      eapply Forall_impl; [| exact HX]. intros on Hon. cbv beta in Hon |- *. right. lia. }
    split; [apply KC; [lia | cbn; lia | exact C1]|]. split; [apply KC; [lia | cbn; lia | exact C2]|].
    split; [apply KC; [lia | cbn; lia | exact C3]|]. split; [apply KC; [lia | cbn; lia | exact C4]|].
    apply KC; [lia | cbn; lia | exact C5].
  Qed.

  Lemma oh_ifr_keep : forall (w : pmwA H) X m m', ffkeepX w X m m' -> Forall (fun on : Z * Z => fst on + snd on <= 9040) X ->
    ifrA H w m -> ifrA H w m'.
  Proof.
    intros w X m m' K HX (ext & tid & rid & C1 & C2 & C3 & C4 & C5 & C6 & C7 & R1 & R2 & R3).
    assert (KC : forall k cs, 9040 <= k -> k + Z.of_nat (cells_size cs) <= 16384 ->
              rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m' (wa_ff w + k) cs).
    { intros k cs Hk Hks C. apply K; [lia | exact Hks | | exact C].
      eapply Forall_impl; [| exact HX]. intros on Hon. cbv beta in Hon |- *. right. lia. }
    exists ext, tid, rid.
    split; [apply KC; [lia | cbn; lia | exact C1]|]. split; [apply KC; [lia | cbn; lia | exact C2]|].
    split; [apply KC; [lia | cbn; lia | exact C3]|]. split; [apply KC; [lia | cbn; lia | exact C4]|].
    split; [apply KC; [lia | cbn; lia | exact C5]|]. split; [apply KC; [lia | cbn; lia | exact C6]|].
    split; [apply KC; [lia | cbn; lia | exact C7]|].
    exact (conj R1 (conj R2 R3)).
  Qed.

  Lemma oh_popnd_keep : forall (w : pmwA H) X m m' off t, ffkeepX w X m m' -> Forall (fun on : Z * Z => 132 <= fst on) X ->
    popndA H w m off t -> popndA H w m' off t.
  Proof.
    intros w X m m' off t K HX (C1 & C2 & C3 & C4 & C5 & C6).
    assert (KC : forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 132 ->
              rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m' (wa_ff w + k) cs).
    { intros k cs Hk Hks C. apply K; [lia | lia | | exact C].
      eapply Forall_impl; [| exact HX]. intros on Hon. cbv beta in Hon |- *. left. lia. }
    split; [apply KC; [lia | cbn; lia | exact C1]|]. split; [apply KC; [lia | cbn; lia | exact C2]|].
    split; [apply KC; [lia | cbn; lia | exact C3]|]. split; [apply KC; [lia | cbn; lia | exact C4]|].
    split; [apply KC; [lia | cbn; lia | exact C5]|].
    apply KC; [lia | cbn; lia | exact C6].
  Qed.

  Lemma oh_arm_default : forall t, t < 1 \/ 107 < t -> arm_pcA t = 0xf2bf8.
  Proof.
    intros t Ht. unfold arm_pcA.
    destruct ((1 <=? t) && (t <=? 107))%bool eqn:E; [| reflexivity].
    apply andb_prop in E. destruct E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  Qed.

  Lemma oh_pushk : forall (w : pmwA H) (I : ictxR) (Q : config -> Prop) (lw : Z) (c : pmc) (b' cap' : Z),
    pmw_okA H w -> EXITKA H LINV w lw Q ->
    i_io I + 1 <= c_widx c -> pi_nodes c + 2 <= c_widx c + 3 -> t3b (c_v1 c) + omeas I c <= 3 * 2 ^ 16 + 1 ->
    Zlen (t3b (c_v2 c)) <= c_widx c - i_io I ->
    Zlen (t3b (c_v3 c)) + zw_next (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 1 ->
    zw_stack_ok (t3b (c_v3 c)) -> nty (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I) -> iaccA I c ->
    c_widx c < i_io I + i_iwc I -> t3b (c_v3 c) <> [] -> Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c)) ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc', OLIA H LINV w s' LB' LBs' m' mo' c' msF' R' F' fc' I ->
       omeas I c' < omeas I c -> as_SR H Q (mkCfg msF' mo')) ->
    PUSHKAX H LINV w I Q (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap')) (fst (take_first (t3b (c_v3 c)))).
  Proof.
    intros w I Q lw c b' cap' OK EXK Hw1 ACC CNT V2L V3L ZW HTY IACC Hlt Hne FR3 HEADK.
    unfold omeas in CNT, HEADK. unfold pi_nodes in ACC.
    set (xs0 := t3b (c_v3 c)) in *.
    pose proof (take_first_range xs0 FR3) as [Rt FR1].
    pose proof (take_first_len xs0 Hne) as [Hlen1 Hlen1'].
    pose proof (zw_next_range xs0) as Hzr0. pose proof (Zlen_nonneg xs0) as Hl0.
    assert (Htf : take_first xs0 = (fst (take_first xs0), snd (take_first xs0))) by (destruct (take_first xs0); reflexivity).
    intros s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' nw l' spal OB6 Hspal Hincl U22 U25 U18 Cnw Hnw Hoff Hmd
           Ew6 Ev16 Ev26 Hn6 Exs6 Hsf Hl' Hlits Em2 Hm1 Hm3 Hnrid.
    unfold pi_nodes in Hn6.
    cbn [set_v3A c_widx c_v1 c_v2 c_v3 c_m1 c_m2 c_m3 t3b fst snd] in Ew6, Ev16, Ev26, Exs6, Em2, Hm1, Hm3, Hn6.
    assert (Hnw0 : 0 <= nw < 2 ^ 16) by (destruct Hnw as [?|(-> & _)]; lia).
    assert (Hnw' : 1 <= nw \/ (nw = 0 /\ zw_type (fst (take_first xs0)) = true /\ l' = [])) by (destruct Hnw as [Hq|Hq]; [left; lia | right; exact Hq]).
    eapply (TAIL spal w I s' LB' LBs' m' mo' c' msF' R' F' fc' tbl' (fst (take_first xs0)) nw Q OK OB6 Hspal Hincl U22 U25 U18
              ltac:(lia) Cnw Hnw0 Hmd);
      [rewrite Ew6; lia | rewrite Ew6; lia | rewrite Ev26, Ew6; lia | rewrite Ev16; intros Ev1; lia | exact (CHK w lw Q OK EXK) |].
    intros s7 LB7 LBs7 m7 mo7 msF7 R7 F7 fc7 b1 cap1 v2 OB7 Hl7 Hn7.
    rewrite Ev26 in Hl7. rewrite Ew6 in Hn7.
    pose proof (zw_next_range (snd (take_first xs0) ++ l')) as Hzr1. pose proof (zw_next_range (snd (take_first xs0))) as Hzr2.
    pose proof (Zlen_nonneg l') as Hl'0.
    assert (HM : 3 * Z.max 0 (i_io I + i_iwc I - (c_widx c + nw)) + zw_next (snd (take_first xs0) ++ l') + 1
                 <= 3 * Z.max 0 (i_io I + i_iwc I - c_widx c) + zw_next xs0
            /\ Zlen (snd (take_first xs0)) + Zlen l' + zw_next (snd (take_first xs0) ++ l') <= 127 * (c_widx c + nw - i_io I) + 1).
    { destruct Hnw as [Hnw1|(Hnw2 & Hzt & ->)].
      - split; lia.
      - rewrite app_nil_r in *. subst nw. destruct (zw_take_zero xs0 ZW Hne Hzt) as [Z1 Z0].
        rewrite Z0, Z1. change (Zlen (@nil Z)) with 0. lia. }
    destruct HM as [HM1 HM2].
    eapply (HEADK s7 LB7 LBs7 m7 mo7 _ msF7 R7 F7 fc7); [split; [exact OB7|] |].
    - unfold pi_nodes, omeas.
      cbn [set_scalA set_v1A set_v2A c_widx c_icount c_endian c_reqconv c_v1 c_v2 c_v3 c_m1 c_m2 c_m3 t3b fst snd].
      rewrite Ew6, Ev16, Exs6.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite Zlen_app; lia|].
      split; [exact (zw_take_push xs0 l' ZW Hne Hsf)|].
      split.
      { replace (c_widx c + nw - i_io I) with (c_widx c - i_io I + nw) by lia.
        exact (nty_step (i_op I) xs0 l' nw (c_widx c - i_io I) Hne HTY Hnw'
                 ltac:(destruct Hlits as [Hlq|(Nq1 & Nq2 & _)]; [left; exact Hlq | right; split; [exact Nq1 | exact Nq2]])). }
      unfold iaccA.
      apply (PmODefsS1.iacc_step (generates_type := tg_generates_type) I c _ (fst (take_first xs0)) (snd (take_first xs0)) l' nw IACC Hne Hw1 Htf);
        cbn [set_scalA set_v1A set_v2A c_widx c_v3 c_m1 c_m2 c_m3 t3b fst snd];
        first [reflexivity | exact Exs6 | exact Hnw' | exact Hlits | exact Em2 | exact Hm1 | exact Hm3 | exact Hnrid].
    - unfold omeas. cbn [set_scalA set_v1A set_v2A c_widx c_v3 t3b fst snd]. rewrite Ew6, Exs6. lia.
  Qed.

  Lemma oh_arm : forall (w : pmwA H) (I : ictxR) (Q : config -> Prop) (lw : Z) (c : pmc) (b' cap' : Z) s LB LBs m mo msF R F fc (word : Z),
    pmw_okA H w -> EXITKA H LINV w lw Q ->
    i_io I + 1 <= c_widx c -> pi_nodes c + 2 <= c_widx c + 3 -> t3b (c_v1 c) + omeas I c <= 3 * 2 ^ 16 + 1 ->
    Zlen (t3b (c_v2 c)) <= c_widx c - i_io I ->
    Zlen (t3b (c_v3 c)) + zw_next (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 1 ->
    zw_stack_ok (t3b (c_v3 c)) -> nty (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I) -> iaccA I c ->
    c_widx c < i_io I + i_iwc I -> t3b (c_v3 c) <> [] -> Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c)) ->
    c_widx c < wa_n w ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc', OLIA H LINV w s' LB' LBs' m' mo' c' msF' R' F' fc' I ->
       omeas I c' < omeas I c -> as_SR H Q (mkCfg msF' mo')) ->
    OBA H LINV w s LB LBs m mo (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap')) msF R F fc I
      (arm_pcA (fst (take_first (t3b (c_v3 c))))) RT_ARM S_OPER TBL_EEF44 ->
    0 <= word < 2 ^ 32 ->
    PropExec.getr R 22%bv = Z_to_bv 64 (i_op I) -> PropExec.getr R 25%bv = Z_to_bv 64 (i_io I) ->
    PropExec.getr R 18%bv = Z_to_bv 64 (fst (take_first (t3b (c_v3 c)))) -> PropExec.getr R 21%bv = Z_to_bv 64 (sx32A word) ->
    popndA H w m (c_widx c - i_io I) (fst (take_first (t3b (c_v3 c)))) -> rw_cells asegs m (wa_ff w + 176) [C4 (Z_to_bv 64 word)] ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w I Q lw c b' cap' s LB LBs m mo msF R F fc word OK EXK Hw1 ACC CNT V2L V3L ZW HTY IACC Hlt Hne FR3 Hwn HEADK
           OB Hword G22 G25 G18 G21 PO C176.
    pose proof (oh_pushk w I Q lw c b' cap' OK EXK Hw1 ACC CNT V2L V3L ZW HTY IACC Hlt Hne FR3 HEADK) as PK.
    pose proof (take_first_range _ FR3) as [Rt FR1].
    pose proof (take_first_len _ Hne) as [Hlen1 Hlen1'].
    pose proof (zw_next_range (t3b (c_v3 c))) as Hzr0.
    assert (Htf : take_first (t3b (c_v3 c)) = (fst (take_first (t3b (c_v3 c))), snd (take_first (t3b (c_v3 c)))))
      by (destruct (take_first (t3b (c_v3 c))); reflexivity).
    unfold omeas in CNT. unfold pi_nodes in ACC.
    eapply (ARMS (fst (take_first (t3b (c_v3 c)))) w s LB LBs m mo _ msF R F fc I TBL_EEF44 word Q OK);
      [| exact (incl_refl _) | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
       | exact PK | exact (CHK w lw Q OK EXK) |].
    - split; [exact OB|].
      unfold pi_nodes. cbn [set_v3A c_widx c_v1 c_v2 c_v3 c_m1 c_m2 c_m3 t3b fst snd].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact G22|]. split; [exact G25|]. split; [exact G18|]. split; [exact G21|]. split; [exact PO | exact C176].
    - apply (PmODefsS1.iacc_aacc I c _ _ (snd (take_first (t3b (c_v3 c)))) IACC Hne Htf); reflexivity.
  Qed.

  Lemma oh_fix : forall (w : pmwA H) (I : ictxR) (Q : config -> Prop) (lw : Z) (c : pmc) (b' cap' : Z) s LB LBs m mo msF R F fc (x0 : Z),
    pmw_okA H w -> EXITKA H LINV w lw Q ->
    i_io I + 1 <= c_widx c -> pi_nodes c + 2 <= c_widx c + 3 -> t3b (c_v1 c) + omeas I c <= 3 * 2 ^ 16 + 1 ->
    Zlen (t3b (c_v2 c)) <= c_widx c - i_io I ->
    Zlen (t3b (c_v3 c)) + zw_next (t3b (c_v3 c)) <= 127 * (c_widx c - i_io I) + 1 ->
    zw_stack_ok (t3b (c_v3 c)) -> nty (i_op I) (t3b (c_v3 c)) (c_widx c - i_io I) -> iaccA I c ->
    c_widx c < i_io I + i_iwc I -> t3b (c_v3 c) <> [] -> Forall (fun t => 0 <= t < 2 ^ 31) (t3b (c_v3 c)) ->
    c_widx c < wa_n w ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc', OLIA H LINV w s' LB' LBs' m' mo' c' msF' R' F' fc' I ->
       omeas I c' < omeas I c -> as_SR H Q (mkCfg msF' mo')) ->
    c_tr c = [] -> (forall q k, In (q, k) (c_blocks (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap'))) -> k <= 2 ^ 40) ->
    pm_bud (wa_n w) (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap')) -> ipureA I ->
    c_icount c + 4 <= i_io I -> c_endian c = c_reqconv c /\ (c_endian c = 0 \/ c_endian c = 1) -> wa_words w <> 0 /\ 5 <= wa_n w ->
    pi_macct c -> frm_zero fc -> ictxA H w m I -> ifrA H w m ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AT_FIXWORD) fc None m (seg_rom asegs) -> rfull R ->
    PMXA H LINV w s LB LBs m mo (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap')) S_OPER TBL_EEF44 [] -> regs_tbl w R RT_EF07Cc ->
    PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    0 <= x0 < 2 ^ 32 -> PropExec.getr R 10%bv = Z_to_bv 64 (sx32A x0) -> PropExec.getr R 11%bv = Z_to_bv 64 (c_endian c) ->
    PropExec.getr R 18%bv = Z_to_bv 64 (fst (take_first (t3b (c_v3 c)))) -> PropExec.getr R 22%bv = Z_to_bv 64 (i_op I) ->
    PropExec.getr R 25%bv = Z_to_bv 64 (i_io I) ->
    popndA H w m (c_widx c - i_io I) (fst (take_first (t3b (c_v3 c)))) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w I Q lw c b' cap' s LB LBs m mo msF R F fc x0 OK EXK Hw1 ACC CNT V2L V3L ZW HTY IACC Hlt Hne FR3 Hwn HEADK
           Htr Hbsz BUD IP Hic Hend Hw MACC FZ IC IFR KR VIS RF X HT G3 G4 Hx0 G10 G11 G18 G22 G25 PO.
    pose proof (take_first_range _ FR3) as [Rt FR1].
    assert (KOB : forall m1 mo1 msF1 R1 pc, ffkeepX w [(176, 4)] m m1 ->
                  as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs) -> rfull R1 ->
                  PMXA H LINV w s LB LBs m1 mo1 (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap')) S_OPER TBL_EEF44 [] ->
                  regs_tbl w R1 RT_ARM -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
                  OBA H LINV w s LB LBs m1 mo1 (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap')) msF1 R1 F fc I pc RT_ARM S_OPER TBL_EEF44).
    { intros m1 mo1 msF1 R1 pc FK KR1 VIS1 RF1 X1 HT1 G3_1 G4_1.
      assert (HX : Forall (fun on : Z * Z => fst on + snd on <= 9040) [(176, 4)]) by (repeat constructor; cbn; lia).
      constructor; [exact X1 | exact KR1 | exact VIS1 | exact RF1 | exact FZ | exact HT1 | exact G3_1 | exact G4_1 | exact Htr
                   | exact Hbsz | exact BUD | exact IP | exact (oh_ictx_keep w _ m m1 I FK HX IC) | exact (oh_ifr_keep w _ m m1 FK HX IFR)
                   | exact Hic | exact Hend | exact Hw | exact MACC | exact FR1]. }
    assert (HXp : Forall (fun on : Z * Z => 132 <= fst on) [(176, 4)]) by (repeat constructor; cbn; lia).
    assert (TD : 1 <= fst (take_first (t3b (c_v3 c))) <= 107 \/ (fst (take_first (t3b (c_v3 c))) = 0 \/ 107 < fst (take_first (t3b (c_v3 c))) < 2 ^ 31))
      by lia.
    destruct TD as [HtA|HtD].
    - eapply (pm_oh3_A H HHbp LINV LINV_frame HTL w s LB LBs m mo _ msF R F fc (i_io I) (i_op I) _ x0 Q OK KR VIS RF X HT G3 G4 Hx0 G10 G11
                G18 G22 G25 (proj2 Hend) HtA).
      intros msF1 mo1 m1 R1 word KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G10_1 Hword G18_1 G21_1 G22_1 G25_1 C176 FK.
      eapply (pm_dispatchA H HHbp LINV w s LB LBs m1 mo1 _ S_OPER TBL_EEF44 [] [] 0 msF1 R1 F fc _ Q OK X1 KR1 VIS1 RF1 HT1 G10_1 HtA).
      intros msF5 mo5 R5 KR5 VIS5 RF5 X5 KEEP5.
      assert (HT5 : regs_tbl w R5 RT_ARM)
        by exact (regs_tbl_sub w [] R5 _ RT_ARM (regs_keepK w [] R1 R5 RT_ARM DISP_KEPT HT1 KEEP5) ltac:(vm_compute; reflexivity)).
      assert (G3_5 : PropExec.getr R5 3%bv = wa_gp w) by (rewrite (KEEP5 3%bv ltac:(inb)); exact G3_1).
      assert (G4_5 : PropExec.getr R5 4%bv = wa_tp w) by (rewrite (KEEP5 4%bv ltac:(inb)); exact G4_1).
      assert (G18_5 : PropExec.getr R5 18%bv = Z_to_bv 64 (fst (take_first (t3b (c_v3 c))))) by (rewrite (KEEP5 18%bv ltac:(inb)); exact G18_1).
      assert (G21_5 : PropExec.getr R5 21%bv = Z_to_bv 64 (sx32A word)) by (rewrite (KEEP5 21%bv ltac:(inb)); exact G21_1).
      assert (G22_5 : PropExec.getr R5 22%bv = Z_to_bv 64 (i_op I)) by (rewrite (KEEP5 22%bv ltac:(inb)); exact G22_1).
      assert (G25_5 : PropExec.getr R5 25%bv = Z_to_bv 64 (i_io I)) by (rewrite (KEEP5 25%bv ltac:(inb)); exact G25_1).
      exact (oh_arm w I Q lw c b' cap' s LB LBs m1 mo5 msF5 R5 F fc word OK EXK Hw1 ACC CNT V2L V3L ZW HTY IACC Hlt Hne FR3 Hwn HEADK
               (KOB m1 mo5 msF5 R5 _ FK KR5 VIS5 RF5 X5 HT5 G3_5 G4_5) Hword G22_5 G25_5 G18_5 G21_5
               (oh_popnd_keep w _ m m1 _ _ FK HXp PO) C176).
    - eapply (pm_oh3_D H HHbp LINV LINV_frame HTL w s LB LBs m mo _ msF R F fc (i_io I) (i_op I) _ x0 Q OK KR VIS RF X HT G3 G4 Hx0 G10 G11
                G18 G22 G25 (proj2 Hend) HtD).
      intros msF1 mo1 m1 R1 word KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 Hword G18_1 G21_1 G22_1 G25_1 C176 FK.
      rewrite <- (oh_arm_default (fst (take_first (t3b (c_v3 c)))) ltac:(lia)) in VIS1.
      exact (oh_arm w I Q lw c b' cap' s LB LBs m1 mo1 msF1 R1 F fc word OK EXK Hw1 ACC CNT V2L V3L ZW HTY IACC Hlt Hne FR3 Hwn HEADK
               (KOB m1 mo1 msF1 R1 _ FK KR1 VIS1 RF1 X1 HT1 G3_1 G4_1) Hword G22_1 G25_1 G18_1 G21_1
               (oh_popnd_keep w _ m m1 _ _ FK HXp PO) C176).
  Qed.

  Lemma pm_oheadA : forall (w : pmwA H) (I : ictxR) s LB LBs m mo c msF R F fc (Q : config -> Prop) (lw : Z),
    pmw_okA H w -> OLIA H LINV w s LB LBs m mo c msF R F fc I -> c_widx c < i_io I + i_iwc I ->
    EXITKA H LINV w lw Q ->
    (forall s' LB' LBs' m' mo' c' msF' R' F' fc', OLIA H LINV w s' LB' LBs' m' mo' c' msF' R' F' fc' I ->
       omeas I c' < omeas I c -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
Proof using HHbp LINV_frame LINV_cl LINV_relro HOWN HTL TFS ARMS TAIL CHK OHZ HEXH.
    intros w I s LB LBs m mo c msF R F fc Q lw OK HOLI Hlt EXK HEADK.
    destruct (list_eq_dec Z.eq_dec (t3b (c_v3 c)) []) as [E0|Hne];
      [exact (OHZ w I s LB LBs m mo c msF R F fc Q lw OK HOLI Hlt E0 EXK)|].
    destruct HOLI as (OB & Hw1 & ACC & CNT & V2L & V3L & ZW & HTY & IACC).
    pose proof OB as [X KR VIS RF FZ HT G3 G4 Htr Hbsz BUD IP IC IFR Hic Hend Hw MACC FR3].
    pose proof IC as (Cio & Cfw & Ciwc & Cop & Cd).
    pose proof (PmODefsS1.ipure_ranges I IP) as (Riwc & Rop).
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (B1 & B2 & B3 & B4).
    pose proof (wk_n H w OK) as WN.
    pose proof (take_first_range _ FR3) as [Rt FR1].
    pose proof (zw_next_range (t3b (c_v3 c))) as Hzr0.
    pose proof (pm_bud_v3bound _ _ BUD) as Bv3.
    eapply (pm_oh1 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc (i_io I) (i_iwc I) Q OK X Htr Hbsz KR VIS RF FZ HT G3 G4
              ltac:(lia) ltac:(lia) ltac:(lia) Hlt Hne Cio Ciwc).
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 G1_1 G2_1 G10_1 G22_1 FK1.
    pose proof (wk_tr H w OK) as TR.
    eapply (pm_take_first H HHbp LINV LINV_cl LINV_relro HOWN TFS w s LB LBs m1 mo1 c S_INSTR TBL_EEF44 [] [] 0 msF1 R1 F fc 0xf136c Q
              OK X1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) KR1 VIS1 RF1 G1_1 ltac:(reflexivity) ltac:(lia) G2_1 G4_1
              G10_1 Hne FR3);
      [ intros b'' xs'' cap'' Hc''; apply pm_bud_v3cap; [exact BUD|]; unfold capmax in Hc''; lia
      | exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_CREF) ltac:(inlist))
      | exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_RREF) ltac:(inlist))
      | ].
    intros msF2 mo2 m2 R2 s2 LB2 LBs2 b' cap' KR2 VIS2 RF2 X2 KEPT2 G10_2 BUD2 Hcap2 HLB2 FK2.
    assert (HT2 : regs_tbl w R2 RT_EEFB0)
      by exact (regs_tbl_sub w [] R2 _ RT_EEFB0 (regs_keepK w [] R1 R2 RT_EEF98 V4_KEPT HT1 KEPT2) ltac:(vm_compute; reflexivity)).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEPT2 3%bv ltac:(inb)); exact G3_1).
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEPT2 4%bv ltac:(inb)); exact G4_1).
    assert (FKm2 : ffkeep w m m2) by exact (ffkeep_trans w m m1 m2 FK1 FK2).
    assert (Cio2 : rw_cells asegs m2 (wa_ff w + 10112) [C8 (Z_to_bv 64 (i_io I))]) by exact (FKm2 10112 [C8 (Z_to_bv 64 (i_io I))] ltac:(lia) ltac:(cbn; lia) Cio).
    assert (Cop2 : rw_cells asegs m2 (wa_ff w + 9050) [C2 (Z_to_bv 64 (i_op I))]) by exact (FKm2 9050 [C2 (Z_to_bv 64 (i_op I))] ltac:(lia) ltac:(cbn; lia) Cop).
    assert (Hbsz2 : forall q k, In (q, k) (c_blocks (set_v3A c (b', snd (take_first (t3b (c_v3 c))), cap'))) -> k <= 2 ^ 40).
    { intros q k Hin. destruct (c_blocks_v3_in _ _ _ _ _ _ Hin) as [Hin' | ->]; [exact (Hbsz _ _ Hin')|].
      pose proof (pm_bud_v3bound _ _ BUD2) as Bc. cbn [set_v3A c_v3 t3c fst snd] in Bc. lia. }
    assert (IC2 : ictxA H w m2 I) by exact (oh_ictx_keep w [] m m2 I (ffkeepX_nil w m m2 FKm2) (Forall_nil _) IC).
    assert (IFR2 : ifrA H w m2) by exact (oh_ifr_keep w [] m m2 (ffkeepX_nil w m m2 FKm2) (Forall_nil _) IFR).
    destruct (Z_lt_le_dec (c_widx c) (wa_n w)) as [Hwn|Hwn].
    2: { exact (pm_ohx H HHbp LINV LINV_frame HEXH w s2 LB2 LBs2 m2 mo2 _ msF2 R2 F fc (i_io I) (i_iwc I) (i_op I) _ Q OK X2
                  Htr Hbsz2 KR2 VIS2 RF2 FZ HT2 G3_2 G4_2 G10_2 Rt ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)
                  BUD2 Cio2 Cop2 (CHK w lw Q OK EXK)). }
    assert (HX3 : Forall (fun on : Z * Z => fst on + snd on <= 9040) [(128, 4); (124, 4); (120, 4); (116, 4); (114, 2); (112, 2)])
      by (repeat constructor; cbn; lia).
    assert (FP : 4 * c_widx c + 4 <= 8 * ((4 * wa_n w) / 8) \/ (4 * c_widx c = 8 * ((4 * wa_n w) / 8) /\ (4 * wa_n w) mod 8 = 4)).
    { pose proof (Z.div_mod (4 * wa_n w) 8 ltac:(lia)) as Edm. pose proof (Z.mod_pos_bound (4 * wa_n w) 8 ltac:(lia)) as Bdm.
      clear - Hwn B1 Edm Bdm. lia. }
    destruct FP as [FP|FP];
      [ eapply (pm_oh2_F H HHbp LINV LINV_frame w s2 LB2 LBs2 m2 mo2 _ msF2 R2 F fc (i_io I) (i_iwc I) (i_op I) _ Q OK X2
                  Htr Hbsz2 KR2 VIS2 RF2 FZ HT2 G3_2 G4_2 G10_2 Rt ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia)
                  (proj1 Hw) ltac:(cbn; lia) (proj2 Hend) FP Cio2 Cop2)
      | eapply (pm_oh2_P H HHbp LINV LINV_frame w s2 LB2 LBs2 m2 mo2 _ msF2 R2 F fc (i_io I) (i_iwc I) (i_op I) _ Q OK X2
                  Htr Hbsz2 KR2 VIS2 RF2 FZ HT2 G3_2 G4_2 G10_2 Rt ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(lia)
                  (proj1 Hw) ltac:(cbn; lia) (proj2 Hend) FP Cio2 Cop2) ];
      intros msF3 mo3 m3 R3 x0 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 Hx0 G10_3 G11_3 G18_3 G22_3 G25_3 PO3 Cio3 Cop3 FK3;
      exact (oh_fix w I Q lw c b' cap' s2 LB2 LBs2 m3 mo3 msF3 R3 F fc x0 OK EXK Hw1 ACC CNT V2L V3L ZW HTY IACC Hlt Hne FR3 Hwn HEADK
               Htr Hbsz2 BUD2 IP Hic Hend Hw MACC FZ (oh_ictx_keep w _ m2 m3 I FK3 HX3 IC2) (oh_ifr_keep w _ m2 m3 FK3 HX3 IFR2)
               KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 Hx0 G10_3 G11_3 G18_3 G22_3 G25_3 PO3).
  Qed.
End OH.
