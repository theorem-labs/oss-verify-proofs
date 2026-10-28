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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require PmStep5S1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_RtOwn LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmVup LbB_PmExit2 LbB_PmGlue LbB_PmU2K LbB_PmLH LbB_PmLeaf LbB_DiagStmt LbB_PmDS LbB_ContStmt LbB_PmVops LbB_PmU2 LbB_DStat LbB_TablStmt LbB_PiStmt LbB_PmOL LbB_PmPD LbB_PmSL LbB_HFind LbB_HEmpStmt LbB_PmWF LbB_PmWM LbB_PmU3L LbB_PmU3XK LbB_PmWSt LbB_PmU6K LbB_PmU6a LbB_PmU6d LbB_PmEmhB.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac inlistR := cbn; repeat (first [left; reflexivity | right]).

Lemma regs_tbl_litR {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R r z,
  PropExec.getr R r = Z_to_bv 64 z -> PropExec.getr R r = edenot (Eseed bvmap_empty (wenv_vals w ++ [])) (ELit z).
Proof. intros w R r z Hr. rewrite Hr. reflexivity. Qed.

Lemma regs_tbl_eqR {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R R' RT,
  regs_tbl w R RT -> (forall r, PropExec.getr R' r = PropExec.getr R r) -> regs_tbl w R' RT.
Proof.
  intros w R R' RT HT E. unfold regs_tbl, regs_tblX in *. rewrite Forall_forall in *. intros [r e] Hin.
  cbn [fst snd]. rewrite (E r). exact (HT (r, e) Hin).
Qed.

Lemma bsz_set_m1A : forall n c t, 0 <= n < 2 ^ 24 ->
  (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) -> pm_bud n (set_m1A c t) ->
  forall q k, In (q, k) (c_blocks (set_m1A c t)) -> k <= 2 ^ 40.
Proof.
  intros n c t Hn Hb B q k Hin.
  apply (Permutation_in _ (cbk_m1' c t)) in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - unfold umap_blocks in Hin. apply in_app_iff in Hin as [Hin|Hin].
    + destruct (t3b t =? 0); [contradiction|]. destruct Hin as [E|[]]. injection E as _ <-.
      destruct B as (_ & B1 & _). cbn [set_m1A c_m1] in B1. lia.
    + apply in_map_iff in Hin as (e & E & _). injection E as _ <-. lia.
  - apply (Hb q k). apply (Permutation_in _ (Permutation_sym (cbk_m1 c))). apply in_app_iff. right. exact Hin.
Qed.

Lemma macct_set_m1A : forall c t, pi_macct c ->
  Zlength (t3c (c_m1 c)) <= Zlength (t3c t) ->
  (t3b t = t3b (c_m1 c) \/ ((t3b (c_m1 c) = 0 \/ Zlength (t3c (c_m1 c)) = t3b (c_m1 c)) /\ t3b t = bseq_next (t3b (c_m1 c)))) ->
  In (t3b (c_m1 c)) BSEQ -> t3b (c_m1 c) <> BSEQ_LAST ->
  pi_macct (set_m1A c t).
Proof.
  intros c t (M1 & M2 & M3 & M3K & M2K) Hlen Hb Hin Hlast. unfold pi_macct. cbn [set_m1A c_m1 c_m2 c_m3].
  split; [| split; [exact M2 | split; [exact M3 | split; [exact M3K | exact M2K]]]].
  pose proof (PmStep5S1.bseq_next_le _ Hin Hlast) as [Hn _].
  unfold Zlen, HRep.Zlength in *.
  destruct Hb as [-> | ([E0|Efull] & ->)]; lia.
Qed.

Section U6R.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HPDIAGE : pdiagE_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.

  Lemma HHr : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma ifrA_set_rid : forall (w : pmwA H) m m' (rid' : Z),
    ifrA H w m -> ffkeepX w [(9060, 4)] m m' -> rw_cells asegs m' (wa_ff w + 9060) [C4 (Z_to_bv 64 rid')] -> 0 <= rid' < 2 ^ 32 ->
    ifrA H w m'.
  Proof.
    intros w m m' rid' (ext & tid & rid & D1 & D2 & D3 & D4 & D5 & D6 & D7 & R1 & R2 & R3) K C HX.
    exists ext, tid, rid'.
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D1 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D2 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D3 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D4 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [exact C|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D6 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D7 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [exact R1|]. split; [exact R2 | exact HX].
  Qed.

  Theorem arm_RID_A : forall t, t = 3 -> arm_stmtA H LINV t 0xf2744.
  Proof.
    intros t Ht w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q25 & Q18 & Q21 & PO & C176).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmxa_restrict H HHr LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pose proof (ipure_ranges I IP) as [IWC IOP].
    destruct (Z.eq_dec wv 0) as [W0|Wn0].
    {
      assert (Q21z : PropExec.getr R 21%bv = Z_to_bv 64 0) by (rewrite Q21, W0; reflexivity).
      exact (pm_u6_d0 H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE w s LB LBs m mo c msF R F fc Q
               OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD Q21z CK). }

    assert (HWV : 0 < wv < 2 ^ 32) by lia.

    eapply (pm_u6_1 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc wv Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Q21 HWV).
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 Gra1 G2_1 G10_1 G11_1 G21_1 CD1 FK1 KX1.
    assert (IC1 : ictxA H w m1 I) by (eapply (ictxA_ffkeepX H w m m1); [exact IC | exact FK1 | vm_compute; reflexivity]).
    assert (FR1 : ifrA H w m1) by (exact (ifrA_set_rid w m m1 wv FR FK1 CD1 ltac:(lia))).
    destruct (popndA_ffkeepX H w m m1 _ _ _ OK PO FK1 ltac:(vm_compute; reflexivity)) as [PO1 _].
    assert (Q22_1 : PropExec.getr R1 22%bv = Z_to_bv 64 (i_op I)) by (rewrite (KX1 22%bv ltac:(inlistR)); exact Q22).

    assert (AK1 : accessible m1 (wa_ff w + 9060) 4).
    { apply (ff_accessible m1 (wa_ff w) _ 9060 4 (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1)); [lia | lia | lia | lia | unfold AAPP_HI; lia | vm_compute; reflexivity]. }
    eapply (pm_find_m1 H HHbp LINV LINV_cl LINV_relro w s LB LBs m1 mo1 c _ TBL_EEF44 [] [] 0 msF1 R1 F fc 0xf2760 (wa_ff w + 9060) wv Q
              OK X1 ltac:(vm_compute; reflexivity) ltac:(reflexivity) KR1 VIS1 RF1 G2_1 Gra1 eq_refl ltac:(lia) G10_1 G11_1
              CD1 ltac:(lia) AK1 ltac:(clear - Q2; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(left; clear - Q3 Q7 Q9; lia) ltac:(lia)).
    intros msF2 mo2 m2 R2 p KR2 VIS2 RF2 X2 KEEP2 G10_2 Hfound MU2 WM2 FFK2.
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlistR)); exact G3_1).
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlistR)); exact G4_1).
    pose proof (regs_keep w [] R1 R2 RT_ARM HT1 KEEP2) as HT2. change (rt_keep RT_ARM) with RT_ARM in HT2.
    pose proof (ffkeepX_nil w m1 m2 FFK2) as FK2.
    assert (KX2 : forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R2 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP2 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlistR)). exact (KX1 rr Hrr). }
    assert (CD2 : rw_cells asegs m2 (wa_ff w + 9060) [C4 (Z_to_bv 64 wv)]) by (apply (FFK2 9060 [C4 (Z_to_bv 64 wv)] ltac:(lia) ltac:(cbn; lia) CD1)).
    destruct Hfound as [P0 | (Pp & Pce & P16 & AD2 & v & Hin & Hv & Cv)].
    2: {
      exact (pm_u6_dd H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE HU32 w s LB LBs m2 mo2 c msF2 R2 F fc p wv Q
               OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HT2 G3_2 G4_2 BUD ltac:(rewrite (KEEP2 21%bv ltac:(inlistR)); exact G21_1) G10_2
               ltac:(clear - Pp Pce P16 AC1 AC2; split; [Z.div_mod_to_equations; lia | lia]) CD2 ltac:(lia) CK). }

    subst p.
    assert (G21_2 : PropExec.getr R2 21%bv = Z_to_bv 64 (wa_ff w + 9060)) by (rewrite (KEEP2 21%bv ltac:(inlistR)); exact G21_1).
    assert (E21 : PropExec.getr R2 21%bv = edenot (Eseed bvmap_empty (wenv_vals w ++ [])) (WADD WV_FF 9060)).
    { rewrite G21_2. symmetry. unfold WADD. eapply ev_add; [reflexivity | lia | lia]. }
    assert (HTnf : regs_tbl w R2 RT_U6F0).
    { apply (regs_tbl_sub w [] R2 _ RT_U6F0 (regs_tbl_cons w [] R2 _ 21%bv (WADD WV_FF 9060) E21
               (regs_tbl_cons w [] R2 RT_ARM 10%bv (ELit 0) (regs_tbl_litR w R2 _ _ G10_2) HT2))). vm_compute; reflexivity. }
    eapply (pm_u6_g H HHbp LINV LINV_frame w s LB LBs m2 mo2 c msF2 R2 F fc Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HTnf G3_2 G4_2).
    intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 Gra3 G2_3 G10_3 KX3 EM3. subst m3.
    assert (Q23_3 : PropExec.getr R3 10%bv = Z_to_bv 64 (i_op I)) by (rewrite G10_3, (KX2 22%bv ltac:(inlistR)); exact Q22).
    eapply (pm_leaf0 H HHr LINV LINV_frame AT_GENERATES_TYPE 0 _ _ _ (tla_generates_type HTL) (i_op I) w s LB LBs m2 mo3 c _ _ _ [] 0
              msF3 R3 F fc 0xf3aa8 Q OK X3 KR3 VIS3 RF3 G2_3 Gra3 eq_refl ltac:(lia) ltac:(lia) eq_refl);
      [cbn beta iota; split; [lia | exact Q23_3] | vm_compute; reflexivity | reflexivity |].
    intros msF4 mo4 m4 R4 KR4 VIS4 RF4 X4 KEEP4 MU4 WM4 (b & Gb & _).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv ltac:(inlistR)); exact G3_3).
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv ltac:(inlistR)); exact G4_3).
    pose proof (regs_keep w [] R3 R4 RT_U6G HT3 KEEP4) as HT4. change (rt_keep RT_U6G) with RT_U6G in HT4.
    assert (FK4 : ffkeepX w [] m2 m4).
    { apply (ffkeepX_munch w _ _ _ _ MU4 WM4). apply Forall_cons; [left; cbn [fst]; lia | apply Forall_nil]. }
    assert (KX4 : forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R4 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP4 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlistR)). rewrite (KX3 rr Hrr). exact (KX2 rr Hrr). }
    assert (FK14 : ffkeepX w [] m1 m4) by (eapply (ffkeepX_trans w _ _ _ _ _ _ FK2 FK4); apply incl_refl).
    assert (CD4 : rw_cells asegs m4 (wa_ff w + 9060) [C4 (Z_to_bv 64 wv)])
      by (eapply (ffkeepX_cell w _ m1 m4); [exact FK14 | exact CD1 | lia | cbn; lia | vm_compute; reflexivity]).
    assert (FR4 : ifrA H w m4) by (eapply (ifrA_ffkeepX H w m1 m4); [exact FR1 | exact FK14 | vm_compute; reflexivity]).

    assert (TAIL : forall (val : Z) msF5 mo5 m5 R5, 0 <= val < 2 ^ 32 ->
              as_AKREL H s (mkCfg msF5 mo5) -> as_VIS H s msF5 = MS R5 F (Z_to_bv 64 0xf3ad0) fc None m5 (seg_rom asegs) -> rfull R5 ->
              PMXA H LINV w s LB LBs m5 mo5 c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] ->
              regs_tbl w R5 RT_U6X -> PropExec.getr R5 3%bv = wa_gp w -> PropExec.getr R5 4%bv = wa_tp w ->
              PropExec.getr R5 19%bv = Z_to_bv 64 (sx32A val) -> ffkeepX w [] m4 m5 ->
              (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R5 rr = PropExec.getr R4 rr) ->
              as_SR H Q (mkCfg msF5 mo5)).
    { intros val msF5 mo5 m5 R5 Hval KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 G19_5 FK5 KX5.

      eapply (pm_u6_eb H HHbp LINV LINV_frame w s LB LBs m5 mo5 c msF5 R5 F fc Q OK X5 Htr Hbsz KR5 VIS5 RF5 FZ0 HT5 G3_5 G4_5).
      intros msF6 mo6 m6 R6 KR6 VIS6 RF6 X6 HT6 G3_6 G4_6 Gra6 G2_6 G10_6 G11_6 G19_6 FK6 KX6.
      assert (FK16 : ffkeepX w [] m1 m6).
      { eapply (ffkeepX_trans w [] [] _ m1 m5 m6); [| exact FK6 | apply incl_refl | apply incl_refl].
        eapply (ffkeepX_trans w _ _ _ _ _ _ FK14 FK5); apply incl_refl. }
      assert (CDk6 : rw_cells asegs m6 (wa_ff w + 9060) [C4 (Z_to_bv 64 wv)])
        by (eapply (ffkeepX_cell w _ m1 m6); [exact FK16 | exact CD1 | lia | cbn; lia | vm_compute; reflexivity]).
      assert (AK6 : accessible m6 (wa_ff w + 9060) 4).
      { apply (ff_accessible m6 (wa_ff w) _ 9060 4 (xa_fsh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X6)); [lia | lia | lia | lia | unfold AAPP_HI; lia | vm_compute; reflexivity]. }
      assert (ACC : 2 * (Zlength (t3c (c_m1 c)) + 1) <= wa_n w + 2).
      { pose proof (proj1 AACC Ht) as A1. unfold Zlen, HRep.Zlength in *. lia. }
      eapply (pm_emh_m1 H HHbp LINV LINV_cl LINV_relro HOWN w s LB LBs m6 mo6 c _ TBL_EEF44 [] msF6 R6 F fc 0xf3adc 9060 wv Q
                OK X6 ltac:(vm_compute; reflexivity) ltac:(reflexivity) KR6 VIS6 RF6 FZ0 Gra6 eq_refl ltac:(lia) G2_6 G4_6 G10_6 G11_6
                AK6 ltac:(lia) ltac:(lia) eq_refl
                CDk6 ltac:(lia) BUD ACC).
      intros msF7 mo7 m7 s7 LB7 LBs7 F7 fc7 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 q v tt inserted
             KR7 VIS7 FZ7 X7 Hin7 Hv7 Hlen7 Hni7 Hins7 BUD7 Hbk7 Hbs7 Hlast7 FFC7.
      match type of VIS7 with _ = MS ?RR _ _ _ _ _ _ => set (R7 := RR) in * end.
      assert (RF7 : rfull R7) by apply rfull_mkR.
      assert (KEEP7 : forall r, In r KEPT_REGS -> PropExec.getr R7 r = PropExec.getr R6 r).
      { intros r Hr. unfold KEPT_REGS in Hr. cbn [In] in Hr.
        destruct Hr as [<-|Hr]; [rewrite Gra6; reflexivity|].
        repeat (destruct Hr as [<-|Hr]; [reflexivity|]). destruct Hr. }
      assert (G3_7 : PropExec.getr R7 3%bv = wa_gp w) by (rewrite (KEEP7 3%bv ltac:(inlistR)); exact G3_6).
      assert (G4_7 : PropExec.getr R7 4%bv = wa_tp w) by (rewrite (KEEP7 4%bv ltac:(inlistR)); exact G4_6).
      assert (G10_7 : PropExec.getr R7 10%bv = Z_to_bv 64 (q + 20)) by reflexivity.
      pose proof (regs_keep w [] R6 R7 RT_U6M HT6 KEEP7) as HT7. change (rt_keep RT_U6M) with RT_U6M in HT7.
      pose proof (ffkeepX_nil w m6 m7 FFC7) as FK7.

      destruct tt as [[bl bc] ents]. cbn [t3a t3b t3c fst snd] in Hin7, Hlen7, Hni7, Hins7, Hbk7.
      destruct (in_split _ _ Hin7) as (l1 & l2 & Eents).
      set (c7 := set_m1A c (bl, bc, ents)) in *.
      assert (Htr7 : c_tr c7 = []) by exact Htr.
      pose proof (wk_n H w OK) as WN.
      assert (Hbsz7 : forall q0 k0, In (q0, k0) (c_blocks c7) -> k0 <= 2 ^ 40) by (exact (bsz_set_m1A (wa_n w) c (bl, bc, ents) WN Hbsz BUD7)).
      pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7) as RH7.
      pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7) as [OWN1 OWN2].
      assert (XBc : In (q, 24) (c_blocks c7)).
      { apply (Permutation_in _ (Permutation_sym (cbk_m1 c7))). apply in_or_app; left. unfold mblk1, c7, set_m1A. cbn [c_m1 c_m2 c_m3 t3a t3b t3c fst snd].
        unfold umap_blocks. apply in_or_app; right. apply in_map_iff. exists (q, (wv, v)). split; [reflexivity | exact Hin7]. }
      destruct (xb_facts H HHr w s7 LB7 LBs7 [] m7 c7 (q, 24) OK RH7 OWN1 OWN2 XBc) as (pid & XB1 & XB2 & XB3 & XBR). cbn [fst snd] in XB1, XB2, XB3, XBR.
      pose proof XBR as (R0 & R16 & Rn & RI & RC & RF' & RAPP).
      pose proof (blk_apart_ff H HHr w s7 LB7 m7 _ OK RH7 XB2) as HQF. cbn [blk_addr blk_size fst snd] in HQF.
      pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7) as (SHc7 & _).
      pose proof (proj1 SHc7) as SH17. unfold c7 in SH17. cbn [set_m1A c_m1 t3a t3b t3c fst snd] in SH17.
      assert (AD7 : addressable m7 q 24) by (exact (proj2 SH17 q wv v Hin7)).

      eapply (pm_u6_h1 H HHbp LINV LINV_frame w s7 LB7 LBs7 m7 mo7 c7 msF7 R7 F7 fc7 q Q OK X7 Htr7 Hbsz7 KR7 VIS7 RF7 FZ7 HT7 G3_7 G4_7 G10_7
                ltac:(clear - R0 R16 RC AC1 AC2; split; [Z.div_mod_to_equations; lia | lia]) AD7 HQF).
      intros msF8 mo8 m8 R8 KR8 VIS8 RF8 X8 HT8 G3_8 G4_8 G10_8 G19_8 FK8 KX8.

      assert (G19_8' : PropExec.getr R8 19%bv = Z_to_bv 64 (sx32A val)).
      { rewrite G19_8. change (PropExec.getr R7 19%bv) with (PropExec.getr R6 19%bv). rewrite G19_6. exact G19_5. }
      unfold c7 in X8. rewrite Eents in X8.
      eapply (pm_sw_f17f8 H HHbp LINV LINV_cl w s7 LB7 LBs7 m8 mo8 c _ TBL_EEF44 [] msF8 R8 F7 fc7 bl bc l1 l2 q wv v val Q
                OK X8 ltac:(vm_compute; reflexivity) ltac:(reflexivity) KR8 VIS8 RF8 G10_8 G19_8' Hval).
      intros msF9 mo9 m9 R9 KR9 VIS9 RF9 X9 HR9 FFC9.
      set (c9 := set_m1A c (bl, bc, l1 ++ (q, (wv, val)) :: l2)) in *.
      assert (Elen : Zlength (l1 ++ (q, (wv, val)) :: l2) = Zlength ents) by (rewrite Eents; unfold Zlength; rewrite !length_app; reflexivity).
      assert (BUD9 : pm_bud (wa_n w) c9).
      { clear - BUD7 Elen. unfold c7 in BUD7. unfold pm_bud in BUD7 |- *. unfold c9.
        cbn [set_m1A c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr t3a t3b t3c fst snd] in BUD7 |- *. rewrite Elen. exact BUD7. }
      assert (Htr9 : c_tr c9 = []) by exact Htr.
      assert (Hbsz9 : forall q0 k0, In (q0, k0) (c_blocks c9) -> k0 <= 2 ^ 40) by (exact (bsz_set_m1A (wa_n w) c _ WN Hbsz BUD9)).
      assert (MAC9 : pi_macct c9).
      { apply (macct_set_m1A c _ MAC); cbn [t3a t3b t3c fst snd]; [rewrite Elen; lia | exact Hbk7 | exact Hbs7 | exact Hlast7]. }
      pose proof (regs_tbl_eqR w R8 R9 RT_U6M HT8 HR9) as HT9.
      assert (G3_9 : PropExec.getr R9 3%bv = wa_gp w) by (rewrite (HR9 3%bv); exact G3_8).
      assert (G4_9 : PropExec.getr R9 4%bv = wa_tp w) by (rewrite (HR9 4%bv); exact G4_8).

      eapply (pm_u6_h3 H HHbp LINV LINV_frame w s7 LB7 LBs7 m9 mo9 c9 msF9 R9 F7 fc7 Q OK X9 Htr9 Hbsz9 KR9 VIS9 RF9 FZ7 HT9 G3_9 G4_9).
      intros msF10 mo10 m10 R10 KR10 VIS10 RF10 X10 HT10 G3_10 G4_10 KX10 EM10. subst m10.

      assert (FK19 : ffkeepX w [] m1 m9).
      { eapply (ffkeepX_trans w [] [] _ m1 m6 m9); [exact FK16 | | apply incl_refl | apply incl_refl].
        eapply (ffkeepX_trans w [] [] _ m6 m7 m9); [exact FK7 | | apply incl_refl | apply incl_refl].
        eapply (ffkeepX_trans w [] [] _ m7 m8 m9); [exact FK8 | exact (ffkeepX_nil w m8 m9 FFC9) | apply incl_refl | apply incl_refl]. }
      assert (IC9 : ictxA H w m9 I) by (eapply (ictxA_ffkeepX H w m1 m9); [exact IC1 | exact FK19 | vm_compute; reflexivity]).
      assert (FR9 : ifrA H w m9) by (eapply (ifrA_ffkeepX H w m1 m9); [exact FR1 | exact FK19 | vm_compute; reflexivity]).
      destruct (popndA_ffkeepX H w m1 m9 _ _ _ OK PO1 FK19 ltac:(vm_compute; reflexivity)) as [PO9 MD9].
      pose proof PO9 as (K944 & K946 & K948 & K952 & K956 & K960).
      assert (KXA : forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R10 rr = PropExec.getr R rr).
      { intros rr Hrr. rewrite (KX10 rr Hrr), (HR9 rr), (KX8 rr Hrr).
        replace (PropExec.getr R7 rr) with (PropExec.getr R6 rr)
          by (symmetry; apply KEEP7; cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlistR).
        rewrite (KX6 rr Hrr), (KX5 rr Hrr). exact (KX4 rr Hrr). }
      eapply (PK s7 LB7 LBs7 m9 mo10 c9 msF10 R10 F7 fc7 TBL_EEF44 1 []).
      + constructor; try assumption.
      + apply incl_refl.
      + rewrite (KXA 22%bv) by inlistR. exact Q22.
      + rewrite (KXA 25%bv) by inlistR. exact Q25.
      + exists t. split; [rewrite (KXA 18%bv) by inlistR; exact Q18 | lia].

      + exact K946.
      + left; lia.
      + exists (c_widx c - i_io I), t. split; [exact K944 | exact K948].
      + exact MD9.
      + reflexivity. + reflexivity. + reflexivity.
      + unfold pi_nodes, c9. cbn [set_m1A c_m1 c_m2 c_m3 t3a t3b t3c fst snd]. change (Z.min 1 1) with 1.
        unfold Zlen, Zlength in *. rewrite Elen. lia.
      + rewrite app_nil_r. reflexivity.
      + exact PmZw.seed_free_nil.
      + rewrite PmZw.Zlen_nil. lia.
      + left; reflexivity.
      + reflexivity.
      + right. split; [exact Ht|]. unfold c9. cbn [set_m1A c_m1 t3a t3b t3c fst snd]. unfold Zlen, Zlength in *. rewrite Elen. lia.
      + left; reflexivity.
      + intros []. }

    destruct b.
    -
      assert (HTe : regs_tbl w R4 RT_U6E1).
      { apply (regs_tbl_sub w [] R4 _ RT_U6E1 (regs_tbl_cons w [] R4 RT_U6G 10%bv (ELit 1) (regs_tbl_litR w R4 _ _ Gb) HT4)). vm_compute; reflexivity. }
      eapply (pm_u6_ea1 H HHbp LINV LINV_frame w s LB LBs m4 mo4 c msF4 R4 F fc wv Q OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HTe G3_4 G4_4 CD4 ltac:(lia)).
      intros msF5 mo5 m5 R5 KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 G19_5 FK5 KX5.
      exact (TAIL wv msF5 mo5 m5 R5 ltac:(lia) KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 G19_5 FK5 KX5).
    -
      assert (HTe : regs_tbl w R4 RT_U6E0).
      { apply (regs_tbl_sub w [] R4 _ RT_U6E0 (regs_tbl_cons w [] R4 RT_U6G 10%bv (ELit 0) (regs_tbl_litR w R4 _ _ Gb) HT4)). vm_compute; reflexivity. }
      pose proof FR4 as FR4'. destruct FR4' as (ext & tid & rid & _ & _ & _ & Ctid & _ & _ & _ & _ & Rtid & _).
      eapply (pm_u6_ea0 H HHbp LINV LINV_frame w s LB LBs m4 mo4 c msF4 R4 F fc tid Q OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HTe G3_4 G4_4 Ctid Rtid).
      intros msF5 mo5 m5 R5 KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 G19_5 FK5 KX5.
      exact (TAIL tid msF5 mo5 m5 R5 Rtid KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 G19_5 FK5 KX5).
  Qed.
End U6R.

