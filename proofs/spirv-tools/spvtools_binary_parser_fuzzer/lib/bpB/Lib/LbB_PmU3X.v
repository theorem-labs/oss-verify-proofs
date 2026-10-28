(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Ox Require F12.
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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmExit2 LbB_PmGlue LbB_PmU2K LbB_PmLH LbB_PmLeaf LbB_PmLeafW LbB_DiagStmt LbB_PmDS LbB_ContStmt LbB_PmVup LbB_PmWG LbB_PmWVt LbB_PmWPT LbB_DStat LbB_TablStmt LbB_PmOL LbB_PmPD LbB_PmSL LbB_RtOwn LbB_PmU3L LbB_PmU3XK LbB_PmU3Xa LbB_PmU3Xb LbB_PmU3Xc LbB_PmU3Xnf LbB_PiStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac inlist := cbn; repeat (first [left; reflexivity | right]).

Lemma regs_tbl_lit {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R r z,
  PropExec.getr R r = Z_to_bv 64 z -> PropExec.getr R r = edenot (Eseed bvmap_empty (wenv_vals w ++ [])) (ELit z).
Proof.
  intros w R r z Hr. rewrite Hr. reflexivity.
Qed.

Section U3X.
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
  Hypothesis HPDIAG0 : pdiag0_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis HVOT : votpb_stmt H.
  Hypothesis HPT : push_types_stmtA H.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.

  Lemma HHx : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

  Theorem arm_EXTNUM_A : arm_stmtA H LINV 7 0xf2628.
Proof.
    intros w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q25 & Q18 & Q21 & PO & C176).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmxa_restrict H HHx LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pose proof FR as FR'.
    destruct FR' as (ext & tid & rid & _ & _ & CEXT & _ & _ & _ & _ & HEXT & _ & _).
    apply (pm_u3x_1 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc ext wv Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0
             CEXT HEXT Q21 Hword).
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 Gra1 G2_1 G10_1 G11_1 G12_1 CD1 FK1 KX1.
    pose proof (mdef_of_rw_cells m1 (wa_ff w + 2976) [C8 (Z_to_bv 64 0)] CD1 ltac:(unfold AFS_HDR in Q4; lia)) as MD1.
    eapply (@pm_lookup HCEIL H HHx LINV LINV_frame AT_LOOKUP_EXT 3%nat _ _ (@tla_lookup_ext HCEIL HTL) ext wv 2976
              w s LB LBs m1 mo1 c _ TBL_EEF44 [] [] 0 msF1 R1 F fc _ Q []);
      [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | exact G2_1 | exact Gra1 | reflexivity | lia
      | exact G10_1 | lia | intros Hn2; discriminate Hn2 | intros _; split; [exact G11_1 | split; [exact Hword | exact G12_1]]
      | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | apply incl_refl
      | vm_compute; reflexivity | vm_compute; reflexivity | exact MD1 | ].
    intros msF2 mo2 m2 R2 r KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 Gr Hr Hiff Hfound Hmiss.
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv) by inlist; exact G3_1).
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv) by inlist; exact G4_1).
    pose proof (regs_keep w [] R1 R2 RT_PM_U3X_1_1 HT1 KEEP2) as HT2.
    assert (FK2 : ffkeepX w [(2976, 8)] m1 m2).
    { apply (ffkeepX_munch w _ _ m1 m2 MU2 WM2). cbn [offs_wins map fst snd].
      apply Forall_cons; [left; cbn [fst snd]; unfold TL_STACK; lia |].
      apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    lazymatch type of CEXT with rw_cells _ _ (wa_ff w + ?k) ?cs =>
      assert (CEXT1 : rw_cells asegs m1 (wa_ff w + k) cs)
        by (eapply (ffkeepX_cell w _ m m1); [exact FK1 | exact CEXT | lia | cbn; lia | vm_compute; reflexivity]);
      assert (CEXT2 : rw_cells asegs m2 (wa_ff w + k) cs)
        by (eapply (ffkeepX_cell w _ m1 m2); [exact FK2 | exact CEXT1 | lia | cbn; lia | vm_compute; reflexivity])
    end.
    assert (KX2 : forall rr, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R2 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP2 rr); [exact (KX1 rr Hrr)|]. destruct Hrr as [<- | [<- | [<- | []]]]; inlist. }
    pose proof (ipure_ranges I IP) as (IWC & IOP).
    pose proof (pm_bud_v3bound (wa_n w) c BUD) as CAPB.
    pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR.
    assert (TRR : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF])
      by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_RREF) ltac:(inlist)).
    assert (TRC : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF])
      by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_CREF) ltac:(inlist)).
    assert (Ht36 : 7 <> OT_RESULT_ID /\ 7 <> OT_LITERAL_INTEGER /\ 7 <> OT_LITERAL_STRING)
      by (unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING; lia).
    assert (GB : Zlen (t3b (c_v3 c)) = t3c (c_v3 c) -> forall b'' xs'', pm_bud (wa_n w) (set_v3A c (b'', xs'', vgrow (t3c (c_v3 c))))).
    { intros Hfull b'' xs''. apply pm_bud_v3cap; [exact BUD|]. unfold vgrow. lia. }
    apply (pm_u3x_2 H HHbp LINV LINV_frame w s LB LBs m2 mo2 c msF2 R2 F fc ext r Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HT2 G3_2 G4_2
             CEXT2 HEXT Gr).
    { intros _ msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 Gra3 G2_3 G10_3 EM3 KX3. subst m3.
    eapply (@pm_leaf0 HCEIL H HHx LINV LINV_frame _ AT_IS_NONSEMANTIC 0 _ _ _ (@tla_is_nonsemantic HCEIL HTL) ext
              w s LB LBs m2 mo3 c _ TBL_EEF44 [] [] 0 msF3 R3 F fc _ Q);
      [ exact OK | exact X3 | exact KR3 | exact VIS3 | exact RF3 | exact G2_3 | exact Gra3 | reflexivity | lia
      | lia | reflexivity | split; [lia | exact G10_3]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF4 mo4 m4 R4 KR4 VIS4 RF4 X4 KEEP4 MU4 WM4 QF4.
    destruct QF4 as (b & Gb & _).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv) by inlist; exact G3_3).
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv) by inlist; exact G4_3).
    pose proof (regs_keep w [] R3 R4 RT_PM_U3X_2_1 HT3 KEEP4) as HT4.
    assert (FK4 : ffkeepX w [] m2 m4).
    { apply (ffkeepX_munch w [] _ m2 m4 MU4 WM4).
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (KX4 : forall rr, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R4 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP4 rr); [rewrite (KX3 rr Hrr); exact (KX2 rr Hrr)|].
      destruct Hrr as [<- | [<- | [<- | []]]]; inlist. }
    pose proof (ffkeepX_trans w [(2976, 8)] [] [(2976, 8)] m m2 m4
                  (ffkeepX_trans w [(2976, 8)] [(2976, 8)] [(2976, 8)] m m1 m2 FK1 FK2 (incl_refl _) (incl_refl _))
                  FK4 (incl_refl _) (incl_nil_l _)) as FK04.
    destruct b.
    -
      pose proof (regs_tbl_sub w [] R4 ((10%bv, ELit 1) :: RT_X3) RT_X3NT
                    (regs_tbl_cons w [] R4 RT_X3 10%bv (ELit 1) (regs_tbl_lit w R4 10%bv 1 Gb) HT4)
                    ltac:(vm_compute; reflexivity)) as HTnt.
      apply (pm_u3x_nt H HHbp LINV LINV_frame w s LB LBs m4 mo4 c msF4 R4 F fc Q OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HTnt G3_4 G4_4).
      intros msF5 mo5 m5 R5 KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 Gra5 G2_5 G10_5 G11_5 C52 FK5 KX5.
      eapply (pm_votpb3 H HHbp LINV LINV_cl HOWN HVOT w s LB LBs m5 mo5 c _ TBL_EEF44 [] [] 0 msF5 R5 F fc _ 3520 52 Q);
        [ exact OK | exact X5 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR5 | exact VIS5 | exact RF5
        | exact Gra5 | reflexivity | lia | exact G2_5 | exact G4_5 | exact G10_5 | exact G11_5
        | vm_compute; reflexivity | lia | lia | reflexivity | exact C52 | lia | exact BUD | exact GB | exact TRR | ].
      intros msF6 mo6 m6 R6 s6 LB6 LBs6 b' cap' KR6 VIS6 RF6 X6 KEEP6 BUD6 GROW6 CELLS6.
      assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (rewrite (KEEP6 3%bv) by inlist; exact G3_5).
      assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (rewrite (KEEP6 4%bv) by inlist; exact G4_5).
      pose proof (regs_tbl_sub w [] R6 _ RT_XK (regs_keepK w [] R5 R6 RT_PM_U3X_NT_1 V4_KEPT HT5 KEEP6)
                    ltac:(vm_compute; reflexivity)) as HT6.
      pose proof (pm_bud_v3bound (wa_n w) _ BUD6) as CAP6.
      assert (Hbsz6 : forall q k, In (q, k) (c_blocks (set_v3A c (b', t3b (c_v3 c) ++ [52], cap'))) -> k <= 2 ^ 40).
      { intros q k Hin. destruct (c_blocks_v3_in c b' _ cap' q k Hin) as [Hin' | ->]; [exact (Hbsz q k Hin') | cbn in CAP6; lia]. }
      assert (FK6 : ffkeepX w [] m5 m6) by (intros k cs Hk Hkn _ C; exact (CELLS6 k cs Hk Hkn C)).
      apply (pm_u3x_t1 H HHbp LINV LINV_frame w s6 LB6 LBs6 m6 mo6 (set_v3A c (b', t3b (c_v3 c) ++ [52], cap')) msF6 R6 F fc Q
               OK X6 Htr Hbsz6 KR6 VIS6 RF6 FZ0 HT6 G3_6 G4_6).
      intros msF7 mo7 m7 R7 KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 KX7 FK7.
      pose proof (ffkeepX_trans w [(3520, 4)] [] [(3520, 4)] m4 m5 m7 FK5
                    (ffkeepX_trans w [] [] [] m5 m6 m7 FK6 FK7 (incl_nil_l _) (incl_nil_l _)) (incl_refl _) (incl_nil_l _)) as FK47.
      pose proof (ffkeepX_trans w [(2976, 8)] [(3520, 4)] [(2976, 8); (3520, 4)] m m4 m7 FK04 FK47
                    ltac:(intros x [<- | []]; left; reflexivity) ltac:(intros x [<- | []]; right; left; reflexivity)) as FKall.
      destruct (popndA_ffkeepX H w m m7 [(2976, 8); (3520, 4)] (c_widx c - i_io I) 7 OK PO FKall eq_refl) as [PO7 MD7].
      destruct PO7 as (K112 & K114 & K116 & _).
      assert (G18_7 : PropExec.getr R7 18%bv = Z_to_bv 64 7).
      { rewrite (KX7 18%bv) by inlist. rewrite (KEEP6 18%bv) by inlist. rewrite (KX5 18%bv) by inlist.
        rewrite (KX4 18%bv) by inlist. exact Q18. }
      apply (PK s6 LB6 LBs6 m7 mo7 (set_v3A c (b', t3b (c_v3 c) ++ [52], cap')) msF7 R7 F fc TBL_EEF44 1 [OT_VARIABLE_ID]).
      + constructor; [exact X7 | exact KR7 | exact VIS7 | exact RF7 | exact FZ0 | exact HT7 | exact G3_7 | exact G4_7 | exact Htr
                     | exact Hbsz6 | exact BUD6 | exact IP | exact (ictxA_ffkeepX H w m m7 I _ IC FKall eq_refl)
                     | exact (ifrA_ffkeepX H w m m7 _ FR FKall eq_refl) | exact Hic | exact Hend | exact Hw | exact MAC | ].
        apply Forall_app. split; [exact V3R | apply Forall_cons; [unfold OT_VARIABLE_ID; lia | apply Forall_nil]].
      + apply incl_refl.
      + rewrite (KX7 22%bv) by inlist. rewrite (KEEP6 22%bv) by inlist. rewrite (KX5 22%bv) by inlist.
        rewrite (KX4 22%bv) by inlist. exact Q22.
      + rewrite (KX7 25%bv) by inlist. rewrite (KEEP6 25%bv) by inlist. rewrite (KX5 25%bv) by inlist.
        rewrite (KX4 25%bv) by inlist. exact Q25.
      + exists 7. split; [exact G18_7 | lia].
      + exact K114.
      + left; lia.
      + exists (c_widx c - i_io I), 7. split; [exact K112 | exact K116].
      + exact MD7.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + change (pi_nodes c <= pi_nodes c + Z.min 1 1). change (Z.min 1 1) with 1. lia.
      + reflexivity.
      + intros tt [<- | []]. reflexivity.
      + unfold Zlen. cbn [length]. lia.
      + right. exact Ht36.
      + reflexivity.
      + left; reflexivity.
      + left; reflexivity.
      + exact notrid_varid.
    -
      pose proof (regs_tbl_sub w [] R4 ((10%bv, ELit 0) :: RT_X3) RT_X3NF
                    (regs_tbl_cons w [] R4 RT_X3 10%bv (ELit 0) (regs_tbl_lit w R4 10%bv 0 Gb) HT4)
                    ltac:(vm_compute; reflexivity)) as HTnf.
      exact (pm_u3x_nf H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU32 HPDIAG0 w s LB LBs m4 mo4 c msF4 R4 F fc Q
               OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HTnf G3_4 G4_4 BUD CK). }
    intros HrZ msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 Gra3 G2_3 G10_3 EM3 KX3. subst m3.
    assert (R0 : r = 0).
    { destruct (Z.eq_dec r 0) as [E0 | NE0]; [exact E0 | exfalso].
      apply Z.mod_divide in HrZ; [destruct HrZ as [k Hk]; nia | lia]. }
    eapply (@pm_leaf0 HCEIL H HHx LINV LINV_frame _ AT_IS_NONSEMANTIC 0 _ _ _ (@tla_is_nonsemantic HCEIL HTL) ext
              w s LB LBs m2 mo3 c _ TBL_EEF44 [] [] 0 msF3 R3 F fc _ Q);
      [ exact OK | exact X3 | exact KR3 | exact VIS3 | exact RF3 | exact G2_3 | exact Gra3 | reflexivity | lia
      | lia | reflexivity | split; [lia | exact G10_3]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF4 mo4 m4 R4 KR4 VIS4 RF4 X4 KEEP4 MU4 WM4 QF4.
    destruct QF4 as (b & Gb & _).
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv) by inlist; exact G3_3).
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv) by inlist; exact G4_3).
    pose proof (regs_keep w [] R3 R4 RT_PM_U3X_2_2 HT3 KEEP4) as HT4.
    assert (FK4 : ffkeepX w [] m2 m4).
    { apply (ffkeepX_munch w [] _ m2 m4 MU4 WM4).
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (KX4 : forall rr, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R4 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP4 rr); [rewrite (KX3 rr Hrr); exact (KX2 rr Hrr)|].
      destruct Hrr as [<- | [<- | [<- | []]]]; inlist. }
    pose proof (ffkeepX_trans w [(2976, 8)] [] [(2976, 8)] m m2 m4
                  (ffkeepX_trans w [(2976, 8)] [(2976, 8)] [(2976, 8)] m m1 m2 FK1 FK2 (incl_refl _) (incl_refl _))
                  FK4 (incl_refl _) (incl_nil_l _)) as FK04.
    destruct (Hfound R0) as (d & CDd & HED).
    assert (CD4 : rw_cells asegs m4 (wa_ff w + 2976) [C8 (Z_to_bv 64 d)])
      by (eapply (ffkeepX_cell w [] m2 m4); [exact FK4 | exact CDd | lia | cbn; lia | vm_compute; reflexivity]).
    pose proof TG_ok as GOK. pose proof tg_maxlen as TML.
    pose proof (proj2 (proj2 tg_rid1)) as RIDX.
    let T := type of (pm_u3x_t2 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q) in
    lazymatch T with context [as_VIS H s msF = MS R F (Z_to_bv 64 ?pc) fc None m _] => pose (PCT2 := pc) end.
    assert (TAIL : forall (pre : list Z) s7 LB7 LBs7 m7 mo7 c7 msF7 R7 (sp_p : Z) (ll : list Z),
               as_AKREL H s7 (mkCfg msF7 mo7) ->
               as_VIS H s7 msF7 = MS R7 F (Z_to_bv 64 AT_PUSH_TYPES) fc None m7 (seg_rom asegs) -> rfull R7 ->
               PMXA H LINV w s7 LB7 LBs7 m7 mo7 c7 [3; 4; 11; 13; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] ->
               regs_tbl w R7 RT_PM_U3X_FF_3 -> PropExec.getr R7 3%bv = wa_gp w -> PropExec.getr R7 4%bv = wa_tp w ->
               PropExec.getr R7 1%bv = Z_to_bv 64 PCT2 -> PropExec.getr R7 2%bv = Z_to_bv 64 (wa_s1 w) ->
               PropExec.getr R7 10%bv = Z_to_bv 64 (wa_ff w + 3024) -> PropExec.getr R7 11%bv = Z_to_bv 64 (wa_p w + 264) ->
               rw_cells asegs m7 (wa_ff w + 3024) [C8 (Z_to_bv 64 sp_p); C8 (Z_to_bv 64 (Zlen ll))] ->
               g_ext TG ext wv = Some ll -> spanA sp_p ll ->
               ffkeepX w [(2976, 8); (3008, 4); (3024, 16)] m m7 ->
               (forall rr, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R7 rr = PropExec.getr R rr) ->
               c7 = set_v3A c (t3a (c_v3 c7), t3b (c_v3 c) ++ pre, t3c (c_v3 c7)) ->
               pm_bud (wa_n w) c7 -> (forall q k, In (q, k) (c_blocks c7) -> k <= 2 ^ 40) ->
               seed_free pre -> Zlen pre <= 1 -> ~ In OT_RESULT_ID pre -> Forall (fun t => 0 <= t < 2 ^ 31) pre ->
               as_SR H Q (mkCfg msF7 mo7)).
    { intros pre s7 LB7 LBs7 m7 mo7 c7 msF7 R7 sp_p ll KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN FK7 KX7
             Ec7 BUD7 Hbsz7 SFpre Lpre NRpre Rpre.
      pose proof (go_len_ext TG GOK ext wv ll GX) as LL. unfold HRep.Zlength in LL. change (Zlen ll <= g_maxlen TG) in LL.
      assert (LR : Forall (fun t => 0 <= t < 2 ^ 31) ll).
      { apply Forall_forall. intros x Hx. eapply (go_range TG GOK ll x); [right; right; exists ext, wv; exact GX | exact Hx]. }
      pose proof (pm_bud_v3bound (wa_n w) c7 BUD7) as CAP7.
      assert (V7 : t3b (c_v3 c7) = t3b (c_v3 c) ++ pre) by (rewrite Ec7; reflexivity).
      assert (LEN7 : Zlen (t3b (c_v3 c7)) <= Zlen (t3b (c_v3 c)) + 1) by (rewrite V7, Zlen_app; lia).
      assert (BUDm : forall b'' xs'' cap'', 0 <= cap'' <= capmax (Zlen (t3b (c_v3 c7))) (t3c (c_v3 c7)) (Zlen ll) ->
                       pm_bud (wa_n w) (set_v3A c7 (b'', xs'', cap''))).
      { intros b'' xs'' cap'' Hc. apply pm_bud_v3cap; [exact BUD7|]. unfold capmax in Hc. lia. }
      assert (Htr7 : c_tr c7 = []) by (rewrite Ec7; exact Htr).
      eapply (pm_push_types H HHbp LINV LINV_cl LINV_relro HOWN HPT w s7 LB7 LBs7 m7 mo7 c7 _ TBL_EEF44 [] [] 0 msF7 R7 F fc _ 3024
                sp_p ll Q);
        [ exact OK | exact X7 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR7 | exact VIS7 | exact RF7
        | exact Gra7 | reflexivity | lia
        | exact G2_7 | exact G4_7 | exact G10_7 | exact G11_7 | vm_compute; reflexivity | lia | lia | reflexivity
        | exact CS7 | exact SPN | lia | exact LR | exact BUDm | exact TRC | exact TRR | ].
      intros msF8 mo8 m8 R8 s8 LB8 LBs8 b8 cap8 KR8 VIS8 RF8 X8 KEEP8 BUD8 CAPR8 GROW8 CELLS8.
      assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv) by inlist; exact G3_7).
      assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv) by inlist; exact G4_7).
      pose proof (regs_tbl_sub w [] R8 _ RT_XK (regs_keepK w [] R7 R8 RT_PM_U3X_FF_3 V4_KEPT HT7 KEEP8)
                    ltac:(vm_compute; reflexivity)) as HT8.
      pose proof (pm_bud_v3bound (wa_n w) _ BUD8) as CAP8.
      assert (Hbsz8 : forall q k, In (q, k) (c_blocks (set_v3A c7 (b8, push_types ll (t3b (c_v3 c7)), cap8))) -> k <= 2 ^ 40).
      { intros q k Hin. destruct (c_blocks_v3_in c7 b8 _ cap8 q k Hin) as [Hin' | ->]; [exact (Hbsz7 q k Hin') | cbn in CAP8; lia]. }
      assert (FK8 : ffkeepX w [] m7 m8) by (intros k cs Hk Hkn _ C; exact (CELLS8 k cs Hk Hkn C)).
      apply (pm_u3x_t2 H HHbp LINV LINV_frame w s8 LB8 LBs8 m8 mo8 (set_v3A c7 (b8, push_types ll (t3b (c_v3 c7)), cap8)) msF8 R8 F fc
               Q OK X8 Htr7 Hbsz8 KR8 VIS8 RF8 FZ0 HT8 G3_8 G4_8).
      intros msF9 mo9 m9 R9 KR9 VIS9 RF9 X9 HT9 G3_9 G4_9 KX9 FK9.
      pose proof (ffkeepX_trans w [(2976, 8); (3008, 4); (3024, 16)] [] [(2976, 8); (3008, 4); (3024, 16)] m m7 m9 FK7
                    (ffkeepX_trans w [] [] [] m7 m8 m9 FK8 FK9 (incl_nil_l _) (incl_nil_l _)) (incl_refl _) (incl_nil_l _)) as FKall.
      destruct (popndA_ffkeepX H w m m9 [(2976, 8); (3008, 4); (3024, 16)] (c_widx c - i_io I) 7 OK PO FKall eq_refl) as [PO9 MD9].
      destruct PO9 as (K112 & K114 & K116 & _).
      destruct (push_types_split ll (t3b (c_v3 c7))) as (l2 & El2 & Ll2 & Sub2).
      assert (V38 : t3b (c_v3 (set_v3A c7 (b8, push_types ll (t3b (c_v3 c7)), cap8))) = t3b (c_v3 c) ++ (pre ++ l2)).
      { change (push_types ll (t3b (c_v3 c7)) = t3b (c_v3 c) ++ (pre ++ l2)). rewrite El2, V7, app_assoc. reflexivity. }
      assert (G18_9 : PropExec.getr R9 18%bv = Z_to_bv 64 7).
      { rewrite (KX9 18%bv) by inlist. rewrite (KEEP8 18%bv) by inlist. rewrite (KX7 18%bv) by inlist. exact Q18. }
      apply (PK s8 LB8 LBs8 m9 mo9 (set_v3A c7 (b8, push_types ll (t3b (c_v3 c7)), cap8)) msF9 R9 F fc TBL_EEF44 1 (pre ++ l2)).
      - constructor; [exact X9 | exact KR9 | exact VIS9 | exact RF9 | exact FZ0 | exact HT9 | exact G3_9 | exact G4_9 | exact Htr7
                     | exact Hbsz8 | exact BUD8 | exact IP | exact (ictxA_ffkeepX H w m m9 I _ IC FKall eq_refl)
                     | exact (ifrA_ffkeepX H w m m9 _ FR FKall eq_refl) | rewrite Ec7; exact Hic | rewrite Ec7; exact Hend | exact Hw
                     | rewrite Ec7; exact MAC | ].
        rewrite V38. apply Forall_app. split; [exact V3R|]. apply Forall_app. split; [exact Rpre|].
        apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) LR x (Sub2 x Hx)).
      - apply incl_refl.
      - rewrite (KX9 22%bv) by inlist. rewrite (KEEP8 22%bv) by inlist. rewrite (KX7 22%bv) by inlist. exact Q22.
      - rewrite (KX9 25%bv) by inlist. rewrite (KEEP8 25%bv) by inlist. rewrite (KX7 25%bv) by inlist. exact Q25.
      - exists 7. split; [exact G18_9 | lia].
      - exact K114.
      - left; lia.
      - exists (c_widx c - i_io I), 7. split; [exact K112 | exact K116].
      - exact MD9.
      - rewrite Ec7. reflexivity.
      - rewrite Ec7. reflexivity.
      - rewrite Ec7. reflexivity.
      - lazymatch goal with |- pi_nodes ?x <= _ => assert (EN : pi_nodes x = pi_nodes c) by (rewrite Ec7; reflexivity) end.
        rewrite EN. change (Z.min 1 1) with 1. lia.
      - exact V38.
      - exact (seed_free_app pre l2 SFpre (fun tt Htt => go_ext_zw TG GOK ext wv ll GX tt (Sub2 tt Htt))).
      - rewrite Zlen_app. lia.
      - right. exact Ht36.
      - rewrite Ec7. reflexivity.
      - left. rewrite Ec7. reflexivity.
      - left. rewrite Ec7. reflexivity.
      - intros Hin. destruct (in_app_or _ _ _ Hin) as [Hin' | Hin']; [exact (NRpre Hin') | exact (RIDX ext wv ll GX (Sub2 OT_RESULT_ID Hin'))]. }
    destruct b.
    -
      pose proof (regs_tbl_sub w [] R4 ((10%bv, ELit 1) :: rt_keep RT_PM_U3X_2_2) RT_X3FT
                    (regs_tbl_cons w [] R4 _ 10%bv (ELit 1) (regs_tbl_lit w R4 10%bv 1 Gb) HT4)
                    ltac:(vm_compute; reflexivity)) as HTft.
      apply (pm_u3x_ft H HHbp LINV LINV_frame w s LB LBs m4 mo4 c msF4 R4 F fc Q OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HTft G3_4 G4_4).
      intros msF5 mo5 m5 R5 KR5 VIS5 RF5 X5 HT5 G3_5 G4_5 Gra5 G2_5 G10_5 G11_5 C52 FK5 KX5.
      eapply (pm_votpb3 H HHbp LINV LINV_cl HOWN HVOT w s LB LBs m5 mo5 c _ TBL_EEF44 [] [] 0 msF5 R5 F fc _ 3008 52 Q);
        [ exact OK | exact X5 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR5 | exact VIS5 | exact RF5
        | exact Gra5 | reflexivity | lia | exact G2_5 | exact G4_5 | exact G10_5 | exact G11_5
        | vm_compute; reflexivity | lia | lia | reflexivity | exact C52 | lia | exact BUD | exact GB | exact TRR | ].
      intros msF6 mo6 m6 R6 s6 LB6 LBs6 b' cap' KR6 VIS6 RF6 X6 KEEP6 BUD6 GROW6 CELLS6.
      assert (G3_6 : PropExec.getr R6 3%bv = wa_gp w) by (rewrite (KEEP6 3%bv) by inlist; exact G3_5).
      assert (G4_6 : PropExec.getr R6 4%bv = wa_tp w) by (rewrite (KEEP6 4%bv) by inlist; exact G4_5).
      pose proof (regs_tbl_sub w [] R6 _ RT_XK (regs_keepK w [] R5 R6 RT_PM_U3X_FT_1 V4_KEPT HT5 KEEP6)
                    ltac:(vm_compute; reflexivity)) as HT6.
      pose proof (pm_bud_v3bound (wa_n w) _ BUD6) as CAP6.
      assert (Hbsz6 : forall q k, In (q, k) (c_blocks (set_v3A c (b', t3b (c_v3 c) ++ [52], cap'))) -> k <= 2 ^ 40).
      { intros q k Hin. destruct (c_blocks_v3_in c b' _ cap' q k Hin) as [Hin' | ->]; [exact (Hbsz q k Hin') | cbn in CAP6; lia]. }
      assert (FK6 : ffkeepX w [] m5 m6) by (intros k cs Hk Hkn _ C; exact (CELLS6 k cs Hk Hkn C)).
      pose proof (ffkeepX_trans w [(3008, 4)] [] [(3008, 4)] m4 m5 m6 FK5 FK6 (incl_refl _) (incl_nil_l _)) as FK46.
      assert (CD6 : rw_cells asegs m6 (wa_ff w + 2976) [C8 (Z_to_bv 64 d)])
        by (eapply (ffkeepX_cell w _ m4 m6); [exact FK46 | exact CD4 | lia | cbn; lia | vm_compute; reflexivity]).
      apply (pm_u3x_f2 H HHbp LINV LINV_frame HTL w s6 LB6 LBs6 m6 mo6 (set_v3A c (b', t3b (c_v3 c) ++ [52], cap')) msF6 R6 F fc
               d ext wv Q OK X6 Htr Hbsz6 KR6 VIS6 RF6 FZ0 HT6 G3_6 G4_6 CD6 HED).
      intros msF7 mo7 m7 R7 sp_p ll KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN FK7 KX7.
      apply (TAIL [OT_VARIABLE_ID] s6 LB6 LBs6 m7 mo7 (set_v3A c (b', t3b (c_v3 c) ++ [52], cap')) msF7 R7 sp_p ll
               KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN).
      + exact (ffkeepX_trans w [(2976, 8); (3008, 4)] [(3024, 16)] [(2976, 8); (3008, 4); (3024, 16)] m m6 m7
                 (ffkeepX_trans w [(2976, 8)] [(3008, 4)] [(2976, 8); (3008, 4)] m m4 m6 FK04 FK46
                    ltac:(intros x [<- | []]; left; reflexivity) ltac:(intros x [<- | []]; right; left; reflexivity))
                 FK7 ltac:(intros x [<- | [<- | []]]; [left | right; left]; reflexivity)
                 ltac:(intros x [<- | []]; right; right; left; reflexivity)).
      + intros rr Hrr. rewrite (KX7 rr Hrr), (KEEP6 rr) by (destruct Hrr as [<- | [<- | [<- | []]]]; inlist).
        rewrite (KX5 rr Hrr). exact (KX4 rr Hrr).
      + reflexivity.
      + exact BUD6.
      + exact Hbsz6.
      + intros tt [<- | []]. reflexivity.
      + unfold Zlen. cbn [length]. lia.
      + exact notrid_varid.
      + apply Forall_cons; [unfold OT_VARIABLE_ID; lia | apply Forall_nil].
    -
      pose proof (regs_tbl_sub w [] R4 ((10%bv, ELit 0) :: rt_keep RT_PM_U3X_2_2) RT_X3FF
                    (regs_tbl_cons w [] R4 _ 10%bv (ELit 0) (regs_tbl_lit w R4 10%bv 0 Gb) HT4)
                    ltac:(vm_compute; reflexivity)) as HTff.
      apply (pm_u3x_ff H HHbp LINV LINV_frame HTL w s LB LBs m4 mo4 c msF4 R4 F fc d ext wv Q OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HTff
               G3_4 G4_4 CD4 HED).
      intros msF7 mo7 m7 R7 sp_p ll KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN FK7 KX7.
      assert (ETA : forall c0 : pmc, c0 = set_v3A c0 (t3a (c_v3 c0), t3b (c_v3 c0), t3c (c_v3 c0)))
        by (intros [? ? ? ? ? ? ? ? ? [[? ?] ?] ?]; reflexivity).
      apply (TAIL [] s LB LBs m7 mo7 c msF7 R7 sp_p ll KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN).
      + exact (ffkeepX_trans w [(2976, 8)] [(3024, 16)] [(2976, 8); (3008, 4); (3024, 16)] m m4 m7 FK04 FK7
                 ltac:(intros x [<- | []]; left; reflexivity) ltac:(intros x [<- | []]; right; right; left; reflexivity)).
      + intros rr Hrr. rewrite (KX7 rr Hrr). exact (KX4 rr Hrr).
      + rewrite app_nil_r. apply ETA.
      + exact BUD.
      + exact Hbsz.
      + exact PmZw.seed_free_nil.
      + unfold Zlen. cbn [length]. lia.
      + intros [].
      + apply Forall_nil.
Qed.
End U3X.
