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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablFacts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmExit2 LbB_PmGlue LbB_PmU2K LbB_PmLH LbB_PiStmt LbB_PmLeaf LbB_PmLeafW LbB_DiagStmt LbB_PmDS LbB_ContStmt LbB_PmVup LbB_PmWG LbB_PmWVt LbB_PmWPT LbB_DStat LbB_TablStmt LbB_PmOL LbB_PmPD LbB_PmSL LbB_RtOwn LbB_PmU3L LbB_PmU3XK LbB_PmU4Ea LbB_PmU4Eb LbB_PmU4Ed LbB_PmU4Sa LbB_PmU4Sd.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac inlist := cbn; repeat (first [left; reflexivity | right]).

Definition ENUM_TYPES : list Z := [13; 14; 15; 16; 17; 18; 19; 20; 21; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 49; 51; 57; 58; 59; 60; 62; 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 82; 83; 84; 85; 105; 107].

Definition enum_et (t : Z) : Z := if t =? 49 then 26 else if t =? 76 then 75 else if t =? 51 then 34 else if t =? 105 then 33 else t.

Lemma enum_facts : forall t, In t ENUM_TYPES -> t <> OT_RESULT_ID /\ t <> OT_LITERAL_INTEGER /\ t <> OT_LITERAL_STRING.
Proof.
  intros t H. unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING. unfold ENUM_TYPES in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [repeat split; discriminate|]). destruct H.
Qed.
Lemma enum_et_range : forall t, 0 <= t < 2 ^ 31 -> 0 <= enum_et t < 2 ^ 31.
Proof.
  intros t Ht. unfold enum_et. destruct (Z.eqb_spec t 49); [lia|]. destruct (Z.eqb_spec t 76); [lia|].
  destruct (Z.eqb_spec t 51); [lia|]. destruct (Z.eqb_spec t 105); lia.
Qed.

Lemma regs_tbl_litE {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) R r z,
  PropExec.getr R r = Z_to_bv 64 z -> PropExec.getr R r = edenot (Eseed bvmap_empty (wenv_vals w ++ [])) (ELit z).
Proof. intros w R r z Hr. rewrite Hr. reflexivity. Qed.

Section U4E.
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
  Hypothesis HPT : push_types_stmtA H.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.

  Lemma HHe : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma popndA_set_typeE : forall (w : pmwA H) m m' off t (t' : Z),
    popndA H w m off t -> ffkeepX w [(116, 4); (6928, 8)] m m' -> rw_cells asegs m' (wa_ff w + 116) [C4 (Z_to_bv 64 t')] ->
    popndA H w m' off t'.
  Proof.
    intros w m m' off t t' (P0 & P1 & P2 & P3 & P4 & P5) K C.
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P0 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P1 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [exact C|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P3 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact P4 | lia | cbn; lia | vm_compute; reflexivity]|].
    eapply (ffkeepX_cell w _ m m'); [exact K | exact P5 | lia | cbn; lia | vm_compute; reflexivity].
  Qed.

  Theorem arm_ENUM_A : forall t, In t ENUM_TYPES -> arm_stmtA H LINV t 0xf14b0.
  Proof.
    intros t HIn w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    pose proof (enum_facts t HIn) as Ht36.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q25 & Q18 & Q21 & PO & C1108).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmxa_restrict H HHe LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pose proof (ipure_ranges I IP) as [IWC IOP].
    pose proof (pm_bud_v3bound _ _ BUD) as CAPB.
    pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR.
    assert (TRR : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF]) by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_RREF) ltac:(inlist)).
    assert (TRC : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF]) by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_CREF) ltac:(inlist)).
    pose proof (enum_et_range t Ht31) as HET.
    pose proof TG_ok as GOK. pose proof tg_maxlen as TML. pose proof (proj1 (proj2 tg_rid1)) as RIDX.
    pose proof PO as PO'. destruct PO' as (_ & _ & C948 & _).

    assert (KONT : forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) ->
      as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_LOOKUP_OPERAND) fc None m1 (seg_rom asegs) -> rfull R1 ->
      PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 27; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] ->
      regs_tbl w R1 RT_E1 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
      PropExec.getr R1 1%bv = Z_to_bv 64 0xf1544 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) ->
      PropExec.getr R1 10%bv = Z_to_bv 64 t -> PropExec.getr R1 11%bv = PropExec.getr R 21%bv ->
      PropExec.getr R1 12%bv = Z_to_bv 64 (wa_ff w + 6928) ->
      rw_cells asegs m1 (wa_ff w + 116) [C4 (Z_to_bv 64 (enum_et t))] -> rw_cells asegs m1 (wa_ff w + 6928) [C8 (Z_to_bv 64 0)] ->
      ffkeepX w [(116, 4); (6928, 8)] m m1 ->
      (forall rr : reg, In rr [18%bv; 21%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) ->
      as_SR H Q (mkCfg msF1 mo1)).
    { intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 Gra1 G2_1 G10_1 G11_1 G12_1 CT1 CE1 FK1 KX1.
      pose proof (popndA_set_typeE w m m1 _ _ _ PO FK1 CT1) as PO1.
      assert (IC1 : ictxA H w m1 I) by (eapply (ictxA_ffkeepX H w m m1); [exact IC | exact FK1 | vm_compute; reflexivity]).
      assert (FR1 : ifrA H w m1) by (eapply (ifrA_ffkeepX H w m m1); [exact FR | exact FK1 | vm_compute; reflexivity]).
      assert (MD1 : mdef m1 (wa_ff w + 6928) 8) by (exact (mdef_of_rw_cells m1 _ _ CE1 ltac:(unfold AIMG_TOP, AFS_HDR in *; lia))).
      assert (G11' : PropExec.getr R1 11%bv = Z_to_bv 64 (sx32A wv)) by (rewrite G11_1; exact Q21).

      eapply (pm_lookup H HHe LINV LINV_frame _ _ _ _ (tla_lookup_operand HTL) t wv 6928 w s LB LBs m1 mo1 c _ TBL_EEF44 [] [] 0
                msF1 R1 F fc 0xf1544 Q [] OK X1 KR1 VIS1 RF1 G2_1 Gra1 eq_refl ltac:(lia) G10_1 ltac:(lia)
                ltac:(intros Hn2; discriminate Hn2) ltac:(intros _; exact (conj G11' (conj Hword G12_1))) eq_refl);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity | exact MD1 |].
      intros msF2 mo2 m2 R2 r KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 Gr Hr Hiff Hfound Hmiss.
      assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlist)); exact G3_1).
      assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlist)); exact G4_1).
      pose proof (regs_keep w [] R1 R2 RT_E1 HT1 KEEP2) as HT2. change (rt_keep RT_E1) with RT_E1 in HT2.
      assert (FK2 : ffkeepX w [(6928, 8)] m1 m2).
      { apply (ffkeepX_munch w _ _ _ _ MU2 WM2). apply Forall_cons; [left; cbn [fst]; unfold TL_STACK; lia|].
        cbn [offs_wins map]. apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
      assert (CT2 : rw_cells asegs m2 (wa_ff w + 116) [C4 (Z_to_bv 64 (enum_et t))]).
      { eapply (ffkeepX_cell w _ m1 m2); [exact FK2 | exact CT1 | lia | cbn; lia | vm_compute; reflexivity]. }
      destruct (popndA_ffkeepX H w m1 m2 _ _ _ OK PO1 FK2 ltac:(vm_compute; reflexivity)) as [PO2 _].
      assert (IC2 : ictxA H w m2 I) by (eapply (ictxA_ffkeepX H w m1 m2); [exact IC1 | exact FK2 | vm_compute; reflexivity]).
      assert (FR2 : ifrA H w m2) by (eapply (ifrA_ffkeepX H w m1 m2); [exact FR1 | exact FK2 | vm_compute; reflexivity]).
      assert (KX2 : forall rr : reg, In rr [18%bv; 21%bv; 22%bv; 25%bv] -> PropExec.getr R2 rr = PropExec.getr R rr).
      { intros rr Hrr. rewrite (KEEP2 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlist)). exact (KX1 rr Hrr). }
      assert (FK02 : ffkeepX w [(116, 4); (6928, 8)] m m2).
      { apply (ffkeepX_trans w [(116, 4); (6928, 8)] [(6928, 8)] _ m m1 m2 FK1 FK2); [apply incl_refl|].
        intros on Hon. cbn in Hon. destruct Hon as [<-|[]]. cbn. right; left; reflexivity. }
      destruct (Z.eq_dec r 0) as [R0|RN0].
      2: {
        exact (pm_u4e_d H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU32 HTL LINV_relro HPDIAG0 w s LB LBs m2 mo2 c msF2 R2 F fc r (enum_et t) Q
                 OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HT2 G3_2 G4_2 Gr (conj RN0 Hr) CT2 HET BUD CK). }

      destruct (Hfound R0) as (d & CDd & HOD).
      assert (HTf : regs_tbl w R2 RT_E2F).
      { apply (regs_tbl_sub w [] R2 _ RT_E2F (regs_tbl_cons w [] R2 RT_E1 10%bv (ELit 0) (regs_tbl_litE w R2 _ _ ltac:(rewrite Gr, R0; reflexivity)) HT2)). vm_compute; reflexivity. }
      eapply (pm_u4e_f H HHbp LINV LINV_frame HTL w s LB LBs m2 mo2 c msF2 R2 F fc d t wv Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HTf G3_2 G4_2 CDd HOD).
      intros msF7 mo7 m7 R7 sp_p ll KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN FK7 KX7.
      pose proof (go_len_operand _ GOK t wv ll GX) as LL. unfold Zlength in LL. change (Zlen ll <= g_maxlen TG) in LL.
      assert (LR : Forall (fun t => 0 <= t < 2 ^ 31) ll).
      { apply Forall_forall. intros x Hx. eapply (go_range _ GOK ll x); [right; left; exists t, wv; exact GX | exact Hx]. }
      assert (BUDm : forall b'' xs'' cap'', 0 <= cap'' <= capmax (Zlen (t3b (c_v3 c))) (t3c (c_v3 c)) (Zlen ll) ->
                     pm_bud (wa_n w) (set_v3A c (b'', xs'', cap''))).
      { intros b'' xs'' cap'' Hc. apply pm_bud_v3cap; [exact BUD|]. unfold capmax in Hc. clear - Hc CAPB LL TML Hlen Hw2 IWC Hw1. lia. }
      eapply (pm_push_types H HHbp LINV LINV_cl LINV_relro HOWN HPT w s LB LBs m7 mo7 c _ TBL_EEF44 [] [] 0 msF7 R7 F fc 0xf17e8 7424 sp_p ll Q
                OK X7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) KR7 VIS7 RF7 Gra7 eq_refl ltac:(lia) G2_7 G4_7 G10_7 G11_7
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) eq_refl CS7 SPN ltac:(lia) LR BUDm TRC TRR).
      intros msF8 mo8 m8 R8 s8 LB8 LBs8 b8 cap8 KR8 VIS8 RF8 X8 KEEP8 BUD8 CAPR8 GROW8 CELLS8.
      set (c8 := set_v3A c (b8, push_types ll (t3b (c_v3 c)), cap8)) in *.
      assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv ltac:(inlist)); exact G3_7).
      assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv ltac:(inlist)); exact G4_7).
      pose proof (regs_keepK w [] R7 R8 RT_E1 V4_KEPT HT7 KEEP8) as HT8.
      replace (rt_keepK V4_KEPT RT_E1) with RT_E1 in HT8 by (vm_compute; reflexivity).
      pose proof (pm_bud_v3bound _ _ BUD8) as CAP8.
      assert (Hbsz8 : forall q k, In (q, k) (c_blocks c8) -> k <= 2 ^ 40).
      { intros q k Hin. subst c8. destruct (c_blocks_v3_in c _ _ _ _ _ Hin) as [Hin'| ->]; [exact (Hbsz _ _ Hin') |].
        cbn [set_v3A c_v3 t3c snd] in CAP8. clear - CAP8. lia. }
      assert (FK8 : ffkeepX w [] m7 m8) by (intros k cs Hk Hkn _ C; exact (CELLS8 k cs Hk Hkn C)).
      assert (Htr8 : c_tr c8 = []) by (subst c8; exact Htr).
      eapply (pm_u4e_t H HHbp LINV LINV_frame w s8 LB8 LBs8 m8 mo8 c8 msF8 R8 F fc Q OK X8 Htr8 Hbsz8 KR8 VIS8 RF8 FZ0 HT8 G3_8 G4_8).
      intros msF9 mo9 m9 R9 KR9 VIS9 RF9 X9 HT9 G3_9 G4_9 KX9 FK9.

      assert (FKall : ffkeepX w [(116, 4); (6928, 8); (7424, 16)] m m9).
      { apply (ffkeepX_trans w [(116, 4); (6928, 8); (7424, 16)] [] _ m m7 m9); [| | intros x Hx; exact Hx | apply incl_nil_l].
        - apply (ffkeepX_trans w [(116, 4); (6928, 8)] [(7424, 16)] _ m m2 m7 FK02 FK7);
            [intros x Hx; clear - Hx; cbn in Hx |- *; tauto | intros x Hx; clear - Hx; cbn in Hx |- *; tauto].
        - exact (ffkeepX_trans w _ _ _ m7 m8 m9 FK8 FK9 (incl_nil_l _) (incl_nil_l _)). }
      assert (FK29 : ffkeepX w [(7424, 16)] m2 m9).
      { apply (ffkeepX_trans w [(7424, 16)] [] _ m2 m7 m9 FK7); [| intros x Hx; exact Hx | apply incl_nil_l].
        exact (ffkeepX_trans w _ _ _ m7 m8 m9 FK8 FK9 (incl_nil_l _) (incl_nil_l _)). }
      destruct (popndA_ffkeepX H w m2 m9 _ _ _ OK PO2 FK29 ltac:(vm_compute; reflexivity)) as [PO9 MD9].
      destruct PO9 as (K944 & K946 & K948 & _).
      destruct (PmZw.push_types_split ll (t3b (c_v3 c))) as (l2 & El2 & Ll2 & Sub2).
      assert (V38 : t3b (c_v3 c8) = t3b (c_v3 c) ++ l2).
      { subst c8. cbn [set_v3A c_v3 t3b fst snd]. rewrite El2. reflexivity. }
      eapply (PK s8 LB8 LBs8 m9 mo9 c8 msF9 R9 F fc TBL_EEF44 1 l2).
      + constructor; try assumption; try (subst c8; assumption);
          first [ eapply (ictxA_ffkeepX H w m m9); [exact IC | exact FKall | vm_compute; reflexivity]
                | eapply (ifrA_ffkeepX H w m m9); [exact FR | exact FKall | vm_compute; reflexivity]
                | (rewrite V38; apply Forall_app; split; [exact V3R|];
                   apply Forall_forall; intros x Hx; exact (proj1 (Forall_forall _ _) LR x (Sub2 x Hx))) ].
      + apply incl_refl.
      + rewrite (KX9 22%bv ltac:(inlist)), (KEEP8 22%bv ltac:(inlist)), (KX7 22%bv ltac:(inlist)), (KX2 22%bv ltac:(inlist)). exact Q22.
      + rewrite (KX9 25%bv ltac:(inlist)), (KEEP8 25%bv ltac:(inlist)), (KX7 25%bv ltac:(inlist)), (KX2 25%bv ltac:(inlist)). exact Q25.
      + exists t. split; [rewrite (KX9 18%bv ltac:(inlist)), (KEEP8 18%bv ltac:(inlist)), (KX7 18%bv ltac:(inlist)), (KX2 18%bv ltac:(inlist)); exact Q18 | lia].
      + exact K946.
      + left; lia.
      + exists (c_widx c - i_io I), (enum_et t). split; [exact K944 | exact K948].
      + exact MD9.
      + subst c8; reflexivity. + subst c8; reflexivity. + subst c8; reflexivity.
      + subst c8. unfold pi_nodes. cbn [set_v3A c_m1 c_m2 c_m3]. lia.
      + exact V38.
      + intros tt Htt. exact (go_operand_zw _ GOK t wv ll GX tt (Sub2 tt Htt)).
      + lia.
      + right. exact Ht36.
      + subst c8; reflexivity.
      + left; subst c8; reflexivity.
      + left; subst c8; reflexivity.
      + intros Hin. exact (RIDX t wv ll GX (Sub2 _ Hin)). }

    assert (HTt : forall z, t = z -> regs_tbl w R (RT_E0 z)).
    { intros z <-. unfold RT_E0. apply regs_tbl_app; [exact HT0|]. apply Forall_cons; [cbn [fst snd]; rewrite Q18; reflexivity | apply Forall_nil]. }
    assert (Hcases : t = 49 \/ t = 76 \/ t = 51 \/ t = 105 \/ (t <> 49 /\ t <> 76 /\ t <> 51 /\ t <> 105)) by lia.
    destruct Hcases as [E49 | [E76 | [E51 | [E105 | HNR]]]].
    - pose proof (HTt 49 E49) as HTz. subst t.
      exact (pm_u4e_1_49 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
    - pose proof (HTt 76 E76) as HTz. subst t.
      exact (pm_u4e_1_76 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
    - pose proof (HTt 51 E51) as HTz. subst t.
      exact (pm_u4e_1_51 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
    - pose proof (HTt 105 E105) as HTz. subst t.
      exact (pm_u4e_1_105 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HTz G3_0 G4_0 KONT).
    - assert (EE : enum_et t = t) by (unfold enum_et; rewrite !(proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
      rewrite EE in KONT.
      exact (pm_u4e_1_g H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc t Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0
               Q18 Ht31 HNR C948 KONT).
  Qed.

  Theorem arm_SRCLANG_A : forall t, t = 12 -> arm_stmtA H LINV t 0xf2950.
  Proof.
    intros t Et w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC. subst t.
    assert (Ht36 : 12 <> OT_RESULT_ID /\ 12 <> OT_LITERAL_INTEGER /\ 12 <> OT_LITERAL_STRING) by (unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING; lia).
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q25 & Q18 & Q21 & PO & C1108).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmxa_restrict H HHe LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pose proof (ipure_ranges I IP) as [IWC IOP].
    pose proof (pm_bud_v3bound _ _ BUD) as CAPB.
    pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR.
    assert (TRR : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF]) by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_RREF) ltac:(inlist)).
    assert (TRC : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF]) by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_CREF) ltac:(inlist)).
    pose proof TG_ok as GOK. pose proof tg_maxlen as TML. pose proof (proj1 (proj2 tg_rid1)) as RIDX.

    eapply (pm_u4s_1 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0).
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 Gra1 G2_1 G10_1 G11_1 G12_1 CE1 FK1 KX1.
      destruct (popndA_ffkeepX H w m m1 _ _ _ OK PO FK1 ltac:(vm_compute; reflexivity)) as [PO1 _].
      pose proof PO1 as PO1'. destruct PO1' as (_ & _ & CT1 & _).
      assert (IC1 : ictxA H w m1 I) by (eapply (ictxA_ffkeepX H w m m1); [exact IC | exact FK1 | vm_compute; reflexivity]).
      assert (FR1 : ifrA H w m1) by (eapply (ifrA_ffkeepX H w m m1); [exact FR | exact FK1 | vm_compute; reflexivity]).
      assert (MD1 : mdef m1 (wa_ff w + 7456) 8) by (exact (mdef_of_rw_cells m1 _ _ CE1 ltac:(unfold AIMG_TOP, AFS_HDR in *; lia))).
      assert (G11' : PropExec.getr R1 11%bv = Z_to_bv 64 (sx32A wv)) by (rewrite G11_1; exact Q21).

      eapply (pm_lookup H HHe LINV LINV_frame _ _ _ _ (tla_lookup_operand HTL) 12 wv 7456 w s LB LBs m1 mo1 c _ TBL_EEF44 [] [] 0
                msF1 R1 F fc 0xf296c Q [] OK X1 KR1 VIS1 RF1 G2_1 Gra1 eq_refl ltac:(lia) G10_1 ltac:(lia)
                ltac:(intros Hn2; discriminate Hn2) ltac:(intros _; exact (conj G11' (conj Hword G12_1))) eq_refl);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | apply incl_refl | reflexivity | reflexivity | exact MD1 |].
      intros msF2 mo2 m2 R2 r KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 Gr Hr Hiff Hfound Hmiss.
      assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv ltac:(inlist)); exact G3_1).
      assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv ltac:(inlist)); exact G4_1).
      pose proof (regs_keep w [] R1 R2 RT_S1 HT1 KEEP2) as HT2. change (rt_keep RT_S1) with RT_S1 in HT2.
      assert (FK2 : ffkeepX w [(7456, 8)] m1 m2).
      { apply (ffkeepX_munch w _ _ _ _ MU2 WM2). apply Forall_cons; [left; cbn [fst]; unfold TL_STACK; lia|].
        cbn [offs_wins map]. apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
      assert (CT2 : rw_cells asegs m2 (wa_ff w + 116) [C4 (Z_to_bv 64 12)]).
      { eapply (ffkeepX_cell w _ m1 m2); [exact FK2 | exact CT1 | lia | cbn; lia | vm_compute; reflexivity]. }
      destruct (popndA_ffkeepX H w m1 m2 _ _ _ OK PO1 FK2 ltac:(vm_compute; reflexivity)) as [PO2 _].
      assert (IC2 : ictxA H w m2 I) by (eapply (ictxA_ffkeepX H w m1 m2); [exact IC1 | exact FK2 | vm_compute; reflexivity]).
      assert (FR2 : ifrA H w m2) by (eapply (ifrA_ffkeepX H w m1 m2); [exact FR1 | exact FK2 | vm_compute; reflexivity]).
      assert (KX2 : forall rr : reg, In rr [18%bv; 21%bv; 22%bv; 25%bv] -> PropExec.getr R2 rr = PropExec.getr R rr).
      { intros rr Hrr. rewrite (KEEP2 rr ltac:(cbn in Hrr; decompose [or] Hrr; try contradiction; subst rr; inlist)). exact (KX1 rr Hrr). }
      assert (FK02 : ffkeepX w [(7456, 8)] m m2) by (exact (ffkeepX_trans w _ _ _ m m1 m2 FK1 FK2 (fun x Hx => Hx) (fun x Hx => Hx))).
      destruct (Z.eq_dec r 0) as [R0|RN0].
      2: {
        exact (pm_u4s_d H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU32 HTL LINV_relro HPDIAG0 w s LB LBs m2 mo2 c msF2 R2 F fc r Q
                 OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HT2 G3_2 G4_2 Gr (conj RN0 Hr) CT2 BUD CK). }

      destruct (Hfound R0) as (d & CDd & HOD).
      assert (HTf : regs_tbl w R2 RT_S2F).
      { apply (regs_tbl_sub w [] R2 _ RT_S2F (regs_tbl_cons w [] R2 RT_S1 10%bv (ELit 0) (regs_tbl_litE w R2 _ _ ltac:(rewrite Gr, R0; reflexivity)) HT2)). vm_compute; reflexivity. }
      eapply (pm_u4s_f H HHbp LINV LINV_frame HTL w s LB LBs m2 mo2 c msF2 R2 F fc d 12 wv Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HTf G3_2 G4_2 CDd HOD).
      intros msF7 mo7 m7 R7 sp_p ll KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN FK7 KX7.
      pose proof (go_len_operand _ GOK 12 wv ll GX) as LL. unfold Zlength in LL. change (Zlen ll <= g_maxlen TG) in LL.
      assert (LR : Forall (fun t => 0 <= t < 2 ^ 31) ll).
      { apply Forall_forall. intros x Hx. eapply (go_range _ GOK ll x); [right; left; exists 12, wv; exact GX | exact Hx]. }
      assert (BUDm : forall b'' xs'' cap'', 0 <= cap'' <= capmax (Zlen (t3b (c_v3 c))) (t3c (c_v3 c)) (Zlen ll) ->
                     pm_bud (wa_n w) (set_v3A c (b'', xs'', cap''))).
      { intros b'' xs'' cap'' Hc. apply pm_bud_v3cap; [exact BUD|]. unfold capmax in Hc. clear - Hc CAPB LL TML Hlen Hw2 IWC Hw1. lia. }
      eapply (pm_push_types H HHbp LINV LINV_cl LINV_relro HOWN HPT w s LB LBs m7 mo7 c _ TBL_EEF44 [] [] 0 msF7 R7 F fc 0xf35e8 7952 sp_p ll Q
                OK X7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) KR7 VIS7 RF7 Gra7 eq_refl ltac:(lia) G2_7 G4_7 G10_7 G11_7
                ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) eq_refl CS7 SPN ltac:(lia) LR BUDm TRC TRR).
      intros msF8 mo8 m8 R8 s8 LB8 LBs8 b8 cap8 KR8 VIS8 RF8 X8 KEEP8 BUD8 CAPR8 GROW8 CELLS8.
      set (c8 := set_v3A c (b8, push_types ll (t3b (c_v3 c)), cap8)) in *.
      assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv ltac:(inlist)); exact G3_7).
      assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv ltac:(inlist)); exact G4_7).
      pose proof (regs_keepK w [] R7 R8 RT_S1 V4_KEPT HT7 KEEP8) as HT8.
      replace (rt_keepK V4_KEPT RT_S1) with RT_S1 in HT8 by (vm_compute; reflexivity).
      pose proof (pm_bud_v3bound _ _ BUD8) as CAP8.
      assert (Hbsz8 : forall q k, In (q, k) (c_blocks c8) -> k <= 2 ^ 40).
      { intros q k Hin. subst c8. destruct (c_blocks_v3_in c _ _ _ _ _ Hin) as [Hin'| ->]; [exact (Hbsz _ _ Hin') |].
        cbn [set_v3A c_v3 t3c snd] in CAP8. clear - CAP8. lia. }
      assert (FK8 : ffkeepX w [] m7 m8) by (intros k cs Hk Hkn _ C; exact (CELLS8 k cs Hk Hkn C)).
      assert (Htr8 : c_tr c8 = []) by (subst c8; exact Htr).
      eapply (pm_u4s_t H HHbp LINV LINV_frame w s8 LB8 LBs8 m8 mo8 c8 msF8 R8 F fc Q OK X8 Htr8 Hbsz8 KR8 VIS8 RF8 FZ0 HT8 G3_8 G4_8).
      intros msF9 mo9 m9 R9 KR9 VIS9 RF9 X9 HT9 G3_9 G4_9 KX9 FK9.

      assert (FKall : ffkeepX w [(7456, 8); (7952, 16)] m m9).
      { apply (ffkeepX_trans w [(7456, 8); (7952, 16)] [] _ m m7 m9); [| | intros x Hx; exact Hx | apply incl_nil_l].
        - apply (ffkeepX_trans w [(7456, 8)] [(7952, 16)] _ m m2 m7 FK02 FK7);
            [intros x Hx; clear - Hx; cbn in Hx |- *; tauto | intros x Hx; clear - Hx; cbn in Hx |- *; tauto].
        - exact (ffkeepX_trans w _ _ _ m7 m8 m9 FK8 FK9 (incl_nil_l _) (incl_nil_l _)). }
      assert (FK29 : ffkeepX w [(7952, 16)] m2 m9).
      { apply (ffkeepX_trans w [(7952, 16)] [] _ m2 m7 m9 FK7); [| intros x Hx; exact Hx | apply incl_nil_l].
        exact (ffkeepX_trans w _ _ _ m7 m8 m9 FK8 FK9 (incl_nil_l _) (incl_nil_l _)). }
      destruct (popndA_ffkeepX H w m2 m9 _ _ _ OK PO2 FK29 ltac:(vm_compute; reflexivity)) as [PO9 MD9].
      destruct PO9 as (K944 & K946 & K948 & _).
      destruct (PmZw.push_types_split ll (t3b (c_v3 c))) as (l2 & El2 & Ll2 & Sub2).
      assert (V38 : t3b (c_v3 c8) = t3b (c_v3 c) ++ l2).
      { subst c8. cbn [set_v3A c_v3 t3b fst snd]. rewrite El2. reflexivity. }
      eapply (PK s8 LB8 LBs8 m9 mo9 c8 msF9 R9 F fc TBL_EEF44 1 l2).
      + constructor; try assumption; try (subst c8; assumption);
          first [ eapply (ictxA_ffkeepX H w m m9); [exact IC | exact FKall | vm_compute; reflexivity]
                | eapply (ifrA_ffkeepX H w m m9); [exact FR | exact FKall | vm_compute; reflexivity]
                | (rewrite V38; apply Forall_app; split; [exact V3R|];
                   apply Forall_forall; intros x Hx; exact (proj1 (Forall_forall _ _) LR x (Sub2 x Hx))) ].
      + apply incl_refl.
      + rewrite (KX9 22%bv ltac:(inlist)), (KEEP8 22%bv ltac:(inlist)), (KX7 22%bv ltac:(inlist)), (KX2 22%bv ltac:(inlist)). exact Q22.
      + rewrite (KX9 25%bv ltac:(inlist)), (KEEP8 25%bv ltac:(inlist)), (KX7 25%bv ltac:(inlist)), (KX2 25%bv ltac:(inlist)). exact Q25.
      + exists 12. split; [rewrite (KX9 18%bv ltac:(inlist)), (KEEP8 18%bv ltac:(inlist)), (KX7 18%bv ltac:(inlist)), (KX2 18%bv ltac:(inlist)); exact Q18 | lia].
      + exact K946.
      + left; lia.
      + exists (c_widx c - i_io I), 12. split; [exact K944 | exact K948].
      + exact MD9.
      + subst c8; reflexivity. + subst c8; reflexivity. + subst c8; reflexivity.
      + subst c8. unfold pi_nodes. cbn [set_v3A c_m1 c_m2 c_m3]. lia.
      + exact V38.
      + intros tt Htt. exact (go_operand_zw _ GOK 12 wv ll GX tt (Sub2 tt Htt)).
      + lia.
      + right. exact Ht36.
      + subst c8; reflexivity.
      + left; subst c8; reflexivity.
      + left; subst c8; reflexivity.
      + intros Hin. exact (RIDX 12 wv ll GX (Sub2 _ Hin)).
  Qed.
End U4E.
