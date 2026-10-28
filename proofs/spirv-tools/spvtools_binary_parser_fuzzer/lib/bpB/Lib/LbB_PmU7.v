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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmExit2 LbB_PmGlue LbB_PmU2K LbB_PmLH LbB_PmLeaf LbB_PmLeafW LbB_DiagStmt LbB_PmDS LbB_ContStmt LbB_PmVup LbB_PmWG LbB_PmWPT LbB_DStat LbB_TablStmt LbB_PmOL LbB_PmPD LbB_PmSL LbB_RtOwn LbB_PmU3L LbB_PmU3XK LbB_PmU7K LbB_PmU7a LbB_PmU7b LbB_PmU7dn LbB_PmU7dr LbB_PmU7db LbB_PiStmt.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac inl7 := cbn; repeat (first [left; reflexivity | right]).

Definition spec_len_okbA : bool :=
  forallb (fun op => match tg_op op with Some l => 3 <=? Z.of_nat (length l) | None => true end) SPECOPS.
Lemma spec_len_okbA_true : spec_len_okbA = true.
Proof.
  vm_compute. reflexivity.
Qed.
Lemma tg_spec_lenA : forall op l, g_specop TG op = true -> g_op TG op = Some l -> 3 <= Zlen l.
Proof.
  intros op l Hs Hg.
  destruct (proj1 (existsb_exists (Z.eqb op) SPECOPS) Hs) as (op' & Hin & Heq).
  apply Z.eqb_eq in Heq. subst op'.
  pose proof spec_len_okbA_true as OK. unfold spec_len_okbA in OK.
  rewrite forallb_forall in OK. specialize (OK op Hin).
  assert (Hg' : tg_op op = Some l) by exact Hg. rewrite Hg' in OK.
  apply Z.leb_le in OK. exact OK.
Qed.

Lemma in_skipnA : forall {T} n (l : list T) x, In x (skipn n l) -> In x l.
Proof.
  intros T n l x Hx. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact Hx.
Qed.
Lemma Zlen_skipn2 : forall (l : list Z), 2 <= Zlen l -> Zlen (skipn 2 l) = Zlen l - 2.
Proof.
  intros l Hl. unfold Zlen in *. rewrite length_skipn. lia.
Qed.

Lemma spanA_skip2 : forall p l, spanA p l -> 2 <= Zlen l -> spanA (p + 8) (skipn 2 l).
Proof.
  intros p l (R1 & R2 & R3 & R4) Hl.
  pose proof (Zlen_skipn2 l Hl) as EL.
  split; [lia|]. split; [rewrite EL; lia|]. split; [rewrite Zplus_mod, R3; reflexivity|].
  intros m TV. destruct (R4 m TV) as [RE RA]. split.
  - intros i Hi. rewrite EL in Hi. destruct (RE (i + 2) ltac:(lia)) as [Hr Hf].
    assert (EN : Znth i (skipn 2 l) = Znth (i + 2) l).
    { unfold Znth. rewrite nth_skipn. f_equal. lia. }
    rewrite EN. split; [exact Hr|]. replace (p + 8 + 4 * i) with (p + 4 * (i + 2)) by lia. exact Hf.
  - rewrite EL. eapply accessible_sub; [exact RA | lia | lia | lia].
Qed.

Section U7.
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
  Hypothesis HPDIAGE : pdiagE_stmtA H LINV ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis HPT : push_types_stmtA H.
  Hypothesis LINV_cl : forall m m', LINV m -> (forall a, 0 <= a < 2 ^ 64 -> aimg_client a -> m' (wa a) = m (wa a)) -> LINV m'.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.
  Hypothesis HOWN : rt_own H.

  Lemma HHe7 : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

  Theorem arm_SPEC_A : forall t, t = 8 -> arm_stmtA H LINV t 992260.
Proof.
    intros t Ht w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC. subst t.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q25 & Q18 & Q21 & PO & C176).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (pmxa_restrict H HHe7 LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pose proof (ipure_ranges I IP) as (IWC & IOP).
    pose proof (pm_bud_v3bound (wa_n w) c BUD) as CAPB.
    pose proof (wk_tr H w OK) as TR. unfold pm_tr_ok, PM_DEL_RAS in TR.
    assert (TRR : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF])
      by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_RREF) ltac:(inl7)).
    assert (TRC : trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF])
      by exact (proj1 (Forall_forall _ _) TR (v4_del_ra VOT_SLOW_CREF) ltac:(inl7)).
    pose proof TG_ok as GOK. pose proof tg_maxlen as TML.
    destruct (Z.lt_ge_cases wv (2 ^ 31)) as [Hsmall | Hbig].
    2: exact (pm_u7_dn H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU32 HTL LINV_relro HPDIAG0 w s LB LBs m mo c msF R F fc wv Q
                OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Q21 (conj Hbig (proj2 Hword)) BUD CK).
    assert (Hwv : 0 <= wv < 2 ^ 31) by lia.
    assert (Q21s : PropExec.getr R 21%bv = Z_to_bv 64 wv)
      by (rewrite Q21; f_equal; unfold sx32A, PrsGrammar.sx32; destruct (Z.ltb_spec wv (2 ^ 31)); lia).
    apply (pm_u7_1 H HHbp LINV LINV_frame w s LB LBs m mo c msF R F fc wv Q OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Q21s Hwv).
    intros msF1 mo1 m1 R1 KR1 VIS1 RF1 X1 HT1 G3_1 G4_1 Gra1 G2_1 G11_1 EM1 KX1. subst m1.
    eapply (@pm_leaf0 HCEIL H HHe7 LINV LINV_frame _ AT_SPEC_LOOKUP TL_STACK _ _ _ (@tla_spec_lookup HCEIL HTL) wv
              w s LB LBs m mo1 c _ TBL_EEF44 [] [] 0 msF1 R1 F fc _ Q);
      [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | exact G2_1 | exact Gra1 | reflexivity | lia
      | unfold TL_STACK; lia | reflexivity
      | split; [exact Hwv | split; [exact G11_1 | apply LINV_relro; eapply xa_linv; exact X1]]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF2 mo2 m2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 QF2.
    destruct QF2 as (r & Gr & Hr & Hspec).
    assert (G3_2 : PropExec.getr R2 3%bv = wa_gp w) by (rewrite (KEEP2 3%bv) by inl7; exact G3_1).
    assert (G4_2 : PropExec.getr R2 4%bv = wa_tp w) by (rewrite (KEEP2 4%bv) by inl7; exact G4_1).
    pose proof (regs_keep w [] R1 R2 RT_PM_U7_1_1 HT1 KEEP2) as HT2.
    assert (FK2 : ffkeepX w [] m m2).
    { apply (ffkeepX_munch w [] _ m m2 MU2 WM2).
      apply Forall_cons; [left; cbn [fst snd]; unfold TL_STACK; lia | apply Forall_nil]. }
    assert (C176_2 : rw_cells asegs m2 (wa_ff w + 176) [C4 (Z_to_bv 64 wv)]).
    { apply (FK2 176 [C4 (Z_to_bv 64 wv)] ltac:(lia) ltac:(cbn; lia) (Forall_nil _) C176). }
    assert (KX2 : forall rr, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R2 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP2 rr); [exact (KX1 rr Hrr)|].
      destruct Hrr as [<- | [<- | [<- | []]]]; inl7. }
    destruct (Z.eq_dec r 0) as [R0 | RN0].
    2: exact (pm_u7_dr H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HU32 HTL LINV_relro HPDIAG0 w s LB LBs m2 mo2 c msF2 R2 F fc r Q
                OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HT2 G3_2 G4_2 Gr (conj RN0 Hr) BUD CK).
    pose proof (proj1 Hspec R0) as HSP.
    pose proof (regs_tbl_app w [] R2 (rt_keep RT_PM_U7_1_1) [(10%bv, ELit 0)] HT2
                  ltac:(apply Forall_cons; [cbn [fst snd]; rewrite Gr, R0; reflexivity | apply Forall_nil])) as HTf2.
    apply (pm_u7_2 H HHbp LINV LINV_frame w s LB LBs m2 mo2 c msF2 R2 F fc wv Q OK X2 Htr Hbsz KR2 VIS2 RF2 FZ0 HTf2 G3_2 G4_2 C176_2 Hwv).
    intros msF3 mo3 m3 R3 KR3 VIS3 RF3 X3 HT3 G3_3 G4_3 Gra3 G2_3 G10_3 G11_3 CE3 FK3 KX3.
    pose proof (mdef_of_rw_cells m3 (wa_ff w + 4000) [C8 (Z_to_bv 64 0)] CE3 ltac:(unfold AFS_HDR in Q4; lia)) as MD3.
    eapply (@pm_lookup HCEIL H HHe7 LINV LINV_frame AT_LOOKUP_OPCODE 2%nat _ _ (@tla_lookup_opcode HCEIL HTL) wv 0 4000
              w s LB LBs m3 mo3 c _ TBL_EEF44 [] [] 0 msF3 R3 F fc _ Q []);
      [ exact OK | exact X3 | exact KR3 | exact VIS3 | exact RF3 | exact G2_3 | exact Gra3 | reflexivity | lia
      | exact G10_3 | lia | intros _; exact G11_3 | intros Hn3; discriminate Hn3
      | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | apply incl_refl | vm_compute; reflexivity | vm_compute; reflexivity
      | exact MD3 | ].
    intros msF4 mo4 m4 R4 r4 KR4 VIS4 RF4 X4 KEEP4 MU4 WM4 Gr4 Hr4 Hiff4 Hfound4 Hmiss4.
    assert (G3_4 : PropExec.getr R4 3%bv = wa_gp w) by (rewrite (KEEP4 3%bv) by inl7; exact G3_3).
    assert (G4_4 : PropExec.getr R4 4%bv = wa_tp w) by (rewrite (KEEP4 4%bv) by inl7; exact G4_3).
    pose proof (regs_keep w [] R3 R4 RT_PM_U7_2_1 HT3 KEEP4) as HT4.
    assert (FK4 : ffkeepX w [(4000, 8)] m3 m4).
    { apply (ffkeepX_munch w _ _ m3 m4 MU4 WM4). cbn [offs_wins map fst snd].
      apply Forall_cons; [left; cbn [fst snd]; unfold TL_STACK; lia |].
      apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    assert (KX4 : forall rr, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R4 rr = PropExec.getr R rr).
    { intros rr Hrr. rewrite (KEEP4 rr); [rewrite (KX3 rr Hrr); exact (KX2 rr Hrr)|].
      destruct Hrr as [<- | [<- | [<- | []]]]; inl7. }
    pose proof (ffkeepX_trans w [] [(4000, 8)] [(4000, 8)] m m2 m4 FK2
                  (ffkeepX_trans w [(4000, 8)] [(4000, 8)] [(4000, 8)] m2 m3 m4 FK3 FK4 (incl_refl _) (incl_refl _))
                  (incl_nil_l _) (incl_refl _)) as FK04.
    destruct (Z.eq_dec r4 0) as [R40 | R4N].
    2: exact (pm_u7_db H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE w s LB LBs m4 mo4 c msF4 R4 F fc r4 Q
                OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HT4 G3_4 G4_4 Gr4 (conj R4N Hr4) BUD CK).
    destruct (Hfound4 R40) as (d & CDd & HID).
    pose proof (regs_tbl_app w [] R4 (rt_keep RT_PM_U7_2_1) [(10%bv, ELit 0)] HT4
                  ltac:(apply Forall_cons; [cbn [fst snd]; rewrite Gr4, R40; reflexivity | apply Forall_nil])) as HTf4.
    apply (pm_u7_3 H HHbp LINV LINV_frame HTL w s LB LBs m4 mo4 c msF4 R4 F fc d wv Q OK X4 Htr Hbsz KR4 VIS4 RF4 FZ0 HTf4 G3_4 G4_4
             CDd HID (fun l Hl => tg_spec_lenA wv l HSP Hl)).
    intros msF7 mo7 m7 R7 sp_p ll KR7 VIS7 RF7 X7 HT7 G3_7 G4_7 Gra7 G2_7 G10_7 G11_7 CS7 GX SPN FK7 KX7.
    pose proof (tg_spec_lenA wv ll HSP GX) as L3.
    pose proof (go_len_op TG GOK wv ll GX) as LL. unfold HRep.Zlength in LL. change (Zlen ll <= g_maxlen TG) in LL.
    pose proof (Zlen_skipn2 ll ltac:(lia)) as EL2.
    pose proof (spanA_skip2 sp_p ll SPN ltac:(lia)) as SPN2.
    assert (CS7' : rw_cells asegs m7 (wa_ff w + 4496) [C8 (Z_to_bv 64 (sp_p + 8)); C8 (Z_to_bv 64 (Zlen (skipn 2 ll)))])
      by (rewrite EL2; exact CS7).
    assert (LR : Forall (fun t => 0 <= t < 2 ^ 31) (skipn 2 ll)).
    { apply Forall_forall. intros x Hx. eapply (go_range TG GOK ll x); [left; exists wv; exact GX | exact (in_skipnA 2 ll x Hx)]. }
    assert (BUDm : forall b'' xs'' cap'', 0 <= cap'' <= capmax (Zlen (t3b (c_v3 c))) (t3c (c_v3 c)) (Zlen (skipn 2 ll)) ->
                     pm_bud (wa_n w) (set_v3A c (b'', xs'', cap''))).
    { intros b'' xs'' cap'' Hc. apply pm_bud_v3cap; [exact BUD|]. unfold capmax in Hc. rewrite EL2 in Hc. lia. }
    assert (LL48 : Zlen (skipn 2 ll) <= 48) by (rewrite EL2; lia).
    eapply (pm_push_types H HHbp LINV LINV_cl LINV_relro HOWN HPT w s LB LBs m7 mo7 c _ TBL_EEF44 [] [] 0 msF7 R7 F fc _ 4496
              (sp_p + 8) (skipn 2 ll) Q);
      [ exact OK | exact X7 | vm_compute; reflexivity | vm_compute; reflexivity | exact KR7 | exact VIS7 | exact RF7 | exact Gra7 | reflexivity | lia
      | exact G2_7 | exact G4_7 | exact G10_7 | exact G11_7 | vm_compute; reflexivity | lia | lia | reflexivity
      | exact CS7' | exact SPN2 | exact LL48 | exact LR | exact BUDm | exact TRC | exact TRR | ].
    intros msF8 mo8 m8 R8 s8 LB8 LBs8 b8 cap8 KR8 VIS8 RF8 X8 KEEP8 BUD8 CAPR8 GROW8 CELLS8.
    set (c8 := set_v3A c (b8, push_types (skipn 2 ll) (t3b (c_v3 c)), cap8)) in *.
    assert (G3_8 : PropExec.getr R8 3%bv = wa_gp w) by (rewrite (KEEP8 3%bv) by inl7; exact G3_7).
    assert (G4_8 : PropExec.getr R8 4%bv = wa_tp w) by (rewrite (KEEP8 4%bv) by inl7; exact G4_7).
    pose proof (regs_tbl_sub w [] R8 _ RT_S7H (regs_keepK w [] R7 R8 RT_PM_U7_3_3 V4_KEPT HT7 KEEP8)
                  ltac:(vm_compute; reflexivity)) as HT8.
    pose proof (pm_bud_v3bound (wa_n w) c8 BUD8) as CAP8.
    assert (Hbsz8 : forall q k, In (q, k) (c_blocks c8) -> k <= 2 ^ 40).
    { intros q k Hin. destruct (c_blocks_v3_in c b8 _ cap8 q k Hin) as [Hin' | ->]; [exact (Hbsz q k Hin') | cbn in CAP8; lia]. }
    assert (FK8 : ffkeepX w [] m7 m8) by (intros k cs Hk Hkn _ C; exact (CELLS8 k cs Hk Hkn C)).
    apply (pm_u7_4 H HHbp LINV LINV_frame w s8 LB8 LBs8 m8 mo8 c8 msF8 R8 F fc Q OK X8 Htr Hbsz8 KR8 VIS8 RF8 FZ0 HT8 G3_8 G4_8).
    intros msF9 mo9 m9 R9 KR9 VIS9 RF9 X9 HT9 G3_9 G4_9 KX9 FK9.
    pose proof (ffkeepX_trans w [(4496, 16)] [] [(4496, 16)] m4 m7 m9 FK7
                  (ffkeepX_trans w [] [] [] m7 m8 m9 FK8 FK9 (incl_nil_l _) (incl_nil_l _)) (incl_refl _) (incl_nil_l _)) as FK49.
    pose proof (ffkeepX_trans w [(4000, 8)] [(4496, 16)] [(4000, 8); (4496, 16)] m m4 m9 FK04 FK49
                  ltac:(intros x [<- | []]; left; reflexivity) ltac:(intros x [<- | []]; right; left; reflexivity)) as FKall.
    destruct (popndA_ffkeepX H w m m9 [(4000, 8); (4496, 16)] (c_widx c - i_io I) 8 OK PO FKall eq_refl) as [PO9 MD9].
    destruct PO9 as (K112 & K114 & K116 & _).
    destruct (push_types_split (skipn 2 ll) (t3b (c_v3 c))) as (l2 & El2 & Ll2 & Sub2).
    apply (PK s8 LB8 LBs8 m9 mo9 c8 msF9 R9 F fc TBL_EEF44 1 l2).
    - constructor; [exact X9 | exact KR9 | exact VIS9 | exact RF9 | exact FZ0 | exact HT9 | exact G3_9 | exact G4_9 | exact Htr
                   | exact Hbsz8 | exact BUD8 | exact IP | exact (ictxA_ffkeepX H w m m9 I _ IC FKall eq_refl)
                   | exact (ifrA_ffkeepX H w m m9 _ FR FKall eq_refl) | exact Hic | exact Hend | exact Hw | exact MAC | ].
      change (t3b (c_v3 c8)) with (push_types (skipn 2 ll) (t3b (c_v3 c))). rewrite El2.
      apply Forall_app. split; [exact V3R|].
      apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) LR x (Sub2 x Hx)).
    - apply incl_refl.
    - rewrite (KX9 22%bv) by inl7. rewrite (KEEP8 22%bv) by inl7. rewrite (KX7 22%bv) by inl7.
      rewrite (KX4 22%bv) by inl7. exact Q22.
    - rewrite (KX9 25%bv) by inl7. rewrite (KEEP8 25%bv) by inl7. rewrite (KX7 25%bv) by inl7.
      rewrite (KX4 25%bv) by inl7. exact Q25.
    - exists 8. split; [| lia].
      rewrite (KX9 18%bv) by inl7. rewrite (KEEP8 18%bv) by inl7. rewrite (KX7 18%bv) by inl7.
      rewrite (KX4 18%bv) by inl7. exact Q18.
    - exact K114.
    - left; lia.
    - exists (c_widx c - i_io I), 8. split; [exact K112 | exact K116].
    - exact MD9.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - assert (EN : pi_nodes c8 = pi_nodes c) by reflexivity. rewrite EN. change (Z.min 1 1) with 1. lia.
    - exact El2.
    - intros tt Htt. exact (go_spec_zw TG GOK wv ll HSP GX tt (Sub2 tt Htt)).
    - lia.
    - right. unfold OT_RESULT_ID, OT_LITERAL_INTEGER, OT_LITERAL_STRING. lia.
    - reflexivity.
    - left; reflexivity.
    - left; reflexivity.
    - intros Hin. exact (tg_spec_rid wv ll HSP GX (Sub2 OT_RESULT_ID Hin)).
Qed.
End U7.
