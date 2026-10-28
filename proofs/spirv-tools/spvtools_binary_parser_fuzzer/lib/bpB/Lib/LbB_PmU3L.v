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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmExit2 LbB_PmGlue LbB_PmU2K LbB_PmLH LbB_ContV4 LbB_TablStmt LbB_PmOL.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition RT_U3L_1 : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 0); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984));
   (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32);
   (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section U3L.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Definition cells_apart (X : list (Z * Z)) (cells : list (Z * Z)) : bool :=
    forallb (fun kn : Z * Z => forallb (fun on : Z * Z => (fst kn + snd kn <=? fst on) || (fst on + snd on <=? fst kn))%bool X) cells.

  Lemma cells_apart_in : forall X cells k n, cells_apart X cells = true -> In (k, n) cells ->
    forallb (fun on : Z * Z => (k + n <=? fst on) || (fst on + snd on <=? k))%bool X = true.
  Proof. intros X cells k n Hc Hin. exact (proj1 (forallb_forall _ _) Hc (k, n) Hin). Qed.

  Definition ICTX_CELLS : list (Z * Z) := [(10112, 8); (9120, 4); (9136, 2); (9050, 2); (9616, 8)].
  Lemma ictxA_ffkeepX : forall (w : pmwA H) m m' I X,
    ictxA H w m I -> ffkeepX w X m m' -> cells_apart X ICTX_CELLS = true -> ictxA H w m' I.
  Proof.
    intros w m m' I X (D1 & D2 & D3 & D4 & D5) K B.
    split; [| split; [| split; [| split]]];
      (eapply (ffkeepX_cell w X m m'); [exact K | eassumption | lia | cbn; lia | eapply (cells_apart_in X ICTX_CELLS); [exact B | cbn; tauto]]).
  Qed.

  Definition IFR_CELLS : list (Z * Z) := [(9040, 8); (9048, 2); (9052, 4); (9056, 4); (9060, 4); (9064, 8); (9072, 8)].
  Lemma ifrA_ffkeepX : forall (w : pmwA H) m m' X,
    ifrA H w m -> ffkeepX w X m m' -> cells_apart X IFR_CELLS = true -> ifrA H w m'.
  Proof.
    intros w m m' X (ext & tid & rid & D1 & D2 & D3 & D4 & D5 & D6 & D7 & R1 & R2 & R3) K B.
    exists ext, tid, rid.
    do 7 (split; [eapply (ffkeepX_cell w X m m'); [exact K | eassumption | lia | cbn; lia | eapply (cells_apart_in X IFR_CELLS); [exact B | cbn; tauto]]|]).
    split; [exact R1|]. split; [exact R2 | exact R3].
  Qed.

  Lemma mdef_app : forall m a n1 n2, mdef m a n1 -> mdef m (a + n1) n2 -> 0 <= n1 -> mdef m a (n1 + n2).
  Proof.
    intros m a n1 n2 D1 D2 Hn i Hi. destruct (Z.lt_ge_cases i n1); [apply D1; lia|].
    replace (a + i) with (a + n1 + (i - n1)) by lia. apply D2. lia.
  Qed.
  Lemma popnd_mdef : forall (w : pmwA H) m (v0 v1 v2 v3 v4 v5 : word), pmw_okA H w ->
    rw_cells asegs m (wa_ff w + 112) [C2 v0] -> rw_cells asegs m (wa_ff w + 114) [C2 v1] -> rw_cells asegs m (wa_ff w + 116) [C4 v2] ->
    rw_cells asegs m (wa_ff w + 120) [C4 v3] -> rw_cells asegs m (wa_ff w + 124) [C4 v4] -> rw_cells asegs m (wa_ff w + 128) [C4 v5] ->
    mdef m (wa_ff w + 112) 20.
  Proof.
    intros w m v0 v1 v2 v3 v4 v5 OK C0 C1 C2' C3 C4' C5.
    pose proof (pm_geom H w OK) as G. cbn zeta in G. destruct G as (_ & _ & _ & Q4 & _). unfold AFS_HDR in Q4.
    assert (D : forall k c, rw_cells asegs m (wa_ff w + k) [c] -> 0 <= k -> mdef m (wa_ff w + k) (Z.of_nat (csize c))).
    { intros k c C Hk. pose proof (mdef_of_rw_cells_hi m _ _ C ltac:(lia)) as D. cbn [cells_size] in D. rewrite Nat.add_0_r in D. exact D. }
    pose proof (D 112 _ C0 ltac:(lia)) as D0. pose proof (D 114 _ C1 ltac:(lia)) as D1.
    pose proof (D 116 _ C2' ltac:(lia)) as D2. pose proof (D 120 _ C3 ltac:(lia)) as D3.
    pose proof (D 124 _ C4' ltac:(lia)) as D4. pose proof (D 128 _ C5 ltac:(lia)) as D5.
    cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ] in D0, D1, D2, D3, D4, D5.
    change 20 with (2 + (2 + (4 + (4 + (4 + 4))))).
    apply mdef_app; [exact D0 | | lia]. replace (wa_ff w + 112 + 2) with (wa_ff w + 114) by lia.
    apply mdef_app; [exact D1 | | lia]. replace (wa_ff w + 114 + 2) with (wa_ff w + 116) by lia.
    apply mdef_app; [exact D2 | | lia]. replace (wa_ff w + 116 + 4) with (wa_ff w + 120) by lia.
    apply mdef_app; [exact D3 | | lia]. replace (wa_ff w + 120 + 4) with (wa_ff w + 124) by lia.
    apply mdef_app; [exact D4 | | lia]. replace (wa_ff w + 124 + 4) with (wa_ff w + 128) by lia.
    exact D5.
  Qed.

  Lemma popndA_ffkeepX : forall (w : pmwA H) m m' X off t, pmw_okA H w ->
    popndA H w m off t -> ffkeepX w X m m' -> cells_apart X [(112, 20)] = true ->
    popndA H w m' off t /\ mdef m' (wa_ff w + 112) 20.
  Proof.
    intros w m m' X off t OK (P0 & P1 & P2 & P3 & P4 & P5) K B.
    assert (KK : forall k cs, rw_cells asegs m (wa_ff w + k) cs -> 112 <= k -> k + Z.of_nat (cells_size cs) <= 132 -> rw_cells asegs m' (wa_ff w + k) cs).
    { intros k cs C Hk Hkn. apply (K k cs ltac:(lia) ltac:(lia)); [| exact C].
      apply Forall_forall. intros on Hin. pose proof (cells_apart_in X [(112, 20)] 112 20 B ltac:(left; reflexivity)) as Q.
      pose proof (proj1 (forallb_forall _ _) Q on Hin) as Q'. cbn beta in Q'.
      apply Bool.orb_true_iff in Q'. destruct Q' as [Q'|Q']; apply Z.leb_le in Q'; lia. }
    pose proof (KK 112 _ P0 ltac:(lia) ltac:(cbn; lia)) as K0. pose proof (KK 114 _ P1 ltac:(lia) ltac:(cbn; lia)) as K1.
    pose proof (KK 116 _ P2 ltac:(lia) ltac:(cbn; lia)) as K2. pose proof (KK 120 _ P3 ltac:(lia) ltac:(cbn; lia)) as K3.
    pose proof (KK 124 _ P4 ltac:(lia) ltac:(cbn; lia)) as K4. pose proof (KK 128 _ P5 ltac:(lia) ltac:(cbn; lia)) as K5.
    split; [exact (conj K0 (conj K1 (conj K2 (conj K3 (conj K4 K5)))))|].
    exact (popnd_mdef w m' _ _ _ _ _ _ OK K0 K1 K2 K3 K4 K5).
  Qed.

  Theorem arm_LITFLOAT_A : forall t, t = 10 -> arm_stmtA H LINV t 0xf26fc.
  Proof.
    intros t Ht w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q25 & Q18 & Q21 & PO & C176).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmxa_restrict H HHm LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pm_go HHm LINV_frame OK X0r KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 50%nat [OL_PUSHK] (@nil bool) 41%N
          S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_U3L_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc.
    assert (FK : ffkeepX w [(116, 12)] m M1).
    { pose proof (munch_sym (Eseed R (wenv_vals w ++ [])) m (s_log SSr) [(EVar 33%N, 116, 128)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc.
      cbn [num_wins map] in MUc. rewrite ?EFc in MUc.
      apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)).
      apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as FW. change (fsz PM_FCLASS) with 16384 in FW.
    assert (WRk : forall k n, 0 <= k -> k + n <= 16384 -> wr_at asegs m (wa_ff w + k) n).
    { intros k n Hk Hkn. destruct FW as (F1 & F2 & F3). split; [lia|]. split; [lia|]. intros i Hi.
      replace (wa_ff w + k + i) with (wa_ff w + (k + i)) by lia. apply F3. lia. }
    assert (C948 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 10)]).
    { subst M1. eapply (rw_cells_log_nth_sb _ m _ 2%nat (EVar 33%N) 116 4 (ELit 10));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFc; reflexivity | apply WRk; lia | reflexivity | exact Logic.I | reflexivity]. }
    assert (C952 : rw_cells asegs M1 (wa_ff w + 120) [C4 (Z_to_bv 64 3)]).
    { subst M1. eapply (rw_cells_log_nth_sb _ m _ 1%nat (EVar 33%N) 120 4 (ELit 3));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFc; reflexivity | apply WRk; lia | reflexivity | exact Logic.I | reflexivity]. }
    assert (C956 : rw_cells asegs M1 (wa_ff w + 124) [C4 (Z_to_bv 64 32)]).
    { subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat (EVar 33%N) 124 4 (ELit 32));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFc; reflexivity | apply WRk; lia | reflexivity | exact Logic.I | reflexivity]. }
    destruct PO as (P944 & P946 & P948 & P952 & P956 & P960).
    assert (K944 : rw_cells asegs M1 (wa_ff w + 112) [C2 (Z_to_bv 64 (c_widx c - i_io I))])
      by (eapply (ffkeepX_cell w _ m M1); [exact FK | exact P944 | lia | cbn; lia | vm_compute; reflexivity]).
    assert (K946 : rw_cells asegs M1 (wa_ff w + 114) [C2 (Z_to_bv 64 1)])
      by (eapply (ffkeepX_cell w _ m M1); [exact FK | exact P946 | lia | cbn; lia | vm_compute; reflexivity]).
    assert (K960 : rw_cells asegs M1 (wa_ff w + 128) [C4 (Z_to_bv 64 0)])
      by (eapply (ffkeepX_cell w _ m M1); [exact FK | exact P960 | lia | cbn; lia | vm_compute; reflexivity]).
    eapply (PK s LB LBs M1 mo1 c msF1 R1 F fc TBL_EEF44 1 []).
    - constructor; try assumption.
      + eapply (regs_tbl_sub w [] R1 _ RT_PUSHK HTx1). vm_compute; reflexivity.
      + rewrite (HR1 3%bv). exact G3_0.
      + rewrite (HR1 4%bv). exact G4_0.
      + eapply (ictxA_ffkeepX w m M1); [exact IC | exact FK | vm_compute; reflexivity].
      + eapply (ifrA_ffkeepX w m M1); [exact FR | exact FK | vm_compute; reflexivity].
    - apply incl_refl.
    - rewrite (HR1 22%bv). exact Q22.
    - rewrite (HR1 25%bv). exact Q25.
    - exists t. split; [rewrite (HR1 18%bv); exact Q18 | lia].
    - exact K946.
    - left; lia.
    - exists (c_widx c - i_io I), 10. split; [exact K944 | exact C948].
    - exact (popnd_mdef w M1 _ _ _ _ _ _ OK K944 K946 C948 C952 C956 K960).
    - reflexivity. - reflexivity. - reflexivity.
    - change (Z.min 1 1) with 1. lia.
    - rewrite app_nil_r. reflexivity.
    - exact PmZw.seed_free_nil.
    - rewrite PmZw.Zlen_nil. lia.
    - left; reflexivity.
    - reflexivity.
    - left; reflexivity.
    - left; reflexivity.
    - intros [].
  Qed.

  Theorem arm_LITINT_A : forall t, (t = 6 \/ t = 45) -> arm_stmtA H LINV t 0xf23f4.
  Proof.
    intros t Ht w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q22 & Q25 & Q18 & Q21 & PO & C176).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmxa_restrict H HHm LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    pm_go HHm LINV_frame OK X0r KR0 VIS0 RF0 HT0 (@nil word)
          (@nil kentry) 50%nat [OL_PUSHK] (@nil bool) 41%N
          S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_U3L_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
    replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity.
    pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc.
    assert (FK : ffkeepX w [(116, 12)] m M1).
    { pose proof (munch_sym (Eseed R (wenv_vals w ++ [])) m (s_log SSr) [(EVar 33%N, 116, 128)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc.
      cbn [num_wins map] in MUc. rewrite ?EFc in MUc.
      apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)).
      apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
    pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as FW. change (fsz PM_FCLASS) with 16384 in FW.
    assert (WRk : forall k n, 0 <= k -> k + n <= 16384 -> wr_at asegs m (wa_ff w + k) n).
    { intros k n Hk Hkn. destruct FW as (F1 & F2 & F3). split; [lia|]. split; [lia|]. intros i Hi.
      replace (wa_ff w + k + i) with (wa_ff w + (k + i)) by lia. apply F3. lia. }
    assert (C948 : rw_cells asegs M1 (wa_ff w + 116) [C4 (Z_to_bv 64 6)]).
    { subst M1. eapply (rw_cells_log_nth_sb _ m _ 2%nat (EVar 33%N) 116 4 (ELit 6));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFc; reflexivity | apply WRk; lia | reflexivity | exact Logic.I | reflexivity]. }
    assert (C952 : rw_cells asegs M1 (wa_ff w + 120) [C4 (Z_to_bv 64 1)]).
    { subst M1. eapply (rw_cells_log_nth_sb _ m _ 1%nat (EVar 33%N) 120 4 (ELit 1));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFc; reflexivity | apply WRk; lia | reflexivity | exact Logic.I | reflexivity]. }
    assert (C956 : rw_cells asegs M1 (wa_ff w + 124) [C4 (Z_to_bv 64 32)]).
    { subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat (EVar 33%N) 124 4 (ELit 32));
        [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFc; reflexivity | apply WRk; lia | reflexivity | exact Logic.I | reflexivity]. }
    destruct PO as (P944 & P946 & P948 & P952 & P956 & P960).
    assert (K944 : rw_cells asegs M1 (wa_ff w + 112) [C2 (Z_to_bv 64 (c_widx c - i_io I))])
      by (eapply (ffkeepX_cell w _ m M1); [exact FK | exact P944 | lia | cbn; lia | vm_compute; reflexivity]).
    assert (K946 : rw_cells asegs M1 (wa_ff w + 114) [C2 (Z_to_bv 64 1)])
      by (eapply (ffkeepX_cell w _ m M1); [exact FK | exact P946 | lia | cbn; lia | vm_compute; reflexivity]).
    assert (K960 : rw_cells asegs M1 (wa_ff w + 128) [C4 (Z_to_bv 64 0)])
      by (eapply (ffkeepX_cell w _ m M1); [exact FK | exact P960 | lia | cbn; lia | vm_compute; reflexivity]).
    eapply (PK s LB LBs M1 mo1 c msF1 R1 F fc TBL_EEF44 1 []).
    - constructor; try assumption.
      + eapply (regs_tbl_sub w [] R1 _ RT_PUSHK HTx1). vm_compute; reflexivity.
      + rewrite (HR1 3%bv). exact G3_0.
      + rewrite (HR1 4%bv). exact G4_0.
      + eapply (ictxA_ffkeepX w m M1); [exact IC | exact FK | vm_compute; reflexivity].
      + eapply (ifrA_ffkeepX w m M1); [exact FR | exact FK | vm_compute; reflexivity].
    - apply incl_refl.
    - rewrite (HR1 22%bv). exact Q22.
    - rewrite (HR1 25%bv). exact Q25.
    - exists t. split; [rewrite (HR1 18%bv); exact Q18 | lia].
    - exact K946.
    - left; lia.
    - exists (c_widx c - i_io I), 6. split; [exact K944 | exact C948].
    - exact (popnd_mdef w M1 _ _ _ _ _ _ OK K944 K946 C948 C952 C956 K960).
    - reflexivity. - reflexivity. - reflexivity.
    - change (Z.min 1 1) with 1. lia.
    - rewrite app_nil_r. reflexivity.
    - exact PmZw.seed_free_nil.
    - rewrite PmZw.Zlen_nil. lia.
    - left; reflexivity.
    - reflexivity.
    - left; reflexivity.
    - left; reflexivity.
    - intros [].
  Qed.

End U3L.
