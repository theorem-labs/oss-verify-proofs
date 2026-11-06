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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HCommon.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsInv PmBase PmHyps PmLoopS1 PmBody1S1 PmZw PmODefsS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_MILB LbA_PrsStmt LbA_Own LbA_PmBase LbA_FSlots LbA_PmOwn LbA_PmCut LbA_PmTac LbA_PmHdr LbA_PmCall LbA_PmExit2 LbA_PmGlue LbA_PmU2K LbA_PmLH LbA_PmLeaf LbA_DiagStmt LbA_PmDS LbA_DStat LbA_TablStmt LbA_PmOL LbA_PmPD LbA_PmU3L LbA_PmU3Td LbA_PmU3Sd LbA_PmU3Dd.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition RT_U3T_1 : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 10432)); (18%bv, EVar 33); (19%bv, EVar 32);
   (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512));
   (22%bv, ELit 18446744073709551608); (25%bv, EAlu ALU_ADD (EVar 33) (ELit 944))].
Definition RT_U3S_1 : list (reg * expr) :=
  [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (18%bv, EVar 33); (19%bv, EVar 32);
   (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 10512));
   (22%bv, ELit 18446744073709551608); (25%bv, EAlu ALU_ADD (EVar 33) (ELit 944))].

Lemma sx32A_range : forall x, 0 <= x < 2 ^ 32 -> 0 <= sx32A x < 2 ^ 64 /\ (x <> 0 -> 1 <= sx32A x).
Proof. intros x Hx. unfold sx32A, PrsGrammar.sx32. destruct (Z.ltb_spec x (2 ^ 31)); lia. Qed.

Lemma w2le4_sx32A : forall x, 0 <= x < 2 ^ 32 -> word_to_le_bytes 4 (Z_to_bv 64 (sx32A x)) = word_to_le_bytes 4 (Z_to_bv 64 x).
Proof.
  intros x Hx. rewrite <- (swrap32_sx32A x Hx). change 4%nat with (N.to_nat 4). change 32%N with (8 * 4)%N.
  apply word_to_le_bytes_swrap. cbn; lia.
Qed.

Section U3T.
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
  Hypothesis HINT : put_int_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.
  Hypothesis LINV_relro : forall m, LINV m -> relro0 m.

  Lemma HHt : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma ifrA_set_tid : forall (w : pmwA H) m m' (tid' : Z),
    ifrA H w m -> ffkeepX w [(10432, 4)] m m' -> rw_cells asegs m' (wa_ff w + 10432) [C4 (Z_to_bv 64 tid')] -> 0 <= tid' < 2 ^ 32 ->
    ifrA H w m'.
  Proof.
    intros w m m' tid' (ext & tid & rid & D1 & D2 & D3 & D4 & D5 & D6 & D7 & R1 & R2 & R3) K C HT.
    exists ext, tid', rid.
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D1 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D2 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D3 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [exact C|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D5 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D6 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [eapply (ffkeepX_cell w _ m m'); [exact K | exact D7 | lia | cbn; lia | vm_compute; reflexivity]|].
    split; [exact R1|]. split; [exact HT | exact R3].
  Qed.

  Theorem arm_TYPEID_A : forall t, t = 2 -> arm_stmtA H LINV t 0xf03c4.
  Proof.
    intros t Ht w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q23 & Q24 & Q26 & Q27 & PO & C1108).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmxa_restrict H HHt LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    destruct (sx32A_range wv Hword) as [SXR SXP].
    destruct (Z.eq_dec wv 0) as [W0|Wn0].
    -
      assert (Q27z : PropExec.getr R 27%bv = Z_to_bv 64 0) by (rewrite Q27, W0; reflexivity).
      exact (pm_u3_tyd H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HPDIAGE w s LB LBs m mo c msF R F fc Q
               OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD Q27z CK).
    -
      specialize (SXP Wn0).
      assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [])) m [KRange (EVar 27) 1 (2 ^ 64)]).
      { apply Forall_cons; [| apply Forall_nil]. cbn [kentry_ok].
        change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 27)) with (PropExec.getr R 27%bv). rewrite Q27, u64_of_Z by lia. lia. }
      pm_goX HHt LINV_frame OK X0r KR0 VIS0 RF0 HT0 (@nil word)
            [KRange (EVar 27) 1 (2 ^ 64)] HK1 50%nat [OL_PUSHK] (@nil bool) 41%N
            S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_U3T_1.
      { split_scs. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M1 := mm) in * end.
      replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity.
      pose proof (ev_ff H w _ OK (env_world_seed H w R (@nil word))) as EFc. change (EVar WV_FF) with (EVar 33%N) in EFc.
      assert (FK : ffkeepX w [(10432, 4)] m M1).
      { pose proof (munch_sym (Eseed R (wenv_vals w ++ [])) m (s_log SSr) [(EVar 33%N, 10432, 10436)] Hlf1 ltac:(vm_compute; reflexivity)) as MUc.
        cbn [num_wins map] in MUc. rewrite ?EFc in MUc.
        apply (ffkeepX_munch w _ _ _ _ MUc (wmono_mem_denot _ _ _)).
        apply Forall_cons; [right; right; apply Exists_cons_hd; cbn [fst snd]; lia | apply Forall_nil]. }
      pose proof (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as FW. change (fsz PM_FCLASS) with 16384 in FW.
      assert (WRk : forall k n, 0 <= k -> k + n <= 16384 -> wr_at asegs m (wa_ff w + k) n).
      { intros k n Hk Hkn. destruct FW as (F1 & F2 & F3). split; [lia|]. split; [lia|]. intros i Hi.
        replace (wa_ff w + k + i) with (wa_ff w + (k + i)) by lia. apply F3. lia. }
      assert (C10432 : rw_cells asegs M1 (wa_ff w + 10432) [C4 (Z_to_bv 64 wv)]).
      { subst M1. eapply (rw_cells_log_nth_sb _ m _ 0%nat (EVar 33%N) 10432 4 (EVar 27%N));
          [exact Hlf1 | reflexivity | vm_compute; reflexivity | rewrite EFc; reflexivity | apply WRk; lia | reflexivity | exact Logic.I |].
        cbn [cbytes]. change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 27)) with (PropExec.getr R 27%bv). rewrite Q27.
        symmetry. apply w2le4_sx32A. exact Hword. }
      destruct (popndA_ffkeepX H w m M1 _ _ _ OK PO FK ltac:(vm_compute; reflexivity)) as [PO1 MD1].
      destruct PO1 as (K944 & K946 & K948 & _).
      eapply (PK s LB LBs M1 mo1 c msF1 R1 F fc TBL_EEF44 1 []).
      + constructor; try assumption.
        * eapply (regs_tbl_sub w [] R1 _ RT_PUSHK HTx1). vm_compute; reflexivity.
        * rewrite (HR1 3%bv). exact G3_0.
        * rewrite (HR1 4%bv). exact G4_0.
        * eapply (ictxA_ffkeepX H w m M1); [exact IC | exact FK | vm_compute; reflexivity].
        * eapply (ifrA_set_tid w m M1 wv); [exact FR | exact FK | exact C10432 | exact Hword].
      + apply incl_refl.
      + rewrite (HR1 23%bv). exact Q23.
      + rewrite (HR1 24%bv). exact Q24.
      + rewrite (HR1 26%bv). exact Q26.
      + exact K946.
      + left; lia.
      + exists (c_widx c - i_io I), t. split; [exact K944 | exact K948].
      + exact MD1.
      + reflexivity. + reflexivity. + reflexivity.
      + change (Z.min 1 1) with 1. lia.
      + rewrite app_nil_r. reflexivity.
      + exact PmZw.seed_free_nil.
      + rewrite PmZw.Zlen_nil. lia.
      + left; reflexivity.
      + reflexivity.
      + left; reflexivity.
      + left; reflexivity.
      + intros [].
  Qed.

  Theorem arm_SCOPE_A : forall t, (t = 4 \/ t = 5) -> arm_stmtA H LINV t 0xefbe8.
  Proof.
    intros t Ht w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q23 & Q24 & Q26 & Q27 & PO & C1108).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmxa_restrict H HHt LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    destruct (sx32A_range wv Hword) as [SXR SXP].
    destruct (Z.eq_dec wv 0) as [W0|Wn0].
    -
      assert (Q27z : PropExec.getr R 27%bv = Z_to_bv 64 0) by (rewrite Q27, W0; reflexivity).
      destruct Ht as [-> | ->].
      + exact (pm_u3_scd4 H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HTL LINV_relro HPDIAG0 w s LB LBs m mo c msF R F fc Q
                 OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD Q27z Q26 CK).
      + exact (pm_u3_scd5 H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HTL LINV_relro HPDIAG0 w s LB LBs m mo c msF R F fc Q
                 OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD Q27z Q26 CK).
    -
      specialize (SXP Wn0).
      assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [])) m [KRange (EVar 27) 1 (2 ^ 64)]).
      { apply Forall_cons; [| apply Forall_nil]. cbn [kentry_ok].
        change (edenot (Eseed R (wenv_vals w ++ [])) (EVar 27)) with (PropExec.getr R 27%bv). rewrite Q27, u64_of_Z by lia. lia. }
      pm_goX HHt LINV_frame OK X0r KR0 VIS0 RF0 HT0 (@nil word)
            [KRange (EVar 27) 1 (2 ^ 64)] HK1 50%nat [OL_PUSHK] (@nil bool) 41%N
            S_OPER (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_U3S_1.
      { split_scs. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      replace (mem_denot (Eseed R (wenv_vals w ++ [])) m (s_log SSr)) with m in * by reflexivity.
      replace (s_pc SSr) with OL_PUSHK in VIS1 by reflexivity.
      pose proof PO as (K944 & K946 & K948 & K952 & K956 & K960).
      eapply (PK s LB LBs m mo1 c msF1 R1 F fc TBL_EEF44 1 []).
      + constructor; try assumption.
        * eapply (regs_tbl_sub w [] R1 _ RT_PUSHK HTx1). vm_compute; reflexivity.
        * rewrite (HR1 3%bv). exact G3_0.
        * rewrite (HR1 4%bv). exact G4_0.
      + apply incl_refl.
      + rewrite (HR1 23%bv). exact Q23.
      + rewrite (HR1 24%bv). exact Q24.
      + rewrite (HR1 26%bv). exact Q26.
      + exact K946.
      + left; lia.
      + exists (c_widx c - i_io I), t. split; [exact K944 | exact K948].
      + exact (popnd_mdef H w m _ _ _ _ _ _ OK K944 K946 K948 K952 K956 K960).
      + reflexivity. + reflexivity. + reflexivity.
      + change (Z.min 1 1) with 1. lia.
      + rewrite app_nil_r. reflexivity.
      + exact PmZw.seed_free_nil.
      + rewrite PmZw.Zlen_nil. lia.
      + left; reflexivity.
      + reflexivity.
      + left; reflexivity.
      + left; reflexivity.
      + intros [].
  Qed.

  Theorem arm_DEFAULT_A : forall t, arm_stmtA H LINV t 0xf0930.
  Proof.
    intros t w s LB LBs m mo c msF R F fc I tbl wv Q OK HAE IT TC TK TN PK CK AACC.
    destruct HAE as (OB & Hw1 & Hw2 & Hn & Hv1 & Hv2 & Hlen & Ht31 & Hword & Q23 & Q24 & Q26 & Q27 & PO & C1108).
    destruct OB as [X0 KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Htr Hbsz BUD IP IC FR Hic Hend Hw MAC V3R].
    pose proof (pmxa_restrict H HHt LINV LINV_frame w _ _ _ _ _ _ _ _ _ _ _ TBL_EEF44 [] OK X0 IT (incl_refl _)) as X0r.
    exact (pm_u3_dfd H HHbp LINV LINV_frame ds_repA DSL HCSEQ HDTOR HINT HPDIAG0 w s LB LBs m mo c msF R F fc t Q
             OK X0r Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 BUD Q26 Ht31 CK).
  Qed.
End U3T.
