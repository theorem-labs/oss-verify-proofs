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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt LbB_PmLeaf LbB_PmLH LbB_PmVops LbB_PmExit2 LbB_PmU2K LbB_PmOHK LbB_PmOL.

Definition RT_PM_OH1_1 : list (reg * expr) :=
  [(1%bv, ELit 988012); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 32) (ELit 264));
   (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 9136)); (22%bv, EAlu ALU_ADD (EVar 33) (ELit 10112)); (23%bv, EVar 32);
   (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (25%bv, EAlu ALU_ADD (EVar 32) (ELit 264)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Section OH1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_oh1 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (io iwc : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c S_INSTR TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 OL_HEAD) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_EEF44 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    0 <= io ->
    0 <= iwc < 2 ^ 16 ->
    io + iwc <= 2 ^ 62 ->
    c_widx c < io + iwc ->
    t3b (c_v3 c) <> [] ->
    rw_cells asegs m (wa_ff w + 10112) [C8 (Z_to_bv 64 io)] ->
    rw_cells asegs m (wa_ff w + 9136) [C2 (Z_to_bv 64 iwc)] ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_TAKE_FIRST) fc None m1 (seg_rom asegs) -> rfull R1 ->
       PMXA H LINV w s LB LBs m1 mo1 c S_INSTR TBL_EEF44 [] -> regs_tbl w R1 RT_EEF98 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w ->
       PropExec.getr R1 1%bv = Z_to_bv 64 0xf136c -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w + 264) ->
       PropExec.getr R1 22%bv = Z_to_bv 64 (wa_ff w + 10112) -> ffkeep w m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc io iwc Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 Hio Hiwc Hsum HLT HV3 CIO CIWC KC.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    pose proof (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as V3. unfold vec32 in V3.
    destruct V3 as (V0 & V24 & Vdef & Vlen & Vcap & Vb & Ve & Vc & Vel).
    assert (VB : 0 <= t3a (c_v3 c) /\ t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)) <= 2 ^ 63)
      by (destruct Vcap as [(Hb0 & Hc0) | (Hb1 & Hb2 & Hb3 & Hb4 & _)]; lia).
    assert (ZL : 0 < Zlen (t3b (c_v3 c))) by (unfold Zlen; destruct (t3b (c_v3 c)); [congruence | cbn [length]; lia]).
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 (c_widx c); Z_to_bv 64 (t3a (c_v3 c)); Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)))])) m
                    [KWord (SA (EVar WV_FF) 10112) 8 (EVar 41); KWord (SA (EVar WV_FF) 9136) 2 (EVar 42); KWord (SA (EVar WV_P) O_WIDX) 8 (EVar 43);
                     KWord (SA (EVar WV_P) 264) 8 (EVar 44); KWord (SA (EVar WV_P) 272) 8 (EVar 45)]).
    { pose proof (env_world_seed H w R [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 (c_widx c); Z_to_bv 64 (t3a (c_v3 c)); Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)))]) as HE.
      pose proof (ev_ff H w _ OK HE) as EF. pose proof (ev_p H w _ OK HE) as EP.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs _ m (wa_ff w + 10112) _ 0%nat (C8 (Z_to_bv 64 io))); [exact CIO | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs _ m (wa_ff w + 9136) _ 0%nat (C2 (Z_to_bv 64 iwc))); [exact CIWC | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity]. }
      apply Forall_cons.
      { pmk_entry H HHm w OK X0 HE. }
      apply Forall_cons.
      { eapply (kword_of_fld _ m (wa_p w + O_V3) 8 (t3a (c_v3 c))); [exact Vb | lia | unfold estart; cbn [a_base a_off]; rewrite EP; unfold O_V3; lia | unfold O_V3; lia | unfold O_V3; cbn [Z.of_nat]; lia | reflexivity]. }
      apply Forall_cons; [| apply Forall_nil].
      { eapply (kword_of_fld _ m (wa_p w + O_V3 + 8) 8 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)))); [exact Ve | lia | unfold estart; cbn [a_base a_off]; rewrite EP; unfold O_V3; lia | unfold O_V3; lia | unfold O_V3; cbn [Z.of_nat]; lia | reflexivity]. } }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 (c_widx c); Z_to_bv 64 (t3a (c_v3 c)); Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)))]
          [KWord (SA (EVar WV_FF) 10112) 8 (EVar 41); KWord (SA (EVar WV_FF) 9136) 2 (EVar 42); KWord (SA (EVar WV_P) O_WIDX) 8 (EVar 43);
           KWord (SA (EVar WV_P) 264) 8 (EVar 44); KWord (SA (EVar WV_P) 272) 8 (EVar 45)] HK1 200%nat [AT_TAKE_FIRST] [true; true] 46%N
          S_INSTR (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_OH1_1.
    { set (E := Eseed R (wenv_vals w ++ [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 (c_widx c); Z_to_bv 64 (t3a (c_v3 c)); Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)))])).
      assert (S41 : edenot E (EVar 41) = Z_to_bv 64 io) by reflexivity.
      assert (S42 : edenot E (EVar 42) = Z_to_bv 64 iwc) by reflexivity.
      assert (S43 : edenot E (EVar 43) = Z_to_bv 64 (c_widx c)) by reflexivity.
      assert (S44 : edenot E (EVar 44) = Z_to_bv 64 (t3a (c_v3 c))) by reflexivity.
      assert (S45 : edenot E (EVar 45) = Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)))) by reflexivity.
      assert (EZ : edenot E (EExt false 0 2 (EVar 42)) = Z_to_bv 64 iwc) by (apply edenot_zext16; [exact S42 | lia]).
      assert (EA : edenot E (EAlu ALU_ADD (EVar 41) (EExt false 0 2 (EVar 42))) = Z_to_bv 64 (io + iwc)).
      { change (alu64 ALU_ADD (edenot E (EVar 41)) (edenot E (EExt false 0 2 (EVar 42))) = Z_to_bv 64 (io + iwc)).
        rewrite S41, EZ. apply HLib.w_add; lia. }
      split_scs; cbn [sc_denot].
      all: first
        [ rewrite S44, S45, HLib.br_ne by lia; apply (proj2 (Bool.negb_true_iff _)); apply Z.eqb_neq; lia
        | rewrite S43, EA, HLib.br_ltu by lia; apply Z.ltb_lt; lia ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    assert (MM : mem_denot (Eseed R (wenv_vals w ++ [Z_to_bv 64 io; Z_to_bv 64 iwc; Z_to_bv 64 (c_widx c); Z_to_bv 64 (t3a (c_v3 c)); Z_to_bv 64 (t3a (c_v3 c) + 4 * Zlen (t3b (c_v3 c)))])) m (s_log SSr) = m)
      by reflexivity.
    rewrite MM in VIS1, X1.
    replace (s_pc SSr) with AT_TAKE_FIRST in VIS1 by reflexivity.
    assert (G3_1 : PropExec.getr R1 3%bv = wa_gp w) by (rewrite (HR1 3%bv); exact G3_0).
    assert (G4_1 : PropExec.getr R1 4%bv = wa_tp w) by (rewrite (HR1 4%bv); exact G4_0).
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_OH1_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    eapply (KC msF1 mo1 m R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_EEF98 HT1 ltac:(vm_compute; reflexivity)) G3_1 G4_1).
    all: first [ exact (ffkeep_refl w m) | rtf HT1 ].
  Qed.

End OH1.
