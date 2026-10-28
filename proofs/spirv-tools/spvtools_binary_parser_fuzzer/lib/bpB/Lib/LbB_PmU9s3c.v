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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmVops LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmPD LbB_PmSL LbB_PmU3XK LbB_SnStmt LbB_PmU9c.

Ltac u9n_sc E R p HX10 :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCFlat (SA (EVar 10) ?o) (ELit ?l)) =>
      eapply (sc_flat_lit asegs _ _ _ _ (p + o) l);
      [unfold estart; cbn [a_base a_off]; change (edenot E (EVar 10)) with (PropExec.getr R 10%bv); rewrite HX10, u64_of_Z by lia; lia | apply elit_u; lia | lia | lia | lia]
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 10) (ELit ?o)) (ELit 3)) _) (ELit ?l)) =>
      eapply (sc_flat_lit asegs _ _ _ _ ((p + o) / 8 + SHBASE) l);
      [apply (estart_sh _ _ (p + o)); [change (edenot E (EAlu ALU_ADD (EVar 10) (ELit o))) with (alu64 ALU_ADD (PropExec.getr R 10%bv) (Z_to_bv 64 o)); rewrite HX10; apply SymExec.alu64_add_lit | lia]
      | apply elit_u; lia | lia | lia | lia]
  | |- _ => idtac
  end.

Definition RT_PM_U9_S3C_1 : list (reg * expr) := [(1%bv, ELit 998160); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EVar 32); (11%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (21%bv, EAlu ALU_ADD (EVar 33) (ELit 4528)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Ltac fixpc VIS pc :=
  lazymatch type of VIS with context [s_pc ?ss] => replace (s_pc ss) with pc in VIS by reflexivity end.
Section U9s3c.
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

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

  Lemma pm_u9_s3c : forall (w : pmwA H) s LB LBs m mo c msF R F fc (p v sel : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 20; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf21c8) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    PropExec.getr R 21%bv = Z_to_bv 64 (wa_ff w + 4528) ->
    PropExec.getr R 10%bv = Z_to_bv 64 p ->
    0 < p /\ p + 24 <= 2 ^ 47 ->
    p mod 16 = 0 ->
    addressable m p 24 ->
    fld ASEGS m (p + 20) 4 v ->
    0 < v < 2 ^ 32 ->
    rw_cells asegs m (wa_ff w + 4528) [C4 (Z_to_bv 64 sel)] ->
    0 <= sel < 2 ^ 32 ->
    sel <> v ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 ASN_ENTRY) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 20; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_ARM -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf3b10 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 8%bv = Z_to_bv 64 (wa_sp0 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_p w) -> PropExec.getr R1 11%bv = Z_to_bv 64 (wa_ff w + 112) -> PropExec.getr R1 12%bv = Z_to_bv 64 (sx32A v) -> m1 = m -> (forall rr : reg, In rr [22%bv; 25%bv; 18%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc p v sel Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 G21_0 HR10 Pb P16 AD FLD Hv CSEL Hsel SNV K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (xa_scal _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as (B1 & B2 & B3 & B4).
    assert (HT0' : regs_tbl w R (RT_ARM ++ [(21%bv, EAlu ALU_ADD (EVar 33) (ELit 4528))])).
    { apply regs_tbl_app; [exact HT0|]. apply Forall_cons; [| apply Forall_nil].
      cbn [fst snd]. rewrite G21_0. symmetry. eapply ev_add; [reflexivity | lia | lia]. }
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) m
                    [KRange (EVar 10) 1 (2 ^ 64); KAlign (EVar 10) 16;
                     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 10) (ELit 20)) (ELit 3)) SHBASE) 1 (ELit 0);
                     KWord (SA (EVar 10) 20) 4 (EVar 41); KWord (SA (EVar WV_FF) 4528) 4 (EVar 42)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) OK (env_world_seed H w R [Z_to_bv 64 v; Z_to_bv 64 sel])) as EF.
      apply Forall_cons.
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) (EVar 10)) with (PropExec.getr R 10%bv).
        rewrite HR10, Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia. lia. }
      apply Forall_cons.
      { cbn [kentry_ok]. change (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) (EVar 10)) with (PropExec.getr R 10%bv).
        rewrite HR10, Z_to_bv_unsigned, bv_wrap64_mod, (Z.mod_small p (2 ^ 64)) by lia. split; [lia | exact P16]. }
      apply Forall_cons.
      { apply (kshadow0 (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) m (EAlu ALU_ADD (EVar 10) (ELit 20)) (p + 20));
          [ apply (eq_trans (y := alu64 ALU_ADD (PropExec.getr R 10%bv) (Z_to_bv 64 20))); [reflexivity | rewrite HR10; apply w_add; lia]
          | lia
          | eapply (sh0_of_addressable m p 24 (p + 20)); [exact AD | change (8 * (24 / 8)) with 24; lia] ]. }
      apply Forall_cons.
      { apply (kword_of_fld (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) m (p + 20) 4 v (SA (EVar 10) 20) (EVar 41));
          [ exact FLD | lia
          | unfold estart; cbn [a_base a_off]; change (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) (EVar 10)) with (PropExec.getr R 10%bv);
            rewrite HR10, u64_of_Z by lia; lia
          | lia | cbn [Z.of_nat]; lia | reflexivity ]. }
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m (wa_ff w + 4528) _ 0%nat (C4 (Z_to_bv 64 sel)));
        [ exact CSEL | reflexivity | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity ]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0' [Z_to_bv 64 v; Z_to_bv 64 sel]
          [KRange (EVar 10) 1 (2 ^ 64); KAlign (EVar 10) 16;
           KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 10) (ELit 20)) (ELit 3)) SHBASE) 1 (ELit 0);
           KWord (SA (EVar 10) 20) 4 (EVar 41); KWord (SA (EVar WV_FF) 4528) 4 (EVar 42)] HK1 80%nat [ASN_ENTRY] [false; false] 43%N
          [3; 4; 20; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) TBL_EEF44 (@nil (Z * expr)) RT_PM_U9_S3C_1.
    { pose proof (shaddr_bounds (p + 20) ltac:(unfold AAPP_HI; lia)) as SHP.
      split_scs.
      - apply sc_br_of.
        rewrite (edenot_sext32 (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) 42 sel eq_refl ltac:(lia)).
        rewrite (edenot_sext32 (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) 41 v eq_refl ltac:(lia)).
        rewrite br_eq by (unfold sx32A, PrsGrammar.sx32; destruct (sel <? 2 ^ 31), (v <? 2 ^ 31); cbn beta iota; lia).
        apply Z.eqb_neq. unfold sx32A, PrsGrammar.sx32. destruct (sel <? 2 ^ 31), (v <? 2 ^ 31); cbn beta iota; lia.
      - apply sc_br_of.
        rewrite (edenot_sext32 (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) 41 v eq_refl ltac:(lia)).
        change (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) (ELit 0)) with (Z_to_bv 64 0).
        rewrite br_eq by (unfold sx32A, PrsGrammar.sx32; destruct (v <? 2 ^ 31); cbn beta iota; lia).
        apply Z.eqb_neq. unfold sx32A, PrsGrammar.sx32. destruct (v <? 2 ^ 31); cbn beta iota; lia.
      - u9n_sc (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) R p HR10.
      - u9n_sc (Eseed R (wenv_vals w ++ [Z_to_bv 64 v; Z_to_bv 64 sel])) R p HR10. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    fixpc VIS1 ASN_ENTRY.
    lazymatch type of X1 with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => change mm with m in VIS1, X1 end.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U9_S3C_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    eapply (K msF1 mo1 m R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_ARM HT1 ltac:(vm_compute; reflexivity)));
      [ rewrite (HR1 3%bv); exact G3_0
      | rewrite (HR1 4%bv); exact G4_0
      | rtf HT1 | rtf HT1 | rtf HT1 | rtf HT1 | rtf HT1
      | rewrite (HR1 12%bv); apply (eq_trans (y := Z_to_bv 64 (sx32A v))); [apply (edenot_sext32 _ 41 v); [reflexivity | lia] | reflexivity]
      | reflexivity
      | intros rr Hrr; cbn in Hrr; destruct Hrr as [<-|[<-|[<-|[]]]];
        [rewrite (HR1 22%bv) | rewrite (HR1 25%bv) | rewrite (HR1 18%bv)]; first [reflexivity | symmetry; rtf HT0] ].
  Qed.

End U9s3c.
