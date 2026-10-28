(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Cells Step Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX HMLib HM AH0Spec0 AH0Facts AH0Base AH0Layout AH0K AH0Mem1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Mem0 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.None"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"].


Section Mem0.
  Context {hAR : arun}.
  Variable mem : word -> option byte.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Hypothesis HCOM : Forall (cell_ok ASEGS mem) (cells_common p).
  Hypothesis HDEF : me_def p mem.
  Variable STKHI : Z.
  Variable FOG : list (Z * Z).
  Variable TF : Z.
  Hypothesis STKHI_gt : SP p < STKHI.
  Hypothesis STKHI_47 : STKHI <= 2 ^ 47.
  (* [comment removed for export] *)
  Hypothesis HWIN : forall a : word, SP p <= bv_unsigned a < STKHI -> mem a <> None.
  Let bp := bp_of p STKHI FOG TF.
  Local Ltac pv := cbn; tauto.

  (* [comment removed for export] *)
  #[using="Type"] Lemma def_wr_at : ltac2:(CDefT.buildp (gd_tbl_AH0Mem0 ()) "Plo,$0.Pn,$0.P,Pa,(1.&40.)P,(2.(3.R3.(4.&40.R1.))(5.(4.&40.R1.)(6.R3.R2.)))(7.(8.(9.(1.&8.))A1.Vmem,R2.(:.(1.&8.))))P,(3.=R3.)P,(3.=R3.)P,(3.(6.R5.R4.)(;.+2.+40.))(<.$=.Vmem,R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros lo n H Hlo Hn Hhi. split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi.
    assert (U : bv_unsigned (wa (lo + i)) = lo + i) by (unfold wa; rewrite u_zbv; apply Z.mod_small; lia).
    pose proof (H (wa (lo + i)) ltac:(rewrite U; lia)) as D. unfold wview. destruct (mem (wa (lo + i))); [discriminate | exfalso; exact (D eq_refl)].
  Qed.

  #[using="HCN HCOM HDEF STKHI_gt STKHI_47 HWIN"] Theorem h0_hm_maps : hm_maps (L0_of bp) mem.
  Proof.
    pose proof HDEF as D. unfold me_def in D.
    ddestruct D as (_ & _ & _ & _ & Dfstk & _ & _ & Dtreg & Dthr & _ & _ & Dhigh & Dlow).
    revert Dfstk Dtreg Dthr Dhigh Dlow.
    rewrite ?(u_fstk p HCN), ?(u_treg p HCN), ?(u_thr p HCN). rewrite ?(u_wlit p) by lia. intros Dfstk Dtreg Dthr Dhigh Dlow.
    pose proof (proj1 (PG_range p HCN v_thr ltac:(pv))) as Gthr. pose proof (proj1 (PG_range p HCN v_treg ltac:(pv))) as Gtreg.
    pose proof (proj1 (PG_range p HCN v_fstk ltac:(pv))) as Gfstk. pose proof (r_s1 p HCN) as S1. pose proof (r_s2 p HCN) as S2.
    unfold hm_maps. cbn [l_stk_lo l_stk_hi l_T l_ctx l_ctxlen l_fs L0_of bp bp_of bp_sp0 bp_stkhi bp_T bp_ctx bp_fs]. fold (SP p).
    split; [apply def_wr_at; [exact Dlow | lia | lia | lia]|].
    split; [apply def_wr_at; [exact Dhigh | lia | lia | lia]|].
    split.
    { (* [comment removed for export] *)
      replace (STKHI - (SP p - 2 ^ 23)) with (2 ^ 23 + (STKHI - SP p)) by lia.
      apply (proj2 (wr_at_app asegs mem (SP p - 2 ^ 23) (2 ^ 23) (STKHI - SP p) ltac:(lia) ltac:(lia))). split.
      - me_wr (HF mem p HCOM) ((((#0x8000 * v_s1) + (#16 * v_s2)) .+ (-0x800000)))%tm X.
        pose proof (cwr_wr_at mem _ _ X) as W. revert W.
        match goal with |- wr_at _ _ ?a ?n -> _ => replace a with (SP p - 2 ^ 23); [replace n with (2 ^ 23); [intros W; exact W|]|] end.
        + rewrite u_zbv, Z.mod_small by lia. reflexivity.
        + unfold ABoot.PropExec.v_addi. rewrite u_zbv.
          match goal with |- _ = (bv_unsigned ?w + _) mod _ => change w with (winst p ((#0x8000 * v_s1) + (#16 * v_s2))%tm) end.
          rewrite (zev_exact p) by (cbn [zev]; lia). cbn [zev]. unfold SP. rewrite Z.mod_small; lia.
      - replace (SP p - 2 ^ 23 + 2 ^ 23) with (SP p) by lia. apply def_wr_at; [| unfold SP; lia | lia | lia]. intros a Ha. apply HWIN. lia. }
    split; [apply def_wr_at; [exact Dthr | lia | lia | lia]|].
    split; [apply def_wr_at; [exact Dtreg | lia | lia | lia]|].
    apply def_wr_at; [unfold kFakeBytes; exact Dfstk | lia | unfold kFakeBytes; lia | unfold kFakeBytes; lia].
  Qed.
End Mem0.
