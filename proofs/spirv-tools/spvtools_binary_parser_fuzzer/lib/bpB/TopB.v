(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsConst BsIface BsDriverLaws RtB_Iface RtB_TR RtB_Td RtB_Own BS_InstDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_DRep LbB_DiagStmt LbB_PrsStmt LbB_TablStmt LbB_ContStmt LbB_StateStmt LbB_RtOwn LbB_TopDefs LbB_LibTR
  LbB_SnStmt LbB_PmS8T LbB_PiStmt LbB_HdrGet.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_Top LbB_WoTop LbB_PmAll LbB_PmWNT LbB_NPut LbB_Ex LbB_SnT LbB_DCtor LbB_PqS LbB_DtS LbB_DPd LbB_TablLeaves LbB_TablReg LbB_TablTF LbB_TablPT17
  LbB_ContV4 LbB_ContVo LbB_ContVot LbB_HStMva LbB_HStDt LbB_HdrGetP LbB_TdKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Drv Require Import DvB_FuzzStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Drv Require DvB_Top DvB_FzInvA.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA Require BaseAsanA.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Fixpoint zl_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && zl_eqb a' b'
  | _, _ => false
  end.
Lemma zl_eqb_eq : forall a b, zl_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] E; cbn in E; try discriminate; [reflexivity|].
  apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1. subst. f_equal. exact (IH b E2).
Qed.
Definition zll_mem (t : list Z) (L : list (list Z)) : bool := existsb (zl_eqb t) L.
Lemma zll_mem_In : forall t L, zll_mem t L = true -> In t L.
Proof. intros t L E. apply existsb_exists in E as (u & Hin & Eu). apply zl_eqb_eq in Eu. subst. exact Hin. Qed.
Definition z_mem (x : Z) (l : list Z) : bool := existsb (Z.eqb x) l.
Lemma z_mem_notin : forall x l, z_mem x l = false -> ~ In x l.
Proof.
  intros x l E Hin. assert (T : z_mem x l = true) by (apply existsb_exists; exists x; split; [exact Hin | apply Z.eqb_refl]).
  rewrite E in T. discriminate.
Qed.

Lemma TOP_PF_in_LIB_A :
  Forall (fun pp : Z * list Z => In (fst pp :: snd pp ++ [0xe8790]) LIB_A /\ ~ In (fst pp) (snd pp ++ [0xe8790])) (fz_pf FZP_A).
Proof.
  assert (C : forallb (fun pp : Z * list Z => zll_mem (fst pp :: snd pp ++ [0xe8790]) LIB_A && negb (z_mem (fst pp) (snd pp ++ [0xe8790]))) (fz_pf FZP_A) = true)
    by (vm_compute; reflexivity).
  apply Forall_forall. intros pp Hin. pose proof (proj1 (forallb_forall _ _) C pp Hin) as K. cbn beta in K.
  apply andb_true_iff in K as [K1 K2]. apply negb_true_iff in K2.
  split; [exact (zll_mem_In _ _ K1) | exact (z_mem_notin _ _ K2)].
Qed.

Lemma free_sites_traced : forall (rs : list Z) (TRS : list (list Z)),
  TRS = TR_bp LIB_A ->
  forallb (fun r => zll_mem [APC0_FREE; r] (TR_base ++ LIB_A) && negb (APC0_FREE =? r)) rs = true ->
  Forall (fun r : Z => trace_ok TRS APC0_FREE [r]) rs.
Proof.
  intros rs TRS -> C. apply Forall_forall. intros r Hin. pose proof (proj1 (forallb_forall _ _) C r Hin) as K. cbn beta in K.
  apply andb_true_iff in K as [K1 K2]. apply negb_true_iff in K2. apply Z.eqb_neq in K2.
  unfold TR_bp. apply trace_ok_of_full; [exact (zll_mem_In _ _ K1) |]. intros [E|[]]. apply K2. symmetry. exact E.
Qed.

Lemma po_tr_ok_A : forall H : asr, as_TR H = TR_bp LIB_A -> fz_tr_ok FZP_A H.
Proof.
  intros H E. cbn [fz_tr_ok FZP_A]. unfold po_tr_ok, pm_tr_ok. split.
  - apply (free_sites_traced PM_DEL_RAS (as_TR H) E). vm_compute. reflexivity.
  - apply (free_sites_traced (ST_MVA_DEL_RAS ++ ST_DTOR_DEL_RAS ++ RESV_DEL_RAS) (as_TR H) E). vm_compute. reflexivity.
Qed.

Section All.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Hypothesis HOWN : rt_own H.
  Hypothesis HTD : td_law H.

  Theorem parse_inst_A : parse_inst_stmtB H LINV_P5.
  Proof.
    exact (LbB_PmAll.parse_inst_okB_all H HHbp LINV_P5
      (fun m m' W L MU _ FW => LbB_TdKit.LINV_P5_munch_hi W m m' L MU FW)
      LINV_P5_cl (fun m L => proj1 L) HOWN ds_repA0
      (LbB_DRep.ds_laws_A LINV_P5 (fun m L => L))
      (LbB_DCtor.ds_ctor_okA H (proj1 HHbp))
      (LbB_PqS.put_cseq_okA H HHbp) (LbB_DtS.dtor_okA H HHbp)
      (LbB_NPut.put_u16_ok H HHbp HTD) (LbB_NPut.put_u32_ok H HHbp HTD) (LbB_NPut.put_u64_ok H HHbp HTD)
      (LbB_Ex.exhausted_A H HHbp HTD) (LbB_DPd.pdiag0_okA H HHbp) (LbB_DPd.pdiagE_okA H HHbp)
      (LbB_NPut.put_int_ok H HHbp HTD)
      LbB_TablLeaves.tabl_leaves_okA LbB_TablReg.fixword_okA
      (LbB_TablTF.take_first_okA H HHbp) (LbB_TablPT17.push_types_okA H HHbp)
      (LbB_ContV4.v4slow_f79f8 H (proj1 HHbp)) (LbB_ContV4.v4slow_f7c80 H (proj1 HHbp))
      (LbB_ContVo.vopnd_slow_ok H (proj1 HHbp)) (LbB_ContVot.votpb_ok H (proj1 HHbp))
      (LbB_SnT.setnum_okA H HHbp HTD)).
  Qed.

  Theorem binary_parse_A : binary_parse_stmtA H LINV_P5.
  Proof.
    exact (LbB_WoTop.binary_parse_okA H HHbp HOWN (LbB_HStMva.st_mva_ok H HHbp) (LbB_HStDt.st_dtor_ok H HHbp)
      parse_inst_A (LbB_HdrGetP.hdr_get_okA LbB_TablReg.fixword_okA) ds_repA0
      (LbB_DRep.ds_laws_A LINV_P5 (fun m L => L)) (LbB_DCtor.ds_ctor_okA H (proj1 HHbp))
      (LbB_PqS.put_cseq_okA H HHbp) (LbB_DtS.dtor_okA H HHbp)
      (LbB_NPut.put_u32_ok H HHbp HTD) (LbB_NPut.put_u64_ok H HHbp HTD)).
  Qed.

  Theorem fuzz_all : fuzz_stmt H FZP_A.
  Proof. exact (LbB_Top.fuzz_A H HHbp binary_parse_A). Qed.
End All.

  Theorem as_realizes_spec_B_final : BaseAsanA.as_realizes_spec_B.
  Proof.
    apply (DvB_Top.as_realizes_spec_B_of_lib FZP_A LIB_A).
    - intros HCEIL H HH DL OWN TD.
      exact (fuzz_all H HH OWN TD).
    - exact FZP_A_ok.
    - exact DvB_FzInvA.fzinv_A.
    - exact DvB_FzInvA.fzinv'_A.
    - exact LIB_A_len.
    - exact FZP_A_pcost.
    - exact TOP_PF_in_LIB_A.
    - exact po_tr_ok_A.
    - intros HC p. exact (@RtB_Own.inst_rt_own HC p).
  Qed.
