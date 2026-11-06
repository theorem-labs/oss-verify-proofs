(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsConst AsIface AsDriverLaws RtA_Iface RtA_TR RtA_Td RtA_Own AS_InstDefs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_DStat LbA_DRep LbA_DiagStmt LbA_PrsStmt LbA_TablStmt LbA_ContStmt LbA_StateStmt LbA_RtOwn LbA_TopDefs LbA_LibTR
  LbA_SnStmt LbA_PmS8T.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_Top LbA_WoTop LbA_PmAll LbA_PmWNT LbA_NPut LbA_Ex LbA_SnT LbA_DCtor LbA_PqS LbA_DtS LbA_DPd LbA_TablLeaves LbA_TablReg LbA_TablTF LbA_TablPT17
  LbA_ContV4 LbA_ContVo LbA_ContVot LbA_HStMva LbA_HStDt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Drv Require Import DvA_FuzzStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Drv Require DvA_Top DvA_FzInvA.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA Require BaseAsanA.
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
  Forall (fun pp : Z * list Z => In (fst pp :: snd pp ++ [0xe8b48]) LIB_A /\ ~ In (fst pp) (snd pp ++ [0xe8b48])) (fz_pf FZP_A).
Proof.
  assert (C : forallb (fun pp : Z * list Z => zll_mem (fst pp :: snd pp ++ [0xe8b48]) LIB_A && negb (z_mem (fst pp) (snd pp ++ [0xe8b48]))) (fz_pf FZP_A) = true)
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
  - apply (free_sites_traced (ST_MVA_DEL_RAS ++ ST_DTOR_DEL_RAS) (as_TR H) E). vm_compute. reflexivity.
Qed.

Section All.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Hypothesis HOWN : rt_own H.
  Hypothesis HTD : td_law H.

  Theorem parse_module_A : parse_module_stmtA H LINV_P5.
  Proof.
    eapply (LbA_PmAll.parse_module_okA_all H HHbp LINV_P5).
    - intros m m' W L MU _ FW. exact (LbA_TdKit.LINV_P5_munch_hi W m m' L MU FW).
    - exact LINV_P5_cl.
    - intros m L. exact (proj1 L).
    - exact HOWN.
    - exact (LbA_DRep.ds_laws_A LINV_P5 (fun m L => L)).
    - exact (LbA_DCtor.ds_ctor_okA H (proj1 HHbp)).
    - exact (LbA_PqS.put_cseq_okA H HHbp).
    - exact (LbA_DtS.dtor_okA H HHbp).
    - exact (LbA_NPut.put_u16_ok H HHbp HTD).
    - exact (LbA_NPut.put_u32_ok H HHbp HTD).
    - exact (LbA_NPut.put_u64_ok H HHbp HTD).
    - exact (LbA_Ex.exhausted_A H HHbp HTD).
    - exact (LbA_DPd.pdiag0_okA H HHbp).
    - exact (LbA_DPd.pdiagE_okA H HHbp).
    - exact (LbA_NPut.put_int_ok H HHbp HTD).
    - exact LbA_TablLeaves.tabl_leaves_okA.
    - exact LbA_TablReg.fixword_okA.
    - exact (LbA_TablTF.take_first_okA H HHbp).
    - exact (LbA_TablPT17.push_types_okA H HHbp).
    - exact (LbA_ContV4.v4slow_f79f8 H (proj1 HHbp)).
    - exact (LbA_ContV4.v4slow_f7c80 H (proj1 HHbp)).
    - exact (LbA_ContVo.vopnd_slow_ok H (proj1 HHbp)).
    - exact (LbA_ContVot.votpb_ok H (proj1 HHbp)).
    - exact (LbA_SnT.setnum_okA H HHbp HTD).
  Qed.

  Theorem binary_parse_A : binary_parse_stmtA H LINV_P5.
  Proof. exact (LbA_WoTop.binary_parse_okA H HHbp HOWN (LbA_HStMva.st_mva_ok H HHbp) (LbA_HStDt.st_dtor_ok H HHbp) parse_module_A). Qed.

  Theorem fuzz_all : fuzz_stmt H FZP_A.
  Proof. exact (LbA_Top.fuzz_A H HHbp binary_parse_A). Qed.
End All.

  Theorem as_realizes_spec_A_final : BaseAsanA.as_realizes_spec_A.
  Proof.
    apply (DvA_Top.as_realizes_spec_A_of_lib FZP_A LIB_A).
    - intros HCEIL H HH DL OWN TD.
      exact (fuzz_all H HH OWN TD).
    - exact FZP_A_ok.
    - exact DvA_FzInvA.fzinv_A.
    - exact DvA_FzInvA.fzinv'_A.
    - exact LIB_A_len.
    - exact FZP_A_pcost.
    - exact TOP_PF_in_LIB_A.
    - exact po_tr_ok_A.
    - intros HC p. exact (@RtA_Own.inst_rt_own HC p).
  Qed.
