(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr km.

(* [comment removed for export] *)
Module F0T_asmC.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "cons"; "pair"; "prod"; "nil"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "valuation"; "rl"; "rm"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "UStopLe"; "Wcan"; "AE_A"; "JL_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_internal_inited"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "J_free_tol_preT"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "offp"; "qcondCx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates"; "Pre_mid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_asmC"; "entry_pureC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls"; "cls_hyp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "L_free_tol"; "Pre_free_tolI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel"; "refillA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA GlueA GlueA2 SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ContractFreeNull.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require it.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_wf DepotCall.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ContractFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.CertFreeNullInit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.it.SpineMallocS5 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instok.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvQ8 F0A_drain.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQ1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.F0A_sem OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instok OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kg.F0A_asm OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvQ8 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_skelC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_asmC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma post_refill_T : ltac2:(tb__ "0|5|
S3S7S1eS1eA2A1M0G0S1bS16SbS3SeQ40A1A1S10S15S1S20R3R2S5S7S12S14A2M1S6S12S14S27S19A1M2S1aS29S1A1M3R7R6S2aR5Z18A2R4A5A4S8G1A1M4A3R1A6S15S1S20R4R3S5G1S6S12S14G2S1aG3R8R7R6R5A5A4G4A3R2A6F_;Fw;Ftp;Frho;FKc;FA;FXGL;FCST;").
Proof.
  intros CST XGL A Kc rho tp w (L & JL & rho' & tp' & Hin & Hag & Hsm & HJL).
  destruct Hin as [E|[]]. injection E as <- <-.
  exists (L_free_tol AE_A), (JL_free (AInvA segsA) CST XGL A Kc), rho', tp'.
  split; [left; reflexivity|]. split; [exact Hag|]. split; [exact Hsm|].
  destruct HJL as (A' & l1 & l2 & HA' & ELV & ELV' & EF & EV & EKm & EKf & EG & MK & HKc & CK).
  exists A', l1, l2. split; [exact HA'|]. split; [exact ELV|]. split; [exact ELV'|]. split; [exact EF|]. split; [exact EV|]. split; [exact EKm|].
  split; [exact EKf|]. split; [exact EG|]. split; [exact MK|]. split; [exact HKc|].
  intros c Hc Hne HF. apply (CK c Hc Hne). unfold class_fresh, refillA in *. cbn [aa_cls].
  rewrite nth_list_upd_other; [exact HF|]. change (Z.to_nat 24) with 24%nat. intros E. apply Hne. clear -E Hc. lia.
Qed.

Lemma entry_pure_C_T : ltac2:(tb__ "0|1|
S2S2S1bS16SbS3SeQ40M0A1A1S10S26R7SfG0SaR3PcA2A2SfG0SaR3PdA2A2A3S0S2S1cR6A1S4A3S22R8R7A2S11S1S1dR8R7A2S28S19A1R6R5R4A6S25RbS18U0A1S17RaR9R7A6F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Ff;Fkhi;").
Proof.
  intros khi f A Kc rho tp w HK Hii QC [_ [HJ _]]. destruct HJ as (HA & _ & HL & _ & _ & HB & _).
  split; [exact HL|]. split; [exact HB|]. split; [exists tp, (cfg_model (w_cfg w)); exact HA|].
  pose proof (cls_hyp_blk khi _ _ HK) as HCL.
  destruct (blkF_mem A rho tp _ _ _ HA HL HCL) as (t & T1 & T2 & T3 & T4 & _).
  destruct (junkF_ok_min A rho tp _ HA) as (jv & JM & Hjv).
  exists t, jv. split; [exact (conj (conj T1 (conj T2 (conj T3 T4))) Hjv)|]. split; [exact JM|].
  exact (instG_here_C A rho tp _ _ _ HA HL HCL Hii eq_refl eq_refl t (conj T1 (conj T2 (conj T3 T4))) jv Hjv f QC khi (Wcan 0) UStopLe HK).
Qed.

Lemma mid_vars_T : ltac2:(tb__ "0|0|
S0S2S24S21S13S23S18U0A1S17A2A1A2S4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma mid_repin_T : ltac2:(tb__ "0|3|
S1bS16SbSbS3SeQ40A1M0A1S10S1fS0S2S21R1A1S4A3S0G0SaR6R2A2SaR5R2A2A3F_;Fi;S1fS0S3SeQ8A1M1A1ScR6R1A2ScR5R1A2A3Fl;S0G0S9G1A1F_;SdR6A1SdR5A1A3S11S1S1dR9R8A2S23S18U0A1S17A2M2R7R5R4A6S11S1S1dRaR9A2G2R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho2';Frho2;FKc;FA;").
Proof.
  intros A Kc rho2 rho2' tp w Hw Hl Hm [(Hsm & HMI & Hwf & Hsh & Hhz) HJ].
  assert (Hag : agree_below NF rho2 rho2').
  { split; [|split; [exact Hl | intros a; rewrite Hm; reflexivity]]. intros i Hi. apply Hw. unfold offp.
    destruct (Pos.eqb_spec i 127) as [->|_]; [exfalso; unfold NF in Hi; lia|]. destruct (Pos.eqb_spec i 130) as [->|_]; [exfalso; unfold NF in Hi; lia | reflexivity]. }
  split.
  - split; [exact (smatch_agree_vars segsA offp rho2 rho2' _ _ Hw Hl Hm mid_vars_T Hsm)|]. split; [exact HMI|]. split; [exact Hwf|]. split; [|exact Hhz].
    unfold shadow_ok. cbn [Pre_mid ax_X]. apply Forall_nil.
  - exact (JTr_agree A Kc rho2 rho2' tp _ _ Hag HJ).
Qed.
End F0T_asmC.

(* [comment removed for export] *)
Module F0T_cLTCf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "list"; "nil"; "andb"; "Some"; "option"; "false"; "prod"; "negb"; "pair"; "length"; "app"; "orb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sobj"; "sv"; "sprop"; "swf"; "ss_lenient"; "ss_facts"; "ss_objs"; "SVar"; "sprop_below"; "sprop_eqb"; "SLit"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "entsF"; "leaves_at"; "BIGX"; "DEPE"; "MSE"; "PSE"; "sM_of"; "CASX"; "CD_of"; "F_typ"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "XD"; "XDr"; "casx"; "d3F"; "d4F"; "qvar"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_cLTCf"; "C4_LTCf"; "EC_LTCf"; "C2_LTCf"; "C3_LTCf"; "ED_LTCf"; "LT_LTCf"; "RR_LTCf"; "T1_LTCf"; "S1c_LTCf"; "TR_LTCf"; "l1_LTCf"; "sR_LTCf"; "CD_LTCf"; "EX_LTCf"; "Ems_LTCf"; "Eps_LTCf"; "P0_LTCf"; "TM_LTCf"; "TRs_LTCf"; "run3_LTCf"; "LH0_LTCf"; "RD_LTCf"; "RM_LTCf"; "TDr_LTCf"; "TM0_LTCf"; "l2_LTCf"; "l3_LTCf"; "l4_LTCf"; "run2_LTCf"; "run4_LTCf"; "run5_LTCf"; "run5d_LTCf"; "Ebg_LTCf"; "EfD_LTCf"; "Erf_LTCf"; "Erq2_LTCf"; "Erq_LTCf"; "KEPT1_LTCf"; "T0_LTCf"; "T2_LTCf"; "TD_LTCf"; "KEPT_LTCf"; "XR_LTCf"; "XS_LTCf"; "XW_LTCf"; "l1okb_LTCf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "K_i1"; "K_i2"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "UStopLe"; "AE_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "sDv_of"; "LOOPX"; "P0T_g"; "PreDv"; "atpc"; "FACTS_Tg"; "F_ext"; "PostDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cLTBf"; "TQ_LTBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG"; "dchkbT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_LTCf : list ulink := Wcan 0.
Definition st_LTCf : ustop := UStopLe.
Definition F0_LTCf : list sprop := FACTS_Tg false (VFC true).
Definition P0_LTCf : axst := ltac2:(tb__ "0|0|
S86SaS7cS7aS19S7bS6fS2A1A4S70S2A1A3").

Definition l1_LTCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_LTCf.
Definition LH0_LTCf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_LTCf) DUMMY).
Definition l2_LTCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_LTCf.
Definition LH1_LTCf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_LTCf) DUMMY).
Definition LT_LTCf : axst := Eval vm_compute in LT_ofg LH1_LTCf F0_LTCf.
Definition EX_LTCf : axst := Eval vm_compute in EX_ofg LH1_LTCf F0_LTCf.
Definition l3_LTCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_LTCf (SVar pFR)).
Definition l4_LTCf : list leafA := Eval vm_compute in runA FUELF [CASX] EX_LTCf.
Definition S1c_LTCf : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_LTCf DUMMY)) (F0_LTCf ++ F_ext).

Lemma RUN1_LTCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S82S4S11S2eS6S11A1A3A3S51A3S4bA3"). Proof. Time vmr. Qed.
Lemma RUN2f_LTCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S82S4S11S85S6S11A1A3A3S55A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN3f_LTCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S82S4S11S85S6S11A1A3A3Sb4S46S20S83A1A2A3S5bA3"). Proof. Time vmr. Qed.
Lemma RUN4f_LTCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2eS6S11A1A3S4eA3S5cA3"). Proof. Time vmr. Qed.

Definition l1okb_LTCf (l : list leafA) : bool := ltac2:(tb__ "0|1|
S7fS15S15S10Sb7S24S13S17R1A1M0A1A1S82A2S27G0S49A2A2LL;Vl;A3").
Lemma chk_LTCf : ltac2:(tb__ "0|a|
S0S3S7S7S7S7S7S7S7S7S7S7S7S7S7S7S7S7S7S7ScS5S15A1M0S3Lx;M1S4bS2S15G0SaLl0;Ll;M2X5x2A1ScG1S5aS2G2X5x2A1A2ScG1S5bS2G2X5x2A1A2ScG1S5cS2G2X5x2A1A2S6eS4bA1A2Sb6SeS15S88S82S4bA2A2U1A2A2S7fS15S15S10S27S17R1A1M3S46A2S27G3S4eA2A2LL;S5aA3A2S1cS13Sb5S46S20S83A1M4A2A1A1A2S25S18S13S46A1M5A1M6G4A2A2S7fS15Sb3S46S4eS83A3S5bA3A2S7fS15S15S27G3S49A2LL;S5cA3A2S78S77S18S13S51A1M7A1A2A2S78S77S18S13S55A1M8A1A2A2S78S77G6A2A2S78S77S18S13S4eA1M9A1A2A2ScS1dG7A1A1A2ScS1dG8A1A1A2ScS1dG5A1A1A2ScS1dG9A1A1A2S2A3").
Proof. Time vmr. Qed.
Lemma LH0eq_LTCf : ltac2:(tb__ "0|0|
S0S14S17S7dS15U0S88S82S4bA2S40A4A1S55A3"). Proof. vmr. Qed.

Lemma SIDE_LTCf : ltac2:(tb__ "0|0|
S0S3Sa8S51S46A2S2A3"). Proof. Time vmr. Qed.
Lemma OBND_LTCf : ltac2:(tb__ "0|1|
S0S5SbSbS1aS1aA2S1aA2M0A1S7cS19G0Sa7S1fS13S46A1A1A4S7cS19G0Sa7S1fS13S51A1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_LTCf : axst := C2_of S1c_LTCf.
Definition run2_LTCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S2aS6S11A1A3S43A3").
Definition EfD_LTCf : axst := leaf 0 run2_LTCf.
Definition ED_LTCf : axst := ED_of EfD_LTCf.
Definition RD_LTCf : list sobj := RDv_of ED_LTCf.
Definition TD_LTCf : axst := TDv_of ED_LTCf.
Definition TDr_LTCf : axst := TDr_of TD_LTCf.

Definition CD_LTCf : axst := ltac2:(tb__ "0|0|
S2fS58A1S14S3bR1S81S1bS1bScS80S1bS22R1A1S8aA3A1Lf;S1eS13R1A1A1A3A2TC;").
Definition run3_LTCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S2cS4S11S29S6S11A1A3A3S4dA3").
Definition Eps_LTCf : axst := leaf 0 run3_LTCf.
Definition Ebg_LTCf : axst := leaf 1 run3_LTCf.
Definition C3_LTCf : axst := C3_of Eps_LTCf.
Definition run4_LTCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S2bS6S11A1A3S44A3").
Definition Ems_LTCf : axst := leaf 0 run4_LTCf.
Definition C4_LTCf : axst := C4_of Ems_LTCf.
Definition RM_LTCf : list sobj := RM_of C4_LTCf.
Definition TM0_LTCf : axst := TM0_of C4_LTCf.
Definition TM_LTCf : axst := TM_of C4_LTCf.

Definition run5_LTCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S94S6S11A1A3S52A3").
Definition Erf_LTCf : axst := leaf 0 run5_LTCf.
Definition XR_LTCf : list axform := XRC Erf_LTCf.
Definition EC_LTCf : axst := EC_of Erf_LTCf.
Definition sR_LTCf : wsub := sR_of (E3_of Erf_LTCf).
Definition RR_LTCf : list sobj := RR_of EC_LTCf sR_LTCf.
Definition KEPT_LTCf : list sobj := KEPT_of EC_LTCf RR_LTCf.

Definition T0_LTCf : axst := ltac2:(tb__ "0|0|
S9cS42S4cS47A3").
Definition XS_LTCf : list axform := XS_of T0_LTCf.
Definition T1_LTCf : axst := T1_of T0_LTCf.
Definition KEPT1_LTCf : list sobj := KEPT1_of T1_LTCf.
Definition T2_LTCf : axst := T2_of T1_LTCf.
Definition TR_LTCf : axst := TR_of T1_LTCf.

Definition TRs_LTCf : axst := TRs_of TR_LTCf.
Definition run5d_LTCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S3fS6S11A1A3S53A3").
Definition Erq_LTCf : axst := leaf 0 run5d_LTCf.
Definition XW_LTCf : list axform := XW Erq_LTCf.
Definition Erq2_LTCf : axst := Erq2_of Erq_LTCf.

Lemma D2_LTCf : ltac2:(tb__ "0|4|
S0S9SbS5SbS1aS1aA2M0A1M1S5S1bA1M2A2M3A1S8cS13S49A1S13S43A1A2S8G3SdG1G2S4G0SdS1aS1aS37S3cA4S6G0A1A3S30A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_LTCf : ltac2:(tb__ "0|1|
S1S0S3S1cS13S43A1M0A1S2A3S1S0S12S18G0A1S18S13S49A1A1A3S0S3S1dG0A1SaA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_LTCf : ltac2:(tb__ "0|0|
S0S3S78S77S18S13S43A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_LTCf : ltac2:(tb__ "0|0|
S0S14S16S49S13S43A1A2S43A3"). Proof. vmr. Qed.
Lemma RUN2_LTCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2aS6S11A1A3S43A3S5dA3"). Proof. unfold run2_LTCf; reflexivity. Qed.
Lemma L2_LTCf : ltac2:(tb__ "0|0|
S1S0S3S28S5dS4S11S2aS6S11A1A3A2S2A3S0S14S3eU0S5dA2S62A3A2"). Proof. Time (split; [vmr | unfold EfD_LTCf; reflexivity]). Qed.
Lemma AXD_LTCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS62S35A2S8S14S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_LTCf : ltac2:(tb__ "0|1|
S0S9S5S19A1M0A1S8fS45S87S84S45A1A3S8G0S56A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_LTCf : ltac2:(tb__ "0|0|
S0S3S90S45S87S84S45A1S56S4S14S8bS6S14A1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_LTCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS69S36A2S8S14S58A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_LTCf : ltac2:(tb__ "0|0|
S0S3Sb2S58S4dA2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_LTCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2cS4S11S29S6S11A1A3A3S4dA3S54A3"). Proof. unfold run3_LTCf; reflexivity. Qed.
Lemma L3_LTCf : ltac2:(tb__ "0|0|
S1S0S3S28S54S4S11S2cS4S11S29S6S11A1A3A3A2S2A3S1S0S14S3eU0S54A2S50A3S0S14S3eU1S54A2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_LTCf | unfold Ebg_LTCf]; reflexivity]). Qed.
Lemma NX3_LTCf : ltac2:(tb__ "0|1|
S1S0S3S78S77S18S13S4dA1M0A1A2S2A3S0S3S1dG0A1SaA3A2"). Proof. split; vmr. Qed.

Lemma BGF_LTCf : ltac2:(tb__ "0|0|
S0S3S80S1bS22SacA1S1eS13S61A1A1A3S2A3"). Proof. vmr. Qed.
Lemma D3_LTCf : ltac2:(tb__ "0|3|
S0S9SbS5SbS1aS1aA2A1M0S5S1bA1M1A2M2A1S8cS13S50A1S13S44A1A2S8G2SdG0G1S38S6S1bA1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_LTCf : ltac2:(tb__ "0|0|
S0S14S16S50S13S44A1A2S44A3"). Proof. vmr. Qed.
Lemma NX3b_LTCf : ltac2:(tb__ "0|0|
S0S3S78S77S18S13S44A1A1A2S2A3"). Proof. vmr. Qed.
Lemma W3_LTCf : ltac2:(tb__ "0|1|
S1S0S3S1cS13S44A1M0A1S2A3S1S0S12S18G0A1S18S13S50A1A1A3S0S3S1dG0A1SaA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_LTCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2bS6S11A1A3S44A3S5eA3"). Proof. unfold run4_LTCf; reflexivity. Qed.
Lemma L4_LTCf : ltac2:(tb__ "0|0|
S1S0S3S28S5eS4S11S2bS6S11A1A3A2S2A3S0S14S3eU0S5eA2S4fA3A2"). Proof. Time (split; [vmr | unfold Ems_LTCf; reflexivity]). Qed.
Lemma D4_LTCf : ltac2:(tb__ "0|3|
S0S9SbS5SbS1aS1aA2A1M0S5S1bA1M1A2M2A1S8cS13S4fA1S13S41A1A2S8G2SdG0G1S39S6S1bA1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_LTCf : ltac2:(tb__ "0|0|
S0S14S16S4fS13S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_LTCf : ltac2:(tb__ "0|1|
S1S0S3S1cS13S41A1M0A1S2A3S1S0S12S18G0A1S18S13S4fA1A1A3S0S3S1dG0A1SaA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_LTCf : ltac2:(tb__ "0|1|
S0S9S5S19A1M0A1S8fS41S8dS2dS41A1A3S8G0S57A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_LTCf : ltac2:(tb__ "0|0|
S0S3S92S41S8dS2dS41A1S57S7cS15S14S17S8eA4A5S2A3"). Proof. Time vmr. Qed.
Lemma HTM_LTCf : ltac2:(tb__ "0|0|
S0S14S91S2dS41A1S8dS32S41S57A5S59A3"). Proof. unfold TM0_LTCf, TM0_of, RM_LTCf; reflexivity. Qed.
Lemma FBM_LTCf : ltac2:(tb__ "0|3|
S1S0S3S7fS1bS21S18S13S41A1M0A1M1A1S1eG0A1M2A3S2A3S1S0S3S7fS1bS21S18S13S59A1A1A1G2A3S2A3S0S3S78S77G1A2S2A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_LTCf : ltac2:(tb__ "0|0|
S0S14S96S59S1eS13S41A1A1A2S52A3"). Proof. vmr. Qed.

Lemma NX5_LTCf : ltac2:(tb__ "0|1|
S1S0S3S78S77S18S13S52A1M0A1A2S2A3S0S3S1dG0A1SaA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_LTCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S94S6S11A1A3S52A3S5fA3"). Proof. unfold run5_LTCf; reflexivity. Qed.
Lemma L5_LTCf : ltac2:(tb__ "0|0|
S1S0S3S28S5fS4S11S94S6S11A1A3A2S2A3S0S14S3eU0S5fA2S63A3A2"). Proof. Time (split; [vmr | unfold Erf_LTCf; reflexivity]). Qed.
Lemma AXR_LTCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS63S6bA2S8S14S42A2A3"). Proof. Time vmr. Qed.

Lemma HER_LTCf : ltac2:(tb__ "0|1|
S0S9S5S19A1M0A1S8fS42S93S4cA3S8G0S47A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_LTCf : ltac2:(tb__ "0|0|
S0S3S90S42S93S4cS47S4S14S95S6S14A1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma OBJS_LTCf : ltac2:(tb__ "0|0|
S0S5S19A1S1fS13S42A1A1SfS19S6aS47A3A3"). Proof. Time vmr. Qed.
Lemma HT0_LTCf : ltac2:(tb__ "0|0|
S0S14S67S96S91S4cS93S95S42S47A5S1eS13S42A1A1A2A3"). Proof. unfold T0_LTCf, T0_of; reflexivity. Qed.
Lemma HXS_LTCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS67S6cA2S8S14S48A2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_LTCf : ltac2:(tb__ "0|0|
S0S5S19A1S1fS13S48A1A1SfS19S66S4S19S31S4S19S7bS71A1S4S19S7bS72A1S6S19A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_LTCf : ltac2:(tb__ "0|0|
S0S14S68S16S48Sa9S13S48A1S66A2A2A3"). Proof. unfold T2_LTCf, T2_of, KEPT1_LTCf; reflexivity. Qed.
Lemma HTR_LTCf : ltac2:(tb__ "0|2|
S0S14S4aS98S68S4S7aS99S9bS18S13S48A1A1M0S79G0A1M1A3S6S7aA1A3S79G1A1A3A3"). Proof. unfold TR_LTCf, TR_of, T2_LTCf; reflexivity. Qed.
Lemma RCHK_LTCf : ltac2:(tb__ "0|0|
S0S3S9aU0S2S42S48S4aS4cS47S9bA8S2A3"). Proof. Time vmr. Qed.

Lemma HTRs_LTCf : ltac2:(tb__ "0|0|
S0S14S53S98S4aSadS18S13S4aA1A1A3A3"). Proof. unfold TRs_LTCf, TRs_of; reflexivity. Qed.
Lemma CCHK_LTCf : ltac2:(tb__ "0|0|
S0S3SaeU0S3S3aL_;S2S34S33X3x2S4aS53A4S2A3"). Proof. Time vmr. Qed.
Lemma RUN5d_LTCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S3fS6S11A1A3S53A3S60A3"). Proof. unfold run5d_LTCf; reflexivity. Qed.
Lemma L5d_LTCf : ltac2:(tb__ "0|0|
S1S0S3S28S60S4S11S3fS6S11A1A3A2S2A3S0S14S3eU0S60A2S65A3A2"). Proof. Time (split; [vmr | unfold Erq_LTCf; reflexivity]). Qed.
Lemma AXW_LTCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS65S6dA2S8S14S64A2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_LTCf : ltac2:(tb__ "0|0|
S0S3S27S64SafA2S2A3"). Proof. Time vmr. Qed.
Lemma DCHK_LTCf : ltac2:(tb__ "0|1|
S0S3Sb0U0M0S73S6fS2A1G0A2S45S69S84S45A1S56A6S2A3"). Proof. Time vmr. Qed.

Lemma Wa_LTCf : ltac2:(tb__ "0|0|
S0S3S1cS9dS74U0A1A1A1S2A3"). Proof. vmr. Qed.
Lemma Da_LTCf : ltac2:(tb__ "0|4|
S0S9SbS5SbS1aS1aA2M0A1M1S5S1bA1M2A2M3A1S8cS13Sb1S76A1A1S9dS74U0A1A1A2S8G3SdG1G2S4G0SdS1aS1aS20P18A1S23SabA1A4S6G0A1A3S6S1bA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_LTCf : ltac2:(tb__ "0|0|
S0S3S1cS9eS74U0A1S6fS2A1A2A1S2A3"). Proof. vmr. Qed.
Lemma Wc_LTCf : ltac2:(tb__ "0|0|
S0S3S1cS9fS74U0A1S6fS2A1A2A1S2A3"). Proof. vmr. Qed.
Lemma Wd_LTCf : ltac2:(tb__ "0|0|
S0S3S1cSa0S74U0A1S6fS2A1A2A1S2A3"). Proof. vmr. Qed.
Lemma Fb_LTCf : ltac2:(tb__ "0|0|
S0S3S7fS1bS21SaaA1S89SaS70S2A1A2A3S2A3"). Proof. vmr. Qed.
Lemma XI_LTCf : ltac2:(tb__ "0|3|
S0S9S14A1S7eSa1SaS74U0M0A1S6fS2A1M1S70S2A1M2A4S97G0SeS7aG1A2A2A2S8S14S86SaS7cS7aS19S7bG1A4G2A3A2A3"). Proof. vmr. Qed.

Definition PMID_LTCf : axst := ltac2:(tb__ "0|0|
Sa2SaS74U0A1S75S7cS7aS19S7bS6fS2A1A4S70S2A1A5").
Lemma Wbm_LTCf : ltac2:(tb__ "0|0|
S0S3S1cSa3S74U0A1S75S6fS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_LTCf : ltac2:(tb__ "0|0|
S0S3S1cSa4S74U0A1S75S6fS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_LTCf : ltac2:(tb__ "0|0|
S0S3S1cSa5S74U0A1S75S6fS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_LTCf : ltac2:(tb__ "0|4|
S0S9S14A1S7eSa6SaS74U0M0A1M1S75S6fS2A1M2S70S2A1M3A5S97G0SeS7aG2A2A2A2S8S14Sa2SaG1S75S7cS7aS19S7bG2A4G3A5A2A3"). Proof. vmr. Qed.
End F0T_cLTCf.

(* [comment removed for export] *)
Module F0T_cTCe.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "list"; "nil"; "false"; "andb"; "Some"; "option"; "prod"; "negb"; "pair"; "length"; "app"; "orb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sobj"; "sv"; "sprop"; "swf"; "ss_lenient"; "ss_facts"; "ss_objs"; "SVar"; "sprop_below"; "sprop_eqb"; "SLit"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "entsF"; "leaves_at"; "BIGX"; "DEPE"; "MSE"; "PSE"; "sM_of"; "CASX"; "CD_of"; "F_typ"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "XD"; "XDr"; "casx"; "d3F"; "d4F"; "qvar"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_cTCe"; "C4_TCe"; "EC_TCe"; "C2_TCe"; "C3_TCe"; "ED_TCe"; "LT_TCe"; "RR_TCe"; "T1_TCe"; "S1c_TCe"; "TR_TCe"; "l1_TCe"; "sR_TCe"; "CD_TCe"; "EX_TCe"; "Ems_TCe"; "Eps_TCe"; "P0_TCe"; "TM_TCe"; "TRs_TCe"; "run3_TCe"; "LH0_TCe"; "RD_TCe"; "RM_TCe"; "TDr_TCe"; "TM0_TCe"; "l2_TCe"; "l3_TCe"; "l4_TCe"; "run2_TCe"; "run4_TCe"; "run5_TCe"; "run5d_TCe"; "Ebg_TCe"; "EfD_TCe"; "Erf_TCe"; "Erq2_TCe"; "Erq_TCe"; "KEPT1_TCe"; "T0_TCe"; "T2_TCe"; "TD_TCe"; "KEPT_TCe"; "XR_TCe"; "XS_TCe"; "XW_TCe"; "l1okb_TCe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "K_i1"; "K_i2"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "UStopLe"; "AE_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "sDv_of"; "LOOPX"; "P0T_g"; "PreDv"; "atpc"; "FACTS_Tg"; "F_ext"; "PostDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBe"; "TQ_TBe"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG"; "dchkbT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_TCe : list ulink := Wcan 0.
Definition st_TCe : ustop := UStopLe.
Definition F0_TCe : list sprop := FACTS_Tg true (VFC false).
Definition P0_TCe : axst := ltac2:(tb__ "0|0|
S86S2S7cS7aS19S7bS6fS7A1A4S70S7A1A3").

Definition l1_TCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_TCe.
Definition LH0_TCe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_TCe) DUMMY).
Definition l2_TCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_TCe.
Definition LH1_TCe : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_TCe) DUMMY).
Definition LT_TCe : axst := Eval vm_compute in LT_ofg LH1_TCe F0_TCe.
Definition EX_TCe : axst := Eval vm_compute in EX_ofg LH1_TCe F0_TCe.
Definition l3_TCe : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_TCe (SVar pFR)).
Definition l4_TCe : list leafA := Eval vm_compute in runA FUELF [CASX] EX_TCe.
Definition S1c_TCe : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_TCe DUMMY)) (F0_TCe ++ F_ext).

Lemma RUN1_TCe : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S82S4S11S2eS6S11A1A3A3S51A3S4bA3"). Proof. Time vmr. Qed.
Lemma RUN2f_TCe : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S82S4S11S85S6S11A1A3A3S55A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN3f_TCe : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S82S4S11S85S6S11A1A3A3Sb4S46S20S83A1A2A3S5bA3"). Proof. Time vmr. Qed.
Lemma RUN4f_TCe : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2eS6S11A1A3S4eA3S5cA3"). Proof. Time vmr. Qed.

Definition l1okb_TCe (l : list leafA) : bool := ltac2:(tb__ "0|1|
S7fS15S15S10Sb7S24S13S17R1A1M0A1A1S82A2S27G0S49A2A2LL;Vl;A3").
Lemma chk_TCe : ltac2:(tb__ "0|a|
S0S3S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8S8ScS5S15A1M0S3Lx;M1S4bS2S15G0S7Ll0;Ll;M2X5x2A1ScG1S5aS2G2X5x2A1A2ScG1S5bS2G2X5x2A1A2ScG1S5cS2G2X5x2A1A2S6eS4bA1A2Sb6SeS15S88S82S4bA2A2U1A2A2S7fS15S15S10S27S17R1A1M3S46A2S27G3S4eA2A2LL;S5aA3A2S1cS13Sb5S46S20S83A1M4A2A1A1A2S25S18S13S46A1M5A1M6G4A2A2S7fS15Sb3S46S4eS83A3S5bA3A2S7fS15S15S27G3S49A2LL;S5cA3A2S78S77S18S13S51A1M7A1A2A2S78S77S18S13S55A1M8A1A2A2S78S77G6A2A2S78S77S18S13S4eA1M9A1A2A2ScS1dG7A1A1A2ScS1dG8A1A1A2ScS1dG5A1A1A2ScS1dG9A1A1A2S2A3").
Proof. Time vmr. Qed.
Lemma LH0eq_TCe : ltac2:(tb__ "0|0|
S0S14S17S7dS15U0S88S82S4bA2S40A4A1S55A3"). Proof. vmr. Qed.

Lemma SIDE_TCe : ltac2:(tb__ "0|0|
S0S3Sa8S51S46A2S2A3"). Proof. Time vmr. Qed.
Lemma OBND_TCe : ltac2:(tb__ "0|1|
S0S5SbSbS1aS1aA2S1aA2M0A1S7cS19G0Sa7S1fS13S46A1A1A4S7cS19G0Sa7S1fS13S51A1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_TCe : axst := C2_of S1c_TCe.
Definition run2_TCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S2aS6S11A1A3S43A3").
Definition EfD_TCe : axst := leaf 0 run2_TCe.
Definition ED_TCe : axst := ED_of EfD_TCe.
Definition RD_TCe : list sobj := RDv_of ED_TCe.
Definition TD_TCe : axst := TDv_of ED_TCe.
Definition TDr_TCe : axst := TDr_of TD_TCe.

Definition CD_TCe : axst := ltac2:(tb__ "0|0|
S2fS58A1S14S3bR1S81S1bS1bScS80S1bS22R1A1S8aA3A1Lf;S1eS13R1A1A1A3A2TC;").
Definition run3_TCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S2cS4S11S29S6S11A1A3A3S4dA3").
Definition Eps_TCe : axst := leaf 0 run3_TCe.
Definition Ebg_TCe : axst := leaf 1 run3_TCe.
Definition C3_TCe : axst := C3_of Eps_TCe.
Definition run4_TCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S2bS6S11A1A3S44A3").
Definition Ems_TCe : axst := leaf 0 run4_TCe.
Definition C4_TCe : axst := C4_of Ems_TCe.
Definition RM_TCe : list sobj := RM_of C4_TCe.
Definition TM0_TCe : axst := TM0_of C4_TCe.
Definition TM_TCe : axst := TM_of C4_TCe.

Definition run5_TCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S94S6S11A1A3S52A3").
Definition Erf_TCe : axst := leaf 0 run5_TCe.
Definition XR_TCe : list axform := XRC Erf_TCe.
Definition EC_TCe : axst := EC_of Erf_TCe.
Definition sR_TCe : wsub := sR_of (E3_of Erf_TCe).
Definition RR_TCe : list sobj := RR_of EC_TCe sR_TCe.
Definition KEPT_TCe : list sobj := KEPT_of EC_TCe RR_TCe.

Definition T0_TCe : axst := ltac2:(tb__ "0|0|
S9cS42S4cS47A3").
Definition XS_TCe : list axform := XS_of T0_TCe.
Definition T1_TCe : axst := T1_of T0_TCe.
Definition KEPT1_TCe : list sobj := KEPT1_of T1_TCe.
Definition T2_TCe : axst := T2_of T1_TCe.
Definition TR_TCe : axst := TR_of T1_TCe.

Definition TRs_TCe : axst := TRs_of TR_TCe.
Definition run5d_TCe : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S3fS6S11A1A3S53A3").
Definition Erq_TCe : axst := leaf 0 run5d_TCe.
Definition XW_TCe : list axform := XW Erq_TCe.
Definition Erq2_TCe : axst := Erq2_of Erq_TCe.

Lemma D2_TCe : ltac2:(tb__ "0|4|
S0SaSbS5SbS1aS1aA2M0A1M1S5S1bA1M2A2M3A1S8cS13S49A1S13S43A1A2S9G3SdG1G2S4G0SdS1aS1aS37S3cA4S6G0A1A3S30A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_TCe : ltac2:(tb__ "0|1|
S1S0S3S1cS13S43A1M0A1S2A3S1S0S12S18G0A1S18S13S49A1A1A3S0S3S1dG0A1S7A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_TCe : ltac2:(tb__ "0|0|
S0S3S78S77S18S13S43A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_TCe : ltac2:(tb__ "0|0|
S0S14S16S49S13S43A1A2S43A3"). Proof. vmr. Qed.
Lemma RUN2_TCe : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2aS6S11A1A3S43A3S5dA3"). Proof. unfold run2_TCe; reflexivity. Qed.
Lemma L2_TCe : ltac2:(tb__ "0|0|
S1S0S3S28S5dS4S11S2aS6S11A1A3A2S2A3S0S14S3eU0S5dA2S62A3A2"). Proof. Time (split; [vmr | unfold EfD_TCe; reflexivity]). Qed.
Lemma AXD_TCe : ltac2:(tb__ "0|0|
S0SaS14A1S7eS62S35A2S9S14S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_TCe : ltac2:(tb__ "0|1|
S0SaS5S19A1M0A1S8fS45S87S84S45A1A3S9G0S56A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_TCe : ltac2:(tb__ "0|0|
S0S3S90S45S87S84S45A1S56S4S14S8bS6S14A1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_TCe : ltac2:(tb__ "0|0|
S0SaS14A1S7eS69S36A2S9S14S58A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_TCe : ltac2:(tb__ "0|0|
S0S3Sb2S58S4dA2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_TCe : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2cS4S11S29S6S11A1A3A3S4dA3S54A3"). Proof. unfold run3_TCe; reflexivity. Qed.
Lemma L3_TCe : ltac2:(tb__ "0|0|
S1S0S3S28S54S4S11S2cS4S11S29S6S11A1A3A3A2S2A3S1S0S14S3eU0S54A2S50A3S0S14S3eU1S54A2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_TCe | unfold Ebg_TCe]; reflexivity]). Qed.
Lemma NX3_TCe : ltac2:(tb__ "0|1|
S1S0S3S78S77S18S13S4dA1M0A1A2S2A3S0S3S1dG0A1S7A3A2"). Proof. split; vmr. Qed.

Lemma BGF_TCe : ltac2:(tb__ "0|0|
S0S3S80S1bS22SacA1S1eS13S61A1A1A3S2A3"). Proof. vmr. Qed.
Lemma D3_TCe : ltac2:(tb__ "0|3|
S0SaSbS5SbS1aS1aA2A1M0S5S1bA1M1A2M2A1S8cS13S50A1S13S44A1A2S9G2SdG0G1S38S6S1bA1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_TCe : ltac2:(tb__ "0|0|
S0S14S16S50S13S44A1A2S44A3"). Proof. vmr. Qed.
Lemma NX3b_TCe : ltac2:(tb__ "0|0|
S0S3S78S77S18S13S44A1A1A2S2A3"). Proof. vmr. Qed.
Lemma W3_TCe : ltac2:(tb__ "0|1|
S1S0S3S1cS13S44A1M0A1S2A3S1S0S12S18G0A1S18S13S50A1A1A3S0S3S1dG0A1S7A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_TCe : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2bS6S11A1A3S44A3S5eA3"). Proof. unfold run4_TCe; reflexivity. Qed.
Lemma L4_TCe : ltac2:(tb__ "0|0|
S1S0S3S28S5eS4S11S2bS6S11A1A3A2S2A3S0S14S3eU0S5eA2S4fA3A2"). Proof. Time (split; [vmr | unfold Ems_TCe; reflexivity]). Qed.
Lemma D4_TCe : ltac2:(tb__ "0|3|
S0SaSbS5SbS1aS1aA2A1M0S5S1bA1M1A2M2A1S8cS13S4fA1S13S41A1A2S9G2SdG0G1S39S6S1bA1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_TCe : ltac2:(tb__ "0|0|
S0S14S16S4fS13S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_TCe : ltac2:(tb__ "0|1|
S1S0S3S1cS13S41A1M0A1S2A3S1S0S12S18G0A1S18S13S4fA1A1A3S0S3S1dG0A1S7A3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_TCe : ltac2:(tb__ "0|1|
S0SaS5S19A1M0A1S8fS41S8dS2dS41A1A3S9G0S57A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_TCe : ltac2:(tb__ "0|0|
S0S3S92S41S8dS2dS41A1S57S7cS15S14S17S8eA4A5S2A3"). Proof. Time vmr. Qed.
Lemma HTM_TCe : ltac2:(tb__ "0|0|
S0S14S91S2dS41A1S8dS32S41S57A5S59A3"). Proof. unfold TM0_TCe, TM0_of, RM_TCe; reflexivity. Qed.
Lemma FBM_TCe : ltac2:(tb__ "0|3|
S1S0S3S7fS1bS21S18S13S41A1M0A1M1A1S1eG0A1M2A3S2A3S1S0S3S7fS1bS21S18S13S59A1A1A1G2A3S2A3S0S3S78S77G1A2S2A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_TCe : ltac2:(tb__ "0|0|
S0S14S96S59S1eS13S41A1A1A2S52A3"). Proof. vmr. Qed.

Lemma NX5_TCe : ltac2:(tb__ "0|1|
S1S0S3S78S77S18S13S52A1M0A1A2S2A3S0S3S1dG0A1S7A3A2"). Proof. split; vmr. Qed.
Lemma RUN5_TCe : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S94S6S11A1A3S52A3S5fA3"). Proof. unfold run5_TCe; reflexivity. Qed.
Lemma L5_TCe : ltac2:(tb__ "0|0|
S1S0S3S28S5fS4S11S94S6S11A1A3A2S2A3S0S14S3eU0S5fA2S63A3A2"). Proof. Time (split; [vmr | unfold Erf_TCe; reflexivity]). Qed.
Lemma AXR_TCe : ltac2:(tb__ "0|0|
S0SaS14A1S7eS63S6bA2S9S14S42A2A3"). Proof. Time vmr. Qed.

Lemma HER_TCe : ltac2:(tb__ "0|1|
S0SaS5S19A1M0A1S8fS42S93S4cA3S9G0S47A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_TCe : ltac2:(tb__ "0|0|
S0S3S90S42S93S4cS47S4S14S95S6S14A1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma OBJS_TCe : ltac2:(tb__ "0|0|
S0S5S19A1S1fS13S42A1A1SfS19S6aS47A3A3"). Proof. Time vmr. Qed.
Lemma HT0_TCe : ltac2:(tb__ "0|0|
S0S14S67S96S91S4cS93S95S42S47A5S1eS13S42A1A1A2A3"). Proof. unfold T0_TCe, T0_of; reflexivity. Qed.
Lemma HXS_TCe : ltac2:(tb__ "0|0|
S0SaS14A1S7eS67S6cA2S9S14S48A2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_TCe : ltac2:(tb__ "0|0|
S0S5S19A1S1fS13S48A1A1SfS19S66S4S19S31S4S19S7bS71A1S4S19S7bS72A1S6S19A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_TCe : ltac2:(tb__ "0|0|
S0S14S68S16S48Sa9S13S48A1S66A2A2A3"). Proof. unfold T2_TCe, T2_of, KEPT1_TCe; reflexivity. Qed.
Lemma HTR_TCe : ltac2:(tb__ "0|2|
S0S14S4aS98S68S4S7aS99S9bS18S13S48A1A1M0S79G0A1M1A3S6S7aA1A3S79G1A1A3A3"). Proof. unfold TR_TCe, TR_of, T2_TCe; reflexivity. Qed.
Lemma RCHK_TCe : ltac2:(tb__ "0|0|
S0S3S9aU0S7S42S48S4aS4cS47S9bA8S2A3"). Proof. Time vmr. Qed.

Lemma HTRs_TCe : ltac2:(tb__ "0|0|
S0S14S53S98S4aSadS18S13S4aA1A1A3A3"). Proof. unfold TRs_TCe, TRs_of; reflexivity. Qed.
Lemma CCHK_TCe : ltac2:(tb__ "0|0|
S0S3SaeU0S3S3aL_;S7S34S33X3x2S4aS53A4S2A3"). Proof. Time vmr. Qed.
Lemma RUN5d_TCe : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S3fS6S11A1A3S53A3S60A3"). Proof. unfold run5d_TCe; reflexivity. Qed.
Lemma L5d_TCe : ltac2:(tb__ "0|0|
S1S0S3S28S60S4S11S3fS6S11A1A3A2S2A3S0S14S3eU0S60A2S65A3A2"). Proof. Time (split; [vmr | unfold Erq_TCe; reflexivity]). Qed.
Lemma AXW_TCe : ltac2:(tb__ "0|0|
S0SaS14A1S7eS65S6dA2S9S14S64A2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_TCe : ltac2:(tb__ "0|0|
S0S3S27S64SafA2S2A3"). Proof. Time vmr. Qed.
Lemma DCHK_TCe : ltac2:(tb__ "0|1|
S0S3Sb0U0M0S73S6fS7A1G0A2S45S69S84S45A1S56A6S2A3"). Proof. Time vmr. Qed.

Lemma Wa_TCe : ltac2:(tb__ "0|0|
S0S3S1cS9dS74U0A1A1A1S2A3"). Proof. vmr. Qed.
Lemma Da_TCe : ltac2:(tb__ "0|4|
S0SaSbS5SbS1aS1aA2M0A1M1S5S1bA1M2A2M3A1S8cS13Sb1S76A1A1S9dS74U0A1A1A2S9G3SdG1G2S4G0SdS1aS1aS20P18A1S23SabA1A4S6G0A1A3S6S1bA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_TCe : ltac2:(tb__ "0|0|
S0S3S1cS9eS74U0A1S6fS7A1A2A1S2A3"). Proof. vmr. Qed.
Lemma Wc_TCe : ltac2:(tb__ "0|0|
S0S3S1cS9fS74U0A1S6fS7A1A2A1S2A3"). Proof. vmr. Qed.
Lemma Wd_TCe : ltac2:(tb__ "0|0|
S0S3S1cSa0S74U0A1S6fS7A1A2A1S2A3"). Proof. vmr. Qed.
Lemma Fb_TCe : ltac2:(tb__ "0|0|
S0S3S7fS1bS21SaaA1S89S2S70S7A1A2A3S2A3"). Proof. vmr. Qed.
Lemma XI_TCe : ltac2:(tb__ "0|3|
S0SaS14A1S7eSa1S2S74U0M0A1S6fS7A1M1S70S7A1M2A4S97G0SeS7aG1A2A2A2S9S14S86S2S7cS7aS19S7bG1A4G2A3A2A3"). Proof. vmr. Qed.

Definition PMID_TCe : axst := ltac2:(tb__ "0|0|
Sa2S2S74U0A1S75S7cS7aS19S7bS6fS7A1A4S70S7A1A5").
Lemma Wbm_TCe : ltac2:(tb__ "0|0|
S0S3S1cSa3S74U0A1S75S6fS7A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_TCe : ltac2:(tb__ "0|0|
S0S3S1cSa4S74U0A1S75S6fS7A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_TCe : ltac2:(tb__ "0|0|
S0S3S1cSa5S74U0A1S75S6fS7A1A3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_TCe : ltac2:(tb__ "0|4|
S0SaS14A1S7eSa6S2S74U0M0A1M1S75S6fS7A1M2S70S7A1M3A5S97G0SeS7aG2A2A2A2S9S14Sa2S2G1S75S7cS7aS19S7bG2A4G3A5A2A3"). Proof. vmr. Qed.
End F0T_cTCe.

(* [comment removed for export] *)
Module F0T_cTCf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "list"; "nil"; "andb"; "Some"; "option"; "prod"; "negb"; "false"; "pair"; "length"; "app"; "orb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_setS"; "la_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sobj"; "sv"; "sprop"; "swf"; "ss_lenient"; "ss_facts"; "ss_objs"; "SVar"; "sprop_below"; "sprop_eqb"; "SLit"; "ss_pc"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states"; "FUELF"; "entsF"; "leaves_at"; "BIGX"; "DEPE"; "MSE"; "PSE"; "sM_of"; "CASX"; "CD_of"; "F_typ"; "O_stT2"; "PostMS"; "QBe"; "QBf"; "XD"; "XDr"; "casx"; "d3F"; "d4F"; "qvar"; "set_factsF"; "vH3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "runA"; "leaf"; "RETQ"; "DUMMY"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lt.F0T_cTCf"; "C4_TCf"; "EC_TCf"; "C2_TCf"; "C3_TCf"; "ED_TCf"; "LT_TCf"; "RR_TCf"; "T1_TCf"; "S1c_TCf"; "TR_TCf"; "l1_TCf"; "sR_TCf"; "CD_TCf"; "EX_TCf"; "Ems_TCf"; "Eps_TCf"; "P0_TCf"; "TM_TCf"; "TRs_TCf"; "run3_TCf"; "LH0_TCf"; "RD_TCf"; "RM_TCf"; "TDr_TCf"; "TM0_TCf"; "l2_TCf"; "l3_TCf"; "l4_TCf"; "run2_TCf"; "run4_TCf"; "run5_TCf"; "run5d_TCf"; "Ebg_TCf"; "EfD_TCf"; "Erf_TCf"; "Erq2_TCf"; "Erq_TCf"; "KEPT1_TCf"; "T0_TCf"; "T2_TCf"; "TD_TCf"; "KEPT_TCf"; "XR_TCf"; "XS_TCf"; "XW_TCf"; "l1okb_TCf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC"; "NVC"; "VFC"; "K_i1"; "K_i2"; "rd_okG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "UStopLe"; "AE_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@Stdlib.Lists.List"; "forallb"; "existsb"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states"; "LOOPH"; "pFR"; "sDv_of"; "LOOPX"; "P0T_g"; "PreDv"; "atpc"; "FACTS_Tg"; "F_ext"; "PostDv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset"; "Pre_memsetA"; "Posts_memsetA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkPA"; "import_postA"; "call_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS"; "Pre_rf"; "RF_ENT"; "L_rf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG"; "XIg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill"; "ax_carve"; "K_st2"; "rchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC"; "eFRc"; "T0_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG"; "sa_t"; "sb_t"; "sc_t"; "sd_t"; "se_t"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG"; "PMID_g"; "sb_mg"; "sc_mg"; "sd_mg"; "se_mg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node"; "obnd"; "side_chkb";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull"; "NW2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "TP_A"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno"; "big_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve"; "NV3"; "cchkb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0T_cTBf"; "TQ_TBf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG"; "dchkbT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol"; "Pre_free_tolI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib"; "entsI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk"; "eleaf_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue"; "carve_link_state"; "carve_plain_state"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import ObjXform ObjUnbase MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.CertFreeNull OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegD_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_instG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ke.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_rcarve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lr.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jf.RefillS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.F0A_cls OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.F0A_inst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ke.F0A_instokC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.F0A_bigno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jl.F0A_dzone OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kj.F0A_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lk.F0A_refill OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_rcarve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lr.F0A_statesC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ix.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require km.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ja.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.IfaceTol OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.UnwT_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.UnwT_chk OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.UnwT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ix.UnwT_node OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_instG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.km.F0T_depotG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.F0T_mstates OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.F0T_minst OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ja.F0T_minstG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.

Definition W_TCf : list ulink := Wcan 0.
Definition st_TCf : ustop := UStopLe.
Definition F0_TCf : list sprop := FACTS_Tg true (VFC true).
Definition P0_TCf : axst := ltac2:(tb__ "0|0|
S86S2S7cS7aS19S7bS6fS2A1A4S70S2A1A3").

Definition l1_TCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; CASX] P0_TCf.
Definition LH0_TCf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l1_TCf) DUMMY).
Definition l2_TCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] LH0_TCf.
Definition LH1_TCf : axst := Eval vm_compute in la_state (nth 0 (atpc LOOPH l2_TCf) DUMMY).
Definition LT_TCf : axst := Eval vm_compute in LT_ofg LH1_TCf F0_TCf.
Definition EX_TCf : axst := Eval vm_compute in EX_ofg LH1_TCf F0_TCf.
Definition l3_TCf : list leafA := Eval vm_compute in runA FUELF [LOOPH; LOOPX] (carve_link_state LT_TCf (SVar pFR)).
Definition l4_TCf : list leafA := Eval vm_compute in runA FUELF [CASX] EX_TCf.
Definition S1c_TCf : axst := Eval vm_compute in S1cT_of (la_state (nth 0 l4_TCf DUMMY)) (F0_TCf ++ F_ext).

Lemma RUN1_TCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S82S4S11S2eS6S11A1A3A3S51A3S4bA3"). Proof. Time vmr. Qed.
Lemma RUN2f_TCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S82S4S11S85S6S11A1A3A3S55A3S5aA3"). Proof. Time vmr. Qed.
Lemma RUN3f_TCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S82S4S11S85S6S11A1A3A3Sb4S46S20S83A1A2A3S5bA3"). Proof. Time vmr. Qed.
Lemma RUN4f_TCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2eS6S11A1A3S4eA3S5cA3"). Proof. Time vmr. Qed.

Definition l1okb_TCf (l : list leafA) : bool := ltac2:(tb__ "0|1|
S7fS15S15S10Sb7S24S13S17R1A1M0A1A1S82A2S27G0S49A2A2LL;Vl;A3").
Lemma chk_TCf : ltac2:(tb__ "0|a|
S0S3S7S7S7S7S7S7S7S7S7S7S7S7S7S7S7S7S7S7SbS5S15A1M0S3Lx;M1S4bS2S15G0ScLl0;Ll;M2X5x2A1SbG1S5aS2G2X5x2A1A2SbG1S5bS2G2X5x2A1A2SbG1S5cS2G2X5x2A1A2S6eS4bA1A2Sb6SeS15S88S82S4bA2A2U1A2A2S7fS15S15S10S27S17R1A1M3S46A2S27G3S4eA2A2LL;S5aA3A2S1cS13Sb5S46S20S83A1M4A2A1A1A2S25S18S13S46A1M5A1M6G4A2A2S7fS15Sb3S46S4eS83A3S5bA3A2S7fS15S15S27G3S49A2LL;S5cA3A2S78S77S18S13S51A1M7A1A2A2S78S77S18S13S55A1M8A1A2A2S78S77G6A2A2S78S77S18S13S4eA1M9A1A2A2SbS1dG7A1A1A2SbS1dG8A1A1A2SbS1dG5A1A1A2SbS1dG9A1A1A2S2A3").
Proof. Time vmr. Qed.
Lemma LH0eq_TCf : ltac2:(tb__ "0|0|
S0S14S17S7dS15U0S88S82S4bA2S40A4A1S55A3"). Proof. vmr. Qed.

Lemma SIDE_TCf : ltac2:(tb__ "0|0|
S0S3Sa8S51S46A2S2A3"). Proof. Time vmr. Qed.
Lemma OBND_TCf : ltac2:(tb__ "0|1|
S0S5SaSaS1aS1aA2S1aA2M0A1S7cS19G0Sa7S1fS13S46A1A1A4S7cS19G0Sa7S1fS13S51A1A1A4A3"). Proof. Time vmr. Qed.

Definition C2_TCf : axst := C2_of S1c_TCf.
Definition run2_TCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S2aS6S11A1A3S43A3").
Definition EfD_TCf : axst := leaf 0 run2_TCf.
Definition ED_TCf : axst := ED_of EfD_TCf.
Definition RD_TCf : list sobj := RDv_of ED_TCf.
Definition TD_TCf : axst := TDv_of ED_TCf.
Definition TDr_TCf : axst := TDr_of TD_TCf.

Definition CD_TCf : axst := ltac2:(tb__ "0|0|
S2fS58A1S14S3bR1S81S1bS1bSbS80S1bS22R1A1S8aA3A1Lf;S1eS13R1A1A1A3A2TC;").
Definition run3_TCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S2cS4S11S29S6S11A1A3A3S4dA3").
Definition Eps_TCf : axst := leaf 0 run3_TCf.
Definition Ebg_TCf : axst := leaf 1 run3_TCf.
Definition C3_TCf : axst := C3_of Eps_TCf.
Definition run4_TCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S2bS6S11A1A3S44A3").
Definition Ems_TCf : axst := leaf 0 run4_TCf.
Definition C4_TCf : axst := C4_of Ems_TCf.
Definition RM_TCf : list sobj := RM_of C4_TCf.
Definition TM0_TCf : axst := TM0_of C4_TCf.
Definition TM_TCf : axst := TM_of C4_TCf.

Definition run5_TCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S94S6S11A1A3S52A3").
Definition Erf_TCf : axst := leaf 0 run5_TCf.
Definition XR_TCf : list axform := XRC Erf_TCf.
Definition EC_TCf : axst := EC_of Erf_TCf.
Definition sR_TCf : wsub := sR_of (E3_of Erf_TCf).
Definition RR_TCf : list sobj := RR_of EC_TCf sR_TCf.
Definition KEPT_TCf : list sobj := KEPT_of EC_TCf RR_TCf.

Definition T0_TCf : axst := ltac2:(tb__ "0|0|
S9cS42S4cS47A3").
Definition XS_TCf : list axform := XS_of T0_TCf.
Definition T1_TCf : axst := T1_of T0_TCf.
Definition KEPT1_TCf : list sobj := KEPT1_of T1_TCf.
Definition T2_TCf : axst := T2_of T1_TCf.
Definition TR_TCf : axst := TR_of T1_TCf.

Definition TRs_TCf : axst := TRs_of TR_TCf.
Definition run5d_TCf : list leafA := ltac2:(tb__ "0|0|
S3dS26S4S11S3fS6S11A1A3S53A3").
Definition Erq_TCf : axst := leaf 0 run5d_TCf.
Definition XW_TCf : list axform := XW Erq_TCf.
Definition Erq2_TCf : axst := Erq2_of Erq_TCf.

Lemma D2_TCf : ltac2:(tb__ "0|4|
S0S9SaS5SaS1aS1aA2M0A1M1S5S1bA1M2A2M3A1S8cS13S49A1S13S43A1A2S8G3SdG1G2S4G0SdS1aS1aS37S3cA4S6G0A1A3S30A4A2A3"). Proof. Time vmr. Qed.
Lemma W2_TCf : ltac2:(tb__ "0|1|
S1S0S3S1cS13S43A1M0A1S2A3S1S0S12S18G0A1S18S13S49A1A1A3S0S3S1dG0A1ScA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma NX2_TCf : ltac2:(tb__ "0|0|
S0S3S78S77S18S13S43A1A1A2S2A3"). Proof. vmr. Qed.
Lemma EQ2_TCf : ltac2:(tb__ "0|0|
S0S14S16S49S13S43A1A2S43A3"). Proof. vmr. Qed.
Lemma RUN2_TCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2aS6S11A1A3S43A3S5dA3"). Proof. unfold run2_TCf; reflexivity. Qed.
Lemma L2_TCf : ltac2:(tb__ "0|0|
S1S0S3S28S5dS4S11S2aS6S11A1A3A2S2A3S0S14S3eU0S5dA2S62A3A2"). Proof. Time (split; [vmr | unfold EfD_TCf; reflexivity]). Qed.
Lemma AXD_TCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS62S35A2S8S14S45A2A3"). Proof. Time vmr. Qed.
Lemma HeD_TCf : ltac2:(tb__ "0|1|
S0S9S5S19A1M0A1S8fS45S87S84S45A1A3S8G0S56A2A3"). Proof. Time vmr. Qed.
Lemma HchkD_TCf : ltac2:(tb__ "0|0|
S0S3S90S45S87S84S45A1S56S4S14S8bS6S14A1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma AXDr_TCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS69S36A2S8S14S58A2A3"). Proof. Time vmr. Qed.
Lemma ENTD_TCf : ltac2:(tb__ "0|0|
S0S3Sb2S58S4dA2S2A3"). Proof. Time vmr. Qed.
Lemma RUN3_TCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2cS4S11S29S6S11A1A3A3S4dA3S54A3"). Proof. unfold run3_TCf; reflexivity. Qed.
Lemma L3_TCf : ltac2:(tb__ "0|0|
S1S0S3S28S54S4S11S2cS4S11S29S6S11A1A3A3A2S2A3S1S0S14S3eU0S54A2S50A3S0S14S3eU1S54A2S61A3A2A2"). Proof. Time (split; [vmr | split; [unfold Eps_TCf | unfold Ebg_TCf]; reflexivity]). Qed.
Lemma NX3_TCf : ltac2:(tb__ "0|1|
S1S0S3S78S77S18S13S4dA1M0A1A2S2A3S0S3S1dG0A1ScA3A2"). Proof. split; vmr. Qed.

Lemma BGF_TCf : ltac2:(tb__ "0|0|
S0S3S80S1bS22SacA1S1eS13S61A1A1A3S2A3"). Proof. vmr. Qed.
Lemma D3_TCf : ltac2:(tb__ "0|3|
S0S9SaS5SaS1aS1aA2A1M0S5S1bA1M1A2M2A1S8cS13S50A1S13S44A1A2S8G2SdG0G1S38S6S1bA1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ3_TCf : ltac2:(tb__ "0|0|
S0S14S16S50S13S44A1A2S44A3"). Proof. vmr. Qed.
Lemma NX3b_TCf : ltac2:(tb__ "0|0|
S0S3S78S77S18S13S44A1A1A2S2A3"). Proof. vmr. Qed.
Lemma W3_TCf : ltac2:(tb__ "0|1|
S1S0S3S1cS13S44A1M0A1S2A3S1S0S12S18G0A1S18S13S50A1A1A3S0S3S1dG0A1ScA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma RUN4_TCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S2bS6S11A1A3S44A3S5eA3"). Proof. unfold run4_TCf; reflexivity. Qed.
Lemma L4_TCf : ltac2:(tb__ "0|0|
S1S0S3S28S5eS4S11S2bS6S11A1A3A2S2A3S0S14S3eU0S5eA2S4fA3A2"). Proof. Time (split; [vmr | unfold Ems_TCf; reflexivity]). Qed.
Lemma D4_TCf : ltac2:(tb__ "0|3|
S0S9SaS5SaS1aS1aA2A1M0S5S1bA1M1A2M2A1S8cS13S4fA1S13S41A1A2S8G2SdG0G1S39S6S1bA1A4A2A3"). Proof. Time vmr. Qed.
Lemma EQ4_TCf : ltac2:(tb__ "0|0|
S0S14S16S4fS13S41A1A2S41A3"). Proof. vmr. Qed.
Lemma W4_TCf : ltac2:(tb__ "0|1|
S1S0S3S1cS13S41A1M0A1S2A3S1S0S12S18G0A1S18S13S4fA1A1A3S0S3S1dG0A1ScA3A2A2"). Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma HeM_TCf : ltac2:(tb__ "0|1|
S0S9S5S19A1M0A1S8fS41S8dS2dS41A1A3S8G0S57A2A3"). Proof. Time vmr. Qed.
Lemma HchkM_TCf : ltac2:(tb__ "0|0|
S0S3S92S41S8dS2dS41A1S57S7cS15S14S17S8eA4A5S2A3"). Proof. Time vmr. Qed.
Lemma HTM_TCf : ltac2:(tb__ "0|0|
S0S14S91S2dS41A1S8dS32S41S57A5S59A3"). Proof. unfold TM0_TCf, TM0_of, RM_TCf; reflexivity. Qed.
Lemma FBM_TCf : ltac2:(tb__ "0|3|
S1S0S3S7fS1bS21S18S13S41A1M0A1M1A1S1eG0A1M2A3S2A3S1S0S3S7fS1bS21S18S13S59A1A1A1G2A3S2A3S0S3S78S77G1A2S2A3A2A2").
Proof. Time (split; [vmr | split; vmr]). Qed.
Lemma ETM_TCf : ltac2:(tb__ "0|0|
S0S14S96S59S1eS13S41A1A1A2S52A3"). Proof. vmr. Qed.

Lemma NX5_TCf : ltac2:(tb__ "0|1|
S1S0S3S78S77S18S13S52A1M0A1A2S2A3S0S3S1dG0A1ScA3A2"). Proof. split; vmr. Qed.
Lemma RUN5_TCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S94S6S11A1A3S52A3S5fA3"). Proof. unfold run5_TCf; reflexivity. Qed.
Lemma L5_TCf : ltac2:(tb__ "0|0|
S1S0S3S28S5fS4S11S94S6S11A1A3A2S2A3S0S14S3eU0S5fA2S63A3A2"). Proof. Time (split; [vmr | unfold Erf_TCf; reflexivity]). Qed.
Lemma AXR_TCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS63S6bA2S8S14S42A2A3"). Proof. Time vmr. Qed.

Lemma HER_TCf : ltac2:(tb__ "0|1|
S0S9S5S19A1M0A1S8fS42S93S4cA3S8G0S47A2A3"). Proof. Time vmr. Qed.
Lemma Hchk_TCf : ltac2:(tb__ "0|0|
S0S3S90S42S93S4cS47S4S14S95S6S14A1A3A5S2A3"). Proof. Time vmr. Qed.
Lemma OBJS_TCf : ltac2:(tb__ "0|0|
S0S5S19A1S1fS13S42A1A1SfS19S6aS47A3A3"). Proof. Time vmr. Qed.
Lemma HT0_TCf : ltac2:(tb__ "0|0|
S0S14S67S96S91S4cS93S95S42S47A5S1eS13S42A1A1A2A3"). Proof. unfold T0_TCf, T0_of; reflexivity. Qed.
Lemma HXS_TCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS67S6cA2S8S14S48A2A3"). Proof. Time vmr. Qed.
Lemma OBJS1_TCf : ltac2:(tb__ "0|0|
S0S5S19A1S1fS13S48A1A1SfS19S66S4S19S31S4S19S7bS71A1S4S19S7bS72A1S6S19A1A3A3A3A3A3"). Proof. Time vmr. Qed.
Lemma HT2_TCf : ltac2:(tb__ "0|0|
S0S14S68S16S48Sa9S13S48A1S66A2A2A3"). Proof. unfold T2_TCf, T2_of, KEPT1_TCf; reflexivity. Qed.
Lemma HTR_TCf : ltac2:(tb__ "0|2|
S0S14S4aS98S68S4S7aS99S9bS18S13S48A1A1M0S79G0A1M1A3S6S7aA1A3S79G1A1A3A3"). Proof. unfold TR_TCf, TR_of, T2_TCf; reflexivity. Qed.
Lemma RCHK_TCf : ltac2:(tb__ "0|0|
S0S3S9aU0S2S42S48S4aS4cS47S9bA8S2A3"). Proof. Time vmr. Qed.

Lemma HTRs_TCf : ltac2:(tb__ "0|0|
S0S14S53S98S4aSadS18S13S4aA1A1A3A3"). Proof. unfold TRs_TCf, TRs_of; reflexivity. Qed.
Lemma CCHK_TCf : ltac2:(tb__ "0|0|
S0S3SaeU0S3S3aL_;S2S34S33X3x2S4aS53A4S2A3"). Proof. Time vmr. Qed.
Lemma RUN5d_TCf : ltac2:(tb__ "0|0|
S0S5S15A1S3dS26S4S11S3fS6S11A1A3S53A3S60A3"). Proof. unfold run5d_TCf; reflexivity. Qed.
Lemma L5d_TCf : ltac2:(tb__ "0|0|
S1S0S3S28S60S4S11S3fS6S11A1A3A2S2A3S0S14S3eU0S60A2S65A3A2"). Proof. Time (split; [vmr | unfold Erq_TCf; reflexivity]). Qed.
Lemma AXW_TCf : ltac2:(tb__ "0|0|
S0S9S14A1S7eS65S6dA2S8S14S64A2A3"). Proof. Time vmr. Qed.
Lemma ENTQ_TCf : ltac2:(tb__ "0|0|
S0S3S27S64SafA2S2A3"). Proof. Time vmr. Qed.
Lemma DCHK_TCf : ltac2:(tb__ "0|1|
S0S3Sb0U0M0S73S6fS2A1G0A2S45S69S84S45A1S56A6S2A3"). Proof. Time vmr. Qed.

Lemma Wa_TCf : ltac2:(tb__ "0|0|
S0S3S1cS9dS74U0A1A1A1S2A3"). Proof. vmr. Qed.
Lemma Da_TCf : ltac2:(tb__ "0|4|
S0S9SaS5SaS1aS1aA2M0A1M1S5S1bA1M2A2M3A1S8cS13Sb1S76A1A1S9dS74U0A1A1A2S8G3SdG1G2S4G0SdS1aS1aS20P18A1S23SabA1A4S6G0A1A3S6S1bA1A4A2A3"). Proof. vmr. Qed.
Lemma Wb_TCf : ltac2:(tb__ "0|0|
S0S3S1cS9eS74U0A1S6fS2A1A2A1S2A3"). Proof. vmr. Qed.
Lemma Wc_TCf : ltac2:(tb__ "0|0|
S0S3S1cS9fS74U0A1S6fS2A1A2A1S2A3"). Proof. vmr. Qed.
Lemma Wd_TCf : ltac2:(tb__ "0|0|
S0S3S1cSa0S74U0A1S6fS2A1A2A1S2A3"). Proof. vmr. Qed.
Lemma Fb_TCf : ltac2:(tb__ "0|0|
S0S3S7fS1bS21SaaA1S89S2S70S2A1A2A3S2A3"). Proof. vmr. Qed.
Lemma XI_TCf : ltac2:(tb__ "0|3|
S0S9S14A1S7eSa1S2S74U0M0A1S6fS2A1M1S70S2A1M2A4S97G0SeS7aG1A2A2A2S8S14S86S2S7cS7aS19S7bG1A4G2A3A2A3"). Proof. vmr. Qed.

Definition PMID_TCf : axst := ltac2:(tb__ "0|0|
Sa2S2S74U0A1S75S7cS7aS19S7bS6fS2A1A4S70S2A1A5").
Lemma Wbm_TCf : ltac2:(tb__ "0|0|
S0S3S1cSa3S74U0A1S75S6fS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wcm_TCf : ltac2:(tb__ "0|0|
S0S3S1cSa4S74U0A1S75S6fS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma Wdm_TCf : ltac2:(tb__ "0|0|
S0S3S1cSa5S74U0A1S75S6fS2A1A3A1S2A3"). Proof. vmr. Qed.
Lemma XIm_TCf : ltac2:(tb__ "0|4|
S0S9S14A1S7eSa6S2S74U0M0A1M1S75S6fS2A1M2S70S2A1M3A5S97G0SeS7aG2A2A2A2S8S14Sa2S2G1S75S7cS7aS19S7bG2A4G3A5A2A3"). Proof. vmr. Qed.
End F0T_cTCf.

