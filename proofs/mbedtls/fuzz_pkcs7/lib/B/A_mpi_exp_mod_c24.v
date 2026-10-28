(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp P_mpi_addsub P_mpi_lset P_mpi_copy P_mpi_divmod_stmt P_mpi_core_exp_mod_working_limbs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_frame_lib A_frame_kit A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_copy
     A_mpi_core_bitlen A_mpi_core_exp_mod_working_limbs A_mpi_lset A_mpi_get_mont_r2 A_mpi_zeroize_and_free A_mpi_cmp_mpi A_mpi_grow A_mpi_core_montmul A_mpi_core_montmul_init
     A_mpi_core_to_mont_rep A_mpi_core_exp_mod_stmtA A_mpi_core_from_mont_rep A_mpi_core_check_zero_ct A_mpi_add_sub A_mpi_add_sub_stmtSZ A_mpi_stmtA_sz
     A_mpi_exp_mod_P A_mpi_exp_mod_C A_mpi_exp_mod_S_c24 A_mpi_stmtA_c24 A_mpi_copy_c24 A_mpi_grow_c24.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_exp_mod_c24 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.vchg"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_core_exp_mod_working_limbs.exp_mod_working_limbs"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2.get_mont_r2_PHI"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.copy_PHI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mod_mpi_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.grow_PHI"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.exp_mod_PHIn"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2.get_mont_r2_FR"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.copy_FR"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mod_mpi_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow.grow_FR"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub.add_sub_FR"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.exp_mod_FRn"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_calloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_lset.mpi_lset_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_LSET"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2.mpi_get_mont_r2_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_get_mont_r2.A_MPI_GET_MONT_R2"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy_c24.mpi_copy_stmtA_x_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_COPY"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_mod_mpi_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_MOD_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_grow_c24.mpi_grow_stmtA_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_GROW"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_to_mont_rep.mpi_core_to_mont_rep_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_to_mont_rep.A_MPI_CORE_TO_MONT_REP"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_exp_mod_stmtA.mpi_core_exp_mod_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_exp_mod_stmtA.A_MPI_CORE_EXP_MOD"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_from_mont_rep.mpi_core_from_mont_rep_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_from_mont_rep.A_MPI_CORE_FROM_MONT_REP"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_add_sub_stmtSZ.add_sub_mpi_stmtA_osz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_ADD_SUB_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_exp_mod_stmtA_szT"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_EXP_MOD"].


(* [comment removed for export] *)
Lemma em_budget_vol : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_c24 ()) "PnA,$0.PnE,$0.PnN,$0.P,(1.(2.=R3.)(2.R3.+2710.))P,(2.=R3.)P,(1.(2.=R3.)(2.R3.+1387.))PdA,$3.PdN,$3.P,(4.$0.(5.R2.)R8.)P,(4.$0.(5.R2.)R7.)(2.(6.(6.(6.(6.(6.(6.(7.(8.(9.R8.R9.)+4.))(:.(;.=+1.==(<.(=.&40.))(>.&40.=)$?.)R3.))(10.R4.))(11.R:.R8.))(12.R8.))(6.(12.R8.)(8.+3.(12.(6.(13.R:.R8.)+4.)))))(8.+2.$14.))(15.R:.R9.R8.))")
(* [comment removed for export] *).
Proof.
  intros nA nE nN HA HE HN dA dN EA EN.
  assert (WLB : 0 <= exp_mod_working_limbs nN nE <= 11 * nN + 1) by (unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * nE); clear - HN; lia).
  assert (VC : vchg (exp_mod_working_limbs nN nE * 4) <= 8 * (11 * nN + 1)).
  { unfold vchg, AVOL_CALL. destruct (_ <? _); clear - WLB; lia. }
  unfold get_mont_r2_PHI, gmr2_G, copy_PHI, mod_mpi_PHIn, exp_mod_PHIn, grow_PHI, AVOL_CALL. cbn [md_n]. rewrite EA, EN.
  generalize dependent (vchg (exp_mod_working_limbs nN nE * 4)). intros vc VC. clear - HA HN VC. lia.
Qed.

Lemma em_budget_fr : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_c24 ()) "PnA,$0.PnE,$0.PnN,$0.Pd,$0.P,(1.(2.=R4.)(2.R4.+2710.))P,(1.(2.=R3.)(2.R3.+1387.))P,(2.=R3.)PdN,$3.P,(4.$0.(5.R1.)R6.)(2.(6.(6.(6.(6.(6.(6.(16.(6.R6.+1.))(17.(;.=+1.==(<.(=.&40.))(>.&40.=)$?.)R2.(13.(6.R6.+1.)+1<.)))(18.R6.))(19.R9.R7.(6.R6.+1.)))(1:.(6.R6.+1.)))(1;.(6.R6.+1.)))(8.+2.(16.(6.R6.+1.))))(1<.R9.R8.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros nA nE nN d HA HN HD dN EN.
  unfold get_mont_r2_FR, gmr2_G, copy_FR, mod_mpi_FRn, grow_FR, add_sub_FR, A_mpi_add_abs_W.add_abs_FR, exp_mod_FRn, calls_FR, fr_charge. cbn [md_n]. rewrite EN.
  assert (DM : d + 1 <= Z.max (d + 1) 28 <= d + 28) by (clear - HD; lia).
  generalize dependent (Z.max (d + 1) 28). intros D DM. rewrite (Z.max_r 0 nN) by (clear - HN; lia). change (Z.max 0 1) with 1.
  clear - HA HN HD DM. nia.
Qed.


Theorem A_mpi_exp_mod_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_exp_mod_c24 ()) "PR,$1=.PHIA,(1>.$1?.R1.)P,(20.(21.R2.))P,Ph,(22.$1?.R3.R2.)PLB,(23.$24.)PLF,(23.$24.)Pm,P,(=.&40.)(25.(=.&8.))Pg,$0.P,(26.$1?.R8.R7.R5.R4.R3.R2.)P,(1.(2.(27.R9.)R2.)(28.R2.(29.$1?.R9.R8.R6.)))(2:.(4.(25.(=.&8.))A1.R4.(2;.(2<.(21.R:.)R3.))(2=.(=.&8.))))P,(4.$0.(2>.R4.)+69484.)P,(2.=(2?.R5.))P,Ph,(22.$1?.R6.R5.)PLB,(23.$24.)PLF,(23.$24.)Pm,P,(=.&40.)(25.(=.&8.))P,(26.$1?.R:.R9.R4.R3.R2.R1.)(30.$0.(31.(32.$0.$0.)$0.(33.$0.$0.)R4.))P,(1.(2.(34.(35.R7.))(36.(35.R7.)))(2.(37.(35.R7.))(38.(35.R7.))))P,Pa,$0.P,(4.$39.(3:.$1?.(2;.R1.))$3;.)P,(1.(2.=R2.)(28.R2.(3<.+2.+40.)))(1.(2.(34.(35.R;.))R3.)(28.R3.(38.(35.R;.))))P,(3=.$1?.R9.R8.$3>.)P,(3?.$1?.R:.R9.$40.)P,(41.$1?.R;.R:.$42.)P,(43.$1?.R<.R;.$44.)P,(45.$1?.R=.R<.$46.)P,(47.$1?.R>.R=.$48.)P,(49.$1?.R?.R>.$4:.)P,(4;.$1?.R10.R?.$4<.)P,(4=.$1?.R11.R10.$4>.)P,(4?.+1.$1?.R12.R11.$50.)(51.$1?.R13.R12.$52.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG SSMAP CALLOC NEEDR HND DIMG ROIMG LSET GMR ZF COPY MODS GROW TOM CEM FROM ADDS.
  unfold mpi_exp_mod_stmtA_szT, mpi_exp_mod_stmtA_sz. intros until slo.
  intros HH HK LFB MX MA ME MN NN4 NXA SXA SXE SXN NXE NXN NSX OSA OSE OSN CRA CRAL CRE CREL CRN CRNL XW XLS ST LOS SLO SS SSL SLL TOP SPA TPV MI RAE OXA OAA OEA ONA IMA IME IMN BUD UW UWX UWA UWE UWN BUDF C24H -> -> -> -> ->.
  pose proof (arl_need_ecp_rt R) as NER. assert (NEEDE : 0 <= arl_need_ecp R) by (clear - NER NEEDR; lia).
  pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
  pose proof MX as [(_ & _ & _ & _ & NRX & OWX) _]. pose proof MA as [(_ & _ & _ & _ & NRA & _) _]. pose proof ME as [(_ & _ & _ & _ & NRE & _) _]. pose proof MN as [(_ & _ & _ & _ & NRN & _) _].
  unfold MPI_MAX_LIMBS in NRX, NRA, NRE, NRN.
  assert (DSX : md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX).
  { destruct XW as [CW _]. eapply (client_wrange_where_A asegs R HIA h LB LF m); [exact HH| intros b Hb; exact Hb| exact CW| clear; lia| exact LOS| clear - SLO NEEDE; lia]. }
  assert (XL0 : md_own dX <> LNull -> crange (hcs asegs R HIA h) (md_p dX) (4 * md_n dX) /\ 0 < md_n dX /\ (md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX)).
  { intros NN. destruct (md_own dX) eqn:EO; [exfalso; exact (NN eq_refl)| | exfalso; exact (NSX eq_refl)]. ddestruct OWX as (N1 & HIN & _).
    split; [exact (aobj_crange _ _ _ _ _ _ (hm_aobj_block asegs R HIA h LB LF m _ _ HH HIN))|]. split; [clear - N1; lia| apply XLS; discriminate]. }
  assert (SXN' : md_addr dX + 16 <= md_addr dN \/ md_addr dN + 16 <= md_addr dX) by (destruct SXN as [Q|Q]; [exfalso; apply NXN; rewrite Q; reflexivity| exact Q]).
  assert (SXE' : md_addr dX + 16 <= md_addr dE \/ md_addr dE + 16 <= md_addr dX) by (destruct SXE as [Q|Q]; [exfalso; apply NXE; rewrite Q; reflexivity| exact Q]).
  set (PHI := exp_mod_PHIn (md_n dA) (md_n dE) (md_n dN)) in *. set (FR := exp_mod_FRn (md_n dA) (md_n dE) (md_n dN) d) in *.
  set (SZB := exp_mod_nz (md_n dX) (md_n dA) (md_n dN)).
  set (Rr := exp_mod_Rsz LB dX dA dE dN).
  assert (RRX : forall r dX', -2^31 < r <= 0 -> binop_keep LB dX dX' -> md_n dX' <= SZB -> Rr r dX').
  { intros r dX' RNG BK SZ. unfold Rr, exp_mod_Rsz, exp_mod_R. split; [split; [exact RNG| exact BK]| exact SZ]. }
  assert (BK0 : binop_keep LB dX dX) by (unfold binop_keep; split; [reflexivity|]; split; [reflexivity|]; split; [intros b Hb; left; exact Hb| clear; lia]).
  assert (SZ0 : md_n dX <= SZB) by (unfold SZB, exp_mod_nz; clear; lia).
  pose proof (em_budget_vol (md_n dA) (md_n dE) (md_n dN) ltac:(clear - NRA; lia) ltac:(clear - NRE; lia) ltac:(clear - NRN NN4; lia) dA dN eq_refl eq_refl) as BV. fold PHI in BV.
  pose proof (em_budget_fr (md_n dA) (md_n dE) (md_n dN) d ltac:(clear - NRA; lia) ltac:(clear - NRN NN4; lia) D0 dN eq_refl) as BF. fold FR in BF.
  assert (VC0 : 0 <= vchg (exp_mod_working_limbs (md_n dN) (md_n dE) * 4)).
  { assert (WLB : 0 <= exp_mod_working_limbs (md_n dN) (md_n dE)) by (unfold exp_mod_working_limbs, exp_mod_welem; destruct (79 <? 32 * md_n dE); clear - NRN; lia).
    unfold vchg, AVOL_CALL. destruct (_ <? _); clear - WLB; lia. }
  assert (GP0 : 0 <= get_mont_r2_PHI (mkMPD 0 1 0 0 [] (Z_to_bv 64 0) LNull) dN) by (unfold get_mont_r2_PHI, gmr2_G; cbn [md_n]; clear - NRN; lia).
  assert (GF0 : 0 <= get_mont_r2_FR (mkMPD 0 1 0 0 [] (Z_to_bv 64 0) LNull) dN (Z.max (d + 1) 28)) by (unfold get_mont_r2_FR, gmr2_G; cbn [md_n]; clear - NRN D0; nia).
  assert (P2 : 0 <= copy_PHI dA) by (unfold copy_PHI, grow_PHI, AVOL_CALL; clear - NRA; lia).
  assert (P3 : 0 <= mod_mpi_PHIn (md_n dA) (md_n dN)) by (unfold mod_mpi_PHIn; clear - NRA NRN; lia).
  assert (P4 : 0 <= grow_PHI (md_n dN)) by (unfold grow_PHI, AVOL_CALL; clear - NRN; lia).
  assert (P5 : 0 <= grow_PHI (md_n dN) + 3 * grow_PHI (Z.max (md_n dA) (md_n dN) + 4)) by (unfold grow_PHI, AVOL_CALL; clear - NRA NRN; lia).
  assert (Q2 : 0 <= copy_FR d) by (unfold copy_FR, calls_FR, fr_charge; clear - D0; lia).
  assert (Q3 : 0 <= mod_mpi_FRn (md_n dA) (md_n dN) (d + 1)) by (apply mod_mpi_FRn_nonneg; [clear - NRA; lia| clear - D0; lia]).
  assert (Q4 : 0 <= grow_FR (d + 1)) by (unfold grow_FR, calls_FR, fr_charge; clear - D0; lia).
  assert (Q5 : 0 <= add_sub_FR (d + 1)) by (unfold add_sub_FR, A_mpi_add_abs_W.add_abs_FR, calls_FR, fr_charge; clear - D0; lia).
  assert (FC0 : 0 <= fr_charge (d + 1)) by (unfold fr_charge; clear - D0; lia).
  assert (PHIlb : 160416 <= PHI) by (unfold PHI, exp_mod_PHIn, grow_PHI, AVOL_CALL; clear - NRA NRN; lia).
  assert (FRlb : 1000 <= FR) by (unfold FR, exp_mod_FRn, calls_FR, fr_charge; clear - NRA NRN D0; nia).
  apply (aevtA_enter asegs (KF asegs R HIA h mo) _ _ mo (conj HK (mo_frame_refl mo))).
  eapply (aevtA_cut_evtA_KF asegs R HIA h mo).
  { eapply (em_pro R HIA IMG h LB LF m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dX (md_addr dA) (md_addr dE) (md_addr dN) lo slo) with (dN := dN);
      first [ assumption | reflexivity | clear - SLO; lia | pose proof MN as [(CNc & _ & N0 & _) _]; pose proof (rw_cells_bound _ _ _ _ CNc) as NB; unfold mpi_cells in NB; cbn [cells_size csize Nat.add] in NB; clear - NB N0; lia
            | match goal with |- ?g => idtac "THM-PRO-LEFT:" g end ]. }
  intros ms' S1. unfold S1P in S1.
  ddestruct S1 as (sp1 & m1 & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x8 & sl & -> & EMBF).
  eapply (em_main R HIA IMG h LB LF m ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dX lo slo) with (mo := mo) (Rr := Rr) (PHI := PHI) (FR := FR) (d := d) (dE := dE) (dN := dN) (SZB := SZB) (dA := dA) (sl := sl);
    first [ assumption | exact EMBF | exact (A_mpi_free.A_mpi_free_spec R HIA IMG ZF NEEDR)
          | apply RRX; [clear; lia| exact BK0| exact SZ0]
          | (intros r dX' dd_H; ddestruct dd_H as ([(-> & LN & _ & _ & _ & LP)|(-> & ->)] & LA & LFR); intros _); [| apply RRX; [unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia| exact BK0| exact SZ0]];
            apply RRX; [clear; lia| unfold binop_keep; split; [exact LA|]; split; [exact LP|]; split; [exact LFR| rewrite LN; clear; lia]| rewrite LN; unfold SZB, exp_mod_nz; clear - NRX; lia]
          | unfold em_GP, em_GF, AVOL_CALL in *; clear - BV BF BUD BUDF VC0 GP0 GF0 P2 P3 P4 P5 Q2 Q3 Q4 Q5 FC0; lia
          | unfold em_GF in *; assert (DMX : d + 1 <= Z.max (d + 1) 28 <= d + 28) by (clear - D0; lia);
            unfold copy_FR, mod_mpi_FRn, grow_FR, add_sub_FR, A_mpi_add_abs_W.add_abs_FR, calls_FR, fr_charge in BF |- *;
            clear - BF DMX D0 NRA NRN; nia
          | unfold FR, exp_mod_FRn, em_F5, em_F4, em_F3, em_F2, em_F1, em_GF, get_mont_r2_FR, gmr2_G, copy_FR, mod_mpi_FRn,
              grow_FR, add_sub_FR, A_mpi_add_abs_W.add_abs_FR, calls_FR, fr_charge; cbn [md_n];
            assert (DMX : d + 1 <= Z.max (d + 1) 28 <= d + 28) by (clear - D0; lia);
            try rewrite (Z.max_r 0 (md_n dN)) by (clear - NRN; lia); try change (Z.max 0 1) with 1;
            clear - DMX D0 NRA NRN; generalize dependent (Z.max (d + 1) 28); intros DD DMX; nia
          | unfold grow_PHI, AVOL_CALL in *; split; [clear - BUD PHIlb; lia| clear - PHIlb; lia]
          | unfold lset_FR, calls_FR, fr_charge in *; split; [clear - BUDF FRlb; lia| clear - FRlb; lia]
          | clear - LFB; lia
          | clear - SLO; lia
          | unfold C24_EXP_MOD, C24_GET_MONT_R2, C24_MOD_MPI in *; clear - C24H; lia
          | unfold SZB, exp_mod_nz; clear; lia
          | match goal with |- ?g => idtac "THM-LEFT:" g end ].
  all: match goal with |- ?g => idtac "THM-LEFT2:" g end.
Qed.
