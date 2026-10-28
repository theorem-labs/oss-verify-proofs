(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux MpiCoreAux HeapIface ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_mpi_core_shift_r U_mpi_cmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_shift_r () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limbs_val"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.pow"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_shift_r_post"].


Definition U_MPI_SHIFT_R : Z := 0x2010c.
Notation MPI_SHIFT_R_STACK := 48 (only parsing).

Definition mpi_shift_r_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (LB : list blk) (dX : mpd) (count lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_shift_r ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R11.(7.(8.O17.O16.O15.O14.R10.R?.R>.O13.O12.(9.&40.=)R=.R<.R;.R:.R9.R8.R7.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R6.R5.R4.R3.)O7.(:.O17.)O6.(;.(2.&40.))R2.(<.O18.)))(5.(=.(>.(?.$10.$10.)(11.$10.$10.(12.(13.&40.O16.)+30.)(13.&40.O16.))(>.(?.$10.$10.)(11.$10.$10.(14.O4.)(15.(14.O4.)(16.+4.(17.O4.))))(18.(?.$10.$10.))))O1.R2.)(5.(19.O18.O1.R2.)(5.(1:.O18.R2.)(5.(1;.O18.R2.O2.(13.&40.O16.))(5.(1<.O18.R2.O5.(1=.(1>.O4.)(1?.O4.)(17.O4.)(14.O4.)R1.(20.O4.)(21.O4.)))(5.(6.$22.(23.(2.&40.)R1.)(23.(2.&40.)(24.O4.)))(6.$10.(25.R1.)(26.(25.(24.O4.))(27.+2.O3.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_shift_r_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_shift_r ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(28.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(4.$29.)PdX,$2:.Pcount,$10.Plo,$10.P,(1<.O2.R5.R4.R3.)P,(2;.(6.$2<.(21.R4.)$2=.))P,P,(6.$2<.(21.R5.)$2>.)(5.(2?.=(14.R6.))(30.(15.(14.R6.)(16.+4.(17.R6.)))R4.))P,(1:.O2.R8.)P,(5.(30.=R6.)(2?.R6.(27.+2.+40.)))P,(1;.O2.R:.R6.(13.&40.R2:.))P,(30.R7.(12.(13.&40.R2;.)+30.))P,(6.$10.(31.(13.&40.R2<.)+10.)=)P,(32.(30.(15.(1>.R;.)+10.)R9.)(30.(13.&40.R2=.)(1>.R;.)))P,P,(6.$2<.(21.R<.)$2>.)(32.(30.(15.(1>.R=.)+10.)(14.R=.))(30.(15.(14.R=.)(16.+4.(17.R=.)))(1>.R=.)))P,(6.$10.(31.(13.&40.R30.)+2.)=)P,(6.(2.&40.)R28.(9.&40.(1>.R>.)))P,(6.(2.&40.)R28.(9.&40.R>.))(33.O2.(34.O2.R33.R32.R31.R30.R2<.R2;.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R14.R13.R11.R10.R?.R>.R12.)(7.(8.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(9.&40.O1.)R13.(;.(2.&40.))R12.(<.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)

Local Ltac if_false_u :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      let E := fresh "E" in
      assert (E : c = false) by (unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; rewrite ?unsigned_lit by lia; first [apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | reflexivity]);
      rewrite E; cbv_concl_iota; clear E
  end.
Local Ltac land_mask0 p k :=
  let E := fresh "E" in
  assert (E : Z.land p k = 0) by
    (first [ change (Z.land p k) with (Z.land p (Z.ones 3)); rewrite Z.land_ones by lia; change (2 ^ 3) with 8
           | change (Z.land p k) with (Z.land p (Z.ones 2)); rewrite Z.land_ones by lia; change (2 ^ 2) with 4 ]; lia);
  rewrite ?E; clear E.

Lemma U_mpi_shift_r_spec : mpi_shift_r_stmt usegs U_MPI_SHIFT_R.
Proof.
  unfold mpi_shift_r_stmt, U_MPI_SHIFT_R. intros until lo. intros MA NST PLO MI CNT ST SLO SPA XS XP RAE -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  dpose ST as (SC & _ & _).
  destruct dX as [X sg n P limbs pad own].
  dpose MA as [[CH (XAL & X0 & LEN & NR & OWN)] SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
  unfold mpi_cells in CH. unfold MPI_MAX_LIMBS in NR.
  pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
  pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. if_false_u. zstep. zstep. land_mask0 X 7. zstep. if_false.
  zstep. rewrite zx16_small by (clear - NR; lia).
  zstep; if_cases KN; zify_cond KN; rewrite ?Z.mod_small in KN by (clear - NR; lia).
  - (* [comment removed for export] *)
    zstep. zstep. apply evt_done. unfold mpi_shift_r_post. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    deexists 15. exists limbs.
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ST|].
    split; [exact MA|]. split; [reflexivity|].
    destruct limbs; [cbn; rewrite Z.div_0_l; [reflexivity| apply Z.pow_nonzero; clear - CNT; lia]| exfalso; cbn [length] in LEN; clear - LEN KN; lia].
  - (* [comment removed for export] *)
    destruct own eqn:EO; [destruct OWN as [_ N0]; exfalso; exact (KN N0)| | exfalso; exact (NST eq_refl)].
    ddestruct OWN as (N1 & PIN & PAL & PX). destruct (PLO eq_refl) as [P0 PL].
    carve_frame 16%nat ST.
    clear MU WM. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
    zstep. zstep. zstep. zstep.
    replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in * by (clear; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    pose proof U_mpi_core_shift_r_spec as SPc. unfold mpi_core_shift_r_stmt, U_MPI_CORE_SHIFT_R, MPI_CORE_SHIFT_R_STACK in SPc.
    eapply evt_cut; [eapply SPc with (xs := limbs) (n := n) (X := P) (cnt := count) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp - 16)) by (clear - SPB SLO SC; lia); try reflexivity; try eassumption|].
    + clear - N1 NR; lia.
    + clear - LEN; lia.
    + clear - PAL. Z.div_mod_to_equations. lia.
    + clear - SLO; lia.
    + clear - SPA. Z.div_mod_to_equations. lia.
    + left. rewrite LEN. clear - PL SLO. lia.
    + cbv beta. intros ms' PO. unfold mpi_core_shift_r_post in PO.
      ddestruct PO as (z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m2 & xs' & -> & MU2 & WM2 & MI2 & ARR2 & LEN2 & SK2 & LV2 & ST2).
      rewrite ?(unsigned_lit (bv_unsigned sp - 16)) in MU2, ST2 by (clear - SPB SLO SC; lia).
      replace (ret_pc (Z_to_bv 64 131380)) with (Z_to_bv 64 131380) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      unfold MPI_CORE_SHIFT_R_STACK in MU2.
      match type of FR with rw_cells _ _ _ ?cs => assert (FR2 : rw_cells usegs m2 (bv_unsigned sp - 16) cs) end.
      { eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|]. cbn. clear - PL SLO. lia. }
      pose proof (munch_refl ([] : list ivl) m2) as MU'. pose proof (wmono_refl usegs m2) as WM'.
      zstep. zstep. release_frame FR2 ST2 (bv_unsigned sp). zstep. zstep.
      replace (Z_to_bv 64 (bv_unsigned sp - 16 + 16)) with (Z_to_bv 64 (bv_unsigned sp)) by (f_equal; clear; lia). rewrite Z_to_bv_bv_unsigned.
      apply evt_done. unfold mpi_shift_r_post. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      deexists 15. exists xs'.
      split; [reflexivity|].
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; intros x Hx; cbn in Hx |- *; clear - Hx; lia. }
      split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
      assert (LV : limbs_val xs' = limbs_val limbs / 2 ^ count).
      { unfold lval in LV2. rewrite !firstn_all2 in LV2 by (rewrite ?LEN2; clear - LEN; lia). exact LV2. }
      split; [| split; [exact LEN2| exact LV]].
      split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [| split; [exact XAL| split; [exact X0| split; [rewrite <- LEN; clear - LEN2; lia| split; [unfold MPI_MAX_LIMBS; exact NR|]]]]].
      * eapply rw_cells_transport; [exact CH| exact MU2| exact WM2| cbn; destruct (XP eq_refl); clear - H XS SLO; lia].
      * split; [exact N1|]. split; [exact PIN|]. split; [exact PAL| exact ARR2].
Qed.
