(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_bitlen.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mpi_set_bit () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_set_bit0_post"].


Definition U_MPI_SET_BIT : Z := 0x1f958.
Notation MPI_SET_BIT_STACK := 80 (only parsing).

Definition mpi_set_bit0_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (LB : list blk) (dX : mpd) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_set_bit ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R11.(7.(8.O16.O15.O14.O13.R10.R?.R>.O12.O11.(9.&40.=)R=.R<.R;.R:.R9.R8.R7.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R6.R5.R4.R3.)O6.(:.O16.)O5.(;.(2.&40.))R2.(<.O17.)))(5.(=.(>.(?.$10.$10.)(11.$10.$10.(12.(13.&40.O15.)+50.)(13.&40.O15.))(>.(?.$10.$10.)(11.$10.$10.(14.O3.)(15.(14.O3.)(16.+4.(17.O3.))))(18.(?.$10.$10.))))O1.R2.)(5.(19.O17.O1.R2.)(5.(1:.O17.R2.)(5.(1;.O17.R2.O2.(13.&40.O15.))(5.(1<.O17.R2.O4.(1=.(1>.O3.)(1?.O3.)(17.O3.)(14.O3.)R1.(20.O3.)(21.O3.)))(6.$22.(23.(2.&40.)R1.)(23.(2.&40.)(24.O3.)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_set_bit0_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_set_bit ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(25.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(4.$26.)PdX,$27.Ppos,$10.Plo,$10.P,(1<.O2.R5.R4.R3.)P,(28.(6.$29.(21.R4.)$2:.))P,P,(6.$29.(21.R5.)$2;.)(5.(2<.=(14.R6.))(2=.(15.(14.R6.)(16.+4.(17.R6.)))R4.))P,(1:.O2.R8.)P,(5.(2=.=R6.)(2<.R6.(2>.+2.+40.)))P,(1;.O2.R:.R6.(13.&40.R2:.))P,(2=.R7.(12.(13.&40.R2;.)+50.))P,(6.$10.(2?.(13.&40.R2<.)+10.)=)P,(30.(2=.(15.(1>.R;.)+10.)R9.)(2=.(13.&40.R2=.)(1>.R;.)))P,P,(6.$29.(21.R<.)$2;.)(30.(2=.(15.(1>.R=.)+10.)(14.R=.))(2=.(15.(14.R=.)(16.+4.(17.R=.)))(1>.R=.)))P,(6.(2.&40.)R27.(9.&40.(1>.R=.)))P,(6.(2.&40.)R27.(9.&40.R=.))P,(6.(2.&40.)R27.(9.&40.=))(31.O2.(32.O2.R33.R32.R31.R30.R2<.R2;.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R14.R13.R11.R10.R>.R12.)(7.(8.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(9.&40.O1.)R13.(;.(2.&40.))R12.(<.O2.)))")
(* [comment removed for export] *).

Local Ltac cond_decide :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  repeat match goal with
    | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
    | |- context [Z.ltb ?x ?y] => first [rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia]
    | |- context [Z.eqb ?x ?y] => first [rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia]
    | |- context [Z.b2z ?b] => progress cbn [Z.b2z]
    | |- context [negb ?b] => progress cbn [negb]
    | |- context [Z.lxor ?x ?y] => is_Zlit x; is_Zlit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
  end; reflexivity.
Local Ltac if_false_x :=
  lazymatch goal with
  | |- ?EVHD (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m (seg_rom ?segs)) =>
      let E := fresh "E" in assert (E : c = false) by cond_decide; rewrite E; cbv_concl_iota; clear E
  end.
Local Ltac land_zero_any :=
  repeat match goal with
  | |- context [Z.land ?p 7] => let E := fresh "E" in
      assert (E : Z.land p 7 = 0) by (change (Z.land p 7) with (Z.land p (Z.ones 3)); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia);
      rewrite E; clear E
  | |- context [Z.land ?p 3] => let E := fresh "E" in
      assert (E : Z.land p 3 = 0) by (change (Z.land p 3) with (Z.land p (Z.ones 2)); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; lia);
      rewrite E; clear E
  end.
Local Ltac rec_checks := zstep; if_false_x; zstep; land_zero_any; zstep; if_false.

Lemma U_mpi_set_bit0_spec : mpi_set_bit0_stmt usegs U_MPI_SET_BIT.
Proof.
  unfold mpi_set_bit0_stmt, U_MPI_SET_BIT. intros until lo. intros MA NST PLO MI POS ST SLO SPA XS XP -> -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
  destruct dX as [X sg n P limbs pad own].
  dpose MA as [[CH (XAL & X0 & LEN & NR & OWN)] SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
  unfold mpi_cells in CH. unfold MPI_MAX_LIMBS in NR.
  pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
  carve_frame 64%nat ST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep; if_cases KV; zify_cond KV; [| exfalso; cbn in KV; lia].
  rec_checks.
  zstep. zstep. zstep.
  replace (bv_unsigned (zx16 (Z_to_bv 64 n)) ≪ 5) with (32 * n)
    by (unfold zx16; rewrite !unsigned_lit by lia; rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep; if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    zstep; if_cases KV0; zify_cond KV0; [| exfalso; apply KV0; reflexivity].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold mpi_set_bit0_post. deexists 15. exists limbs.
    split; [reflexivity|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn in Hx |- *; lia|].
    split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [| reflexivity].
    eapply mpd_at_munch; [exact MA| exact NST| exact MU| exact WM| cbn; split; [lia| exact I]| intros HO; cbn; split; [|exact I]; destruct (PLO HO); lia].
  - (* [comment removed for export] *)
    destruct own eqn:EO; [destruct OWN as [_ N0]; exfalso; lia| | exfalso; exact (NST eq_refl)].
    ddestruct OWN as (N1 & PIN & PAL & PX). destruct (PLO eq_refl) as [P0 PL]. specialize (XP eq_refl).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    apply (fun H => u32arr_transport usegs _ m m1 _ _ H MU WM) in PX; cbn in PX |- *; [| cbn; split; [lia| exact I]].
    zstep. zstep. zstep.
    rewrite !Z.shiftr_div_pow2, !Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. change (2 ^ 2) with 4.
    assert (IB : 0 <= pos / 32 < n) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    set (i := pos / 32) in *.
    zstep; if_false_x. zstep. zstep. zstep. zstep; if_false_x. zstep; if_false_x.
    zstep. land_zero_any. zstep; if_false.
    rd PX i.
    zstep. zstep. zstep. zstep.
    apply (munch_weaken _ [(bv_unsigned sp - 80, bv_unsigned sp); (P, P + 4 * n)]) in MU; [| intros x Hx; clear -Hx; cbn in Hx |- *; lia].
    pose proof (u32arr_store_ok usegs _ P limbs i _ PX ltac:(lia) ltac:(f_equal; lia)) as SOKw.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      pose proof (u32arr_write usegs _ P limbs i v PX ltac:(lia)) as PX1 end.
    store_done.
    zstep; if_false_x.
    zstep. zstep. zstep. zstep.
    lazymatch type of PX1 with u32arr _ _ _ ?l1 =>
      pose proof (u32arr_store_ok usegs _ P l1 i _ PX1 ltac:(rewrite upd_length; lia) ltac:(f_equal; lia)) as SOKw2 end.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      lazymatch type of PX1 with u32arr _ _ _ ?l1 =>
        pose proof (u32arr_write usegs _ P l1 i v PX1 ltac:(rewrite upd_length; lia)) as PX' end end.
    store_done.
    zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => match goal with H : stk usegs mx _ _ |- _ => release_frame FR H (bv_unsigned sp) end end.
    zstep.
    apply evt_done. unfold mpi_set_bit0_post. deexists 15.
    lazymatch type of PX' with u32arr _ _ _ ?l => exists l end.
    split; [reflexivity|]. split; [exact MU|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
    split; [| rewrite !upd_length; reflexivity].
    split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    split; [assumption|]. split; [exact XAL|]. split; [exact X0|]. split; [rewrite !upd_length; exact LEN|]. split; [unfold MPI_MAX_LIMBS; lia|].
    split; [exact N1|]. split; [exact PIN|]. split; [exact PAL| exact PX'].
Qed.
