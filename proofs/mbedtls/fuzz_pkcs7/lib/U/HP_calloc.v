(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_F_memset.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_calloc () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_F_memset.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RP_1.rcalloc_pre_post"; "RP_1.RCALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RP_1.RMALLOC_REPLACED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.to_nat"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RP_1.zeros"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Nat.add"; "RP_1.rcc_post"; "Corelib.Init.Datatypes.nat"; "RP_1.rcc_inner_post"].


Section RP_1. Context {hRP : run_params}.
Definition RCALLOC : Z := 0x3f960.
Definition RMEMSET : Z := 0x46e44.
Definition RMALLOC_REPLACED : Z := 0x7d768.
Definition zeros (n : nat) : list byte := repeat (Z_to_bv 8 0) n.

(* [comment removed for export] *)
Definition rcalloc_pre_post (sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo n : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Lms',$0.(1.(2.&40.)La2,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm1,P,(2.&40.)(3.(2.&8.))(4.(5.$0.R3.(6.(7.(8.&40.+3?9;0.)(8.&40.(9.(:.&40.O22.)-20.))O21.O20.O1?.O1>.O1=.O1<.(8.&40.O1.)(8.&40.O1.)O1:.R2.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O5.(8.&40.+3?;=8.)O4.(;.(2.&40.))R1.(<.$=.)))(4.(>.(?.(10.$11.$11.)(12.$11.$11.(9.(:.&40.O22.)-20.)(:.&40.O22.))(13.(10.$11.$11.)))O3.R1.)(4.(14.$=.O3.R1.)(4.(15.$=.R1.)(4.(16.$=.R1.O2.(9.(:.&40.O22.)-20.))(1.(17.(2.&8.))Lj0,(17.(2.&8.))(18.$=.R2.(9.(:.&40.O22.)-20.)(?.$19.(1:.#8.R1.)(?.$19.(1;.O1;.)(?.$19.(1;.O1<.)(?.$19.(1;.O6.)(13.$19.))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rcalloc_pre : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$11.Pcnt,$11.Psz,$11.P,(16.$=.R4.R3.(:.&40.R24.))P,(1=.(1>.VhRP,)R4.)P,(1=.R5.(1?.(:.&40.R26.)+20.))P,(15.$=.R7.)P,(5.(2.&40.)R20.(8.&40.R6.))P,(5.(2.&40.)R20.(8.&40.R6.))P,(4.(1=.=R8.)(20.R8.(21.+2.+40.)))P,(4.(1=.=R8.)(20.R8.(21.+2.+40.)))P,(20.(22.R:.R9.)(21.+2.+20.))(23.$=.(24.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R24.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R2>.R?.R>.R=.R<.(22.R;.R:.))(6.(7.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(8.&40.$25.)R>.(;.(2.&40.))R=.(<.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until sz. intros ST CLO LO MI A0 A1 C0 S0 PR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. rceilb.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RCALLOC.
  st1. carve_frame 32%nat ST.
  st1. st1. st1. subst a0 a1.
  assert (TAIL : forall a2' m1,
    munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp + -32) ->
    (exists j0, rw_cells rsegs m1 (bv_unsigned sp + -32) [CB 8 j0; C8 s1; C8 s0; C8 ra]) ->
    evt rsegs (rcalloc_pre_post sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sz) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra F fc m lo (cnt * sz))
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cnt) (Z_to_bv 64 sz) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3f9a4) fc None m1 (seg_rom rsegs))).
  { intros a2' m1 MU1 WM1 MI1 ST1 FR1.
    st1. st1. st1. replace (sz * cnt) with (cnt * sz) by lia.
    apply evt_done. unfold rcalloc_pre_post. dexists a2', m1. split; [reflexivity|]. auto 10. }
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - apply TAIL; [exact MU| exact WM| exact MI| exact ST| eexists; exact FR].
  - st1. replace ((sz * cnt) ≫ 64) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; nia).
    st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [| exfalso; lia].
    apply TAIL; [exact MU| exact WM| exact MI| exact ST| eexists; exact FR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rcalloc_null : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Prav,(2.&40.)Ps0v,(2.&40.)Ps1v,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$11.Pj0,(17.(2.&8.))P,(16.$=.R3.R2.(9.(:.&40.R25.)-20.))P,(1=.(1>.VhRP,)R3.)P,(1=.R4.(1?.(:.&40.R27.)+20.))P,(18.$=.R6.(9.(:.&40.R28.)-20.)(?.$19.(1:.#8.R4.)(?.$19.(1;.R9.)(?.$19.(1;.R:.)(?.$19.(1;.R;.)(13.$19.))))))P,(15.$=.R7.)(23.$=.Lms',$0.(4.(5.$0.R1.(6.(7.R>.R2;.R2:.R29.R28.R27.R26.R=.R<.(8.&40.=)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R;.(26.R>.)R:.(;.(2.&40.))R9.(<.$=.)))(16.$=.R9.R8.(:.&40.R2;.)))(6.(7.(8.&40.+3?9;0.)(8.&40.(9.(:.&40.R2:.)-20.))R29.R28.R27.R26.R25.R24.R23.(8.&40.=)R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R:.(8.&40.+3?9;0.)R9.(;.(2.&40.))R8.(<.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until j0. intros ST CLO SP32 FR MI.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. rceilb.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [| exfalso; apply K; reflexivity].
  st1. st1. st1. st1. st1.
  release_frame FR ST (bv_unsigned sp).
  st1. apply evt_done. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
#[using="hRP"] Lemma rcalloc_chk : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$11.P,(4.(20.=R1.)(20.R1.(21.+2.+40.)))P,(18.$=.R3.$27.(?.$19.(28.(8.&40.=))(13.$19.)))(23.$=.Lms',$0.(5.$0.R1.(6.(7.(8.&40.+3?:90.)(8.&40.(9.(:.&40.R24.)-20.))R23.R22.R21.R20.R1?.(8.&40.R4.)R1=.(8.&40.R4.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)R7.(8.&40.+412<<.)R6.(;.(2.&40.))R5.(<.$=.)))(6.(7.(8.&40.+3?9;0.)(8.&40.(9.(:.&40.R23.)-20.))R22.R21.R20.R1?.R1>.R1=.R1<.(8.&40.R3.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R6.(8.&40.+3?9;0.)R5.(;.(2.&40.))R4.(<.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until A. intros HA MRP. unfold RMALLOC_REPLACED in MRP.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; lia|].
  st1. st1. st1. st1. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia; [| exfalso; apply K2; reflexivity].
  st1. st1. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rcalloc_ret_same : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Prav,(2.&40.)Ps0v,(2.&40.)Ps1v,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$11.PA,$11.Pz,$11.Pj0,(17.(2.&8.))P,(16.$=.R5.R4.(9.(:.&40.R26.)-20.))P,(1=.(1>.VhRP,)R5.)P,(1=.R6.(1?.(:.&40.R28.)+20.))P,(18.$=.R8.(9.(:.&40.R29.)-20.)(?.$19.(1:.#8.R4.)(?.$19.(1;.R;.)(?.$19.(1;.R<.)(?.$19.(1;.R=.)(13.$19.))))))P,(15.$=.R9.)P,(29.(5.$11.R7.=))P,(4.(1=.=R8.)(20.R8.+2.))P,(4.(20.=R:.)(20.R:.(21.+2.+40.)))(23.$=.Lms',$0.(4.(5.$0.R1.(6.(7.R13.R2?.R2>.R2=.R2<.R2;.R2:.R12.R11.(8.&40.R<.)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R10.(26.R13.)R?.(;.(2.&40.))R>.(<.$=.)))(16.$=.R>.R=.(:.&40.R2?.)))(6.(7.(8.&40.+3?:90.)(8.&40.(9.(:.&40.R2>.)-20.))R2=.R2<.R2;.R2:.R29.(8.&40.R;.)R28.(2:.R:.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R?.(8.&40.+3?:90.)R>.(;.(2.&40.))R=.(<.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until j0. intros ST CLO SP32 FR MI Hz Z2 HA.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. rceilb. unfold wz.
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [| exfalso; lia].
  st1. st1. st1. st1. st1.
  release_frame FR ST (bv_unsigned sp).
  st1. apply evt_done. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="hRP"] Lemma rblk_chunk m A n a len : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "P,(2;.$=.O5.O4.O3.)P,(1=.O4.O2.)P,(1=.(9.O2.O1.)(9.O4.O3.))P,(1=.=O1.)P,(2<.(1=.(9.O4.O3.)+10000.)(1=.+7>000.O4.))(1.(17.(2.&8.))Ljunk,(17.(2.&8.))(18.$=.O5.O2.(?.$19.(1:.(2=.O1.)R1.)(13.$19.))))")
(* [comment removed for export] *).
Proof. rceilb.
  (intros dd_H; ddestruct dd_H as (W0 & Wn & W); intros H1 H2 H3 IMG).
  assert (W' : wr_at rsegs m a len).
  { split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (A + (a - A + i)) by lia. apply W. lia. }
  ddestruct (rwr_at_bytes_exist m a len W' H3 ltac:(lia)) as (bs & L & B).
  exists bs. apply rw_cells_of_bytes; cbn; [rewrite L; split; reflexivity| rewrite app_nil_r; exact B| rewrite Nat.add_0_r, Z2Nat.id by lia; exact W'].
Qed.

#[using="hRP"] Lemma rblk_read8 m A n a : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "P,(2;.$=.O4.O3.O2.)P,(1=.O3.O1.)P,(1=.(9.O1.+8.)(9.O3.O2.))P,(2<.(1=.(9.O3.O2.)+10000.)(1=.+7>000.O3.))(1.(2.&40.)Lw,(2.&40.)(4.(5.(3.(17.(2.&8.)))(2>.$=.O4.(8.&40.O1.)#8.)(2?.(17.(2.&8.))(30.R1.)))(31.$=.O4.O1.(30.R1.))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros W H1 H2 IMG. destruct (rblk_chunk m A n a 8 W H1 H2 ltac:(lia) IMG) as (bs & RW).
  pose proof RW as [[L B] _]. cbn in L, B. destruct L as [L _]. rewrite app_nil_r in B.
  exists (le_bytes_to_word bs). rewrite (le8_le_bytes_to_word bs L). split; [| exact B].
  pose proof (bytes_at_read rsegs m a bs 0 8 B ltac:(lia) ltac:(rewrite L; cbn; lia)) as R.
  rewrite Z.add_0_r in R. cbn [Z.to_nat skipn] in R. rewrite firstn_all2 in R by (rewrite L; lia). exact R.
Qed.

#[using="hRP"] Lemma le8_zero (w : word) : bv_unsigned w = 0 -> le8 w = zeros 8.
Proof. rceilb. intros H. rewrite <- (Z_to_bv_bv_unsigned w), H. reflexivity. Qed.

#[using="hRP"] Lemma zeros_app a b : zeros a ++ zeros b = zeros (a + b).
Proof. rceilb. unfold zeros. rewrite repeat_app. reflexivity. Qed.

#[using="hRP"] Lemma bytes_at_zeros_join m a k l : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "P,(31.$=.O4.O3.(32.O2.))P,(31.$=.O4.(9.O3.(33.O2.))(32.O1.))(31.$=.O4.O3.(32.(34.O2.O1.)))")
(* [comment removed for export] *).
Proof. rceilb. intros B1 B2. rewrite <- zeros_app. apply bytes_at_app. split; [exact B1|]. unfold zeros at 1. rewrite repeat_length. exact B2. Qed.

(* [comment removed for export] *)
Definition rcc_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A n : Z)
    : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O9.O16.O15.O14.R?.R>.R=.O8.O7.(8.&40.O2.)R<.R;.R:.R9.R8.R7.R6.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R5.R4.R3.R2.)O6.(26.O9.)O5.(;.(2.&40.))R1.(<.$=.)))(4.(>.(?.(10.$11.$11.)(12.$11.$11.O2.(9.O2.O1.))(13.(10.$11.$11.)))O4.R1.)(4.(14.$=.O4.R1.)(4.(15.$=.R1.)(4.(16.$=.R1.O3.(:.&40.O16.))(4.(31.$=.R1.O2.(32.(2=.O1.)))(2;.$=.R1.O2.O1.))))))))))))))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rcc_final : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Prax,(2.&40.)Prav,(2.&40.)Ps0v,(2.&40.)Ps1v,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))Plo,$11.PA,$11.Pn,$11.Pk,$11.Pj0,(17.(2.&8.))P,(16.$=.R6.R5.(9.(:.&40.R29.)-20.))P,(1=.(1>.VhRP,)R6.)P,(1=.R7.(1?.(:.&40.R2;.)+20.))P,(15.$=.R9.)P,(18.$=.R:.(9.(:.&40.R2=.)-20.)(?.$19.(1:.#8.R5.)(?.$19.(1;.R>.)(?.$19.(1;.R?.)(?.$19.(1;.R10.)(13.$19.))))))P,(>.(?.(10.$11.$11.)(12.$11.$11.R9.(9.R9.R8.))(13.(10.$11.$11.)))R<.R;.)P,(14.$=.R=.R<.)P,(2;.$=.R=.R;.R:.)P,(20.=R<.)P,(1=.(9.R=.R<.)(1>.VhRP,))P,(2<.(1=.(9.R>.R=.)+10000.)(1=.+7>000.R>.))P,(4.(1=.=R=.)(1=.R=.R>.))P,(31.$=.R12.(9.R10.R>.)(32.(2=.(1?.R?.R>.))))(23.$=.(35.R36.R35.R34.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R19.R18.R17.R16.R15.R14.R12.R11.R10.)(6.(7.R1:.(8.&40.(9.(:.&40.R36.)-20.))R35.R34.R33.R32.R31.(8.&40.R11.)(8.&40.R?.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R16.(8.&40.+3?:50.)R15.(;.(2.&40.))R13.(<.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until j0. intros ST CLO LO MI FR MU0 WM0 W HA HAn IMG HK ZS.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. rceilb.
  st1. st1. st1. st1. st1. st1. st1.
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  st1.
  destruct (rblk_chunk m A n A k W ltac:(lia) ltac:(lia) ltac:(lia) IMG) as [junk CH].
  eapply evt_mono.
  { eapply memset_spec; [| exact MI]. rewrite !unsigned_lit by lia. exact CH. }
  cbv beta. intros ms' PO. unfold memset_post in PO.
  ddestruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & RW).
  rewrite !unsigned_lit in MU, RW by lia. rewrite Z.mod_0_l in RW by lia.
  unfold rcc_post. deexists 14. exists m'. split; [reflexivity|].
  split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [exact MI'|].
  split. { eapply stk_transport; [exact ST| exact MU| exact WM|]. intros x Hx. left. cbn. lia. }
  split.
  - replace (Z.to_nat n) with (Z.to_nat k + Z.to_nat (n - k))%nat by lia. apply bytes_at_zeros_join.
    + destruct RW as [[_ B] _]. cbn in B. rewrite app_nil_r in B. exact B.
    + rewrite Z2Nat.id by lia. eapply bytes_at_transport; [exact ZS| exact MU|]. unfold zeros. rewrite repeat_length. cbn. lia.
  - eapply wr_at_transport; [exact W| exact WM].
Qed.

(* [comment removed for export] *)
Definition rcc_inner_post (rax sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (A n b : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Lms',$0.(1.$11.Lr',$11.(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(4.(31.$=.O4.R3.(32.(2=.(1?.(9.O3.O2.)R3.))))(4.(4.(1=.O1.R3.)(1=.R3.(9.O3.O2.)))(2<.(4.(20.O1.R3.)(5.$0.R4.(6.(7.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.O18.(8.&40.R3.)(8.&40.O1.)(8.&40.(1?.R3.O1.))R2.R1.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(8.&40.+3?9?8.)O5.(;.(2.&40.))O4.(<.$=.))))(4.(5.$11.R3.O1.)(5.$0.R4.(6.(7.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.O18.(8.&40.O1.)(8.&40.O1.)(8.&40.=)R2.R1.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(8.&40.+3?:38.)O5.(;.(2.&40.))O4.(<.$=.))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rcc_inner : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Pj,$36.Prax,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PA,$11.Pn,$11.Pb,$11.Pr,$11.P,(2;.$=.R5.R4.R3.)P,(2<.(1=.(9.R5.R4.)+10000.)(1=.+7>000.R5.))P,(1=.(9.R6.R5.)(1>.VhRP,))P,(1=.R7.R5.)P,(4.(20.R6.R5.)(1=.R5.(9.R8.R7.)))P,(5.$11.(1?.R6.R7.)(22.+10.(33.R29.)))P,(31.$=.R;.R7.(32.(2=.(1?.(9.R:.R9.)R7.))))(23.$=.(37.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)(6.(7.R2:.R29.R28.R27.R26.R25.R24.R23.R22.(8.&40.R8.)(8.&40.R9.)(8.&40.(1?.R8.R9.))R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(8.&40.+3?:1<.)R=.(;.(2.&40.))R<.(<.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  induction j as [|j IH]; intros until r; intros W IMG CEIL HB HR HJ ZS; [exfalso; lia|].
  dpose W as (W0 & Wn & _).
  ddestruct (rblk_read8 m A n (r + -16) W ltac:(lia) ltac:(lia) IMG) as (w1 & R1 & B1).
  ddestruct (rblk_read8 m A n (r + -8) W ltac:(lia) ltac:(lia) IMG) as (w2 & R2 & B2).
  pose proof (bv_unsigned_in_range 64 w1) as W1R. pose proof (bv_unsigned_in_range 64 w2) as W2R. change (bv_modulus 64) with (2^64) in W1R, W2R.
  pose proof (lor_range64 _ _ W1R W2R) as LR.
  st1. st1. st1. st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    apply evt_done. unfold rcc_inner_post. dexists r, (Z_to_bv 64 (Z.lor (bv_unsigned w1) (bv_unsigned w2))), w2.
    split; [exact ZS|]. split; [lia|]. left. split; [lia| reflexivity].
  - (* [comment removed for export] *)
    apply Z.lor_eq_0_iff in K. destruct K as [K1 K2].
    rewrite (le8_zero w1 K1) in B1. rewrite (le8_zero w2 K2) in B2.
    assert (ZS' : bytes_at rsegs m (r + -16) (zeros (Z.to_nat (A + n - (r + -16))))).
    { replace (Z.to_nat (A + n - (r + -16))) with (8 + (8 + Z.to_nat (A + n - r)))%nat by lia.
      apply bytes_at_zeros_join; [exact B1|]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. replace (r + -16 + 8) with (r + -8) by lia.
      apply bytes_at_zeros_join; [exact B2|]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. replace (r + -8 + 8) with r by lia. exact ZS. }
    st1. st1. st1. if_cases K3; zify_cond K3;
      try (change 18446744073709551615 with (Z.ones 64) in K3; rewrite Z.land_ones, Z.mod_small in K3 by lia); rewrite ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      replace (r - b + -16) with (r + -16 - b) by lia.
      apply (IH rax sp gp tp t0 t1 t2 s0 s1 _ _ a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A n b (r + -16) W IMG CEIL); [lia| lia| lia| exact ZS'].
    + (* [comment removed for export] *)
      apply evt_done. unfold rcc_inner_post. exists b. deexists 2. split; [replace b with (r + -16) by lia; exact ZS'|]. split; [lia|].
      right. split; [reflexivity|]. replace (r + -16) with b by lia. replace (r - b + -16) with 0 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rcc_after_memset m0 m m2 (lo sp32 : Z) cs (A n b len : Z) : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "P,(>.(?.(10.$11.$11.)(12.$11.$11.O2.(9.O2.O1.))(13.(10.$11.$11.)))O9.O8.)P,(14.$=.O9.O8.)P,(1=.O4.O2.)P,(1=.=O1.)P,(1=.(9.O2.O1.)(9.O4.O3.))P,(1=.(9.O4.O3.)(1>.VhRP,))P,(1=.(1>.VhRP,)O7.)P,(1=.O7.O6.)P,(16.$=.O9.O7.O6.)P,(18.$=.O9.O6.O5.)P,(>.(?.(10.$11.$11.)(12.$11.$11.O4.(9.O4.O3.))(13.(10.$11.$11.)))O:.O9.)P,(14.$=.O:.O9.)P,(2;.$=.O9.O4.O3.)(4.(16.$=.O8.O7.O6.)(4.(18.$=.O8.O6.O5.)(4.(>.(?.(10.$11.$11.)(12.$11.$11.O4.(9.O4.O3.))(13.(10.$11.$11.)))O:.O8.)(4.(14.$=.O:.O8.)(2;.$=.O8.O4.O3.)))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros MU WM H1 H2 H3 CEIL CLO LO ST FR MU0 WM0 W. rceilb.
  split. { eapply stk_transport; [exact ST| exact MU| exact WM|]. intros x Hx. left. cbn. lia. }
  split. { eapply rw_cells_transport; [exact FR| exact MU| exact WM|]. cbn. lia. }
  split. { eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU]. intros x Hx. cbn in Hx |- *. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]| eapply wr_at_transport; [exact W| exact WM]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rcc_outer : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "PN,$36.Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps1,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Prax,(2.&40.)Prav,(2.&40.)Ps0v,(2.&40.)Ps1v,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))Plo,$11.PA,$11.Pn,$11.Pq,$11.Pj0,(17.(2.&8.))P,(16.$=.R6.R5.(9.(:.&40.R29.)-20.))P,(1=.(1>.VhRP,)R6.)P,(1=.R7.(1?.(:.&40.R2;.)+20.))P,(15.$=.R9.)P,(18.$=.R:.(9.(:.&40.R2=.)-20.)(?.$19.(1:.#8.R5.)(?.$19.(1;.R>.)(?.$19.(1;.R?.)(?.$19.(1;.R10.)(13.$19.))))))P,(>.(?.(10.$11.$11.)(12.$11.$11.R9.(9.R9.R8.))(13.(10.$11.$11.)))R<.R;.)P,(14.$=.R=.R<.)P,(2;.$=.R=.R;.R:.)P,(20.=R<.)P,(1=.(9.R=.R<.)(1>.VhRP,))P,(2<.(1=.(9.R>.R=.)+10000.)(1=.+7>000.R>.))P,(4.(1=.(9.R?.+1000.)R=.)(1=.R=.(9.R?.R>.)))P,(20.(1?.R>.R10.)(22.+1000.(9.(33.R36.)+1.)))P,(31.$=.R13.R?.(32.(2=.(1?.(9.R11.R10.)R?.))))(23.$=.(35.R37.R36.R35.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1:.R19.R18.R17.R16.R15.R13.R12.R11.)(6.(7.R1;.(8.&40.(9.(:.&40.R37.)-20.))R36.R35.R34.R33.R32.(8.&40.R12.)R31.(8.&40.R10.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R17.(8.&40.+3?:10.)R16.(;.(2.&40.))R14.(<.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  induction N as [|N IH]; intros until j0; intros ST CLO LO MI FR MU0 WM0 W HA CEIL IMG HQ HN ZS; [exfalso; lia|].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose W as (W0 & Wn & _).
  (* [comment removed for export] *)
  st1. st1. st1.
  set (b := q + -4096) in *. assert (Hb : b = q + -4096) by reflexivity. clearbody b.
  replace (Z_to_bv 64 4096) with (Z_to_bv 64 (q - b)) by (f_equal; lia).
  eapply evt_cut.
  { apply (rcc_inner 256 rax _ gp tp t0 t1 t2 _ s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A n b q W IMG CEIL); [lia| lia| lia| exact ZS]. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (r' & a3' & a4' & ZS' & HB' & [[LT ->]|[Er ->]])).
  - (* [comment removed for export] *)
    st1. replace (r' + - (r' - b)) with b by lia. st1. st1.
    destruct (rblk_chunk m A n b (r' - b) W ltac:(lia) ltac:(lia) ltac:(lia) IMG) as [junk CH].
    eapply evt_cut.
    { eapply memset_spec; [| exact MI]. rewrite !unsigned_lit by lia. exact CH. }
    cbv beta. intros ms'' PO. unfold memset_post in PO.
    ddestruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & MI2 & RW).
    rewrite !unsigned_lit in MU, RW by lia. rewrite Z.mod_0_l in RW by lia.
    replace (ret_pc (Z_to_bv 64 0x3fa04)) with (Z_to_bv 64 0x3fa04) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct (rcc_after_memset m0 m m2 lo (bv_unsigned sp + -32) _ A n b (r' - b) MU WM ltac:(lia) ltac:(lia) ltac:(lia) CEIL CLO ltac:(lia) ST FR MU0 WM0 W)
      as (ST2 & FR2 & MU02 & WM02 & W2).
    assert (ZSb : bytes_at rsegs m2 b (zeros (Z.to_nat (A + n - b)))).
    { replace (Z.to_nat (A + n - b)) with (Z.to_nat (r' - b) + Z.to_nat (A + n - r'))%nat by lia. apply bytes_at_zeros_join.
      + destruct RW as [[_ B] _]. cbn in B. rewrite app_nil_r in B. exact B.
      + rewrite Z2Nat.id by lia. replace (b + (r' - b)) with r' by lia. eapply bytes_at_transport; [exact ZS'| exact MU|]. unfold zeros. rewrite repeat_length. cbn. lia. }
    clear ZS ZS' RW CH MU WM ST FR MU0 WM0 W MI.
    st1. st1. st1.
    assert (SH12 : (b + - A) ≫ 12 = (b - A) / 4096) by (rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
    assert (SHR : 0 <= (b - A) / 4096 < 2^52) by (Z.div_mod_to_equations; lia). rewrite SH12.
    if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    + (* [comment removed for export] *)
      replace (b + - A) with (b - A) by lia.
      apply (rcc_final sp gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ rav s0v s1v F fc m0 m2 lo A n (b - A) j0 ST2 CLO LO MI2 FR2 MU02 WM02 W2 HA CEIL IMG);
        [Z.div_mod_to_equations; lia|]. replace (A + (b - A)) with b by lia. replace (n - (b - A)) with (A + n - b) by lia. exact ZSb.
    + (* [comment removed for export] *)
      apply (IH sp gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ rav s0v s1v F fc m0 m2 lo A n b j0 ST2 CLO LO MI2 FR2 MU02 WM02 W2 HA CEIL IMG);
        [Z.div_mod_to_equations; lia| lia| exact ZSb].
  - (* [comment removed for export] *)
    subst r'. st1. replace (b + - 0) with b by lia. st1. st1.
    destruct (rblk_chunk m A n b 0 W ltac:(lia) ltac:(lia) ltac:(lia) IMG) as [junk CH].
    eapply evt_cut.
    { eapply memset_spec; [| exact MI]. rewrite !unsigned_lit by lia. exact CH. }
    cbv beta. intros ms'' PO. unfold memset_post in PO.
    ddestruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & MI2 & RW).
    rewrite !unsigned_lit in MU, RW by lia.
    replace (ret_pc (Z_to_bv 64 0x3fa44)) with (Z_to_bv 64 0x3fa44) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct (rcc_after_memset m0 m m2 lo (bv_unsigned sp + -32) _ A n b 0 MU WM ltac:(lia) ltac:(lia) ltac:(lia) CEIL CLO ltac:(lia) ST FR MU0 WM0 W)
      as (ST2 & FR2 & MU02 & WM02 & W2).
    assert (ZSb : bytes_at rsegs m2 b (zeros (Z.to_nat (A + n - b)))).
    { eapply bytes_at_transport; [exact ZS'| exact MU|]. unfold zeros. rewrite repeat_length. cbn. lia. }
    clear ZS ZS' RW CH MU WM ST FR MU0 WM0 W MI.
    st1. st1. st1.
    assert (SH12 : (b + - A) ≫ 12 = (b - A) / 4096) by (rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
    assert (SHR : 0 <= (b - A) / 4096 < 2^52) by (Z.div_mod_to_equations; lia). rewrite SH12.
    if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    + (* [comment removed for export] *)
      apply (IH sp gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ rav s0v s1v F fc m0 m2 lo A n b j0 ST2 CLO LO MI2 FR2 MU02 WM02 W2 HA CEIL IMG);
        [Z.div_mod_to_equations; lia| lia| exact ZSb].
    + replace (b + - A) with (b - A) by lia.
      apply (rcc_final sp gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ rav s0v s1v F fc m0 m2 lo A n (b - A) j0 ST2 CLO LO MI2 FR2 MU02 WM02 W2 HA CEIL IMG);
        [Z.div_mod_to_equations; lia|]. replace (A + (b - A)) with b by lia. replace (n - (b - A)) with (A + n - b) by lia. exact ZSb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rcalloc_clear : ltac2:(CDefT.buildp (gd_tbl_HP_calloc ()) "Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Prax,(2.&40.)Prav,(2.&40.)Ps0v,(2.&40.)Ps1v,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$11.PA,$11.Pn,$11.Pj0,(17.(2.&8.))P,(16.$=.R5.R4.(9.(:.&40.R27.)-20.))P,(1=.(1>.VhRP,)R5.)P,(1=.R6.(1?.(:.&40.R29.)+20.))P,(15.$=.R8.)P,(18.$=.R9.(9.(:.&40.R2;.)-20.)(?.$19.(1:.#8.R5.)(?.$19.(1;.R<.)(?.$19.(1;.R=.)(?.$19.(1;.R>.)(13.$19.))))))P,(2;.$=.R:.R8.R7.)P,(20.=R9.)P,(1=.(9.R:.R9.)(1>.VhRP,))P,(2<.(1=.(9.R;.R:.)+10000.)(1=.+7>000.R;.))P,(1=.=R;.)(23.$=.(35.R31.R30.R2?.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R14.R13.R12.R11.R10.R?.R>.R=.R<.)(6.(7.R15.(8.&40.(9.(:.&40.R31.)-20.))R30.R2?.R2>.R2=.R2<.(8.&40.R=.)(8.&40.R<.)R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R11.(8.&40.+3?9<4.)R10.(;.(2.&40.))R?.(<.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until j0; intros ST CLO LO MI FR W HA CEIL IMG N0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose W as (W0 & Wn & _).
  assert (CE : rceil < 2^47) by (rceilb; unfold sp_window_lo, stack_max_size; cbn; lia).
  st1. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
  assert (NR : 0 <= n / 4096 < 2^52) by (Z.div_mod_to_equations; lia).
  st1. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    apply (rcc_final sp gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ rax rav s0v s1v F fc m m lo A n n j0 ST CLO LO MI FR (munch_refl _ _) (wmono_refl _ _) W HA CEIL IMG);
      [lia|]. rewrite Z.sub_diag. apply bytes_at_nil. lia.
  - st1. st1. st1. st1. st1. st1.
    set (i0 := (A + n) mod 4096). set (pp0 := A + n - i0).
    assert (I0 : 0 <= i0 < 4096) by (subst i0; apply Z.mod_pos_bound; lia).
    assert (E2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (A + n) 52))) 52 = i0).
    { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst i0. Z.div_mod_to_equations. nia. }
    rewrite E2. rewrite (unsigned_lit (A + n)) by lia. rewrite land_pgmask by lia. fold i0. fold pp0.
    assert (PP : A + 4096 <= pp0 + 4096 /\ pp0 <= A + n /\ A <= pp0) by (subst pp0; Z.div_mod_to_equations; lia).
    replace (A + n - i0) with pp0 by reflexivity.
    destruct (rblk_chunk m A n pp0 i0 W ltac:(lia) ltac:(lia) ltac:(lia) IMG) as [junk CH].
    st1. eapply evt_cut.
    { eapply memset_spec; [| exact MI]. rewrite !unsigned_lit by lia. exact CH. }
    cbv beta. intros ms'' PO. unfold memset_post in PO.
    ddestruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m2 & -> & MU & WM & MI2 & RW).
    rewrite !unsigned_lit in MU, RW by lia. rewrite Z.mod_0_l in RW by lia.
    replace (ret_pc (Z_to_bv 64 0x3f9e8)) with (Z_to_bv 64 0x3f9e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct (rcc_after_memset m m m2 lo (bv_unsigned sp + -32) _ A n pp0 i0 MU WM ltac:(lia) ltac:(lia) ltac:(lia) CEIL CLO ltac:(lia) ST FR (munch_refl _ _) (wmono_refl _ _) W)
      as (ST2 & FR2 & MU02 & WM02 & W2).
    assert (ZSb : bytes_at rsegs m2 pp0 (zeros (Z.to_nat (A + n - pp0)))).
    { destruct RW as [[_ B] _]. cbn in B. rewrite app_nil_r in B. replace (A + n - pp0) with i0 by lia. exact B. }
    clear RW CH MU WM ST FR W MI.
    st1. st1. st1.
    assert (SH12 : (pp0 + - A) ≫ 12 = (pp0 - A) / 4096) by (rewrite Z.shiftr_div_pow2 by lia; f_equal; lia).
    assert (SHR : 0 <= (pp0 - A) / 4096 < 2^52) by (Z.div_mod_to_equations; lia). rewrite SH12.
    if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + (* [comment removed for export] *)
      apply (rcc_outer (Z.to_nat n) sp gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ rav s0v s1v F fc m m2 lo A n pp0 j0 ST2 CLO LO MI2 FR2 MU02 WM02 W2 HA CEIL IMG);
        [Z.div_mod_to_equations; lia| lia| exact ZSb].
    + st1. replace (pp0 + - A) with (pp0 - A) by lia.
      apply (rcc_final sp gp tp _ _ _ _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ rav s0v s1v F fc m m2 lo A n (pp0 - A) j0 ST2 CLO LO MI2 FR2 MU02 WM02 W2 HA CEIL IMG);
        [Z.div_mod_to_equations; lia|]. replace (A + (pp0 - A)) with pp0 by lia. replace (n - (pp0 - A)) with (A + n - pp0) by lia. exact ZSb.
Qed.

End RP_1.
