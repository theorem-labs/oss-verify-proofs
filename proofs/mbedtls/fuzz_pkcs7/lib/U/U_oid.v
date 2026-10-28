(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_string.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_oid () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.or"; "MBEDTLS_ERR_OID_NOT_FOUND"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "oid_lookup1_post"; "oid_lookup2_post"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Image.ro_bytes_b"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.pow"].


Definition MBEDTLS_ERR_OID_NOT_FOUND : Z := -46.

(* [comment removed for export] *)
Definition oid_lookup1_post (segs : list Segment) (L : heap_layout)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (EXT STACK lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_oid ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.(2.&40.)Lv,(2.&40.)(5.(6.$0.R13.(7.(8.O16.O15.O14.O13.R12.R11.R10.O12.O11.R?.R>.R=.R<.R;.R:.R9.R8.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R7.R6.R5.R4.)O6.(9.O16.)O5.(:.(2.&40.))R3.(;.O18.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O4.(10.O4.+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O15.)O3.)(12.&40.O15.))(13.(>.$4.$4.))))O1.R3.)(5.(14.O18.O1.R3.)(5.(15.O18.R3.)(5.(6.(2.&40.)R?.(16.&40.R2.))(5.(17.(6.$4.R2.=)(6.$4.R2.$18.))(5.(19.O18.R3.O4.(=.$1:.(1;.R1.)(13.$1:.)))(5.(1<.O18.R3.O2.(12.&40.O15.))(1=.O18.O17.R3.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition oid_lookup1_stmt (segs : list Segment) (L : heap_layout) (ENTRY TBL TBLN STACK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_oid ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1>.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))POID,$4.PEXT,$4.PP,$4.PLEN,$4.Plo,$4.Ptg,(2.&40.)Ppd,(2.&40.)Pv0,(2.&40.)Pxs,(1?.(2.&8.))P,(19.O6.R:.R9.(20.R4.R3.R6.R7.))P,(21.O6.R;.R8.R2.)P,(6.$4.(22.(23.(2.&8.)R3.))R8.)P,(19.O6.R=.R;.(=.$1:.(1;.R5.)(13.$1:.)))P,(17.(24.(10.R<.+4.)R=.)(24.(10.R=.+18.)R<.))P,(17.(24.(10.R=.+4.)R<.)(24.(10.R<.R;.)R=.))P,(6.$4.(25.R?.+8.)=)P,(6.$4.(25.R?.+4.)=)P,(26.=R11.)P,(26.=R11.)P,(26.=R11.)P,(1<.O6.R15.R10.(12.&40.R35.))P,(24.R11.(11.(12.&40.R36.)O1.))P,(24.(27.O5.)R12.)P,(6.$4.(25.(12.&40.R38.)+10.)=)P,(17.(24.(10.R18.+18.)R14.)(24.(12.&40.R39.)R18.))P,(17.(24.(10.R18.+4.)R15.)(24.(12.&40.R3:.)R18.))P,(17.(24.(10.R18.R17.)R16.)(24.(12.&40.R3;.)R18.))P,(15.O6.R1<.)P,(1=.O6.O5.R1=.)P,(28.O5.O3.O2.)P,(24.(29.O5.)(27.O5.))P,(17.(24.(10.R1>.+4.)(2:.O5.))(24.(29.O5.)R1>.))P,(6.(2.&40.)R39.(16.&40.R20.))P,(6.(2.&40.)R39.(16.&40.R20.))(2;.O6.(2<.O6.O5.R44.R43.R42.R41.R3=.R3<.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R25.R24.R21.O1.R1>.R23.)(7.(8.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R25.(16.&40.O4.)R24.(:.(2.&40.))R23.(;.O6.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition oid_lookup2_post (segs : list Segment) (L : heap_layout)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E1 E2 STACK lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_oid ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.(2.&40.)Lv1,(2.&40.)(1.(2.&40.)Lv2,(2.&40.)(5.(6.$0.R14.(7.(8.O17.O16.O15.O14.R13.R12.R11.O13.O12.R10.R?.R>.R=.R<.R;.R:.R9.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R8.R7.R6.R5.)O7.(9.O17.)O6.(:.(2.&40.))R4.(;.O19.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O5.(10.O5.+4.))(=.(>.$4.$4.)(?.$4.$4.O4.(10.O4.+4.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O16.)O3.)(12.&40.O16.))(13.(>.$4.$4.)))))O1.R4.)(5.(14.O19.O1.R4.)(5.(15.O19.R4.)(5.(6.(2.&40.)R10.(16.&40.R3.))(5.(17.(6.$4.R3.=)(6.$4.R3.$18.))(5.(19.O19.R4.O5.(=.$1:.(1;.R2.)(13.$1:.)))(5.(19.O19.R4.O4.(=.$1:.(1;.R1.)(13.$1:.)))(5.(1<.O19.R4.O2.(12.&40.O16.))(1=.O19.O18.R4.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition oid_lookup2_stmt (segs : list Segment) (L : heap_layout) (ENTRY TBL TBLN STACK : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_oid ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1>.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))POID,$4.PE1,$4.PE2,$4.PP,$4.PLEN,$4.Plo,$4.Ptg,(2.&40.)Ppd,(2.&40.)Pv1,(2.&40.)Pv2,(2.&40.)Pxs,(1?.(2.&8.))P,(19.O6.R<.R;.(20.R5.R4.R7.R8.))P,(21.O6.R=.R9.R2.)P,(6.$4.(22.(23.(2.&8.)R3.))R9.)P,(19.O6.R?.R=.(=.$1:.(1;.R6.)(13.$1:.)))P,(19.O6.R10.R=.(=.$1:.(1;.R6.)(13.$1:.)))P,(17.(24.(10.R?.+4.)R10.)(24.(10.R10.+18.)R?.))P,(17.(24.(10.R10.+4.)R>.)(24.(10.R>.R=.)R10.))P,(17.(24.(10.R10.+4.)R12.)(24.(10.R12.+18.)R10.))P,(17.(24.(10.R11.+4.)R10.)(24.(10.R10.R?.)R11.))P,(17.(24.(10.R13.+4.)R12.)(24.(10.R12.+4.)R13.))P,(6.$4.(25.R15.+8.)=)P,(6.$4.(25.R15.+4.)=)P,(6.$4.(25.R15.+4.)=)P,(26.=R18.)P,(26.=R18.)P,(26.=R18.)P,(26.=R18.)P,(1<.O6.R1=.R17.(12.&40.R3=.))P,(24.R18.(11.(12.&40.R3>.)O1.))P,(24.(27.O5.)R19.)P,(6.$4.(25.(12.&40.R40.)+10.)=)P,(17.(24.(10.R20.+18.)R1;.)(24.(12.&40.R41.)R20.))P,(17.(24.(10.R20.+4.)R1<.)(24.(12.&40.R42.)R20.))P,(17.(24.(10.R20.+4.)R1=.)(24.(12.&40.R43.)R20.))P,(17.(24.(10.R20.R1?.)R1>.)(24.(12.&40.R44.)R20.))P,(15.O6.R25.)P,(1=.O6.O5.R26.)P,(28.O5.O3.O2.)P,(24.(29.O5.)(27.O5.))P,(17.(24.(10.R27.+4.)(2:.O5.))(24.(29.O5.)R27.))P,(17.(24.(10.R27.+4.)(2:.O5.))(24.(29.O5.)R27.))P,(6.(2.&40.)R43.(16.&40.R2:.))P,(6.(2.&40.)R43.(16.&40.R2:.))P,(6.(2.&40.)R43.(16.&40.R2:.))(2;.O6.(2=.O6.O5.R4?.R4>.R4=.R4<.R48.R47.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R30.R2?.R2<.R2;.O1.R28.R2>.)(7.(8.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.)R30.(16.&40.O4.)R2?.(:.(2.&40.))R2>.(;.O6.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ro_image_bytes_at : ltac2:(CDefT.buildp (gd_tbl_P_oid ()) "Psegs,(1?.$2>.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pbs,(1?.(2.&8.))P,(15.R4.R3.)P,(6.$2?.(30.R5.R3.R2.)$31.)P,(24.=R4.)P,(24.(10.R5.(22.(23.(2.&8.)R4.)))(32.+2.+40.))(21.R8.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs m A bs MI RB HA HB.
  pose proof (ro_cells_image segs m A bs MI RB HA HB) as [_ H]. cbn [cells_bytes cbytes] in H.
  rewrite app_nil_r in H. exact H.
Qed.

(* [comment removed for export] *)
Ltac post_pure :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; destruct_exs PO;
  let E := fresh "E" in destruct PO as [E PO]; subst ms'; try destruct_ands PO;
  try (lazymatch goal with
       | |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end).

Tactic Notation "callp" tactic3(apptac) :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ _ _) => eapply evt_cut; [ apptac | post_pure ]
  | |- aevtM _ _ _ (MS _ _ _ _ _ _ _) => eapply aevtM_cut_evt; [ eassumption | apptac | post_pure ]
  end.

(* [comment removed for export] *)
Ltac bcmp_probe SPB ROx HYS :=
  callp (eapply SPB; rewrite ?unsigned_lit by (clear_disj; lia);
         [ exact ROx | exact HYS | reflexivity | clear_disj; lia ]).
