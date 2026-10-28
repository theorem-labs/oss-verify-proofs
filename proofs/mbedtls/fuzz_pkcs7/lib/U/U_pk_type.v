(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image HeapIface Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_pk_free.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_pk_type () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.le"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "pk_get_type_post"].


Definition U_PK_GET_TYPE : Z := 0x29d44.

Definition pk_get_type_post (segs : list Segment) (RSAI : Z) (ECIS : list Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (info : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_type ()) "Lms',$0.(1.(2.&40.)La1,(2.&40.)(1.$3.Lty,$3.(4.(5.$0.R3.(6.(7.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.(8.&40.R1.)R2.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)O4.(9.O21.)O3.(:.(2.&40.))O1.(;.O24.)))(4.P,(5.$3.O2.=)(5.$3.R2.=)(4.P,(5.$3.O2.O23.)(5.$3.R2.+1.)(4.P,(<.$3.O2.O22.)(4.(=.+2.R2.)(=.R2.+4.))(4.(=.=R1.)(=.R1.+4.))))))))")
(* [comment removed for export] *).

Definition pk_get_type_stmt (segs : list Segment) (L : heap_layout) (RSAI : Z) (ECIS : list Z) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_pk_type ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(>.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(?.(2.&8.))PA,$3.Pinfo,$3.Pc,(2.&40.)P,(10.O5.R4.R3.(11.$12.(13.(8.&40.R2.))(11.$12.(13.R1.)(14.$12.))))P,(5.$3.(15.R4.+8.)=)P,(16.=R5.)P,(17.(5.$3.R5.=)(17.(5.$3.R5.O3.)(<.$3.R5.O2.)))P,(18.O5.R8.)P,(19.O5.O4.R9.)P,(5.$3.(15.(1:.&40.R2;.)+2.)=)P,(5.(2.&40.)R23.(8.&40.R:.))(1;.O5.(1<.O5.O3.O2.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R:.R<.)(6.(7.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.)R>.(8.&40.O1.)R=.(:.(2.&40.))R<.(;.O5.)))")
(* [comment removed for export] *).

Section Walk.
  Variable L : heap_layout.
  Hypothesis CA_RSA0 : const_at L U_RSA_INFO 4.
  Hypothesis CA_EC0 : forall e, In e U_EC_INFOS -> const_at L e 4.

  #[using="CA_RSA0 CA_EC0"] Lemma U_pk_get_type_spec : pk_get_type_stmt usegs L U_RSA_INFO U_EC_INFOS U_PK_GET_TYPE.
  Proof.
    unfold pk_get_type_stmt, U_PK_GET_TYPE. intros until c. intros HPK AL NZ HINF MI SOK RA ->.
    pose proof (rw_cells_bound _ _ _ _ HPK) as PKB. cbn [cells_size csize Nat.add] in PKB. change (Z.of_nat 16) with 16 in PKB.
    zstep. if_cases K0; zify_cond K0.
    1-2: try (exfalso; clear -K0 NZ PKB; rewrite ?unsigned_lit in K0 by lia; lia).
    zstep. zstep. if_cases KA; zify_cond KA.
    1-2: try (exfalso; clear -KA AL NZ PKB; rewrite ?unsigned_lit in KA by lia; rewrite ?land_7_mod in KA; lia).
    zstep.
    destruct HINF as [->|HINF].
    - zstep. if_cases KI; zify_cond KI. 2:{ exfalso. clear -KI. apply KI. reflexivity. }
      zstep. apply evt_done. unfold pk_get_type_post. eexists; exists 0. split; [reflexivity|].
      repeat split; intros; try lia.
      + unfold U_RSA_INFO in H. lia.
      + exfalso. unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in H. cbn [In] in H. lia.
    - (* [comment removed for export] *)
      assert (CASES : (info = U_RSA_INFO /\ const_at L info 4) \/ (In info U_EC_INFOS /\ const_at L info 4)).
      { destruct HINF as [->|EI]; [left; split; [reflexivity| exact CA_RSA0]| right; split; [exact EI| exact (CA_EC0 _ EI)]]. }
      clear HINF.
      Ltac fin_ty ty :=
        zstep; zstep;
        apply evt_done; unfold pk_get_type_post; eexists; exists ty; split; [reflexivity|];
        unfold U_RSA_INFO, U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO; cbn [In]; repeat split; intros; lia.
      destruct CASES as [[-> CA]|[EI CA]].
      + let bs := eval vm_compute in (match image_bytes usegs U_RSA_INFO 4 with Some bs => bs | None => [] end) in
        pose proof (statics_ok_cells usegs L m U_RSA_INFO bs SOK CA ltac:(vm_compute; reflexivity)) as TB; cbn [length] in TB.
        unfold U_RSA_INFO in *.
        zstep. if_cases KI; zify_cond KI. { exfalso. clear -KI. cbn in KI. lia. }
        zstep. zstep. if_cases KB; zify_cond KB. { exfalso; clear -KB; cbn in KB; try discriminate; lia. }
        fin_ty 1.
      + unfold U_EC_INFOS, U_ECKEY_INFO, U_ECKEYDH_INFO, U_ECDSA_INFO in EI. cbn [In] in EI.
        destruct EI as [<-|[<-|[<-|[]]]];
        (let e := lazymatch type of CA with const_at _ ?e _ => e end in
         let bs := eval vm_compute in (match image_bytes usegs e 4 with Some bs => bs | None => [] end) in
         pose proof (statics_ok_cells usegs L m e bs SOK CA ltac:(vm_compute; reflexivity)) as TB; cbn [length] in TB;
         zstep; if_cases KI; zify_cond KI; [exfalso; clear -KI; cbn in KI; lia|];
         zstep; zstep; if_cases KB; zify_cond KB; [exfalso; clear -KB; cbn in KB; try discriminate; lia|]);
        [fin_ty 2| fin_ty 3| fin_ty 4].
  Qed.
End Walk.
