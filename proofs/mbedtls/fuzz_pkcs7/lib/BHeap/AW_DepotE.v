(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_MmapAnon AW_MmapDie AW_DepotA AW_DepotB AW_DepotC AW_DepotD.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_DepotE () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_wrap"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dput_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_NODES"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_MAP1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_N"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dblk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_TLM_CREATE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dwf"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dmap1"; "ARUN_1.DepotE.dinsA_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotD.A_DNODE_STORE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"].

Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma amo32_inc : ltac2:(CDefT.buildp (gd_tbl_AW_DepotE ()) "PN,$0.P,(1.(2.=R1.)(3.R1.(4.(5.+2.+1?.)+1.)))(6.(7.&40.)(8.&40.(9.&20.(:.(;.(<.&40.(8.&40.R2.))(5.+2.+20.))(<.&20.(8.&20.+1.)))))(8.&40.(:.R2.+1.)))")
(* [comment removed for export] *).
Proof.
  intros N HN. f_equal. rewrite unsigned_lit by lia.
  replace (bv_unsigned (Z_to_bv 32 1)) with 1 by (vm_compute; reflexivity).
  rewrite (Z.mod_small N) by lia. apply wrap32_small. lia.
Qed.

Section DepotE.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dput_epi : ltac2:(CDefT.buildp (gd_tbl_AW_DepotE ()) "Pra,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Pq0,(7.&40.)Pq1,(7.&40.)Pq2,(7.&40.)Pq3,(7.&40.)Pq4,(7.&40.)Pq5,(7.&40.)Pq6,(7.&40.)Pq7,(7.&40.)Pq8,(7.&40.)Pq9,(7.&40.)Pqra,(7.&40.)PSP,$0.PF,(=.&5.(7.&40.))Pfc,(7.&20.)Pm0,P,(7.&40.)(>.(7.&8.))Pm,P,(7.&40.)(>.(7.&8.))PTR,$0.Pszt,$0.Plo,$0.Pfr,(?.(7.&8.))PW,(?.(10.$0.$0.))P,(11.R6.R:.R2.R5.R4.R;.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)P,(12.$13.R7.R4.(:.R;.-70.))P,(2.(14.VhAR,)R5.)P,(2.R6.(4.R=.+70.))P,(2.R>.(5.+2.+3?.))P,(6.$0.(;.R?.+10.)=)P,(15.VCS,R9.(4.R10.R9.))P,(16.(17.(10.$0.$0.)(18.$0.$0.R:.R11.)R8.)R>.R=.)P,(19.$13.R?.R>.)P,(1:.$13.R?.)(1;.$13.VAL,VCS,Lms',$1<.(1=.P,(7.&40.)(>.(7.&8.))Lm',P,(7.&40.)(>.(7.&8.))(1.(6.$1<.R2.(1>.(1?.R17.(8.&40.R16.)R3>.R3=.R3<.R3;.R3:.R21.R20.R37.R36.R35.R34.R33.R32.R31.R30.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R27.R26.R25.R24.R23.R22.)R15.(20.R17.)R14.(21.(7.&40.))R1.(22.$13.)))(1.(16.(17.(10.$0.$0.)(18.$0.$0.R?.R16.)R=.)R13.R1.)(1.(19.$13.R13.R1.)(1.(1:.$13.R1.)(12.$13.R1.R?.R16.))))))(1>.(1?.R3=.(8.&40.(:.R14.-70.))R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R13.(8.&40.+897>4.)R12.(21.(7.&40.))R10.(22.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qra SP F fc m0 m TR szt lo fr W
      FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold dput_frame in FR.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (SP + -112 + 112) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|eassumption].
  Qed.

  (* [comment removed for export] *)
  Definition dinsA_post (SP : Z) (gp tp s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
      (h bi v N lo : Z) (nb : list Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotE ()) "Lms',$1<.(1=.$0.Lpc,$0.(1=.(7.&40.)Lr1,(7.&40.)(1=.(7.&40.)Lr10,(7.&40.)(1=.(7.&40.)Lr11,(7.&40.)(1=.(7.&40.)Lx5,(7.&40.)(1=.(7.&40.)Lx6,(7.&40.)(1=.(7.&40.)Lx7,(7.&40.)(1=.(7.&40.)Lx12,(7.&40.)(1=.(7.&40.)Lx13,(7.&40.)(1=.(7.&40.)Lx14,(7.&40.)(1=.(7.&40.)Lx15,(7.&40.)(1=.(7.&40.)Lx16,(7.&40.)(1=.(7.&40.)Lx17,(7.&40.)(1=.(7.&40.)Llockw,(7.&40.)(1=.P,(7.&40.)(>.(7.&8.))Lm',P,(7.&40.)(>.(7.&8.))Zk,$0.(23.(:.O4.+1.)+10000.)(1.(6.$1<.R11.(1>.(1?.R?.(8.&40.(:.O12.-70.))O11.O10.R<.R;.R:.(8.&40.=)(8.&40.(:.O4.+1.))R>.R=.R9.R8.R7.R6.R5.R4.(8.&40.(:.$24.(25.+4.O6.)))(8.&40.O7.)(8.&40.$26.)(8.&40.O5.)(8.&40.+????.)(8.&40.(:.O4.+1.))(8.&40.$27.)(8.&40.O5.)O?.O>.O=.O<.O;.O:.)O9.(8.&40.R10.)O8.(21.(7.&40.))R2.(22.$13.)))(1.(16.(17.(10.$0.$0.)(18.$0.$0.O3.(:.O12.-70.))(17.(10.$0.$0.)(18.$0.$0.(:.$24.(25.+4.O6.))(:.(:.$24.(25.+4.O6.))+4.))(17.(10.$0.$0.)(18.$0.$0.$28.(:.$28.+4.))(29.(10.$0.$0.)))))O1.R2.)(1.(19.$13.O1.R2.)(1.(1:.$13.R2.)(1.(2:.$13.R2.(:.$24.(25.+4.O6.))(17.$2;.(2<.R3.)(29.$2;.)))(1.(2:.$13.R2.$28.(17.$2;.(2<.(8.&40.(:.O4.+1.)))(29.$2;.)))(1.(12.$13.R2.O3.(:.O12.-70.))(2=.(1.(6.$0.R10.+897:8.)(1.(6.(7.&40.)R?.R?.)(1.(3.R1.(2>.(2?.$0.O2.)))(6.(7.&40.)R>.(8.&40.(30.O2.R1.))))))(1.(6.$0.R10.$31.)(1.(6.(7.&40.)R?.(8.&40.+89840.))(1.(6.$0.R1.(2>.(2?.$0.O2.)))(1.(6.$0.(:.O4.+1.)(25.+10000.R1.))(1.(6.(7.&40.)R>.(8.&40.$26.))(6.(7.&40.)R=.(8.&40.R1.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma dput_ins_A : ltac2:(CDefT.buildp (gd_tbl_AW_DepotE ()) "Pra,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Ps5,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Pa7,(7.&40.)Px0,(7.&40.)Px2,(7.&40.)Px3,(7.&40.)Px4,(7.&40.)Px5,(7.&40.)Px6,(7.&40.)PSP,$0.PF,(=.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(>.(7.&8.))Ph,$0.Pbi,$0.Pv,$0.PN,$0.Plo,$0.Pnb,(?.$0.)P,(1.(2.=R6.)(3.R6.(5.+2.+40.)))P,(1.(2.=R6.)(3.R6.(5.+2.+14.)))P,(1.(2.=R6.)(2.R6.R5.))P,(32.R4.R6.)P,(2:.$13.R;.(:.$24.(25.+4.R9.))(17.$2;.(2<.(8.&40.R8.))(29.$2;.)))P,(2:.$13.R<.$28.(17.$2;.(2<.(8.&40.R8.))(29.$2;.)))P,(33.VhAR,R=.R7.)P,(12.$13.R>.R9.(:.R11.-70.))P,(2.(14.VhAR,)R:.)P,(2.R;.(4.(4.R13.+70.)+30.))P,(2.R14.(5.+2.+3?.))P,(6.$0.(;.R15.+10.)=)P,(15.VCS,R>.(4.R16.R>.))P,(1:.$13.R14.)(1;.$13.VAL,VCS,(34.R18.R2;.R2:.R28.R27.R23.R22.R21.R20.R17.R16.R14.R13.R12.R11.R10.R?.R15.)(1>.(1?.R2<.(8.&40.(:.R18.-70.))R2;.R2:.R26.R25.R24.(8.&40.=)(8.&40.$24.)R1>.(8.&40.=)R1=.R1<.R1;.R1:.R19.R1?.(8.&40.(:.$24.(25.+4.R13.)))(8.&40.R14.)(8.&40.$26.)R29.(8.&40.+????.)(8.&40.+7???????.)(8.&40.$27.)(8.&40.R12.)R28.R27.R23.R22.R21.R20.)R17.(8.&40.+89738.)R16.(21.(7.&40.))R15.(22.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp s5 s10 s11 t0 t1 t2 t3 t4 t5 t6 a7 x0 x2 x3 x4 x5 x6 SP F fc m h bi v N lo nb
      HR BI VB WF TC NC DM ST LOIMG SPL SPH SPA SCS MI.
    facts. destruct WF as [WN WL]. ddestruct DM as (DM1 & DMF & DML).
    unfold A_DEP, A_DEP_N, A_DEP_NODES, A_DEP_MAP1, A_TLM_CREATE in *.
    pose proof (munch_refl [(lo, SP + -112); (2013400 + 4 * bi, 2013400 + 4 * bi + 4); (6207704, 6207708)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    set (k := (N + 1) / 65536).
    assert (KB : 0 <= k <= Z.of_nat (length nb)).
    { subst k. split; [apply Z.div_pos; lia|]. rewrite WL.
      destruct (Z.eq_dec ((N + 1) mod 65536) 0).
      - pose proof (Z.div_mod (N+1) 65536 ltac:(lia)). pose proof (Z.div_mod N 65536 ltac:(lia)). pose proof (Z.mod_pos_bound N 65536 ltac:(lia)). nia.
      - pose proof (Z.div_mod (N+1) 65536 ltac:(lia)). pose proof (Z.div_mod N 65536 ltac:(lia)).
        pose proof (Z.mod_pos_bound N 65536 ltac:(lia)). pose proof (Z.mod_pos_bound (N+1) 65536 ltac:(lia)). nia. }
    pose proof (DM1 k ltac:(lia)) as MK. unfold A_DEP_MAP1 in MK.
    (* [comment removed for export] *)
    zstep. zstep.
    callxA (eapply (dlock_spec AL IMG ALWF CS CSOK); try eassumption; try lia;
            eapply (crange_sub CS lo (SP - lo)); [exact SCS| lia| lia]).
    (* [comment removed for export] *)
    zstep. zstep. if_cases Ke; zify_cond Ke. 2:{ exfalso. lia. }
    zstep. zstep. zstep. zstep.
    match goal with H : rw_cells _ _ 6207704 _ |- _ => rewrite (amo32_inc N) in H by lia end.
    rewrite (sx32_small N) by lia.
    (* [comment removed for export] *)
    zstep. rewrite (swrap32_small (N + 1)) by lia.
    zstep. zstep. rewrite (Z.mod_small (N + 1) 4294967296) by lia.
    zstep. if_cases Kn; zify_cond Kn. { exfalso. clear -Kn WN. lia. }
    zstep. zstep. rewrite (Z.shiftr_div_pow2 (N + 1) 16) by lia. change (2^16) with 65536. fold k.
    zstep. rewrite (Z.shiftl_mul_pow2 k 3) by lia. change (2^3) with 8.
    zstep. replace (6207720 + k * 8) with (6207720 + 8 * k) by lia.
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases Kb; zify_cond Kb.
    - (* [comment removed for export] *)
      assert (KL : k = Z.of_nat (length nb)).
      { unfold dmap1v in Kb. destruct (Z.ltb_spec0 k (Z.of_nat (length nb))); [| lia]. exfalso.
        dpose (dblk_facts nb k DMF ltac:(lia)) as (B0 & B1 & _). rewrite Z.mod_small in Kb by lia. lia. }
      zstep. zstep.
      apply evtA_done. unfold dinsA_post.
      exists 0x089dc4. deexists 14.
      split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      right. split; [reflexivity|]. split; [reflexivity|]. split; [exact KL|].
      split. { subst k. pose proof (Z.div_mod (N + 1) 65536 ltac:(lia)). pose proof (Z.div_mod N 65536 ltac:(lia)).
               pose proof (Z.mod_pos_bound N 65536 ltac:(lia)). pose proof (Z.mod_pos_bound (N + 1) 65536 ltac:(lia)).
               clear - H H0 H1 H2 KL WL WN. nia. }
      split; reflexivity.
    - (* [comment removed for export] *)
      assert (KL : k < Z.of_nat (length nb)).
      { unfold dmap1v in Kb. destruct (Z.ltb_spec0 k (Z.of_nat (length nb))); [lia|]. exfalso. apply Kb. reflexivity. }
      apply evtA_done. unfold dinsA_post.
      exists 0x0897a8. deexists 14.
      split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      left. split; [reflexivity|]. split; [reflexivity|]. split; [exact KL|].
      unfold dmap1v. replace (k <? Z.of_nat (length nb)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dput_j : ltac2:(CDefT.buildp (gd_tbl_AW_DepotE ()) "PR,(=.&5.(7.&40.))PF,(=.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(>.(7.&8.))P,(1:.$13.R1.)(1;.$13.VAL,VCS,Lms',$1<.(6.$1<.R1.(1>.R6.R5.(8.&40.+897:8.)R4.(21.(7.&40.))R3.(22.$13.)))(1>.R5.R4.(8.&40.+89840.)R3.(21.(7.&40.))R2.(22.$13.)))")
(* [comment removed for export] *).
  Proof. intros R F fc m MI. facts. zstep. apply evtA_done. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dput_ins_B : ltac2:(CDefT.buildp (gd_tbl_AW_DepotE ()) "Pra,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)PSP,$0.PF,(=.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(>.(7.&8.))Ph,$0.Pbi,$0.Pv,$0.Pid,$0.Pblk,$0.P,(1.(2.=R2.)(3.R2.(5.+2.+1?.)))P,(1.(2.=R2.)(3.R2.(5.+2.+2?.)))P,(1:.$13.R8.)(1;.$13.VAL,VCS,Lms',$1<.(1=.(7.&40.)Lx1,(7.&40.)(6.$1<.R2.(1>.(1?.(8.&40.+897<8.)(8.&40.(:.R>.-70.))R20.R1?.R1<.R1;.R1:.(8.&40.=)(8.&40.(:.R6.(25.+10.(;.R7.+10000.))))(8.&40.(:.R6.(25.+10.(;.R7.+10000.))))R1.(8.&40.(:.R>.-68.))(8.&40.R:.)R12.R11.R10.R?.(8.&40.(:.$24.(25.+4.R9.)))(8.&40.R:.)(8.&40.$26.)(8.&40.R8.)(8.&40.+????.)(8.&40.R7.)(8.&40.$27.)(8.&40.R8.)R1>.R1=.R19.R18.R17.R16.)R=.(8.&40.$35.)R<.(21.(7.&40.))R;.(22.$13.))))(1>.(1?.R1?.(8.&40.(:.R<.-70.))R1>.R1=.R1:.R19.R18.(8.&40.=)(8.&40.R5.)(8.&40.R4.)R13.R12.R11.R10.R?.R>.R=.(8.&40.(:.$24.(25.+4.R7.)))(8.&40.R8.)(8.&40.$26.)(8.&40.R6.)(8.&40.+????.)(8.&40.R5.)(8.&40.$27.)(8.&40.R6.)R1<.R1;.R17.R16.R15.R14.)R;.(8.&40.+897:8.)R:.(21.(7.&40.))R9.(22.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp s10 s11 t0 t1 t2 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 SP F fc m h bi v id blk ID BLK MI.
    facts. unfold A_DNODE_STORE.
    (* [comment removed for export] *)
    zstep. rewrite (land16_mod id) by lia.
    zstep. rewrite (Z.shiftl_mul_pow2 (id mod 65536) 4) by lia. change (2^4) with 16.
    zstep. replace (blk + id mod 65536 * 16) with (blk + 16 * (id mod 65536)) by lia.
    zstep. zstep. zstep. zstep. zstep.
    apply evtA_done. eexists. replace (SP + -112 + 8) with (SP + -104) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dput_ins_C : ltac2:(CDefT.buildp (gd_tbl_AW_DepotE ()) "Pgp,(7.&40.)Ptp,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Phsh,(7.&40.)Psid,(7.&40.)Plockw,(7.&40.)Plnkw,(7.&40.)Pq0,(7.&40.)Pq1,(7.&40.)Pq2,(7.&40.)Pq3,(7.&40.)Pq4,(7.&40.)Pq5,(7.&40.)Pq6,(7.&40.)Pq7,(7.&40.)Pq8,(7.&40.)Pq9,(7.&40.)Pqra,(7.&40.)PSP,$0.PF,(=.&5.(7.&40.))Pfc,(7.&20.)Pm0,P,(7.&40.)(>.(7.&8.))Pm,P,(7.&40.)(>.(7.&8.))Ph,$0.Pbi,$0.Pv,$0.Pid,$0.PNODE,$0.PTR,$0.Pszt,$0.Plo,$0.Pfr,(?.(7.&8.))PW,(?.(10.$0.$0.))P,(1.(2.=R7.)(3.R7.(5.+2.+1?.)))P,(1.(2.=R9.)(3.R9.(5.+2.+1?.)))P,(1.(2.=R;.)(3.R;.(5.+2.+14.)))P,(2.+65?000.R9.)P,(2.(:.R:.+10.)(14.VhAR,))P,(6.$0.(;.R;.+10.)=)P,(15.VCS,R<.+10.)P,(2:.$13.R12.R=.(17.$2;.(36.R25.)(17.$2;.(2<.R22.)(17.$2;.(2<.R24.)(29.$2;.)))))P,(2:.$13.R13.(:.$24.(25.+4.R11.))(17.$2;.(2<.R24.)(29.$2;.)))P,(11.R14.R18.R;.R>.R=.R19.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)P,(12.$13.R15.R=.(:.R19.-70.))P,(2.(14.VhAR,)R>.)P,(2.R?.(4.R1;.+70.))P,(2.R1<.(5.+2.+3?.))P,(6.$0.(;.R1=.+10.)=)P,(15.VCS,R12.(4.R1>.R12.))P,(16.(17.(10.$0.$0.)(18.$0.$0.R13.R1?.)(17.(10.$0.$0.)(18.$0.$0.(:.$24.(25.+4.R19.))(:.(:.$24.(25.+4.R19.))+4.))(17.(10.$0.$0.)(18.$0.$0.R16.(:.R16.+10.))R11.)))R1<.R1;.)P,(19.$13.R1=.R1<.)P,(1:.$13.R1=.)(1;.$13.VAL,VCS,Lms',$1<.(1=.P,(7.&40.)(>.(7.&8.))Lm',P,(7.&40.)(>.(7.&8.))(1.(6.$1<.R2.(1>.(1?.R25.(8.&40.R24.)R46.R45.R42.R41.R40.R2?.R2>.(8.&40.R1<.)R3:.R39.R38.R37.R36.R35.R34.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R44.R43.R3?.R3>.R3=.R3<.)R23.(20.R25.)R22.(21.(7.&40.))R1.(22.$13.)))(1.(16.(17.(10.$0.$0.)(18.$0.$0.R18.R24.)(17.(10.$0.$0.)(18.$0.$0.(:.$24.(25.+4.R1>.))(:.(:.$24.(25.+4.R1>.))+4.))(17.(10.$0.$0.)(18.$0.$0.R1;.(:.R1;.+10.))R16.)))R21.R1.)(1.(19.$13.R21.R1.)(1.(1:.$13.R1.)(1.(2:.$13.R1.R1;.(17.$2;.(36.R33.)(17.$2;.(2<.(8.&40.R1=.))(17.$2;.(2<.R32.)(29.$2;.)))))(1.(2:.$13.R1.(:.$24.(25.+4.R1>.))(17.$2;.(2<.(8.&40.R1<.))(29.$2;.)))(12.$13.R1.R18.R24.))))))))(1>.(1?.(8.&40.+897<8.)(8.&40.(:.R22.-70.))R44.R43.R40.R3?.R3>.(8.&40.=)(8.&40.R19.)R39.R38.R37.R36.R35.R34.R33.R32.(8.&40.(:.$24.(25.+4.R1<.)))(8.&40.R1=.)(8.&40.$26.)(8.&40.R1;.)(8.&40.+????.)(8.&40.R1:.)(8.&40.$27.)(8.&40.R1;.)R42.R41.R3=.R3<.R3;.R3:.)R21.(8.&40.+897<8.)R20.(21.(7.&40.))R1>.(22.$13.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 a1 a2 a3 a4 a5 a6 a7 hsh sid lockw lnkw q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 qra SP F fc m0 m h bi v id NODE TR szt lo fr W
      ID VB BI N0 N1 NAL NCS NC TC FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_DEP, A_DEP_NODES, A_DEP_MAP1 in *. unfold dput_frame in FR.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (SP + -112 + 112) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; [eassumption|eassumption].
  Qed.
End DepotE.

End ARUN_1.
