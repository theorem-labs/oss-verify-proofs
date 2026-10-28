(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_F F_am_G F_am_H.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require KArith. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RF_ntf_A HP_RF_am_A HP_RF_am_K HP_RF_am_C HP_RF_am_F HP_RF_am_G.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_am_H () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_avail_meta_area_count"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.brkstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_brk"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.BrkUntried"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.BrkLive"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.impl"; "RocqVerifyHarness.AgentSubmission.Lib.Nodes.node"; "RocqVerifyHarness.AgentSubmission.Lib.Nodes.at_node"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.Exc.exc"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.enode"; "RocqVerifyHarness.AgentSubmission.Lib.Nodes.NBrk"; "RocqVerifyHarness.AgentSubmission.Lib.Decode.dec_brk0"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.epost"; "Corelib.Init.Logic.and"; "RP_1.BRKNODES.rbrk_regs"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Decode.brk_ans"; "RocqVerifyHarness.AgentSubmission.Lib.Decode.dec_brk"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_H.brk_res"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_H.brk_mem"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmmap_entry"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_seq"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.zeros"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_brk"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.BrkDead"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma ram_disp_untried : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pst,$3.P,(4.VhRP,R1.R2.)P,(5.$6.(7.(8.R2.))=)P,(5.$9.(:.(8.R3.))$;.)(<.$=.Lms',$>.(5.$>.R1.(?.(10.R9.R24.R23.R22.R21.R20.R1?.(11.&40.+1000.)(11.&40.=)(11.&40.=)(11.&40.+???.)R1;.R1:.R19.R18.R17.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R8.(11.&40.+403=4.)R7.(14.(0.&40.))R6.(15.$=.)))(?.(10.R8.R23.R22.R21.R20.R1?.R1>.(11.&40.+1000.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.(11.&40.$12.)(11.&40.$13.)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R7.(11.&40.+40398.)R6.(14.(0.&40.))R5.(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until st. intros MR CNT BRK.
  dpose MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (512968 + 912) with 513880 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
  st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L1687275099.43 L3050237658.43 L46590550738.43L53519283860.4300000@00S00b00cS2st3rid3off3C1bS2st3rid3off2C03C1bS2st3rid3off2C0S". (* [comment removed for export] *)
#[using="Type"] Lemma ram_disp_live : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pst,$3.Prid,$16.Poff,$6.P,(4.VhRP,R3.R4.)P,(5.$6.(7.(8.R4.))=)P,(5.$9.(:.(8.R5.))(17.R4.R3.))P,(18.=(19.R6.(1:.$16.$6.R5.R4.)))P,(18.(1;.(19.R7.(1:.$16.$6.R6.R5.))+1000.)(1<.+2.+40.))(<.$=.Lms',$>.(5.$>.R1.(?.(10.R=.R28.R27.R26.R25.R24.R23.(11.&40.+1000.)(11.&40.(1;.(19.R9.(1:.$16.$6.R8.R7.))+1000.))(11.&40.(1;.(19.R9.(1:.$16.$6.R8.R7.))+1000.))(11.&40.-1.)R1?.R1>.R1=.R1<.R1;.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R<.(11.&40.+403;<.)R;.(14.(0.&40.))R:.(15.$=.)))(?.(10.R<.R27.R26.R25.R24.R23.R22.(11.&40.+1000.)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.(11.&40.$12.)(11.&40.$13.)R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R;.(11.&40.+40398.)R:.(14.(0.&40.))R9.(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until off. intros MR CNT BRK C0 C1b.
  dpose MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (512968 + 912) with 513880 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BRKNODES.
Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition rbrk_regs (a0 : word) : _ := ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "(10.Vx1,Vsp,Vgp,Vtp,Vt0,Vt1,Vt2,Vs0,Vs1,O1.Va1,Va2,Va3,Va4,Va5,Va6,(11.&40.+=6.)Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vt3,Vt4,Vt5,Vt6,)")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma ram_brk0_node : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "(1=.$1>.$=.(1?.$=.)(20.$6.)(21.$1>.$6.(22.=)$23.)(24.$6.Lr,$6.Lms',$>.(25.(5.$>.R1.(?.(26.(11.&40.R2.))VF,(11.&40.+403=8.)Vfc,(14.(0.&40.))Vm,(15.$=.)))(25.(27.=R2.)(18.R2.(1<.+2.+40.)))))(?.(26.(11.&40.=))VF,(11.&40.+403=4.)Vfc,(14.(0.&40.))Vm,(15.$=.)))")
(* [comment removed for export] *).
Proof.
  unfold rbrk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
  intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
  rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0x403d4 + 4)%Z with 0x403d8%Z by reflexivity.
  apply evt_done. split; [reflexivity| exact Hr].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ram_brk_node_at (pc : Z) : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "P,(28.(5.$6.O1.+403;<.)(5.$6.O1.+403?8.))Pcur,$6.Preq,$6.P,(29.(5.$6.R1.=))(1=.$1>.$=.(1?.$=.)(20.$2:.)(21.$1>.$2:.(22.R2.)(2;.R3.R2.))(24.$2:.La,$2:.Lms',$>.(5.$>.R1.(?.(26.(11.&40.(2<.R5.R4.R2.)))VF,(11.&40.(1;.O1.+4.))Vfc,(14.(0.&40.))(2=.Vm,R5.R4.R2.)(15.$=.))))(?.(26.(11.&40.R2.))VF,(11.&40.O1.)Vfc,(14.(0.&40.))Vm,(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros Hpc cur req NZ. unfold rbrk_regs.
  destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
    intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
      rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
      [ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
      | rewrite apply_mem_none ];
      apply evt_done; reflexivity).
Qed.
End BRKNODES.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L16794307354.40L22923951931.40L31734794215.41L67691039343.4000000500=00B00CS3curS3cur2CRS3curF". (* [comment removed for export] *)
#[using="Type"] Lemma ram_bu_mid : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Pq0,(0.&8.)Pq1,(2>.(0.&8.))Pq2,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pcur,$6.P,(25.(18.=R1.)(18.R1.(1<.+2.+40.)))P,(5.$6.(2?.R2.+1000.)=)P,(30.$=.R4.(1;.$31.+390.)(32.$33.(34.R9.)(32.$33.(35.#7.R8.)(32.$33.(36.R7.)(37.$33.)))))P,(38.$=.R5.)(<.$=.Lms',$>.(39.(0.&40.)La2',(0.&40.)(39.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(25.(5.$>.R3.(?.(10.R?.R26.R25.R24.R23.R22.R21.(11.&40.+1000.)(11.&40.(1;.R8.+2000.))(11.&40.(1;.R8.+2000.))(11.&40.=)R2.R1?.R1>.R1=.R1<.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R;.(11.&40.+403?8.)R:.(14.(0.&40.))R1.(15.$=.)))(25.(3:.(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+398.)(1;.$31.+3:0.))(37.(3;.$6.$6.)))R9.R1.)(25.(3<.$=.R9.R1.)(25.(38.$=.R1.)(30.$=.R1.(1;.$31.+390.)(32.$33.(34.R>.)(32.$33.(35.#7.R=.)(32.$33.(36.(11.&40.R8.))(37.$33.)))))))))))(?.(10.R<.R23.R22.R21.R20.R1?.R1>.(11.&40.+1000.)(11.&40.=)(11.&40.R5.)(11.&40.+???.)R1=.R1<.R1;.R1:.R19.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R8.(11.&40.+403=8.)R7.(14.(0.&40.))R6.(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until cur. intros CR CAL TC MI.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (land_neg_aligned cur CR CAL) as AL.
  assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
  change (cur mod 4096 = 0) with (pgal cur) in CAL.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (512968 + 912) with 513880 in TC. change (512968 + 920) with 513888 in MU. change (512968 + 928) with 513896 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. st1.
  replace (0 + cur) with cur by lia.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  replace (8192 + cur) with (cur + 8192) by lia.
  apply evt_done. deexists 2. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ram_bu_ok : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Pq0,(0.&8.)Pq1,(2>.(0.&8.))PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pcur,$6.P,(18.=R1.)P,(18.(1;.R2.+2000.)(1<.+2.+40.))P,(30.$=.R4.(1;.$31.+390.)(32.$33.(34.R8.)(32.$33.(35.#7.R7.)(32.$33.(36.(11.&40.R3.))(37.$33.)))))(<.$=.Lms',$>.(5.$>.R1.(?.(10.(11.&40.+4041<.)R23.R22.R21.R20.R1?.R1>.(11.&40.+1000.)(11.&40.(1;.R5.+2000.))(11.&40.R5.)(11.&40.+1000.)(11.&40.=)(11.&40.+32.)(11.&40.-1.)(11.&40.=)R18.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)R8.(11.&40.$3=.)R7.(14.(0.&40.))R6.(15.$=.)))(?.(10.R:.R22.R21.R20.R1?.R1>.R1=.(11.&40.+1000.)(11.&40.(1;.R4.+2000.))(11.&40.(1;.R4.+2000.))R1<.R1;.R1:.R19.R18.R17.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)R7.(11.&40.+403?<.)R6.(14.(0.&40.))R5.(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until cur. intros C0 C1b TC.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (512968 + 912) with 513880 in TC.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L46723112739.53000004S2nw". (* [comment removed for export] *)
#[using="Type"] Lemma ram_b_store : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Pw0,(0.&40.)Pw1,(0.&40.)Pw2,(0.&40.)Pw3,(0.&40.)Pw4,(0.&40.)Pw5,(0.&40.)Pw6,(0.&40.)Pw7,(0.&40.)Pw8,(0.&40.)Pw9,(0.&40.)Pw10,(0.&40.)Pq0,(0.&8.)Pq1,(2>.(0.&8.))Pq2,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pnw,$6.P,(25.(27.=R1.)(18.R1.(1<.+2.+40.)))P,(30.$=.R3.$31.(32.$33.(36.R13.)(32.$33.(3>.R12.)(32.$33.(3>.R11.)(32.$33.(36.R10.)(32.$33.(36.R?.)(32.$33.(36.R>.)(32.$33.(36.R=.)(32.$33.(36.R<.)(32.$33.(36.R;.)(32.$33.(36.R:.)(32.$33.(36.R9.)(37.$33.)))))))))))))P,(30.$=.R4.(1;.$31.+390.)(32.$33.(34.R9.)(32.$33.(35.#7.R8.)(32.$33.(36.R7.)(37.$33.)))))P,(38.$=.R5.)(<.$=.Lms',$>.(39.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(25.(5.$>.R2.(?.(10.R19.R33.R32.R31.R30.R2?.R2>.(11.&40.+1.)(11.&40.(3?.R7.+1000.))R2=.R2<.R2;.R2:.R29.R28.R27.R26.(11.&40.$12.)(11.&40.$13.)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R:.(11.&40.+404:8.)R9.(14.(0.&40.))R1.(15.$=.)))(25.(3:.(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+28.)(1;.$31.+30.))(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+398.)(1;.$31.+3:0.))(37.(3;.$6.$6.))))R8.R1.)(25.(3<.$=.R8.R1.)(25.(38.$=.R1.)(25.(30.$=.R1.$31.(32.$33.(36.R18.)(32.$33.(3>.R17.)(32.$33.(3>.R16.)(32.$33.(36.R15.)(32.$33.(36.R14.)(32.$33.(36.R13.)(32.$33.(36.(11.&40.+1.))(32.$33.(36.R11.)(32.$33.(36.R10.)(32.$33.(36.R?.)(32.$33.(36.R>.)(37.$33.)))))))))))))(30.$=.R1.(1;.$31.+390.)(32.$33.(34.R=.)(32.$33.(35.#7.R<.)(32.$33.(36.(11.&40.R7.))(37.$33.)))))))))))(?.(10.R17.R31.R30.R2?.R2>.R2=.R2<.(11.&40.+1000.)(11.&40.R5.)R2;.R2:.R29.R28.R27.R26.R25.R24.(11.&40.$12.)(11.&40.$13.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R8.(11.&40.+4041<.)R7.(14.(0.&40.))R6.(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until nw. intros NW HC TC MI.
  pose proof (munch_refl [(RCTX + 40, RCTX + 48); (RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (512968 + 912) with 513880 in TC.
  change (512968 + 40) with 513008 in MU. change (512968 + 48) with 513016 in MU. change (512968 + 920) with 513888 in MU. change (512968 + 928) with 513896 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma ram_bl_ok : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Pw0,(0.&40.)Pw1,(0.&40.)Pw2,(0.&40.)Pw3,(0.&40.)Pw4,(0.&40.)Pw5,(0.&40.)Pw6,(0.&40.)Pw7,(0.&40.)Pw8,(0.&40.)Pw9,(0.&40.)Pw10,(0.&40.)Pq0,(0.&8.)Pq1,(2>.(0.&8.))Pq2,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pnw,$6.P,(25.(27.=R1.)(18.R1.(1<.+2.+40.)))P,(30.$=.R3.$31.(32.$33.(36.R13.)(32.$33.(3>.R12.)(32.$33.(3>.R11.)(32.$33.(36.R10.)(32.$33.(36.R?.)(32.$33.(36.R>.)(32.$33.(36.R=.)(32.$33.(36.R<.)(32.$33.(36.R;.)(32.$33.(36.R:.)(32.$33.(36.R9.)(37.$33.)))))))))))))P,(30.$=.R4.(1;.$31.+390.)(32.$33.(34.R9.)(32.$33.(35.#7.R8.)(32.$33.(36.R7.)(37.$33.)))))P,(38.$=.R5.)(<.$=.Lms',$>.(39.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(25.(5.$>.R2.(?.(10.R19.R32.R31.R30.R2?.R2>.R2=.(11.&40.+1.)(11.&40.(3?.R7.+1000.))(11.&40.R7.)R2<.R2;.R2:.R29.R28.R27.R26.(11.&40.$12.)(11.&40.$13.)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R:.(11.&40.+404:8.)R9.(14.(0.&40.))R1.(15.$=.)))(25.(3:.(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+28.)(1;.$31.+30.))(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+398.)(1;.$31.+3:0.))(37.(3;.$6.$6.))))R8.R1.)(25.(3<.$=.R8.R1.)(25.(38.$=.R1.)(25.(30.$=.R1.$31.(32.$33.(36.R18.)(32.$33.(3>.R17.)(32.$33.(3>.R16.)(32.$33.(36.R15.)(32.$33.(36.R14.)(32.$33.(36.R13.)(32.$33.(36.(11.&40.+1.))(32.$33.(36.R11.)(32.$33.(36.R10.)(32.$33.(36.R?.)(32.$33.(36.R>.)(37.$33.)))))))))))))(30.$=.R1.(1;.$31.+390.)(32.$33.(34.R=.)(32.$33.(35.#7.R<.)(32.$33.(36.(11.&40.R7.))(37.$33.)))))))))))(?.(10.R17.R30.R2?.R2>.R2=.R2<.R2;.(11.&40.+1000.)(11.&40.R5.)(11.&40.R5.)R2:.R29.R28.R27.R26.R25.R24.(11.&40.$12.)(11.&40.$13.)R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R8.(11.&40.+403<0.)R7.(14.(0.&40.))R6.(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until nw. intros NW HC TC MI.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  eapply (ram_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L19051936761.48L22706556426.46L2567834584.48 L31332194325.46L31382962973.48L33454592472.48L47898930136.48L811409880.48  00000100700800>00?00@00A00BSS1y2HySS1y2HySSSS". (* [comment removed for export] *)
#[using="Type"] Lemma ram_brk_dead : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Pq0,(0.&8.)Pq1,(2>.(0.&8.))Pq2,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pst,$3.P,(4.VhRP,R1.R3.)P,(3:.(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+398.)(1;.$31.+3:0.))(37.(3;.$6.$6.)))R4.R3.)P,(3<.$=.R5.R4.)P,(5.$6.(7.(8.R4.))=)P,(30.$=.R6.(1;.$31.+390.)(32.$33.(34.R<.)(32.$33.(35.#7.R;.)(32.$33.(36.R:.)(37.$33.)))))P,(5.(0.&8.)R=.(40.(41.(8.R6.))))P,(5.(2>.(0.&8.))R=.(42.#7.))P,(38.$=.R9.)(<.$=.Lms',$>.(39.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(25.(5.$>.R2.(?.(10.R13.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(11.&40.=)(11.&40.-1.)R25.R24.R23.R22.R21.R20.(11.&40.$12.)(11.&40.$13.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R?.(11.&40.+40448.)R>.(14.(0.&40.))R1.(15.$=.)))(25.(3:.(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+398.)(1;.$31.+3:0.))(37.(3;.$6.$6.)))R<.R1.)(25.(3<.$=.R<.R1.)(25.(38.$=.R1.)(4.VhRP,(43.(44.$45.)R;.)R1.))))))(?.(10.R11.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(11.&40.$12.)(11.&40.$13.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R=.(11.&40.+40430.)R<.(14.(0.&40.))R:.(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
  dpose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  lazymatch type of C1 with rw_cells _ _ _ ?cs =>
    assert (C1' : rw_cells rsegs m RCTX cs)
      by (eapply HP_RMallocKit_B.rrw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
          rewrite wa_unsigned by (unfold RCTX in *; lia); unfold RCTX in *; cbn; lia) end.
  clear C1.
  pose proof (munch_refl [(RCTX + 920, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (512968 + 912) with 513880 in TC.
  change (512968 + 920) with 513888 in MU, MU0. change (512968 + 928) with 513896 in MU, MU0.
  (* [comment removed for export] *)
  st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : rmrep (upd_ctx (set_brk BrkDead) st) mX) end.
  { eapply (rmrep_ctx_frameW st _ m0 _ [(RCTX + 920, RCTX + 928)]%Z MR); try reflexivity.
    - unfold RCTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
    - first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_tail_cells, brk_word, RCTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (512968 + 912) with 513880.
      replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
      lazymatch goal with H : rw_cells rsegs ?mX 513880 _ |- _ => exact H end. }
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L31196698808.37L44646566339.37L55245887060.3700000;00@00KS3old2O02O1S3oldS3old2O02O1". (* [comment removed for export] *)
#[using="Type"] Lemma ram_bl_fail : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pst,$3.Pold,$6.P,(4.VhRP,R2.R3.)P,(5.$6.(7.(8.R3.))=)P,(18.=R3.)P,(18.(1;.R4.+1000.)(1<.+2.+40.))P,(38.$=.R7.)(<.$=.Lms',$>.(39.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(25.(5.$>.R2.(?.(10.R=.R24.R23.R22.R21.R20.R1?.(11.&40.+1000.)(11.&40.(1;.R8.+1000.))(11.&40.=)(11.&40.-1.)R1>.R1=.R1<.R1;.R1:.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R<.(11.&40.+40448.)R;.(14.(0.&40.))R1.(15.$=.)))(25.(3:.(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+398.)(1;.$31.+3:0.))(37.(3;.$6.$6.)))R:.R1.)(25.(3<.$=.R:.R1.)(25.(38.$=.R1.)(4.VhRP,(43.(44.$45.)R9.)R1.))))))(?.(10.R;.R22.R21.R20.R1?.R1>.R1=.(11.&40.+1000.)(11.&40.(1;.R6.+1000.))(11.&40.R6.)(11.&40.-1.)R1<.R1;.R1:.R19.R18.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)R:.(11.&40.+403<0.)R9.(14.(0.&40.))R8.(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until old. intros MR CNT O0 O1 MI.
  dpose MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl rsegs m) CNT C6 eq_refl eq_refl MI).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L22925851801.40L3023788465.47 00000<00GS3cur2C03C1bS3cur1q1r1H". (* [comment removed for export] *)
#[using="Type"] Lemma ram_bu_fail : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_H ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Pq0,(0.&8.)Pq1,(2>.(0.&8.))PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pst,$3.Pcur,$6.P,(4.VhRP,R2.R4.)P,(3:.(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+398.)(1;.$31.+3:0.))(37.(3;.$6.$6.)))R5.R4.)P,(3<.$=.R6.R5.)P,(5.$6.(7.(8.R5.))=)P,(18.=R5.)P,(18.R6.(1<.+2.+40.))P,(30.$=.R9.(1;.$31.+390.)(32.$33.(34.R>.)(32.$33.(35.#7.R=.)(32.$33.(36.(11.&40.R7.))(37.$33.)))))P,(5.(0.&8.)R?.(40.(41.(8.R9.))))P,(5.(2>.(0.&8.))R?.(42.#7.))P,(38.$=.R<.)(<.$=.Lms',$>.(39.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(25.(5.$>.R2.(?.(10.R15.R2=.R2<.R2;.R2:.R29.R28.(11.&40.+1000.)(11.&40.(1;.R=.+2000.))(11.&40.=)(11.&40.-1.)R26.R25.R24.R23.R22.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R12.(11.&40.+40448.)R11.(14.(0.&40.))R1.(15.$=.)))(25.(3:.(32.(3;.$6.$6.)(1:.$6.$6.(1;.$31.+398.)(1;.$31.+3:0.))(37.(3;.$6.$6.)))R?.R1.)(25.(3<.$=.R?.R1.)(25.(38.$=.R1.)(4.VhRP,(43.(44.$45.)R>.)R1.))))))(?.(10.R13.R2;.R2:.R29.R28.R27.R26.(11.&40.+1000.)(11.&40.(1;.R;.+2000.))(11.&40.R;.)R25.R24.R23.R22.R21.R20.(11.&40.+=6.)(11.&40.$12.)(11.&40.$13.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R10.(11.&40.+403?<.)R?.(14.(0.&40.))R=.(15.$=.)))")
(* [comment removed for export] *).
Proof.
  intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.
  (* [comment removed for export] *)
  st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
  { apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
  rewrite CF; clear CF.
  eapply (ram_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
