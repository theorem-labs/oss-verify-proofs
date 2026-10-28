(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac ITree Nodes SysStep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_F_syscalls () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.SysStep.sysret_val"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.SysStep.sysret_errno"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "sysret_post"; "stdpp.bitvector.definitions.Z_to_bv"; "close_ret"; "close_errno"].

Definition rsegs := usegs.

Definition sysret_entry := 0x3f928%Z.
Definition read_entry := 0x4731c%Z.
Definition close_entry := 0x472bc%Z.
Definition open_entry := 0x3f7dc%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sysret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r errv : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_F_syscalls ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O16.O15.O14.O13.R?.R>.R=.O12.O11.(8.O6.)R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O4.(9.O16.)O3.(:.(2.&40.))R1.(;.$<.)))(4.(=.(>.(?.$10.$10.)(11.$10.$10.(12.(13.&40.O15.)+10.)(13.&40.O15.))(>.(?.$10.$10.)(11.$10.$10.(14.(13.&40.O13.)-:4.)(14.(14.(13.&40.O13.)-:4.)+4.))(15.(?.$10.$10.))))O1.R1.)(4.(16.$<.O1.R1.)(4.(17.$<.R1.)(4.(18.$<.R1.O2.(13.&40.O15.))(19.$<.R1.(14.(13.&40.O13.)-:4.)(>.$1:.(1;.(1<.O6.O5.))(15.$1:.)))))))))))))))))))))))")
(* [comment removed for export] *).

Lemma sysret_spec : ltac2:(CDefT.buildp (gd_tbl_HP_F_syscalls ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1=.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Perrv,(2.&40.)Plo,$10.P,(18.$<.R3.R1.(13.&40.R23.))P,(19.$<.R4.(14.(13.&40.R22.)-:4.)(>.$1:.(1;.R3.)(15.$1:.)))P,(17.$<.R5.)P,(1>.R4.(12.(13.&40.R26.)+10.))P,(1?.(1>.(14.(14.(13.&40.R25.)-:4.)+4.)(12.(13.&40.R27.)+10.))(1>.(13.&40.R27.)(14.(13.&40.R25.)-:4.)))P,(1>.+:4.(13.&40.R26.))(20.$<.(21.R2:.R29.R28.R27.R23.R22.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R21.R8.R;.R:.R7.R9.)(6.(7.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.)R;.(22.&40.+3?928.)R:.(:.(2.&40.))R9.(;.$<.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros ST ERR MI LO SEP TP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 3 step. if_cases Hc; zify_cond Hc.
  - (* [comment removed for export] *)
    step. unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_small a0) by lia. finish.
  - carve_frame 16%nat ST.
    do 14 step.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    rewrite negw_errno in ERR by lia.
    unfold sysret_post, sysret_val, sysret_errno. rewrite (errno_of_big a0) by lia.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition read_ret (a : read_ans) : word :=
  match a with RdErr _ => Z_to_bv 64 (-1) | RdData bs => Z_to_bv 64 (Z.of_nat (length bs)) end.

Definition read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B : Z) (n : nat) (junk : list byte) (errv : word) (lo : Z) (m : word -> option byte)
    (a : read_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (read_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (B, B + Z.of_nat n); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ match a with
       | RdErr e => rw_cells rsegs m' B [CB n junk]
                    /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 e)] /\ (1 <= e <= 4095)%Z
       | RdData bs => rw_cells rsegs m' B [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)]
                      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv] /\ (length bs <= n)%nat
       end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition close_ret (a : sret) : word :=
  match a with
  | SVal _ => Z_to_bv 64 0
  | SErr e => if (e =? EINTR)%Z then Z_to_bv 64 0 else Z_to_bv 64 (-1)
  end.
Definition close_errno (a : sret) (errv : word) : word :=
  match a with
  | SVal _ => errv
  | SErr e => if (e =? EINTR)%Z then errv else Z_to_bv 64 e
  end.

Definition close_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (errv : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_F_syscalls ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O16.O15.O14.O13.R?.R>.R=.O12.O11.(23.O1.)R<.R;.R:.R9.R8.R7.R6.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R5.R4.R3.R2.)O6.(9.O16.)O5.(:.(2.&40.))R1.(;.$<.)))(4.(=.(>.(?.$10.$10.)(11.$10.$10.(12.(13.&40.O15.)+20.)(13.&40.O15.))(>.(?.$10.$10.)(11.$10.$10.(14.(13.&40.O13.)-:4.)(14.(14.(13.&40.O13.)-:4.)+4.))(15.(?.$10.$10.))))O2.R1.)(4.(16.$<.O2.R1.)(4.(17.$<.R1.)(4.(18.$<.R1.O3.(13.&40.O15.))(19.$<.R1.(14.(13.&40.O13.)-:4.)(>.$1:.(1;.(24.O1.O4.))(15.$1:.)))))))))))))))))))))))")
(* [comment removed for export] *).


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition got_ssp := 0x4bcd8%Z.
Definition ssp_guard := 0x7d330%Z.

Definition open_ret (a : sret) : word :=
  match a with SVal fd => Z_to_bv 64 fd | SErr _ => Z_to_bv 64 (-1) end.
Definition open_errno (a : sret) (errv : word) : word :=
  match a with SVal _ => errv | SErr e => Z_to_bv 64 e end.

Definition open_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P : Z) (path : list byte) (errv canary : word) (lo : Z) (m : word -> option byte) (a : sret) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (open_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (open_errno a errv)]
    /\ bytes_at rsegs m' P (path ++ [Z_to_bv 8 0])
    /\ rw_cells rsegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)]
    /\ rw_cells rsegs m' ssp_guard [C8 canary]
    /\ match a with SVal fd => (3 <= fd <= 4096)%Z | SErr e => (1 <= e <= 4095)%Z end.

