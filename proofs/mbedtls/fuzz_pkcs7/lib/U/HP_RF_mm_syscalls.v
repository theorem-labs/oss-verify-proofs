(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac ITree Nodes SysStep Decode.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_mm_syscalls.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_F_syscalls HP_RMallocRep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require KArith Malloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_mm_syscalls () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Decode.mmap_len"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.impl"; "RocqVerifyHarness.AgentSubmission.Lib.Nodes.node"; "RocqVerifyHarness.AgentSubmission.Lib.Nodes.at_node"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.Exc.exc"; "RocqVerifyHarness.AgentSubmission.Lib.Decode.range_ans"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.enode"; "RocqVerifyHarness.AgentSubmission.Lib.Nodes.NMunmap"; "RocqVerifyHarness.AgentSubmission.Lib.Decode.dec_munmap"; "RocqVerifyHarness.AgentSubmission.Lib.ITree.epost"; "RP_1.rmunmap_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmunmap_entry"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RPAGE_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Nodes.NMprotect"; "RocqVerifyHarness.AgentSubmission.Lib.Decode.dec_mprotect"; "RP_1.rmprotect_post"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmprotect_entry"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Lib.Decode.mmap_addr_ok"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mmap_answer_ok"; "Corelib.Init.Datatypes.false"].

(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (match a with RgDone true => True | _ => wmono rsegs m m' end)
    /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ match a with RgErr e => (1 <= e <= 4095)%Z | _ => True end.

#[using="Type"] Lemma rmunmap_spec : ltac2:(CDefT.buildp (gd_tbl_HP_RF_mm_syscalls ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PA,$3.PL,$3.Perrv,(0.&40.)Plo,$3.P,(4.$5.R5.R1.(6.&40.R25.))P,(7.$5.R6.(8.(6.&40.R24.)-:4.)(9.$:.(;.R3.)(<.$:.)))P,(=.$5.R7.)P,(>.(0.&40.)R20.(?.&40.R7.))P,(>.(0.&40.)R20.(?.&40.R7.))P,(10.=R9.)P,(11.(8.R:.(12.R9.))(13.+2.+40.))P,(14.(10.=R:.)(10.R:.(13.+2.+40.)))P,(11.R9.(15.(6.&40.R2=.)+30.))P,(16.(11.(8.(8.(6.&40.R2<.)-:4.)+4.)(15.(6.&40.R2>.)+30.))(11.(6.&40.R2>.)(8.(6.&40.R2<.)-:4.)))P,(16.(11.(8.R>.(12.R=.))R;.)(11.(6.&40.R2?.)R>.))P,(16.(11.(8.R?.(12.R>.))(8.(6.&40.R2>.)-:4.))(11.(8.(8.(6.&40.R2>.)-:4.)+4.)R?.))P,(11.+:4.(6.&40.R2?.))(17.$18.$5.(19.$5.)(1:.$1;.)(1<.$18.$1;.(1=.R11.R10.)(1>.R11.R10.))(1?.$1;.(20.R33.R32.R31.R30.R2<.R2;.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R14.R13.R11.R10.R?.R>.R12.))(21.(22.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(?.&40.$23.)R13.(24.(0.&40.))R12.(25.$5.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros ST ERR MI -> -> A0 AL L0 LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmunmap_entry. apply impl_enode.
  carve_frame 32%nat ST.
  do 6 step. (* [comment removed for export] *)
  step. step. (* [comment removed for export] *)
  do 3 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as D. clear Hdec.
  destruct ans as [e|[|]].
  - destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
Qed.

#[using="Type"] Lemma rmprotect_args : ltac2:(CDefT.buildp (gd_tbl_HP_RF_mm_syscalls ()) "PA,$3.PL,$3.P,(>.$3.(26.R2.+1000.)=)P,(>.$3.(26.R2.+1000.)=)P,(11.=R4.)P,(11.=R4.)P,(11.(8.(8.R6.R5.)+1000.)(13.+2.+40.))(14.(>.(0.&40.)(?.&40.(27.+?????????????000.(6.&40.(?.&40.R7.))))(?.&40.R7.))(>.(0.&40.)(?.&40.(15.(6.&40.(?.&40.(27.(6.&40.(?.&40.(8.(8.R7.R6.)+???.)))+?????????????000.)))(6.&40.(?.&40.(27.+?????????????000.(6.&40.(?.&40.R7.)))))))(?.&40.R6.)))")
(* [comment removed for export] *).
Proof.
  intros A L HA HL A0 L0 B. rewrite (Z.land_comm 18446744073709547520).
  rewrite (unsigned_lit A), (unsigned_lit (A + L + 4095)) by lia. rewrite !land_m4096 by lia.
  assert (E1 : (A - A mod 4096 = A)%Z) by lia.
  assert (E2 : ((A + L + 4095) - (A + L + 4095) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
  rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (rg_errno a errv)]
    /\ rw_cells rsegs m' RPAGE_SIZE [C8 (Z_to_bv 64 4096)]
    /\ match a with
       | RgErr e => (1 <= e <= 4095)%Z
       | RgDone true => rw_cells rsegs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
       | RgDone false => True
       end.

#[using="Type"] Lemma rmprotect_spec : ltac2:(CDefT.buildp (gd_tbl_HP_RF_mm_syscalls ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PA,$3.PL,$3.PP,$3.Perrv,(0.&40.)Plo,$3.P,(4.$5.R6.R1.(6.&40.R26.))P,(7.$5.R7.(8.(6.&40.R25.)-:4.)(9.$:.(;.R3.)(<.$:.)))P,(7.$5.R8.$28.(9.$:.(29.(?.&40.+1000.))(<.$:.)))P,(=.$5.R9.)P,(>.(0.&40.)R22.(?.&40.R9.))P,(>.(0.&40.)R22.(?.&40.R9.))P,(>.(0.&40.)R22.(?.&40.R9.))P,(>.$3.(26.R<.+1000.)=)P,(>.$3.(26.R<.+1000.)=)P,(10.=R>.)P,(10.=R>.)P,(11.(8.(8.R10.R?.)+1000.)(13.+2.+40.))P,(14.(11.=R?.)(10.R?.(13.+2.+40.)))P,(11.R>.(15.(6.&40.R33.)+20.))P,(16.(11.(8.(8.(6.&40.R32.)-:4.)+4.)(15.(6.&40.R34.)+20.))(11.(6.&40.R34.)(8.(6.&40.R32.)-:4.)))P,(16.(11.(8.R14.R13.)R10.)(11.(6.&40.R35.)R14.))P,(16.(11.(8.R15.R14.)(8.(6.&40.R34.)-:4.))(11.(8.(8.(6.&40.R34.)-:4.)+4.)R15.))P,(16.(11.(8.R16.R15.)+10000.)(11.+7>000.R16.))P,(11.+7>000.R13.)P,(16.(11.(8.(8.(6.&40.R37.)-:4.)+4.)$28.)(11.(8.$28.+8.)(8.(6.&40.R37.)-:4.)))P,(11.+:4.(6.&40.R38.))(17.$18.$5.(19.$5.)(1:.$1;.)(1<.$18.$1;.(2:.R1:.R19.R18.)(2;.R1:.R19.))(1?.$1;.(2<.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R1:.R19.R17.R16.R1;.))(21.(22.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R1=.(?.&40.$2=.)R1<.(24.(0.&40.))R1;.(25.$5.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros ST ERR PG MI -> -> -> AA LA A0 L0 AL PR LO SEP1 SEP2 SEP3 SEP4 SLO SEP5 TP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  unfold rmprotect_entry, RPAGE_SIZE in *. apply impl_enode.
  carve_frame 16%nat ST.
  step. step. step. step.
  do 7 step.
  destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) AL) as [E1 E2]. rewrite E2, E1.
  step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as D. clear Hdec.
  rewrite (mmap_len_aligned L LA) in D.
  destruct ans as [e|[|]].
  - destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    step. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; lia.
  - rewrite D.
    assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr rsegs x = false) by (intros x Hx; apply ref_ro_addr_false; lia).
    sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish.
  - rewrite D. unfold eff0. sys_nret.
    step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
    unfold rmprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed.

#[using="Type"] Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
    : machine_state -> Prop :=
  fun ms' =>
    match a with
    | MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom rsegs)
        /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
        /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ stk rsegs m' lo (bv_unsigned sp)
        /\ rw_cells rsegs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
        /\ (1 <= e <= 4095)%Z
    | MmOk x =>
        (* [comment removed for export] *)
        mmap_addr_ok len avoid x = true /\
        (rceil < x + mmap_len len \/
         exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom rsegs)
         /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
         /\ wmono rsegs m m2 /\ mem_inv rsegs m2
         /\ stk rsegs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
         /\ rw_cells rsegs m2 (errno_addr tp) [C4 errv]
         /\ x + mmap_len len <= rceil)
    end.

(* [comment removed for export] *)
#[using="Type"] Lemma rmmap_rejects_high : ltac2:(CDefT.buildp (gd_tbl_HP_RF_mm_syscalls ()) "Pceil,$3.Plive,(2>.(2?.$3.$3.))Plen,$3.Pavoid,(2>.(2?.$3.$3.))Px,$3.P,(11.=R3.)P,(11.R6.(30.VhRP,))P,(>.$31.(32.R5.R4.R3.)$33.)P,(10.(30.VhRP,)(8.R4.(12.R6.)))(>.$31.(34.R9.R8.R7.R5.)$35.)")
(* [comment removed for export] *).
Proof.
  intros ceil live len avoid x L0 CE AOK BAD.
  pose proof (mmap_addr_ok_true _ _ _ AOK) as ((XA & X0 & XC) & _). rewrite grant_top_max_val in XC.
  pose proof (mmap_len_ge len) as ML.
  unfold Malloc.mmap_answer_ok, Malloc.is_errno_form, Malloc.TWO64.
  replace (2 ^ 64 - 4095 <=? x)%Z with false by (symmetry; apply Z.leb_gt; lia). cbn [andb orb].
  unfold mmap_len in BAD. rewrite <- KArith.round_up_pg_eq in BAD.
  destruct (0 <? x)%Z; destruct (x mod Malloc.PGSZ =? 0)%Z; cbn [andb]; try reflexivity.
  replace (x + Malloc.round_up_pg len <=? ceil)%Z with false; [reflexivity|].
  symmetry. apply Z.leb_gt. lia.
Qed.

#[using="Type"] Lemma rmmap_anon_spec : forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
  let prot := (if isnone then 0 else 3)%Z in
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < len <= 2^62)%Z ->
  (lo <= bv_unsigned sp - 80)%Z -> (rceil <= lo)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none len avoid else dec_mmap len avoid))
       (epost (rmmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
  pose proof (wmono_refl rsegs m) as WM.
  rceilb.
  assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  step. step.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec.
  assert (D : match ans with
              | MmErr e => rsp = efferr e /\ (1 <= e <= 4095)%Z
              | MmOk a => rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] []
                                 else mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])
                          /\ mmap_addr_ok len avoid a = true
              end).
  { destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ Hdec) as D | pose proof (dec_mmap_Some _ _ _ _ Hdec) as D];
      destruct ans; exact D. }
  clear Hdec. destruct ans as [e|x].
  - clear MU1. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
    step. step. step.
    rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
    if_cases K; zify_cond K.
    + (* [comment removed for export] *)
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      finish; lia.
    + (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by lia.
      step. step. step. step.
      replace (Z_to_bv 64 18446744073709551604) with (errno_ret 12) by (apply bv_eq; reflexivity).
      step. call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
      unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
      do 10 step. release_frame FR ST (bv_unsigned sp).
      unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia).
      finish; lia.
  - clear MU. destruct D as [-> Hok]. pose proof (mmap_addr_ok_true _ _ _ Hok) as ((XA & X0 & XC) & XAV).
    rewrite grant_top_max_val in XC. pose proof (mmap_len_ge len) as ML.   (* [comment removed for export] *)
    destruct (Z_lt_le_dec rceil (x + mmap_len len)) as [BAD|XR].
    { (* [comment removed for export] *) apply evt_done. split; [exact Hok| left; exact BAD]. }
    lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
    destruct isnone; sys_nret_raw.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
           set (m' := mm);
           assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
           assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
         end.
    1: pose proof (rw_cells_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_unmaps_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
    2: pose proof (rw_cells_zeros_other rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
       pose proof (stk_zeros rsegs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
    all: fold m' in FR', ST'; clear FR; rename ST into ST0.
    all: step; step; step.
    all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
    all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].
    (* [comment removed for export] *)
    all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.
    (* [comment removed for export] *)
    all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
    all: apply evt_done; unfold rmmap_anon_post, mmap_raw; cbv iota; split; [exact Hok|]; right.
    all: deexists 14; eexists; split; [subst m'; reflexivity|].
    all: split; [exact MU1|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST'|]; split; [exact ERR| exact XR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    R a r u /\
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
    /\ (u = false -> wmono rsegs m m')
    /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 (sysret_errno r errv)].

#[using="Type"] Lemma rmmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L P : Z) (errv : word) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = fixed_shape A L r u) ->
  stk rsegs m lo (bv_unsigned sp) ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 50 ->
  a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
  (0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z -> (0 <= P < 4)%Z ->
  (lo <= bv_unsigned sp - 80)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
  (A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl rsegs (at_node rsegs) (enode (NMmap A L P 50) dec)
       (epost (rmmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros DEC ST ERR MI -> -> -> -> -> -> A0 LEN AL PR LO SEP1 SEP2 SEP3 TP.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (mmap_len_ge L) as ML.
  unfold rmmap_entry. apply impl_enode.
  carve_frame 64%nat ST.
  do 8 step.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
  step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
  (* [comment removed for export] *)
  set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
  set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 P).
  do 6 step. step. step. do 6 step. step.
  subst z0 zm1 z50 zA zL zP.
  step. step. step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. ddestruct (DEC rsp ans Hdec) as (r & u & HR & ->). clear Hdec.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  destruct u; unfold fixed_shape; cbv iota.
  all: sys_nret.
  all: step; step; step.
  all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
  all: step; call_sp sysret_spec; [exact ST | exact ERR | exact MI | lia | lia | lia |]; rename PC into ST; rename POST into ERR.
  all: do 10 step; release_frame FR ST (bv_unsigned sp).
  all: unfold rmmap_fixed_post; apply evt_done; exists r; eexists; deexists 15; split; [exact HR|]; split; [reflexivity|].
  all: split; [ eapply munch_weaken; [|exact MU]; intros y; cbn; lia |].
  all: split; [ first [intros; discriminate | intros _; assumption] |].
  all: split; [lazymatch goal with H : mem_inv rsegs ?mm |- mem_inv rsegs ?mm => exact H end|].
  all: split; [lazymatch goal with H : stk rsegs ?mm ?a ?b |- stk rsegs ?mm _ _ => exact H end|].
  all: lazymatch goal with H : rw_cells rsegs ?mm ?a ?c |- rw_cells rsegs ?mm _ _ => exact H end.
Qed.

End RP_1.
