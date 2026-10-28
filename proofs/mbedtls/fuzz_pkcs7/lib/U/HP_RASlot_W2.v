(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 F_ntf_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A HP_RMallocKit_A2 HP_RMalloc_fp HP_RF_enframe HP_RF_malloc_entry HP_RF_malloc_small HP_RF_ntf_A HP_RF_ntf_C HP_RAllocSlot_iface HP_RASlot_I HP_RMallocKit_A3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RASlot_W2 () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rp_canary"; "Corelib.Init.Datatypes.nil"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "RP_1.rta_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.lowbit"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.upd_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.m_set_avail"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_free.sxv"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Definition rta_frame (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell := ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W2 ()) "(0.$1.(2.#30.O<.)(0.$1.(3.(4.(5.VhRP,)))(0.$1.(3.O;.)(0.$1.(3.O:.)(0.$1.(3.O9.)(0.$1.(3.O8.)(0.$1.(3.O7.)(0.$1.(3.O6.)(0.$1.(3.O5.)(0.$1.(3.O4.)(0.$1.(3.O3.)(0.$1.(3.O2.)(0.$1.(3.O1.)(6.$1.))))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ras_ret : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W2 ()) "Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Px1,(7.&40.)Ps9v,(7.&40.)Ps8v,(7.&40.)Ps7v,(7.&40.)Ps6v,(7.&40.)Ps5v,(7.&40.)Ps4v,(7.&40.)Ps3v,(7.&40.)Ps2v,(7.&40.)Ps1v,(7.&40.)Ps0v,(7.&40.)Prav,(7.&40.)PF,(8.&5.(7.&40.))Pfc,(7.&20.)Pm0,P,(7.&40.)(9.(7.&8.))Pm,P,(7.&40.)(9.(7.&8.))PW,(:.(;.$<.$<.))Pjunk,(:.(7.&8.))Pst',$=.Plo,$<.P,(>.VhRP,R2.R5.)P,(?.$10.R6.)P,(11.$10.R7.(12.(13.&40.R33.)-90.)(14.R5.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.))P,(15.$10.R8.R4.(12.(13.&40.R34.)-90.))P,(16.(17.VhRP,)R5.)P,(16.R6.(18.(13.&40.R36.)+90.))P,(19.(0.(;.$<.$<.)(1:.$<.$<.(18.(13.&40.R37.)+90.)(13.&40.R37.))R:.)R<.R;.)P,(1;.$10.R=.R<.)(1<.$10.Lms',$1=.(1>.(7.&40.)La1',(7.&40.)(1>.(7.&40.)La2',(7.&40.)(1>.P,(7.&40.)(9.(7.&8.))Lm',P,(7.&40.)(9.(7.&8.))(1?.(20.$1=.R4.(21.(22.R15.R3=.R3<.R3;.R3:.R39.R38.R16.R17.R35.R3.R2.R32.R31.R30.R2?.R2>.R18.R19.R1:.R1;.R1<.R1=.R1>.R1?.R26.R25.R24.R23.R22.R21.)R14.(23.R15.)R13.(24.(7.&40.))R1.(25.$10.)))(1?.(19.(0.(;.$<.$<.)(1:.$<.$<.(18.(13.&40.R3=.)+90.)(13.&40.R3=.))R10.)R12.R1.)(1?.(1;.$10.R12.R1.)(1?.(?.$10.R1.)(1?.(15.$10.R1.R=.(13.&40.R3=.))(>.VhRP,R>.R1.)))))))))(21.(22.R1<.(26.&40.(12.(13.&40.R39.)-90.))R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(26.&40.$27.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R10.(26.&40.+41138.)R?.(24.(7.&40.))R=.(25.$10.)))")
(* [comment removed for export] *).
Proof.
  intros until lo. intros MR' MI FR ST LO LOLE MU WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  rceilb; unfold RSSP_GUARD, rta_frame in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st' mX)
      by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; rceilb; lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. deexists 3. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FIN.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : rceil <= lo.

#[using="MR MSL MASK CLO"] Lemma rfin_walk : ltac2:(CDefT.buildp (gd_tbl_HP_RASlot_W2 ()) "Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Px1,(7.&40.)Pgw,(7.&40.)Ps9v,(7.&40.)Ps8v,(7.&40.)Ps7v,(7.&40.)Ps6v,(7.&40.)Ps5v,(7.&40.)Ps4v,(7.&40.)Ps3v,(7.&40.)Ps2v,(7.&40.)Ps1v,(7.&40.)Ps0v,(7.&40.)Prav,(7.&40.)PF,(8.&5.(7.&40.))Pfc,(7.&20.)Pjunk,(:.(7.&8.))P,(20.$<.(13.&40.R?.)VG,)P,(11.$10.Vm,(12.(13.&40.R2<.)-90.)(14.R2.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.))P,(15.$10.Vm,Vlo,(12.(13.&40.R2=.)-90.))P,(16.Vlo,(18.(13.&40.R2>.)+90.))P,(?.$10.Vm,)(1<.$10.Lms',$1=.(1>.(7.&40.)La1',(7.&40.)(1>.(7.&40.)La2',(7.&40.)(1>.(7.&40.)La3',(7.&40.)(1>.P,(7.&40.)(9.(7.&8.))Lm',P,(7.&40.)(9.(7.&8.))(1>.$<.Lk,$<.(1?.(1?.(16.=R1.)(28.R1.+20.))(1?.(20.$<.(29.Vmask,)(2:.+2.R1.))(1?.(20.$1=.R6.(21.(22.R?.R36.R35.R34.R33.R32.R31.R10.R11.(4.R1.)R5.R4.R3.R2<.R2;.R2:.R29.R12.R13.R14.R15.R16.R17.R18.R19.R21.R20.R1?.R1>.R1=.R1<.)R>.(23.R?.)R=.(24.(7.&40.))R2.(25.$10.)))(1?.(19.(0.(;.$<.$<.)(1:.$<.$<.(18.(13.&40.R36.)+90.)(13.&40.R36.))(0.(;.$<.$<.)(1:.$<.$<.VG,(12.VG,+28.))(6.(;.$<.$<.))))Vm,R2.)(1?.(1;.$10.Vm,R2.)(1?.(?.$10.R2.)(1?.(15.$10.R2.Vlo,(13.&40.R36.))(>.VhRP,(2;.Vg,(2<.(18.Vmask,(29.Vmask,)))Vst,)R2.)))))))))))))(21.(22.R15.(26.&40.(12.(13.&40.R30.)-90.))R2?.R2>.R2=.R2<.R2;.R2:.R29.R14.(4.(2=.Vmask,))R28.R27.R26.R25.R24.R23.R22.R21.(26.&40.$27.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R8.(26.&40.+40:78.)R7.(24.(7.&40.))Vm,(25.$10.)))")
(* [comment removed for export] *).
Proof.
  intros until junk. intros HG FR ST LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  dpose (rmeta_chunk_facts st m g MR MSL) as (CH & Gpos & GC & GI1 & GI2 & _). fold G in CH, Gpos, GC, GI1, GI2.
  unfold meta_cells in CH. rewrite <- HG in CH.
  ddestruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
  assert (P2 : 0 < 2 ^ k <= mask).
  { ddestruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L). rewrite LB in E.
    apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
  assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
  pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
  rceilb; unfold rta_frame, RSSP_GUARD in *.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).
  (* [comment removed for export] *)
  pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl rsegs m) as WMg.
  step.
  lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- _ =>
    apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
             (meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
    [| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
     | reflexivity | cbn; tauto ];
    rewrite HG in H;
    pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
  end.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.
  { exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
  clear K0.
  (* [comment removed for export] *)
  step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
  step. step. change 125613361 with rDB32.
  step. step. step. rewrite (mul_srliw27_sxv k) by lia.
  pose proof (rdbi_range k) as DR.
  step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
  lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
  step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.
  (* [comment removed for export] *)
  step.
  rewrite ?LB in MR1.
  eapply evt_mono.
  { eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
      [exact MR1 | assumption | exact FR | exact ST | rceilb; lia | lia | exact MU | exact WM]. }
  cbv beta. (intros ms' dd_H; ddestruct dd_H as (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR')).
  deexists 4. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End FIN.

End RP_1.
