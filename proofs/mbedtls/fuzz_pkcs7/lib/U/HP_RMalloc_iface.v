(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RMalloc_iface () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RLIBC"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RERRNO"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RGOT_SSP"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.block"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.strip"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Heap.MallocHINV.HINV_from"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ref_reserved"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_brk"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.pow"; "RP_1.rclient_addr"; "Corelib.Init.Datatypes.option"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RP_1.rheap_pres"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.blk_addr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.blk_size"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RP_1.rclient_range"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "RP_1.RHEAP"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RP_1.RMALLOC_STACK"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RATP"; "RocqVerifyHarness.AgentSubmission.Heap.Monad.implM"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.bptr"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.raw_malloc"; "RP_1.rmalloc_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RP_1.RMALLOC_SYM"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc_iface.lb_remove"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_so"; "Corelib.Init.Datatypes.pair"; "RP_1.RFREE_STACK"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.raw_free"; "RP_1.rfree_post"; "RP_1.RFREE_SYM"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"].


(* [comment removed for export] *)
(* [comment removed for export] *)

Section RP_1. Context {hRP : run_params}.
Definition RMALLOC_SYM : Z := 0x3fbd8.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0x3fa98.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "(0.(1.(2.$3.O1.)(4.O1.(5.$6.+3:0.)))(0.(1.(2.$7.O1.)(4.O1.(5.$7.+4.)))(0.(1.(2.$8.O1.)(4.O1.(5.$8.+8.)))(1.(2.$9.O1.)(4.O1.(5.$9.+8.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "(:.$;.Lst,$;.(:.(<.$=.)LLB0,(<.$=.)(1.(>.$=.R1.O2.)(1.(?.$;.(10.R2.)(11.O3.))(1.(12.VhRP,R2.O1.)(13.$14.R2.(15.O3.)R1.))))))")
(* [comment removed for export] *).


#[using="Type"] Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof. rceilb.
  (intros s LB LB' m dd_H; ddestruct dd_H as (st & LB0 & HP & H1 & H2 & H3); intros P). dexists st, LB0. split; [|auto].
  eapply Permutation.Permutation_trans; [exact HP| exact P].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x48000 <= a < 0x7e000 /\ ~ ralloc_static a) \/ in_block LB a.

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "Pa,$16.P,(1.(2.=R1.)(4.R1.(17.+2.+40.)))P,(18.O4.O3.R2.)(1.(?.(19.(1:.&8.))A1.O1.(1;.R3.)A1.O2.(1;.R3.))P,(1<.(?.(19.(1:.&8.))(1=.$1>.O2.(1;.R3.))(1?.(1:.&8.))))(1<.(?.(19.(1:.&8.))(1=.$1>.O1.(1;.R4.))(1?.(1:.&8.)))))")
(* [comment removed for export] *).



#[using="hRP"] Lemma rheap_pres_weaken : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "PLB,(<.$=.)PLB',(<.$=.)PSP,$16.PSP',$16.Pm,$20.Pm',$20.P,(21.R6.R4.R2.R1.)P,(2.R5.R4.)P,Pb,$=.P,(22.$=.R1.R8.)(22.$=.R2.R:.)(21.R8.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "(0.(2.O3.O2.)(0.(1.(2.+48000.O2.)(1.(2.(5.O2.O1.)+7>000.)(1.(0.(2.(5.O2.O1.)$3.)(2.(5.$6.+3:0.)O2.))(1.(0.(2.(5.O2.O1.)$7.)(2.(5.$7.+4.)O2.))(1.(0.(2.(5.O2.O1.)$8.)(2.(5.$8.+8.)O2.))(0.(2.(5.O2.O1.)$9.)(2.(5.$9.+8.)O2.)))))))(:.$=.Lb,$=.(1.(22.$=.R1.O4.)(1.(2.(23.R1.)O2.)(2.(5.O2.O1.)(5.(23.R1.)(24.R1.))))))))")
(* [comment removed for export] *).

#[using="hRP"] Lemma rclient_range_addr : forall LB SP A n a,
  rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof. rceilb.
  intros LB SP A n a HR Ha. unfold rclient_range, rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *.
  destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [exact Hb|lia]].
Qed.

#[using="hRP"] Lemma rheap_pres_bytes_at : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "PLB,(<.$=.)PSP,$16.Pm,$20.Pm',$20.PA,$16.Pbs,(<.(1:.&8.))P,(21.R6.R5.R4.R3.)P,(25.$1>.R5.R3.R2.)P,(26.R8.R7.R4.(27.(28.(1:.&8.)R3.)))(25.$1>.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. rceilb.
  (intros LB SP m m' A bs HP dd_H; ddestruct dd_H as (H0 & H1 & HB); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [E _].
  rewrite E. reflexivity.
Qed.

#[using="hRP"] Lemma rheap_pres_wr_at : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "PLB,(<.$=.)PSP,$16.Pm,$20.Pm',$20.PA,$16.Pn,$16.P,(21.R6.R5.R4.R3.)P,(29.$1>.R5.R3.R2.)P,(26.R8.R7.R4.R3.)(29.$1>.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. rceilb.
  (intros LB SP m m' A n HP dd_H; ddestruct dd_H as (H0 & H1 & HW); intros HR). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia])) as [_ W].
  apply W. apply HW. exact Hi.
Qed.

#[using="hRP"] Lemma rheap_pres_rw_cells : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "PLB,(<.$=.)PSP,$16.Pm,$20.Pm',$20.PA,$16.Pcs,(<.$2:.)P,(21.R6.R5.R4.R3.)P,(2;.$1>.R5.R3.R2.)P,(26.R8.R7.R4.(27.(2<.R3.)))(2;.$1>.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rheap_pres_wr_at; eauto.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= rceil /\ (A + n <= 0x10000 \/ 0x7e000 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "(0.(2.(2=.VhRP,)(2>.$16.$16.O1.))(0.(1.(2.+48000.(2>.$16.$16.O1.))(1.(2.(2?.$16.$16.O1.)+7>000.)(1.(0.(2.(2?.$16.$16.O1.)$3.)(2.(5.$6.+3:0.)(2>.$16.$16.O1.)))(1.(0.(2.(2?.$16.$16.O1.)$8.)(2.(5.$8.+8.)(2>.$16.$16.O1.)))(0.(2.(2?.$16.$16.O1.)$9.)(2.(5.$9.+8.)(2>.$16.$16.O1.)))))))(:.$=.Lb,$=.(1.(22.$=.R1.O2.)(1.(2.(23.R1.)(2>.$16.$16.O1.))(2.(2?.$16.$16.O1.)(5.(23.R1.)(24.R1.))))))))")
(* [comment removed for export] *).


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raddr_exposed (s : PState) (n : Z) : Prop :=
  MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init rp_secret rp_canary rceil (reservedZ rsegs)).


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells rsegs m' A [CB (Z.to_nat n) junk]
           /\ (raddr_exposed s n -> A = ptr_addr s' p)
           (* [comment removed for export] *)
           /\ (forall (g : aptr) (i : Z), (s_slots (ps_m s')) !! (fst p) = Some (g, i) -> undersized (get_meta_rec (ps_m s') g) ->
                 junk = repeat (Z_to_bv 8 0) (Z.to_nat n))
       end.

Definition rmalloc_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(30.&5.(1:.&40.))Pfc,(1:.&20.)Pm,$20.Ps,$31.PLB,(<.$=.)Pn,$16.Plo,$16.PB,$16.Perrv,(1:.&40.)P,(32.R6.R5.R7.)P,(33.VhRP,R8.R3.)P,(2.(34.&40.R29.)R4.)P,(35.$1>.R:.R6.(34.&40.R2:.))P,(2.(2=.VhRP,)R7.)P,(2.R8.(36.(34.&40.R2<.)$37.))P,(2;.$1>.R=.(5.(34.&40.R2;.)-:4.)(38.$2:.(39.R7.)(3:.$2:.)))P,(3;.$1>.R>.)P,(?.(1:.&40.)R2=.(3<.&40.$3=.))P,(?.(1:.&40.)R28.(3<.&40.R=.))P,(1.(2.=R>.)(4.R>.(17.+2.+20.)))(3>.$31.$1>.(19.$3?.)(40.R?.)R11.(41.R33.R32.R31.R30.R2<.R2;.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R14.R13.R11.R10.R?.R>.R=.R12.)(42.(43.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.)R14.(3<.&40.$44.)R13.(1?.(1:.&40.))R12.(45.$1>.)))")
(* [comment removed for export] *).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "Lms',$46.(:.(1:.&40.)Lt0,(1:.&40.)(:.(1:.&40.)Lt1,(1:.&40.)(:.(1:.&40.)Lt2,(1:.&40.)(:.(1:.&40.)La0,(1:.&40.)(:.(1:.&40.)La1,(1:.&40.)(:.(1:.&40.)La2,(1:.&40.)(:.(1:.&40.)La3,(1:.&40.)(:.(1:.&40.)La4,(1:.&40.)(:.(1:.&40.)La5,(1:.&40.)(:.(1:.&40.)La6,(1:.&40.)(:.(1:.&40.)La7,(1:.&40.)(:.(1:.&40.)Lt3,(1:.&40.)(:.(1:.&40.)Lt4,(1:.&40.)(:.(1:.&40.)Lt5,(1:.&40.)(:.(1:.&40.)Lt6,(1:.&40.)(:.P,(1:.&40.)(19.(1:.&8.))Lm',P,(1:.&40.)(19.(1:.&8.))(1.(?.$46.R11.(42.(43.O1;.O1:.O19.O18.R10.R?.R>.O17.O16.R=.R<.R;.R:.R9.R8.R7.R6.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R5.R4.R3.R2.)O;.(47.O1;.)O:.(1?.(1:.&40.))R1.(45.$1>.)))(1.(3;.$1>.R1.)(1.(35.$1>.R1.O6.(34.&40.O1:.))(1.(2;.$1>.R1.(5.(34.&40.O18.)-:4.)(38.$2:.(39.O4.)(3:.$2:.)))(1.(33.VhRP,R1.O5.)(1.(21.(48.O7.O8.)(34.&40.O1:.)O3.R1.)(1.(?.(49.$16.$16.)(4:.O1.)(4:.O9.))(1.(?.$4;.(4<.O1.)(4<.O9.))(32.O1.(48.O7.O8.)R1.)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rfree_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(30.&5.(1:.&40.))Pfc,(1:.&20.)Pm,$20.Ps,$31.PLB,(<.$=.)Pp,$3?.PA,$16.Pn,$16.Plo,$16.PB,$16.Perrv,(1:.&40.)P,(32.R8.R7.R9.)P,(22.(49.(49.$3?.$16.)$16.)(4=.(49.$3?.$16.)$16.(4=.$3?.$16.R7.R6.)R5.)R8.)P,(33.VhRP,R;.R4.)P,(2.(34.&40.R2<.)R5.)P,(35.$1>.R=.R7.(34.&40.R2=.))P,(2.(2=.VhRP,)R8.)P,(2.R9.(36.(34.&40.R2?.)$4>.))P,(2;.$1>.R10.(5.(34.&40.R2>.)-:4.)(38.$2:.(39.R8.)(3:.$2:.)))P,(3;.$1>.R11.)P,(?.(1:.&40.)R30.(3<.&40.$3=.))P,(?.(1:.&40.)R2;.(3<.&40.R?.))(3>.$31.$1>.$4;.(4?.R11.)R13.(50.R35.R34.R33.R32.R2>.R2=.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R16.R15.R13.R12.R11.R>.R=.R<.R14.)(42.(43.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R16.(3<.&40.$51.)R15.(1?.(1:.&40.))R14.(45.$1>.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition rfree_null_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_iface ()) "Pra,(1:.&40.)Psp,(1:.&40.)Pgp,(1:.&40.)Ptp,(1:.&40.)Pt0,(1:.&40.)Pt1,(1:.&40.)Pt2,(1:.&40.)Ps0,(1:.&40.)Ps1,(1:.&40.)Pa0,(1:.&40.)Pa1,(1:.&40.)Pa2,(1:.&40.)Pa3,(1:.&40.)Pa4,(1:.&40.)Pa5,(1:.&40.)Pa6,(1:.&40.)Pa7,(1:.&40.)Ps2,(1:.&40.)Ps3,(1:.&40.)Ps4,(1:.&40.)Ps5,(1:.&40.)Ps6,(1:.&40.)Ps7,(1:.&40.)Ps8,(1:.&40.)Ps9,(1:.&40.)Ps10,(1:.&40.)Ps11,(1:.&40.)Pt3,(1:.&40.)Pt4,(1:.&40.)Pt5,(1:.&40.)Pt6,(1:.&40.)PF,(30.&5.(1:.&40.))Pfc,(1:.&20.)Pm,$20.P,(?.(1:.&40.)R19.(3<.&40.=))(52.$1>.Lms',$46.(?.$46.R1.(42.(43.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(47.R24.)R4.(1?.(1:.&40.))R3.(45.$1>.)))(42.(43.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(3<.&40.$51.)R3.(1?.(1:.&40.))R2.(45.$1>.)))")
(* [comment removed for export] *).

#[using="hRP"] Lemma rfree_null_spec : rfree_null_stmt.
Proof. rceilb.
  intros until m. intros ->. unfold RFREE_SYM.
  step. step. if_true. step. apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End RP_1.
