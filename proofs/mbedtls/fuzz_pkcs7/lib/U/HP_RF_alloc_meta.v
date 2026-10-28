(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_F_memcpy.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B2 MallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require KArith. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_am_A F_am_K F_am_K2 F_am_C F_am_D F_am_E F_am_F F_am_G F_am_H F_am_P F_alloc_meta.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A2 HP_RF_ntf_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RF_am_A HP_RF_am_K HP_RF_am_K2 HP_RF_am_C HP_RF_am_D HP_RF_am_E HP_RF_am_F HP_RF_am_G HP_RF_am_H HP_RF_am_P.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_alloc_meta () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Heap.F_alloc_meta.magree"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rauxv_ok"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RAUXV_CELL"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.ram_post"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.brk_link_ps"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rimplT"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.am_rel"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RP_1.ASM.rFP"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_m"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.ps_so"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_P.AMI"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_C.pgal"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.NSLOTS"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aadd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.AREA_HDR"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.META_SIZE"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_metas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_meta_area_tail"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "stdpp.base.is_Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_avail_meta_area_count"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.zeros"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_frame"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_A.am_took"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_K.carve_st"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_avail_meta_areas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.am_finish"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_reserved"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.live_ranges"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ranges_free"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rfresh_addr"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rrepfoot"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B2.rgrp_region_addr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_meta_alloc_shift"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.ptrs_in"; "Stdlib.NArith.BinNat.N.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_next_rid"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.am_after_brk"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ref_reserved"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_AM.AMpre_g"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_P.am_body"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.alloc_meta"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ralloc_meta_entry"].

Module A2 := MallocKit_A2.
Module RA2 := HP_RMallocKit_A2.
Section RP_1. Context {hRP : run_params}.

#[using="hRP"] Lemma rmagree_of_pres C m m' : rpres_except C m m' -> magree C m m'.
Proof. rceilb. intros P a Ha Hc. exact (proj1 (P a Ha Hc)). Qed.
#[using="hRP"] Lemma rpres_of_magree C m m' : magree C m m' -> rpres_except C m m'.
Proof. rceilb. intros A a Ha Hc. split; [exact (A a Ha Hc)|]. rewrite (rwview_ext m m' (wa a) (A a Ha Hc)). auto. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56765667309.1300000>S1A2cs2H01a2Ha". (* [comment removed for export] *)
#[using="hRP"] Lemma rrw_cells_magree C m m' A cs : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "P,(0.$1.O4.O2.O1.)P,(2.O5.O4.O3.)P,Pa,$3.P,(4.(5.O2.R1.)(6.R1.(7.O2.(8.(9.O1.)))))(:.A1.O5.R2.)(0.$1.O3.O2.O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros H AG HC. pose proof (rw_cells_bound _ _ _ _ H). eapply RA2.rrw_cells_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56765667309.1300000>S1A2bs2H01a2Ha". (* [comment removed for export] *)
#[using="hRP"] Lemma rbytes_at_magree C m m' A bs : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "P,(;.$1.O4.O2.O1.)P,(2.O5.O4.O3.)P,Pa,$3.P,(4.(5.O2.R1.)(6.R1.(7.O2.(8.(<.(=.&8.)O1.)))))(:.A1.O5.R2.)(;.$1.O3.O2.O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros H AG HC. pose proof (bytes_at_bound _ _ _ _ H). eapply RA2.rbytes_at_agree; [exact H|]. intros a Ha. apply AG; [lia| apply HC; exact Ha].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59315154296.2600000bS3hRP1B2av2x32x42x52hw2x63x113x123x233rnd1H1a2Ha1Y". (* [comment removed for export] *)
#[using="Type"] Lemma rauxv_ok_magree C m m' B : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "P,(>.VhRP,O3.O1.)P,(2.O4.O3.O2.)P,Pa,$3.P,A1.O4.R1.(4.(6.R2.O1.)(:.(4.(5.$?.R2.)(6.R2.(7.$?.+8.)))))(>.VhRP,O2.O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  (intros dd_H; ddestruct dd_H as (av & x3 & x4 & x5 & hw & x6 & x11 & x12 & x23 & rnd & AC & AL & RN & H); intros AG HC).
  dexists av, x3, x4, x5, hw, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rrw_cells_magree; [exact AC| exact AG|]. cbn. intros a Ha X. destruct (HC a X) as [_ Y]. apply Y. exact Ha.
  - eapply rbytes_at_magree; [exact AL| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _].
    unfold rauxv_list in Ha. rewrite u64s_length, map_length in Ha. cbn in Ha. lia.
  - eapply rbytes_at_magree; [exact RN| exact AG|]. intros a Ha X. destruct (HC a X) as [Y _]. rewrite length_le8 in Ha. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : RAMpre st.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis LO : rceil <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - RAM_STACK.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 0x5d0c8.
Hypothesis KH : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "Pst1,$10.Pmo,$11.Ps',$12.Pms',$13.P,(14.VhRP,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vst,Vs,Vlo,Vm,R4.R3.R2.R1.)P,(15.R5.R3.)(16.VR,Vo,A2.Vk,R6.R5.R4.VQ,R3.)")
(* [comment removed for export] *).

Definition rFP (stX : mstate) (a : Z) : Prop := ralloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ rfresh_addr st a.

#[using="Type"] Lemma rFP_am stX a : ram_fp stX lo (bv_unsigned sp) a -> rFP stX a.
Proof. rceilb. intros H. left. apply ram_fp_alloc_fp. exact H. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L47029017600.42000001S". (* [comment removed for export] *)
#[using="hRP TP"] Lemma rETP : errno_addr tp = 0x5d0c8 - 164.
Proof. rceilb. rewrite TP, unsigned_lit by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="TK KH"] Lemma rfinish_K : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "Pst1,$10.Pmo,$11.PsX,$12.Pm',$17.Pe,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Prv,(=.&40.)P,(18.Vst,R14.R13.)P,(19.VhRP,R15.R12.)P,(1:.$1.R13.)P,(1;.$1.R14.Vlo,(1<.&40.Vsp,))P,(0.$1.R15.(7.(1<.&40.Vtp,)-:4.)(1=.$1>.(1?.R14.)(20.$1>.)))P,(>.VhRP,R16.(1<.&40.Vsp,))P,(2.(21.R1:.)Vm,R17.)P,(15.R1;.R19.)P,(22.$10.(23.R1:.)(23.Vs,))P,(22.(24.$3.$3.)(25.R1;.)(25.Vs,))P,(22.$26.(27.R1<.)(27.Vs,))P,(22.(=.&40.)R<.(28.R1?.R1>.))(16.VR,Vo,A2.Vk,R20.R1?.R1>.VQ,(29.(2:.Vra,Vsp,Vgp,Vtp,R1;.R1:.R19.Vs0,Vs1,R=.R18.R17.R16.R15.R14.R13.R12.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R11.R10.R?.R>.)VF,(2;.Vra,)Vfc,(2<.(=.&40.))R1=.(2=.$1.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros st1 mo sX m' e t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rv REL MR1 MI1 ST1 ERR1 AUX1 AG BL1 P1 P2 P3 ->.
  apply KH; [| exact BL1]. unfold ram_post. deexists 16. split; [reflexivity|].
  split; [exact MI1|]. split; [exact ST1|]. split; [exact ERR1|]. split; [exact AUX1|]. split.
  { apply rpres_of_magree. exact AG. }
  split; [exact MR1|]. split.
  { destruct TK as [T1 T2]. split; intros; rewrite (amr_shadow _ _ _ REL) in *; rewrite (amr_tick _ _ _ REL); eauto. }
  auto.
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L17210430967.56L30141356241.57L50806061080.7000000100>00]SS1a1r1X2r'2RUS1r2r'2L'1q2r01H2H02q02r12H42H5". (* [comment removed for export] *)
#[using="Type"] Lemma rFP_mono stX stY a : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "P,Prid,$2>.Pr,$2?.P,(22.(30.$2?.)(31.$2>.$2?.(32.$2>.$33.$34.$2?.)(35.$2>.$33.$34.$2?.)R2.(36.O3.))(37.$2?.R1.))(38.$2?.Lr',$2?.(4.(22.(30.$2?.)(31.$2>.$2?.(32.$2>.$33.$34.$2?.)(35.$2>.$33.$34.$2?.)R4.(36.O2.))(37.$2?.R1.))(4.(22.$39.(3:.R1.)(3:.R3.))(4.(22.$3.(3;.R1.)(3;.R3.))(5.(3<.R3.)(3<.R1.))))))P,(21.O3.O1.)(21.O2.O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
  ddestruct (HR rid r Hr) as (r' & Hr' & K' & B' & L'). left. right. right. right. dexists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
  assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
  { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
  unfold lr_lo in *. rewrite K', B'. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2584864590.49000003S1r". (* [comment removed for export] *)
#[using="Type"] Lemma rFP_same stX stY a : s_regions stY = s_regions stX -> rFP stX a -> rFP stY a.
Proof. rceilb. intros E. apply rFP_mono. intros rid r Hr. exists r. rewrite E. repeat split; auto; lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L47033307802.46L52224878913.46L52225139025.47L52225139025.5600000100L00i01OSS3hRP2sp2lo2LO1a3RCB1X4LOLES3hRP2sp2lo2LO4LOLE1a3RCB1C1HS3hRP2sp2lo2LO4LOLE1a3RCB1r1X3RBC2D21H". (* [comment removed for export] *)
#[using="AMP LO LOLE"] Lemma rFP_below stX a : rregions_wf stX -> rFP stX a -> a < bv_unsigned sp /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8).
Proof. rceilb.
  (intros dd_H; ddestruct dd_H as (_ & WR & _); intros [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]); rewrite ?TP in X; rceilb; unfold RAUXV_CELL, RLIBC, RCTX, RAM_STACK in *;
    rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
  - destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). pose proof (lr_lo_ge r). rceilb. lia.
  - pose proof (rfresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. rceilb. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="LO TP"] Lemma rerrno_not_amfp stX a : rregions_wf stX -> ram_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. rceilb. intros WF X. rewrite TP. eapply ram_fp_not_errno; [exact X| exact WF| exact LO]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rbrk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. reflexivity. Qed.
(* [comment removed for export] *)
#[using="hRP"] Lemma ram_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> Malloc.M RR) (bl : Malloc.M RR) :
  am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
  = kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. rceilb. reflexivity. Qed.
#[using="Type"] Lemma rconc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. reflexivity. Qed.
#[using="hRP"] Lemma rbrk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof. rceilb.
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
#[using="hRP"] Lemma rconc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. rceilb. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L38043196506.93L6714072449.11700000<00ES2sp2lo4LOLES2tp1a2Ha". (* [comment removed for export] *)
#[using="AMP TK LO LOLE TP KH"] Lemma rcarve_K : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "PstY,$10.Pp,$3=.Pr,$2?.PmX,$17.PsX,$12.Pjunk,(3>.(=.&8.))Pe,(=.&40.)Px1,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps0x,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps4x,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)P,(3?.Vst,R19.)P,(22.(30.$2?.)(31.$2>.$2?.(32.$2>.$33.$34.$2?.)(35.$2>.$33.$34.$2?.)(40.$2>.$3.R19.)(36.R1:.))(37.$2?.R18.))P,(:.(22.$39.(3:.R19.)$41.))P,(5.=(42.$2>.$3.R1;.))P,(5.(7.(42.$2>.$3.R1<.)+1000.)(43.(3<.R1;.)))P,(44.(42.$2>.$3.R1=.))P,(5.(45.R1=.)(7.(3;.R1=.)(42.$2>.$3.R1>.)))P,(22.(30.$46.)(31.$3=.$46.(32.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)(35.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)R1?.(4;.R20.))(2<.$46.))P,Pj,$3.P,(4.(5.=R1.)(6.R1.$4<.))(22.(30.$4=.)(31.$3=.$4=.(32.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$4=.)(35.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$4=.)(4>.R22.(7.$4?.(50.$51.R2.)))(52.R23.))(2<.$4=.))P,Ptl,$3=.P,(22.$11.(53.(54.R23.))(37.$3=.R1.))(55.$46.(31.$3=.$46.(32.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)(35.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)R2.(4;.R24.)))P,(4.(5.+1.(56.(54.R23.)))(6.(56.(54.R23.))(57.+2.+40.)))P,(19.VhRP,R24.R21.)P,(1:.$1.R22.)P,(;.$1.R23.(58.R26.R25.)(59.#1000.))P,(5:.$1.R24.(58.R27.R26.)+1000.)P,(0.$1.R25.(7.(1<.&40.Vsp,)-40.)(5;.VhRP,R23.Vs4,Vs3,Vs2,Vs1,Vs0,Vra,))P,(1;.$1.R26.Vlo,(7.(1<.&40.Vsp,)-40.))P,(0.$1.R27.(7.(1<.&40.Vtp,)-:4.)(1=.$1>.(1?.R24.)(20.$1>.)))P,(>.VhRP,R28.(1<.&40.Vsp,))P,(2.(21.R2<.)Vm,R29.)P,(15.R2=.R29.)P,(22.$10.(23.R2:.)(23.Vs,))P,(22.(24.$3.$3.)(25.R2;.)(25.Vs,))P,(22.$26.(27.R2<.)(27.Vs,))(16.VR,Vo,A2.Vk,(5<.(5=.R31.R30.)(4>.R30.$4?.)+64.)(37.$3=.(4>.R30.$4?.))R2=.VQ,(29.(2:.R2:.(5>.&40.(7.(1<.&40.Vsp,)-40.))Vgp,Vtp,R29.R28.R27.R26.(5>.&40.(58.R31.R30.))R25.R24.R23.R22.R21.R20.R1?.R1>.(5>.&40.$5?.)(5>.&40.$60.)R1=.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1<.R1;.R1:.R19.)VF,(5>.&40.+404:8.)Vfc,(2<.(=.&40.))R2>.(2=.$1.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until t6. intros AI Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX ZB ZW FRX STX ERRX AUXX AGX BLX P1 P2 P3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof MRX as (WFX & _).
  eapply rimplT_evt.
  { eapply (ram_carve_walk sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc mX junk lo stY p r);
      first [exact MRX | exact MIX | exact Hr | exact NK | exact S0 | exact S1 | exact SAL | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT
            | exact (ami_secretr _ _ AI) | exact ZB | exact ZW | exact FRX | exact STX | exact LO | lia]. }
  intros ms2 RP. unfold ram_ret_post in RP.
  ddestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
  pose proof (carve_st_regions stY p) as RC.
  eapply rfinish_K.
  - eapply (ram_rel_carve st stY p r AI); assumption.
  - exact MR2.
  - exact MI2.
  - exact ST2.
  - eapply rrw_cells_magree; [exact ERRX| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X.
    apply (rerrno_not_amfp stY a WFX); [exact (proj1 (ram_fp_same stY _ lo _ a RC) X) | lia].
  - eapply rauxv_ok_magree; [exact AUXX| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stY _ WFX). apply rFP_am. exact (proj1 (ram_fp_same stY _ lo _ a RC) X).
  - assert (RA : s_regions (am_took (carve_st stY p) (aadd p AREA_HDR) 100) = s_regions stY) by (cbn; exact RC).
    eapply magree_trans; [exact AGX| apply rmagree_of_pres; exact PE2| intros a X; exact (rFP_same stY _ a RA X) | intros a X; apply rFP_am; refine (proj2 (ram_fp_same (carve_st stY p) _ lo _ a _) X); reflexivity].
  - unfold brk_link_ps in *. rewrite rbrk_am_took, rbrk_carve. destruct (c_brk (ctx stY)) as [| |rid off]; auto.
    rewrite rconc_am_took, rconc_carve. exact BLX.
  - exact P1.
  - exact P2.
  - exact P3.
  - unfold pw, oconc, wz. rewrite rconc_am_took, rconc_carve. rewrite (conc_aadd stY p AREA_HDR) by (rewrite Hr; eauto). reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L58545818123.59L58545818123.65L58545818123.66L58546108336.4900000I01301c020S3hRP1a3RCB2rg3Hin3RBC2D2S3hRP3stY1a3RCB1b3Hin2rb2Cb3Sb03Sb13RBC2D2S3hRP3stY1a3RCB2ak3Hin3rra2Ca3Sa03Sa13RB03RBC2D2S3hRP1a3RCB1C". (* [comment removed for export] *)
#[using="TP"] Lemma rrepfoot_low stY a : rregions_wf stY -> rrepfoot stY a -> a < rceil /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. rceilb.
  intros WF H. rewrite rETP. dpose WF as (_ & WR & _ & WA & WG). rceilb.
  destruct H as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *; try lia.
  - ddestruct C as (ak & ar & Hak & Hin). ddestruct (rarea_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). rceilb. lia.
  - ddestruct C as (b & gh & Hb & Hin). ddestruct (rgroup_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). rceilb. lia.
  - ddestruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (D1 & _ & D23 & D2). rceilb. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L17260316077.25 L18926302184.114L22089672348.114L23079571339.138L26496810409.138L2740296790.111 L29800690184.141L30687395354.114L30950009275.114L30983301007.138L30987217776.114L32224975529.114L38040802167.141L42150904833.114L46505993046.141L47028918004.114L51882385243.114L53010370357.141L54323714468.114L55713317748.114L56756879236.142L57589880460.114L58577821655.141L59308579027.145L64601901568.114L64606291582.112L64624998266.141L65249657436.114L8832910886.142 00000Z00f01R01^02O02b03603B03i04T05?05a06806W06k07707N07b08=08I08h09409H0:80:H0;10;f0<60<VS1p1r2r23SAL2r14RBAL1q2r01H2H02q02H42q12H9S3stY1p1r2S0S3hRP2sp2lo3stY1p1r2S02S13LO'3RCB3RB03RBC2CpS3stY1p1r2S0S3hRP2sp2lo4LOLE3stY1p1r2S02S13LO'3RCB3RB03RBC2CpS3stY1p1r2S02S13RB0S3stY1p1r2S02e'4CASES3stY1p1r2S0S3hRP2sp2lo4LOLE3stY1p1r2S03LO'3RCB3RB0S3hRP2sp2lo4LOLE3stY1p1r2S03SPR3LO'3RCB3RB0S3hRP2sp2lo4LOLE3stY1p1r2S03SPR3LO'3RCB3RB0S3hRP3stY1p1r2S02S13RCB3RB03RBC2CpS2sp2lo4LOLE3stY1p1r2S0S3hRP2lo3stY1p1r2S03LO'3RCB3RB0S3stY1p1r2S02e'4CASES3stY1p1r2S0S2sp2lo4LOLE3stY1p1r2S0S3stY1p1r2S02e'4CASES3stY1p1r2S03SLR3RB02Cp3LRGS3stY1p1r2S0S3stY1p1r2S02S13SLR3RB02Cp1x2HxS3stY1p1r2S0S3stY1p1r2S02e'4CASES3hRP2sp2lo4LOLE3stY1p1r2S03LO'3RB01y2Hy1H2tp2H0S3stY1p1r2S03IMGS3stY1p1r2S02S13RB03DR14DR233DR22Cp3PAL1HS3stY1p1r2S02S13RB04RBAL3DR14DR233DR22Cp3PAL3IMG2e'1GS3stY1p1r2S03IMGS2sp2lo4LOLE3stY1p1r2S03RB01x2Hx". (* [comment removed for export] *)
Lemma rfinish_path : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "PstY,$10.Pp,$3=.Pr,$2?.PmX,$17.PsX,$12.Pjunk,(3>.(=.&8.))Pe,(=.&40.)Px1,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps4x,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)P,(3?.Vst,R18.)P,(22.$11.(61.(54.R19.))(37.$3=.R18.))P,(22.(30.$2?.)(31.$2>.$2?.(32.$2>.$33.$34.$2?.)(35.$2>.$33.$34.$2?.)(40.$2>.$3.R19.)(36.R1:.))(37.$2?.R18.))P,(:.(22.$39.(3:.R19.)$41.))P,(5.=(42.$2>.$3.R1;.))P,(5.(7.(42.$2>.$3.R1<.)+1000.)(43.(3<.R1;.)))P,(44.(42.$2>.$3.R1=.))P,(5.(45.R1=.)(7.(3;.R1=.)(42.$2>.$3.R1>.)))P,(22.(30.$46.)(31.$3=.$46.(32.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)(35.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)R1?.(4;.R20.))(2<.$46.))P,Pj,$3.P,(4.(5.=R1.)(6.R1.$4<.))(22.(30.$4=.)(31.$3=.$4=.(32.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$4=.)(35.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$4=.)(4>.R22.(7.$4?.(50.$51.R2.)))(52.R23.))(2<.$4=.))P,Ptl,$3=.P,(22.$11.(53.(54.R23.))(37.$3=.R1.))(55.$46.(31.$3=.$46.(32.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)(35.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)R2.(4;.R24.)))P,(4.(5.+1.(56.(54.R23.)))(6.(56.(54.R23.))(57.+2.+40.)))P,(19.VhRP,R24.R21.)P,(1:.$1.R22.)P,(0.$1.R23.(7.(1<.&40.Vsp,)-40.)(5;.VhRP,R21.Vs4,Vs3,Vs2,Vs1,Vs0,Vra,))P,(1;.$1.R24.Vlo,(7.(1<.&40.Vsp,)-40.))P,(0.$1.R25.(7.(1<.&40.Vtp,)-:4.)(1=.$1>.(1?.R22.)(20.$1>.)))P,(>.VhRP,R26.(1<.&40.Vsp,))P,(2.(21.R2:.)Vm,R27.)P,(15.R2;.R27.)P,(22.$10.(23.R28.)(23.Vs,))P,(22.(24.$3.$3.)(25.R29.)(25.Vs,))P,(22.$26.(27.R2:.)(27.Vs,))(16.VR,Vo,(62.VR,R2?.$63.Vk,Vbail,)R2;.VQ,(29.(2:.R28.(5>.&40.(7.(1<.&40.Vsp,)-40.))Vgp,Vtp,R27.R26.R25.(5>.&40.+1000.)(5>.&40.(58.R2?.R2>.))R24.R23.R22.R21.R20.R1?.R1>.R1=.(5>.&40.$5?.)(5>.&40.$60.)R1<.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1;.R1:.R19.R18.)VF,(5>.&40.+40538.)Vfc,(2<.(=.&40.))R2<.(2=.$1.)))")
(* [comment removed for export] *).
Proof using AMP KH LO LOLE TK TP.
  intros until t6. intros AI AMA Hr NK S0 S1 SAL SLR ANone FRESH TL CNT MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. rceilb.
  dpose MRX as (WFX & _ & (_ & _ & PGX & _) & _). dpose WFX as ((RS & RPRS) & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). rceilb.
  pose proof (conc_region' stY p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU. pose proof (lr_lo_ge r) as LRG.
  assert (PAL : conc stY p mod 4096 = 0) by (rewrite Cp; unfold pgal in SAL; clear - RBAL SAL; Z.div_mod_to_equations; lia).
  assert (IMG : conc stY p + 4096 <= 0x10000 \/ 0x7e000 <= conc stY p) by (pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)); lia).
  pose proof rETP as rETP'. pose proof TP as TPv. unfold wz in PGX.
  (* [comment removed for export] *)
  unfold am_finish. rewrite AMA. unfold pgal in SAL. unfold PGSZ at 1. rewrite (proj2 (Z.eqb_eq _ _) SAL). cbn [negb].
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { apply (ram_to_mprotect (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX (conc stY p)). }
  intros ms2 ->.
  eapply (rimplT_mprotect o (conc stY p) PGSZ PROT_RW _ sX).
  { eapply rimpl_enode_dec_weaken; [| intros rsp a Hd; exact (dec_mprotect_rw_weaken _ _ rsp a Hd)].
    unfold PGSZ, PROT_RW.
    eapply rmprotect_spec with (lo := lo) (errv := e);
      [ rewrite unsigned_lit by lia; exact STX | exact ERRX | exact PGX | exact MIX | reflexivity | reflexivity | reflexivity
      | exact PAL | reflexivity | lia | lia | lia | lia | ..]; rewrite ?rETP', ?TPv, ?unsigned_lit by lia; unfold RPAGE_SIZE; try lia. }
  intros ans ms3 [MP G]. unfold rmprotect_post in MP.
  ddestruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & PG3 & CASE).
  rewrite unsigned_lit in MU3, ST3 by lia.
  replace (ret_pc (Z_to_bv 64 0x40548)) with (Z_to_bv 64 0x40548 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
  { eapply rw_cells_transport; [exact FRX| exact MU3| exact WM3|]. rewrite rETP'. cbn. rceilb. lia. }
  assert (MR3 : rmrep stY m3).
  { eapply rmrep_transport_unowned; [exact MRX| exact MU3| exact WM3|].
    intros lo' hi' y [E|[E|[E|[]]]] Hy; inversion E; subst lo' hi'.
    - intros RFt. destruct (rrepfoot_low stY y WFX RFt). rceilb. lia.
    - intros RFt. destruct (rrepfoot_low stY y WFX RFt). lia.
    - eapply (rfresh_page_avoids stY mX p r y MRX); try assumption; lia. }
  assert (M23 : magree (rFP stY) mX m3).
  { eapply magree_of_munch; [exact MU3|].
    cbn. split; [| split; [| split; [| exact I]]]; intros x Hx.
    - left. left. lia.
    - left. right. left. rewrite TPv in Hx. exact Hx.
    - left. right. right. right. dexists (fst p), r. split; [exact Hr|]. split; [exact NK|]. lia. }
  assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AGX| exact M23| intros a X; exact X| intros a X; exact X]).
  assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUXX| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
  clear MU3 WM3.
  destruct ans as [e'|b]; cbn in G.
  - (* [comment removed for export] *)
    cbn [range_val F_mm_syscalls.munmap_ret F_mm_syscalls.rg_errno] in *.
    unfold mprotect_answer_ok, is_errno_form, neg_errno, TWO64, ENOSYS.
    replace ((2 ^ 64 - e' =? 0) || ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64))) with true by (symmetry; apply orb_true_iff; right; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    replace ((2 ^ 64 - e' =? 0) || (2 ^ 64 - e' =? 2 ^ 64 - 38)) with false by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
    cbn [negb].
    eapply rimplT_evt.
    { eapply (ram_mp_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo e' stY);
        first [exact MR3 | exact MI3 | exact TPv | exact ERR3 | exact G | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
    intros ms4 [RP ERR4]. unfold ram_ret_post in RP. cbn [ms_mem] in ERR4.
    ddestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & EQ & PE4 & WM4 & MI4 & ST4 & MR4).
    rewrite EQ in ERR4 |- *. cbn [ms_mem] in ERR4.
    eapply rfinish_K.
    + apply (ram_rel_none st stY AI).
    + exact MR4.
    + exact MI4.
    + exact ST4.
    + exact ERR4.
    + eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
    + eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
    + exact BLX.
    + exact P1.
    + exact P2.
    + exact P3.
    + reflexivity.
  - (* [comment removed for export] *)
    subst b. cbn [range_val] in *.
    unfold mprotect_answer_ok. cbn [Z.eqb orb negb].
    rewrite (am_carve_eq stY p k bail), (ram_take_took (carve_st stY p) p k bail).
    destruct CASE as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
    eapply rimplT_evt.
    { apply (ram_mp_ok0 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc stY p)) u3 u4 u5 u6 u7 u8 u9 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 (Z_to_bv 64 0x40548) F fc m3). }
    intros ms4 ->.
    eapply (rcarve_K stY p r m3 sX junk); first [exact AI | exact Hr | exact NK | exact S0 | exact S1 | exact SLR | exact ANone | exact FRESH | exact TL | exact CNT
      | exact MR3 | exact MI3 | exact ZB | exact ZW | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | exact BLX | exact P1 | exact P2 | exact P3 | idtac].
    unfold pgal. exact SAL.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="hRP"] Lemma rlive_ranges_same stA stB : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "P,(22.(32.$2>.$33.$34.$2?.)(36.O1.)(36.O2.))P,(22.(3>.(24.$3.$3.))(64.O1.)(64.O2.))(22.(3>.(24.$3.$3.))(65.O1.)(65.O2.))")
(* [comment removed for export] *).
Proof. rceilb. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L44243992910.51L64838479326.51L6755913069.51 L68478600214.5100000:00D00E00VS1x1L1a2HaS1x1L1a2HaSS3hRP1x1L1a2XC2Ha". (* [comment removed for export] *)
#[using="Type"] Lemma rfresh_of_ranges_free stY x L a : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "P,(22.(32.$2>.$33.$34.$2?.)(36.O4.)(36.Vst,))P,(22.(3>.(24.$3.$3.))(64.O4.)(64.Vst,))P,(22.$66.(67.(65.O4.)O3.O2.)$63.)P,(5.(7.O3.O2.)(68.VhRP,))P,(4.(5.O3.O1.)(6.O1.(7.O3.O2.)))(69.VhRP,Vst,O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros E1 E2 RF XC Ha. split; [lia|]. rewrite (rlive_ranges_same st stY E1 E2) in RF.
  eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L16087815706.59L57389699694.63L57389699694.6400000500?00IS1a1CS1a2rg3HinS1a2rg3Hin". (* [comment removed for export] *)
#[using="Type"] Lemma rrepfoot_clear stY mY x L a : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "P,(19.VhRP,O5.O4.)P,(22.$66.(67.(65.O5.)O3.O2.)$63.)P,(6:.(6;.O5.O1.)(6<.O5.O1.))(:.(4.(5.O3.O1.)(6.O1.(7.O3.O2.))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros MRY RF H. pose proof MRY as (WF & _). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  pose proof (clear_range_of_ranges_free stY x L RF) as CR.
  assert (IMG : forall y, 0x10000 <= y < 0x7e000 -> ~ (x <= y < x + L)) by (intros y Hy; apply (rimage_clear_of_ranges_free stY x L y RS RF Hy)).
  destruct H as [[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]|C]; unfold RCTX, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
  - apply IMG. lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - ddestruct C as (ak & ar & Hak & Hin). ddestruct (WA ak ar Hak) as (rra & Hra & _).
    eapply (CR (fst ak) rra a Hra). eapply rarea_in_live; eauto.
  - ddestruct C as (b & gh & Hb & Hin). ddestruct (WG b gh Hb) as (rb & Hrb & _).
    eapply (CR (fst b) rb a Hrb). eapply rgroup_in_live; eauto.
  - ddestruct C as (rid & rg & v & Hrg & Krg & Hin & _). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
  - apply IMG. lia.
  - apply IMG. lia.
  - ddestruct C as (rid & rg & Hrg & Krg & Hin). eapply (CR rid rg a Hrg). rewrite (lr_lo_group rg Krg). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00n0@L10706941820.141L11803556607.136L11825081397.134L12366485855.119L18926596843.150L18928426569.123L19245667879.156L19265643551.97 L2179098206.152 L21906295824.139L23014285634.148L23014534341.141L23598322735.139L25071664653.119L26344114431.97 L29804951343.119L30056767660.144L30056767660.146L30063058068.147L30723765111.125L30723846054.141L30724024087.101L30972718900.97 L30985366036.119L30987020851.120L31332189928.143L31332194059.145L34969366989.95 L35057702175.150L35643392539.138L35689789072.119L35691542199.120L37308221042.146L37310060433.123L37401887992.101L38040802167.124L38040802167.139L40100751247.97 L41422703888.95 L41910285729.96 L46108550034.139L46591911764.97 L47039189680.97 L48055533212.136L50594129072.124L53006240274.119L56091525403.141L56391998866.147L5744645808.133 L57587438280.97 L59308579027.126L59308579027.145L59308587280.142L59310612847.123L59738815927.150L636407792.150  L65324126411.139L66975430554.135L6714072449.147 L6714072449.153 L67376300219.95 L8817172550.137 00000C00S01101>01K01T01d02602L02f03303@03Q03o04M04Z04k05<05N05a06206<06^07@07b08408F08Q08d09109809?09^0:50:@0:R0:j0;;0;B0;M0;h0<20<90<_0=60=C0=S0=g0>E0>L0?30?]0?m0@I0@Y0@f0A60AQ0A`0B50B@0BMS3stY1n1x2XA2X03ridS2sp3stY1n1x3ridS3hRP3RCB3stY1n2NR1x2X02XC3ridS3stY1n2e'2ERS3stY1n1x3ridS3stY1n1xS3stY1n1x3rid2rqS2sp2lo4LOLE3stY1nS3stY2rb2PB1n1x2X03ridS3hRP3stY1n2NR1x2X02XC3ridS3stY1n1x3ridS3stY1n1x3ridS3stY3SHR1n1x3ridS3hRP2sp2lo4LOLE3RCB3stY3LO'1nS3hRP2sp2lo4LOLE3RCB3stY3LO'1nS3stY1n2e'2ERS3stY1n1x3rid1y1HS3stY1n1x3rid1y1HS3stY1n1x3rid1y2H0S3stY1n2NR1x2X03ridS3stY1n1x3rid3Hn1S3stY1n2NRS3hRP2sp2lo4LOLE3RCB3stY3SPR3LO'1nS3hRP2sp2lo4LOLE3RCB3stY3SPR3LO'1nS3hRP2sp2lo4LOLE3RCB3stY3SPR3LO'1nS3stY1n1x3rid1y2HyS3stY1n1x3rid1y2HyS3stY3SHR1nS3stY1n2NR1x2X03ridS3stY1n1x3ridS3stY1nS3stY1nS2sp2lo4LOLE3stY1n1x2X03rid1y1XS2sp2lo4LOLE3stY1n1y2HyS3hRP3stY1nS2sp2lo4LOLE3stY1nS2sp2lo4LOLE3stY1n1x3ridS3hRP2lo2LO3stY1nS3stY1nS3stY3SHR1nS3stY1n2NR1x2XA2X03rid1H2H0S3stY1n2NRS3stY1nS3hRP2sp2lo4LOLE3stY3LO'1n1x2X02XC3ridS3hRP3RCB3stY1n2NR1x2XCS3stY1n2e'2ERS3stY1n1x2X03ridS3stY1n1x3rid1y1H2H0S3hRP3RCB3stY1n2NR1x2X02XC3ridS3stY1nS3hRP2sp2lo4LOLE3stY3LO'1n1y2Hy1H2tp2H0S3hRP2sp2lo4LOLE3stY3LO'1n1x2X03rid1y2Hy1HS3stY1n1x3rid2HqS3hRP3RCB3stY1n2NR1x2X02XC1VS3stY1n2NR1x3ridS3stY1n1x3ridS3stY1n2NR1x3ridS3hRP3RCB3stY1n1x2X02XC3ridS2tp3stY1n1a2HaS2tp3stY1n1x3rid1a2HaS3stY3SHR1nS3stY1n1x3rid". (* [comment removed for export] *)
#[using="AMP TK LO LOLE TP KH"] Lemma rmmap_path : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "PstY,$10.PmX,$17.PsX,$12.Pjunk,(3>.(=.&8.))Pe,(=.&40.)Px1,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps1x,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps4x,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)P,(3?.Vst,R17.)P,(22.(32.$2>.$33.$34.$2?.)(36.R18.)(36.Vst,))P,(22.$3.(56.(54.R19.))=)P,(4.(5.=(6=.(54.R1:.)))(5.(6=.(54.R1:.))+26.))P,Ptl,$3=.P,(22.$11.(53.(54.R1<.))(37.$3=.R1.))(55.$46.(31.$3=.$46.(32.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)(35.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$46.)R2.(4;.R1=.)))P,Pq,$3=.Pmr,$4=.P,(22.(30.$4=.)(31.$3=.$4=.(32.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$4=.)(35.$3=.(47.$2>.$33.$3.$48.)(49.$2>.$33.$34.$3.$48.$4:.)$4=.)R2.(52.R1>.))(37.$4=.R1.))(6>.R1?.R3.)P,(6?.Lrid,$2>.(70.R1.(71.R1>.))R1=.)P,(19.VhRP,R1>.R1=.)P,(1:.$1.R1>.)P,(0.$1.R1?.(7.(1<.&40.Vsp,)-40.)(5;.VhRP,R1=.Vs4,Vs3,Vs2,Vs1,Vs0,Vra,))P,(1;.$1.R20.Vlo,(7.(1<.&40.Vsp,)-40.))P,(0.$1.R21.(7.(1<.&40.Vtp,)-:4.)(1=.$1>.(1?.R1>.)(20.$1>.)))P,(>.VhRP,R22.(1<.&40.Vsp,))P,(2.(21.R24.)Vm,R23.)P,(15.R25.R23.)P,(22.$10.(23.R24.)(23.Vs,))P,(22.(24.$3.$3.)(25.R25.)(25.Vs,))P,(22.$26.(27.R26.)(27.Vs,))(16.VR,Vo,(72.VR,R29.$63.Vk,Vbail,)R27.VQ,(29.(2:.R24.(5>.&40.(7.(1<.&40.Vsp,)-40.))Vgp,Vtp,R23.R22.R21.(5>.&40.+1000.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(5>.&40.$5?.)(5>.&40.$60.)R17.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R16.R15.R14.R13.)VF,(5>.&40.+40448.)Vfc,(2<.(=.&40.))R28.(2=.$1.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until t6. intros AI RGY ACNT SHR TL MK PTR MRX MIX FRX STX ERRX AUXX AGX BLX P1 P2 P3.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. rceilb. pose proof rETP as rETP'. pose proof TP as TPv.
  pose proof MRX as (WFX & _). dpose WFX as ((RS & RPRS) & WR & DJ & WA & WG).
  set (n := Z.shiftl 2 (c_meta_alloc_shift (ctx stY))).
  assert (NR : 2 <= n <= 2^39).
  { unfold n. rewrite Z.shiftl_mul_pow2 by lia. split.
    - rewrite <- (Z.mul_1_r 2) at 1. apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r with (b := 0); lia || (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
    - change (2^39) with (2 * 2^38). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
  unfold am_after_brk. rewrite ACNT. cbn [Z.eqb]. fold n.
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { apply (ram_to_mmap (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc mX stY MRX ltac:(lia)). }
  intros ms2 ->. fold n.
  pose proof MRX as MR2. pose proof MIX as MI2. pose proof FRX as FR2. pose proof STX as ST2. pose proof ERRX as ERR2. pose proof AGX as AG2. pose proof AUXX as AUX2.
  set (m2 := mX) in MR2, MI2, FR2, ST2, ERR2, AG2, AUX2 |- *.
  clear MRX MIX FRX STX ERRX AUXX AGX.
  eapply (rimplT_mmap_none o (n * PGSZ) _ sX).
  { unfold PGSZ. replace (Z_to_bv 64 (n * 4096)) with (Z_to_bv 64 (n * 4096)%Z) by reflexivity.
    eapply (rmmap_anon_spec true) with (lo := lo) (errv := e) (avoid := []);
      [ rewrite unsigned_lit by lia; exact ST2 | exact ERR2 | exact MI2 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
      rewrite ?rETP', ?TPv, ?unsigned_lit by lia; try lia. all: rceilb; lia. }
  intros ans ms3 MP. unfold rmmap_anon_post in MP.
  destruct ans as [e'|x].
  - (* [comment removed for export] *)
    ddestruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & ER).
    rewrite unsigned_lit in MU3, ST3 by lia.
    replace (ret_pc (Z_to_bv 64 0x40474)) with (Z_to_bv 64 0x40474 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [mmap_val]. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64.
    replace ((2 ^ 64 - 4095 <=? 2 ^ 64 - e') && (2 ^ 64 - e' <? 2 ^ 64)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    cbn [orb negb]. replace (2 ^ 64 - 4096 <? 2 ^ 64 - e') with true by (symmetry; apply Z.ltb_lt; lia).
    assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. rewrite rETP'. cbn. lia. }
    assert (MR3 : rmrep stY m3).
    { eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
      intros lo' hi' y [E|[E|[]]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); rceilb; lia. }
    assert (M23 : magree (rFP stY) m2 m3).
    { eapply magree_of_munch; [exact MU3|]. cbn. split; [| split; [| exact I]]; intros y Hy; [left; left; lia|]. left. right. left. rewrite TPv in Hy. exact Hy. }
    assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
    eapply rimplT_evt.
    { eapply (ram_mm_fail sp gp tp u0 u1 u2 (Z_to_bv 64 4096) (Z_to_bv 64 n) u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo stY);
        first [exact MR3 | exact MI3 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | lia]. }
    intros ms4 RP. unfold ram_ret_post in RP.
    ddestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m4 & -> & PE4 & WM4 & MI4 & ST4 & MR4).
    eapply rfinish_K.
    + apply (ram_rel_none st stY AI).
    + exact MR4.
    + exact MI4.
    + exact ST4.
    + eapply rrw_cells_magree; [exact ERR3| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp stY a WFX); [exact X| lia].
    + eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below stY a WFX (rFP_am stY a X))].
    + eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| intros a X; exact X| intros a X; exact (rFP_am stY a X)].
    + exact BLX.
    + exact P1.
    + exact P2.
    + exact P3.
    + reflexivity.
  - (* [comment removed for export] *)
    destruct MP as [AOK [BAD|MP]].
    { (* [comment removed for export] *)
      cbn [mmap_val].
      erewrite (rmmap_rejects_high (s_ceil stY)); [cbn [negb]; apply rimplT_undef| unfold PGSZ; lia| rewrite (rmrep_ceil _ _ MR2); lia| exact AOK| exact BAD]. }
    ddestruct MP as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m2' & -> & MU3 & WM3 & MI3 & ST3 & ERR3 & XR3).
    rewrite unsigned_lit in MU3, ST3 by lia.
    replace (ret_pc (Z_to_bv 64 0x40474)) with (Z_to_bv 64 0x40474 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [mmap_val].
    destruct (mmap_answer_ok (s_ceil stY) (live_ranges stY) (n * PGSZ) x) eqn:VOK; cbn [negb]; [| apply rimplT_undef].
    (* [comment removed for export] *)
    unfold mmap_addr_ok in AOK. apply andb_prop in AOK. destruct AOK as [AOK _]. apply andb_prop in AOK. destruct AOK as [AOK XC].
    apply andb_prop in AOK. destruct AOK as [XA X0]. apply Z.eqb_eq in XA. apply Z.ltb_lt in X0. apply Z.leb_le in XC.
    rewrite A2.mmap_len_round_up in XC. rewrite grant_top_max_val in XC. rceilb. change page_size with 4096 in XA.
    assert (LAL : round_up_pg (n * PGSZ) = n * PGSZ) by (apply round_up_pg_aligned; unfold PGSZ; apply Z.mod_mul; lia).
    rewrite LAL in XC.
    (* [comment removed for export] *)
    rewrite A2.mmap_len_round_up, LAL in XR3. clear XC. rename XR3 into XC.
    unfold mmap_answer_ok in VOK. rewrite LAL in VOK. apply orb_prop in VOK.
    assert (RF : ranges_free (live_ranges stY) x (n * PGSZ) = true).
    { destruct VOK as [V|V]; [| apply andb_prop in V; destruct V as [_ V]; exact V].
      unfold is_errno_form, TWO64 in V. apply andb_prop in V. destruct V as [V _]. apply Z.leb_le in V. unfold PGSZ in XC. exfalso. lia. }
    unfold is_err, TWO64. replace (2 ^ 64 - 4096 <? x) with false by (symmetry; apply Z.ltb_ge; unfold PGSZ in XC; lia).
    unfold new_region. cbv beta iota zeta delta [fst snd].
    set (rid := s_next_rid stY).
    dpose (rAMI_new_region st stY RKMeta x (n * PGSZ) AI ltac:(discriminate) ltac:(unfold PGSZ; lia)) as (AI1 & RG1 & CQ1 & CN1).
    unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
    set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
    set (st2 := upd_ctx _ st1).
    assert (E2 : st2 = mm_ok_st st1 rid n) by reflexivity.
    (* [comment removed for export] *)
    unfold F_mm_syscalls.mmap_raw in ST3 |- *. rewrite A2.mmap_len_round_up, LAL in ST3 |- *.
    set (m3 := apply_unmaps m2' [(wa x, Z_to_bv 64 (n * PGSZ))]) in *.
    assert (Hx1 : 0 <= x < 2^64) by (unfold PGSZ in XC; lia). assert (Hn1 : 0 <= n * PGSZ < 2^64) by (unfold PGSZ in *; lia). assert (Hxn : x + n * PGSZ <= 2^64) by (unfold PGSZ in *; lia).
    assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { apply (rw_cells_unmaps_other rsegs m2' x (n * PGSZ) Hx1 Hn1 Hxn).
      - eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. lia.
      - cbn. unfold PGSZ in *. lia. }
    assert (ERR4 : rw_cells rsegs m3 (errno_addr tp) [C4 e]).
    { apply (rw_cells_unmaps_other rsegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); [exact ERR3|]. cbn. rewrite rETP'.
      pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x5d0c8 - 164) RS RF ltac:(lia)).
      pose proof (rimage_clear_of_ranges_free stY x (n * PGSZ) (0x5d0c8 - 161) RS RF ltac:(lia)). unfold PGSZ in *. lia. }
    assert (MI4 : mem_inv rsegs m3) by (apply (mem_inv_unmaps rsegs m2' x (n * PGSZ) Hx1 Hn1 Hxn); exact MI3).
    assert (MR2' : rmrep stY m2').
    { eapply rmrep_transport_unowned; [exact MR2| exact MU3| exact WM3|].
      intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'; intros RFt; destruct (rrepfoot_low stY y WFX RFt); rceilb; lia. }
    assert (MR3 : rmrep stY m3).
    { eapply rmrep_transport_agree'; [exact MR2'|]. intros y Hy HF. unfold m3. apply (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
      rewrite wa_unsigned by lia. pose proof (rrepfoot_clear stY m2' x (n * PGSZ) y MR2' RF HF). lia. }
    assert (MRn : rmrep st1 m3).
    { unfold st1. apply (RA2.rmrep_new_region stY m3 m3 x (n * PGSZ) RKMeta);
        first [ exact MR3
              | eapply ptrs_in_mono; [| exact PTR]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
              | apply (ami_fresh _ _ AI); unfold rid; lia
              | rceilb; rewrite LAL; exact XC
              | rewrite LAL; exact RF
              | intros; reflexivity
              | intros; discriminate
              | unfold PGSZ in *; lia ]. }
    assert (M23 : magree (rFP stY) m2 m3).
    { intros y Hy Hc. unfold m3. rewrite (unmaps_outside m2' x (n * PGSZ) Hx1 Hn1 Hxn).
      - apply MU3. rewrite wa_unsigned by lia. cbn. split; [| exact I]. intros X. apply Hc. left. left. lia.
      - rewrite wa_unsigned by lia. destruct (Z.lt_ge_cases y x); [lia|]. destruct (Z.lt_ge_cases y (x + n * PGSZ)); [| lia].
        exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stY x (n * PGSZ)); [exact RGY| exact (ami_reserved _ _ AI)| exact RF| rceilb; exact XC| lia]. }
    assert (AG3 : magree (rFP stY) m m3) by (eapply magree_trans; [exact AG2| exact M23| intros a X; exact X| intros a X; exact X]).
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)) by (eapply rauxv_ok_magree; [exact AUX2| exact M23| intros a X; exact (rFP_below stY a WFX X)]).
    clearbody m3. clear MU3 WM3 MR2 MR2' MI3 ERR3.
    (* [comment removed for export] *)
    eapply rimplT_evt.
    { eapply (ram_mm_ok sp gp tp u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ ra s0 s1 s2 s3 s4 F fc m3 m3 junk lo x n st1 st1 rid (mkRegion RKMeta x (n * PGSZ)));
        first [exact MRn | exact MI4 | intros a X; exact X | exact RG1 | reflexivity | exact XA | exact X0 | apply rpres_except_refl | apply wmono_refl | exact FR3 | exact ST3 | exact LO | idtac];
        try (rceilb; unfold PGSZ in *; lia).
      change (ctx st1) with (ctx stY). lia. }
    (intros ms4 dd_H; ddestruct dd_H as (m4 & -> & PE4 & WM4 & MI5 & FR4 & ST4 & MR4)).
    pose proof MRn as (WFn & _).
    assert (RG2 : forall q, (s_regions st2) !! q = if decide (q = rid) then Some (mkRegion RKMeta x (n * PGSZ)) else (s_regions stY) !! q).
    { intros q. change (s_regions st2) with (<[rid := mkRegion RKMeta x (n * PGSZ)]> (s_regions stY)).
      destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq| rewrite lookup_insert_ne by congruence]; reflexivity. }
    destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].
    replace (Z_to_bv 64 (x + 4096)) with (Z_to_bv 64 (conc st2 (rid, 4096))) by (change (conc st2 (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
    eapply (rfinish_path st2 (rid, 4096) (mkRegion RKMeta x (n * PGSZ)) m4 sX junk e).
    + unfold st2. apply (rAMI_ctx st st1 _ AI1).
      * cbn. repeat split; reflexivity.
      * cbn. exact (ami_secretr _ _ AI1).
      * right. dexists (rid, PGSZ), (mkRegion RKMeta x (n * PGSZ)). cbn [fst]. split; [reflexivity|]. split; [exact RG1| cbn; discriminate].
      * left. reflexivity.
    + reflexivity.
    + cbn [fst]. rewrite RG2. destruct (decide (rid = rid)); [reflexivity| congruence].
    + cbn. discriminate.
    + cbn. lia.
    + cbn [snd r_len]. rewrite LAL. unfold PGSZ. lia.
    + unfold pgal. reflexivity.
    + cbn. lia.
    + change (s_areas st2) with (s_areas stY). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
      exfalso. destruct (WA _ _ EA) as (rr & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
    + intros j Hj. change (s_metas st2) with (s_metas stY). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
      exfalso. destruct (MK _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr & Hrr & _).
      assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
    + intros tl Htl. change (s_areas st2) with (s_areas stY). apply TL. exact Htl.
    + cbn. lia.
    + exact MR4.
    + exact MI5.
    + exact FR4.
    + exact ST4.
    + eapply rrw_cells_magree; [exact ERR4| apply rmagree_of_pres; exact PE4|]. cbn. intros a Ha X. apply (rerrno_not_amfp st1 a WFn); [exact X| lia].
    + eapply rauxv_ok_magree; [exact AUX3| apply rmagree_of_pres; exact PE4| intros a X; exact (rFP_below st1 a WFn (rFP_am st1 a X))].
    + eapply magree_trans; [exact AG3| apply rmagree_of_pres; exact PE4| |].
      * intros a X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq. rewrite RG2.
        destruct (decide (q = rid)) as [->|NE]; [rewrite FRr in Hq; discriminate|]. repeat split; auto; lia.
      * intros a X. eapply rFP_same; [| exact (rFP_am st1 a X)]. reflexivity.
    + unfold brk_link_ps in *. change (c_brk (ctx st2)) with (c_brk (ctx stY)).
      ddestruct PTR as (_ & _ & _ & _ & _ & _ & PB & _).
      destruct (c_brk (ctx stY)) as [| |rb ob]; auto. change (conc st2 (rb, ob)) with (conc st1 (rb, ob)). rewrite CQ1; [exact BLX|]. cbn [fst]. unfold rid. lia.
    + exact P1.
    + exact P2.
    + exact P3.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55006087436.5200000CS1x1L2HL1H2H02H12H2". (* [comment removed for export] *)
#[using="hRP"] Lemma rimage_range_clear stY x L : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "P,(22.(3>.(24.$3.$3.))(64.O3.)$73.)P,(22.$66.(67.(65.O3.)O2.O1.)$63.)P,(6.=O1.)(6:.(5.(7.O2.O1.)+10000.)(5.+7>000.O2.))")
(* [comment removed for export] *).
Proof. rceilb.
  intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00n0@L10157438998.118L10159569049.115L10517620025.157L11803467556.121L12417435289.154L13855810008.146L14261229597.132L16862414480.130L18889376915.159L18926392770.117L18926756720.123L18939190001.159L18941394330.118L19245667879.164L20519352896.128L22093328857.118L22249353176.146L25069796650.155L25071778694.153L2567834584.146 L29979368849.159L3083493640.119 L31194372668.136L31332194059.138L31382962973.146L31783424797.146L33421808466.140L33424336918.138L33454592472.146L34244755217.145L34254993293.159L35001855670.151L3712931473.122 L3712931473.152 L39638388940.140L39640493300.139L40195148532.129L41293112974.159L41299370787.149L42467272201.125L44483050603.121L44611174109.119L44644643966.115L44708267278.161L44998442968.146L47898930136.146L49997732560.126L50319705501.118L50861315544.146L50906287447.122L50906340591.115L51864552859.122L52101484385.140L55123685831.159L55243536250.120L55661371392.115L57222941531.159L59579068465.121L63189957111.145L6383655373.142 L811409880.146  L839959391.119  00000T01801M02=02l03@03U03n04F04[05005E05Z06206j07H07\08108e09909N09k0:X0;20;F0;Z0<60<P0<d0=<0=`0>]0?70?Q0?k0@D0AF0Ag0BH0Ba0CL0Ca0D60DX0Dl0E@0EY0FN0Fb0GK0H40HK0I;0IP0JD0Jh0K=0KR0LB0LW0Lk0LlS3stI4brid4boff3old1r2Lr3OLD3RB03RL0S3stI4brid4boff3old1r2Lr3OLD3RB03RL0S3stI4brid2rq3old3RL0S3hRP2sp2lo4LOLE3RCB3stI4brid4boff3old3LO'1r3RB0S3hRP2sp2lo3RCB3stI4brid4boff3old3LO'1r3RB03Ho1S3stI4brid1r3old3RL0S3stI4brid4boff3old1rS3stI4brid4boff3old1r3IMGS3stI4brid4boff3old1r2O4S3stI4brid4boff3old1rS3stI4brid4boff3old1rS3stI4brid4boff3old1rS3stI4brid4boff3old1rS3stI4brid4boff3old1r2rqS3hRP2sp2lo4LOLE3stI4brid4boff3old3LO'4RPRS1r3RB02OC3Ho1S3stI4brid4boff3old1r3RB04OALDS3stI4brid1r3old3RL0S3stI4brid4boff3old1rS3hRP2sp2lo4LOLE3RCB3stI4brid4boff3old3LO'1r3RB03Ho1S3stI4brid1r3old3RL0S3stI4brid4boff3old1rS3stI4brid4boff3old1r3OAL3RB0S3hRP3RCB3stI4brid4boff3old4RPRS1r3RB02OC3Ho1S3stI4brid4boff3old1r1y2HyS3stI4brid1r3old3RL0S3stI4brid1r3old3RL0S3stI4brid4boff3old1r1y1H2H0S3stI4brid4boff3old1r1y2HyS3stI4brid1r3old3RL0S3stI4brid4boff3old1r2O4S3stI4brid4boff3old1r2Lr3RB03RL03Ho1S3stI4brid4boff3old1r2Lr3OAL2O43OLD3RB04RBAL3RL04OALD3Ho13IMGS3stI4brid4boff3old1r1y2HyS3stI4brid4boff3old1r1y2HyS3stI4brid4boff3old1r1y2H0S3stI4brid4boff3old1r1y1HS3stI4brid4boff3old1r2Lr3OAL2O43OLD3RB04RBAL3RL04OALD3Ho13IMG1y2HyS3stI4brid4boff3old1r3OLD3RB03Ho1S3stI4brid4boff3old1r3OLD3RB03Ho1S3stI4brid4boff3old1r3IMGS3hRP2sp2lo3RCB3stI4brid4boff3old3LO'1r3RB0S3stI4brid4boff3old1rS3stI4brid4boff3old1rS3stI4brid4boff3old1r3RB03Ho11j2HjS3stI4brid1r3old3RL0S3stI4brid1r3old3RL0S3stI4brid4boff3old1r3IMGS3stI4brid4boff3old1r2Lr3OAL2O43OLD3RB04RBAL3RL04OALDS3stI4brid1r3old3RL0S3hRP3RCB3stI4brid4boff3old4RPRS1r3RB02OCS3hRP3RCB3stI4brid4boff3old1r3OLD3RB03RBCS3stI4brid4boff3old1r1HS3hRP3stI4brid4boff3old4RPRS1r2Lr3RB03RL02OC3Ho1S3stI4brid4boff3old1rS3hRP3RCB3stI4brid4boff3old4RPRS1r2Lr3OLD3RB03RL02OCS3stI4brid4boff3old1r2Lr3OLD3RB03RL0S3stI4brid4boff3old1rS3stI4brid4boff3old1rS3hRP3stI4brid4boff3old4RPRS1r2O43OLD3RB02OC3Ho1S3stI4brid4boff3old1rS3stI4brid1r3old3RL0F". (* [comment removed for export] *)
#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbrk_live_path : forall (stI : mstate) (brid : N) (boff : Z) (m1 : mem) (junk : list byte) (e1 : word)
    (x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
  c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkLive brid boff ->
  ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
  rmrep stI m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells rsegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
  rimplT o (let old := conc stI (brid, boff) in
           let new := old + PGSZ in
           SVis (EBrk new) (fun r =>
             if negb (brk_answer_ok old new r) then bad_answer bail else
             if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
             else if negb (brk_pages_ok stI old PGSZ) then bad_answer bail
             else
               let st1 := upd_region brid (fun rg => mkRegion (r_kind rg) (r_base rg) (boff + PGSZ)) stI in
               let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (brid, boff)) (set_brk (BrkLive brid (boff + PGSZ)) c))) st1 in
               am_after_brk st2 false k bail)) s Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40398) fc None m1 (seg_rom rsegs)).
Proof. rceilb.
  intros until t6. intros AMPI AI RGI BLI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. rceilb. pose proof rETP as rETP'. pose proof TP as TPv.
  dpose MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6) & _). dpose WF1 as ((RS & RPRS) & WR & DJ & WA & WG).
  pose proof (amp_brk stI AMPI) as HB. rewrite BRK in HB. ddestruct HB as (r & Hr & Kr & Lr & OAL & O4 & FRA & UNQ).
  pose proof (conc_region' stI (brid, boff) r Hr) as OLD. cbn [snd] in OLD.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr). rceilb. rewrite Lr in RBC.
  assert (RUB : round_up_pg boff = boff) by (apply round_up_pg_aligned; unfold PGSZ in OAL; exact OAL). rewrite RUB in RBC.
  set (old := conc stI (brid, boff)) in *.
  assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
  assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
  unfold brk_link_ps in BLI. rewrite BRK in BLI. fold old in BLI.
  cbv zeta.
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { eapply (ram_disp_live _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI brid boff); [exact MR1| exact ACNT| exact BRK| fold old; lia| fold old; unfold PGSZ; lia]. }
  intros ms2 ->. fold old.
  eapply (rimplT_brk o (old + PGSZ) _ s).
  { unfold PGSZ; lia. }
  { rewrite BLI. unfold PGSZ.
    exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
             s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 0x403bc (or_introl eq_refl) old (old + 4096) ltac:(lia)). }
  intros a ms3 ->. rewrite BLI. unfold brk_res, brk_mem, rbrk_regs.
  destruct a.
  - (* [comment removed for export] *)
    unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
    destruct (brk_pages_ok stI old PGSZ) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
    unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
    rceilb; unfold PGSZ in OC. unfold PGSZ in RF.
    assert (OALD : old mod 4096 = 0) by (rewrite OLD; rewrite Z.add_mod, RBAL by lia; unfold PGSZ in OAL; rewrite OAL; reflexivity).
    rewrite (brk_new_pages_aligned old 4096) by (first [lia | exact OALD | reflexivity]).
    rewrite (rgr_eq stI brid r boff Hr).
    set (stG := set_regions _ stI).
    unfold PGSZ. rewrite (am_after_brk_false_eq stG _ (brid, boff) k bail) by (cbn; first [lia | reflexivity | unfold PGSZ in OAL; exact OAL]).
    rewrite am_carve_took, carve_st_brk_irrel.
    set (stX := upd_ctx _ stG).
    (* [comment removed for export] *)
    assert (Ho1 : 0 <= old < 2^64) by lia. assert (Hn1 : 0 <= 4096 < 2^64) by lia. assert (Hon : old + 4096 <= 2^64) by lia.
    pose proof (rimage_range_clear stI old 4096 RS RF ltac:(lia)) as IMG.
    set (m2 := apply_zeros m1 [(wa old, Z_to_bv 64 4096)]).
    unfold ctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6. fold old in HX6.
    assert (HC2 : rw_cells rsegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
      by (apply (rw_cells_zeros_other rsegs m1 old 4096 Ho1 Hn1 Hon); [exact HX1| cbn; unfold RCTX; lia]).
    assert (TC2 : rw_cells rsegs m2 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (wz old)])
      by (apply (rw_cells_zeros_other rsegs m1 old 4096 Ho1 Hn1 Hon); [exact HX6| cbn; unfold RCTX; lia]).
    assert (MI2 : mem_inv rsegs m2).
    { apply (mem_inv_zeros rsegs m1 old 4096 Ho1 Hn1 Hon MI1). intros y Hy. apply ref_ro_addr_false. lia. }
    assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra))
      by (apply (rw_cells_zeros_other rsegs m1 old 4096 Ho1 Hn1 Hon); [exact FR1| cbn; lia]).
    assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -64)) by (apply (stk_zeros rsegs m1 old 4096 Ho1 Hn1 Hon); exact ST1).
    assert (ERR2 : rw_cells rsegs m2 (errno_addr tp) [C4 e1])
      by (apply (rw_cells_zeros_other rsegs m1 old 4096 Ho1 Hn1 Hon); [exact ERR1| cbn; rewrite rETP'; lia]).
    pose proof (rw_cells_zeros_new rsegs m1 old 4096 Ho1 Hn1 Hon) as ZN. fold m2 in ZN.
    assert (MU12 : munch [(old, old + 4096)]%Z m1 m2) by (apply (munch_zeros m1 old 4096 Ho1 Hn1 Hon); [apply munch_refl| cbn; lia]).
    assert (WM12 : wmono rsegs m1 m2) by (apply (wmono_zeros rsegs m1 old 4096 Ho1 Hn1 Hon); apply wmono_refl).
    assert (MR2 : rmrep stI m2).
    { eapply rmrep_transport_unowned; [exact MR1| exact MU12| exact WM12|].
      intros lo' hi' y [E|[]] Hy; inversion E; subst lo' hi'. intros RFt. apply (rrepfoot_clear stI m1 old 4096 y MR1 RF (or_introl RFt)). lia. }
    assert (M12 : magree (rFP stI) m1 m2).
    { intros y Hy Hc. unfold m2. apply (zeros_outside m1 old 4096 Ho1 Hn1 Hon). rewrite wa_unsigned by lia.
      destruct (Z.lt_ge_cases y old); [lia|]. destruct (Z.lt_ge_cases y (old + 4096)); [| lia].
      exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI old 4096); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| rceilb; lia| lia]. }
    clearbody m2.
    (* [comment removed for export] *)
    eapply rimplT_evt.
    { eapply (ram_bl_ok _ gp tp t0 t1 t2 (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 _ s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 (old + 4096)); [lia | | | exact MI2].
      - unfold pw in HC2. cbn [oconc] in HC2. exact HC2.
      - unfold wz in TC2. exact TC2. }
    (intros ms4 dd_H; ddestruct dd_H as (m3 & -> & MU3 & WM3 & MI3 & HC3 & TC3)). replace (old + 4096 - 4096) with old by lia.
    (* [comment removed for export] *)
    dpose (rAMI_grow st stI brid r boff AI Hr ltac:(rewrite Kr; discriminate) Lr) as (AIG & CQG & RG'). fold stG in AIG, CQG, RG'.
    assert (MRG : rmrep stG m2).
    { unfold stG. apply (rmrep_grow_region stI m2 brid r boff MR2 Hr);
        first [ rewrite Kr; discriminate
              | exact Lr
              | unfold PGSZ in OAL; exact OAL
              | rewrite <- OLD; exact RF
              | exact (amp_rpos stI AMPI)
              | intros q rq Hq NE KB; apply NE; exact (UNQ q rq Hq KB)
              | rceilb; unfold PGSZ in *; lia ]. }
    assert (PWX : forall q, pw stX q = pw stI q) by (intros [q|]; unfold pw, oconc; [change (conc stX q) with (conc stG q); rewrite CQG|]; reflexivity).
    assert (PWG : forall q, pw stG q = pw stI q) by (intros [q|]; unfold pw, oconc; [rewrite CQG|]; reflexivity).
    assert (CQX : forall q, conc stX q = conc stI q) by (intros q; change (conc stX q) with (conc stG q); apply CQG).
    assert (MRX : rmrep stX m3).
    { eapply (rmrep_ctx_frameW stG stX m2 m3 _ MRG MU3 WM3); try reflexivity.
      - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold ctx_head_cells. rewrite !PWX.
        cbn [ctx stX stG upd_ctx s_ctx set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        change (s_ctx stI) with (ctx stI). unfold wz at 5. exact HC3.
      - right. split; [| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
        unfold actives. apply map_ext. intros i. rewrite PWX, PWG. reflexivity.
      - right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
      - right. split; [reflexivity| intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia].
      - left. unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
        change (conc stX (brid, boff + 4096)) with (conc stG (brid, boff + 4096)).
        rewrite CQG. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold wz.
        replace (r_base r + (boff + 4096)) with (old + 4096) by lia. change (s_ctx stI) with (ctx stI). exact TC3. }
    (* [comment removed for export] *)
    assert (M23 : magree (rFP stX) m2 m3).
    { eapply magree_of_munch; [exact MU3|]. cbn. unfold RCTX. split; [| split; [| exact I]]; intros y Hy; left; right; right; left; unfold RCTX; lia. }
    assert (ZN3 : rw_cells rsegs m3 old [CB (Z.to_nat 4096) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))]).
    { eapply rw_cells_transport; [exact ZN| exact MU3| exact WM3|]. cbn. unfold RCTX. lia. }
    destruct ZN3 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize Nat.add app] in ZB, ZW. rewrite app_nil_r in ZB.
    assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
    assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]; cbn; unfold RCTX; lia).
    assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]; cbn; rewrite rETP'; unfold RCTX; lia).
    assert (AGX1 : forall y, rFP stI y -> rFP stX y).
    { intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. destruct (ami_regions _ _ AI q rq) as (r0 & H0 & _); [rewrite <- RGI; exact Hq|].
      destruct (decide (q = brid)) as [->|NE].
      - eexists. split; [exact RG'|]. rewrite Hr in Hq. inversion Hq; subst. cbn. repeat split; lia.
      - exists rq. change (s_regions stX) with (<[brid := mkRegion (r_kind r) (r_base r) (boff + 4096)]> (s_regions stI)). rewrite lookup_insert_ne by congruence. repeat split; auto; lia. }
    assert (AG3 : magree (rFP stX) m m3).
    { eapply magree_trans; [| exact M23| exact AGX1| intros y X; exact X]. eapply magree_trans; [exact AG1| exact M12| intros y X; exact X| intros y X; exact X]. }
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
    { eapply rauxv_ok_magree; [exact AUX1| |intros y X; exact (rFP_below stX y (proj1 MRX) X)].
      eapply magree_trans; [exact M12| exact M23| exact AGX1| intros y X; exact X]. }
    replace (Z_to_bv 64 old) with (Z_to_bv 64 (conc stX (brid, boff))) by (change (conc stX (brid, boff)) with (conc stG (brid, boff)); rewrite CQG; reflexivity).
    eapply (rcarve_K stX (brid, boff) (mkRegion (r_kind r) (r_base r) (boff + 4096)) m3 _ junk e1);
      first [exact RG' | exact MRX | exact MI3 | exact FR3 | exact ST3 | exact ERR3 | exact AUX3 | exact AG3 | reflexivity | idtac].
    + unfold stX. apply (rAMI_ctx st stG _ AIG).
      * cbn. repeat split; reflexivity.
      * cbn. exact (ami_secretr _ _ AIG).
      * left. reflexivity.
      * right. right. dexists brid, (boff + 4096), (mkRegion (r_kind r) (r_base r) (boff + 4096)). split; [reflexivity|]. split; [exact RG'|]. cbn. rewrite Kr. discriminate.
    + cbn. rewrite Kr. discriminate.
    + cbn. lia.
    + cbn [snd r_len]. rewrite round_up_pg_aligned; [lia|]. rewrite Z.add_mod, OAL by lia. reflexivity.
    + unfold pgal. unfold PGSZ in OAL. exact OAL.
    + cbn [snd r_base]. unfold lr_lo. cbn [r_kind r_base]. rewrite Kr. unfold PGSZ in O4. lia.
    + change (s_areas stX) with (s_areas stI). apply (proj1 (FRA (brid, boff) eq_refl ltac:(cbn; lia))).
    + intros j Hj. change (s_metas stX) with (s_metas stI). apply (proj2 (FRA (aadd (brid, boff) (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
    + intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
    + cbn. lia.
    + change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZB.
    + change (conc stX (brid, boff)) with (conc stG (brid, boff)). rewrite CQG. fold old. exact ZW.
    + unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
      rewrite CQX. rewrite (conc_region' stI (brid, boff + 4096) r Hr). cbn [snd]. unfold PGSZ. lia.
  - (* [comment removed for export] *)
    unfold brk_answer_ok. rewrite Z.eqb_refl.
    replace (old =? old + PGSZ) with false by (symmetry; apply Z.eqb_neq; unfold PGSZ; lia). cbn [orb negb].
    eapply rimplT_evt.
    { unfold PGSZ. eapply (ram_bl_fail _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI old); [exact MR1| exact ACNT| lia| lia| exact MI1]. }
    (intros ms4 dd_H; ddestruct dd_H as (m3 & -> & MU3 & WM3 & MI3 & MRD)).
    assert (M13 : magree (rFP stI) m1 m3).
    { eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
    eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 s junk e1); first [exact MRD | exact MI3 | reflexivity | idtac].
    + apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
    + exact RGI.
    + exact ACNT.
    + change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
    + exact TLI.
    + exact MKI.
    + dpose PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
    + eapply rw_cells_transport; [exact FR1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
    + eapply stk_transport_disjoint; [exact ST1| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
    + eapply rw_cells_transport; [exact ERR1| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
    + eapply rauxv_ok_magree; [exact AUX1| exact M13| intros y X; exact (rFP_below stI y WF1 X)].
    + eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1 M13); intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


Local Ltac2 Set LiaOrc.tbl := fun () => "01k0@L10947458327.106L11803467684.117L11803634851.109L11807078258.107L12415402805.195L18197161723.121L18925874810.158L18926535208.178L18926678662.193L18928498840.113L19245567059.202L19265708313.133L22706596293.184L22923820699.114L22923917470.100L25069682474.193L25069796649.196L25069843881.174L26037337389.158L26344050169.133L26678373646.210L26680472829.193L26682372276.204L26682374324.210L26901956799.174L28002138295.111L28077334119.130L28079382497.178L28083890767.206L29784180006.133L30972783153.157L30972783154.133L31332171611.169L31332171738.184L31332192896.129L31332194059.128L31332194325.167L31332194325.168L31332194325.169L31332194325.193L31332194325.195L31334093916.210L31334095964.204L31338480102.210L3228147421.178 L32532659937.178L33311269285.178L33313544981.113L34210629134.130L34278262948.163L37097343144.199L3710568306.202 L3710568306.203 L3712931473.113 L3712931473.118 L37495718600.199L39106631318.133L39210363599.133L39532249910.199L39621423194.199L39631659935.210L40195148532.122L40494889883.123L44009795506.118L44031104390.175L44483050731.117L44483185900.108L44610905063.163L45197858741.157L45623613246.133L45625714495.127L45625788729.116L47039125430.133L48839323451.184L48839323578.169L48839346420.167L48839346420.168L48839346420.169L48839346420.193L48839346420.195L48841508029.210L48841510077.204L48845639943.210L50324209823.113L50459855632.199L50602379985.168L5115421043.199 L51435258009.199L51489998255.210L51490000303.204L51491899878.167L51491899878.168L51491899878.169L51491899878.193L51491899878.195L51492007465.184L51492007592.169L51493998613.210L51864552859.118L54655238256.158L57212665560.199L5756892644.199 L57587505102.133L57628789700.184L58258292945.163L59308587280.179L59579071025.115L60492756848.129L60494842696.130L60494849046.129L61132225997.111L61429770410.210L62831717169.199L6630996118.133 L7170411736.133 L7172389982.111 L7172521050.178 L7172521177.127 L7174751978.113 L7381912027.110 L828472123.192  L883030363.119  L9164483184.199 00000800W00\01;01]02D02Q02^02k03003@03P03b03j04504F04S05:05D05c06[07B07l08i09609;09S09o0:K0:m0;P0<30<E0<W0<a0<k0==0=O0>?0>Q0?90@00@X0AN0AO0AP0Ad0B00B<0B=0B>0BO0B`0Bj0C40C50C>0CC0CD0CE0Ca0D20D;0DD0DQ0Dk0EE0ER0EW0E`0F90FR0FW0Fi0G;0GT0Gm0H]0I60IH0II0IJ0IK0IS0IT0J40J50J60Jd0K@0Kl0LX0MD0MV0NJ0OA0OY0PB0PM0PW0Pd0Pe0Pj0Q?0Q@0QP0QU0Q^0Qh0R20R:0RR0RS0RX0R`0Rh0S80S@0SH0SM0Sb0Sk0SlS3cur2CRS3hRP2sp2lo4LOLE3LO'3RCB3cur2CRS3curS3hRP2sp2lo4LOLE3LO'3RCB3cur2CRS3hRP2sp2lo3stI3LO'3RCB3cur2CR3ridS3hRP2sp2lo4LOLE3stI3LO'4RPRS3cur2CR2OCS3stI3cur3ridS3stI3cur3ridS3stI3cur3ridS3curS3stI3cur3rid2rqS2sp2lo4LOLE3curS3stI3cur3rid1y2N1S3cur2CRS3cur2CR2C0S3stI3cur3IMG3ridS3stI3cur3ridS3hRP2sp2lo4LOLE3stI3LO'3RCB3cur2CR3ridS3cur1e2HES3hRP2sp2lo4LOLE3LO'3RCB3cur2CRS3hRP2sp2lo3stI3LO'3cur2CR3rid1b1y2Hy2rb2Cb3Sb03Sb14RBCbS3hRP2sp2lo3stI3LO'3RCB3cur2CR3rid1y2HyS3hRP2sp2lo3stI3LO'3cur2CR3rid2rq1y2Hy3RBCS3hRP2sp2lo3stI3LO'3cur2CR3rid1a1y2Hy3rra2Ca3Sa03Sa13RBa4RBCaS3stI3cur3ridS3curS3hRP3stI4RPRS3cur2CR2OCS3hRP3stI4RPRS3cur2CR2OC3ridS3hRP3stI4RPRS3cur2CR2OC3ridS3hRP2sp2lo3stI3LO'4RPRS3cur2CR2OCS3hRP2sp2lo4LOLE3SPR3LO'3RCB3cur2CRS3hRP2sp2lo4LOLE3SPR3LO'3RCB3cur2CRS3stI3cur3rid1y2HyS3stI3cur3rid1y2HyS3cur1y2HyS3cur1y2HyS3stI3cur3rid1y2HyS3stI3cur3rid1y2HyS3hRP2sp2lo4LOLE3stI3SPR3LO'3RCB3cur2CR3rid1y2HyS3stI3cur3rid1y2HyS3hRP3stI3RCB4RPRS3cur2CR2C02OC3rid1y2HyS3hRP3stI3RCB3cur2CR3rid1a1y2Hy3rra2Ca3Sa03Sa13RBa4RBCaS3hRP3stI3RCB3cur2CR3rid2rq1y2Hy3RB03RBCS3hRP3stI3RCB3cur2CR3rid1b1y2Hy2rb2Cb3Sb03Sb13RBb4RBCbFFS3stI3cur2CR3CAL3ridS3cur2CR3CALS3cur1y1H2H0FFS3stI3cur3rid1y1XS3stI3cur3rid1y1XS3cur1y2HyS3cur1y2HyFS3cur3IMGS3curFFS3stI3cur3rid1a1y2Hy3rra3Sa0S3cur2CR3IMG1y2HyS3cur3IMGS3cur3IMGS3stI3cur3ridS3hRP2sp2lo3LO'3RCB3cur2CRS3hRP2sp2lo3LO'3RCB3cur2CRS3stI3cur3ridS3curS3cur3HcnS3hRP3stI3RCB4RPRS3cur2OCS3hRP3stI3RCB4RPRS3cur2OCS3curS3stI3cur3rid1y2N4S3stI3cur3rid1y2N3S3stI3cur2CR3IMG3rid1y2HyS3stI3cur2CR3IMG3rid1y2HyS3hRP2sp2lo4LOLE3stI3LO'4RPRS3cur2CR2OC3rid1y2HyS3stI3cur2CR3IMG3rid1y2HyS3stI3cur3rid1y2HyFFFS3cur2CRFS3hRP3stI3RCB4RPRS3cur2CR2OC3ridFFS3stI3cur2CR3rid1a1y2Hy3rra2Ca3Sa03Sa13RBa3Da2S3stI3cur2CR3rid2rq1y2Hy3Dq2S3hRP2sp2lo4LOLE3stI3LO'3RCB3cur2CR3rid1y2HyS3hRP2sp2lo4LOLE3stI3LO'3RCB3cur2CR3rid1y2HyS2sp3stI3cur3rid1y2Hy3hRP2lo4LOLE3LO'3RCB2CRS3stI3cur3rid1y2HyS3hRP2sp2lo4LOLE3stI3LO'4RPRS3cur2CR2OC3rid1y2Hy3IMGS3hRP2sp2lo4LOLE3stI3LO'3RCB4RPRS3cur2CR2OC3rid1y2N22N3S2sp3stI3cur3rid1y2N12N2S3stI3cur2CR3rid1b1y2Hy2rb2Cb3Sb03Sb13Db2S3stI3cur1HS3cur1e2HES3stI3cur3ridFS3curS3stI3cur3rid1y2N02N1FS3stI3cur3rid2HqS3curS3cur1y1HS3cur1y2H0S3cur1y2HnS3cur2CRS3stI3cur3rid1b1y2Hy3Sb0FS3curS3cur2C0S3cur2C0S3stI3cur2C03ridS3cur2C0S3cur2CRS3curS3stI3cur2CR3rid1q2HqS3cur3IMGF". (* [comment removed for export] *)
Lemma rbrk_untried_path : forall (stI : mstate) (m1 : mem) (junk : list byte) (e1 : word)
    (x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
  RAMpre stI -> AMI st stI -> s_regions stI = s_regions st ->
  c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkUntried ->
  ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
  rmrep stI m1 -> mem_inv rsegs m1 ->
  rw_cells rsegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs m1 lo (bv_unsigned sp + -64) ->
  rw_cells rsegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
  ps_m s = ps_m s ->
  rimplT o (SVis (EBrk 0) (fun cur =>
          if negb (brk0_answer_ok cur) then bad_answer bail else
          let base := round_up_pg cur in
          let new := base + 2 * PGSZ in
          SVis (EBrk new) (fun r =>
            if negb (brk_answer_ok cur new r) then bad_answer bail else
            if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
            else if negb (brk_pages_ok stI base (2 * PGSZ)) then bad_answer bail
            else
              SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
                if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
                let '(st1, rid) := new_region RKBrk base (2 * PGSZ) stI in
                let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                              (set_avail_meta_areas (Some (rid, PGSZ))
                                              (set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
                am_after_brk st2 false k bail)))) s Q
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x40398) fc None m1 (seg_rom rsegs)).
Proof using AMP ERR KH LO LOLE TK TP.
  intros until t6. intros AMPI AI RGI ACNT BRK PTRI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1 _.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. rceilb. pose proof rETP as rETP'. pose proof TP as TPv.
  dpose MR1 as (WF1 & (HX1 & HX2 & HX3 & HX4 & HX5 & HX6) & _). dpose WF1 as ((RS & RPRS) & WR & DJ & WA & WG).
  assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
  assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
  unfold ctx_head_cells in HX1. rewrite ACNT in HX1. unfold ctx_tail_cells, brk_word in HX6. rewrite BRK in HX6.
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { eapply (ram_disp_untried _ gp tp t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
  intros ms2 ->.
  eapply (rimplT_brk0 o _ s).
  { exact (ram_brk0_node x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
             s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1). }
  intros cur ms3 [-> CR]. unfold rbrk_regs.
  destruct (brk0_answer_ok cur) eqn:B0; cbn [negb]; [| apply rimplT_undef].
  unfold brk0_answer_ok, TWO64, PGSZ in B0. apply andb_prop in B0. destruct B0 as [B0 _]. apply andb_prop in B0. destruct B0 as [C0 CAL].
  apply Z.ltb_lt in C0. apply Z.eqb_eq in CAL.
  rewrite (round_up_pg_aligned cur CAL). cbv zeta. unfold PGSZ.
  replace (2 * 4096) with 8192 by reflexivity.
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { eapply (ram_bu_mid _ gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m1 cur); [lia| exact CAL| unfold wz in HX6; exact HX6| exact MI1]. }
  (intros ms4 dd_H; ddestruct dd_H as (a2' & m2 & -> & MU2 & WM2 & MI2 & TC2)).
  eapply (rimplT_brk o (cur + 8192) _ (set_brk_ps cur s)).
  { lia. }
  { exact (ram_brk_node_at x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK)
             s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2 0x403f8 (or_intror eq_refl) cur (cur + 8192) ltac:(lia)). }
  intros a ms5 ->. cbn [ps_brk set_brk_ps]. unfold brk_res, brk_mem, rbrk_regs.
  (* [comment removed for export] *)
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
  assert (ST2 : stk rsegs m2 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
  assert (ERR2 : rw_cells rsegs m2 (errno_addr tp) [C4 e1]) by (eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2|]; cbn; rewrite rETP'; unfold RCTX; lia).
  assert (HC2 : rw_cells rsegs m2 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
    by (eapply rw_cells_transport; [exact HX1| exact MU2| exact WM2|]; cbn; unfold RCTX; lia).
  assert (M12 : magree (rFP stI) m1 m2).
  { eapply magree_of_munch; [exact MU2|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
  destruct a.
  - (* [comment removed for export] *)
    unfold brk_answer_ok. rewrite Z.eqb_refl. cbn [orb negb].
    destruct (brk_pages_ok stI cur 8192) eqn:BPO; cbn [negb]; [| apply rimplT_undef].
    unfold brk_pages_ok in BPO. apply andb_prop in BPO. destruct BPO as [BPO RF]. apply andb_prop in BPO. destruct BPO as [_ OC]. apply Z.leb_le in OC.
    rceilb.
    rewrite (brk_new_pages_aligned cur 8192) by (first [lia | exact CAL | reflexivity]).
    pose proof (rimage_range_clear stI cur 8192 RS RF ltac:(lia)) as IMG.
    assert (Hc1 : 0 <= cur < 2^64) by lia. assert (Hn1 : 0 <= 8192 < 2^64) by lia. assert (Hcn : cur + 8192 <= 2^64) by lia.
    set (m3 := apply_zeros m2 [(wa cur, Z_to_bv 64 8192)]).
    assert (HC3 : rw_cells rsegs m3 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end))
      by (apply (rw_cells_zeros_other rsegs m2 cur 8192 Hc1 Hn1 Hcn); [exact HC2| cbn; unfold RCTX; lia]).
    assert (TC3 : rw_cells rsegs m3 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)])
      by (apply (rw_cells_zeros_other rsegs m2 cur 8192 Hc1 Hn1 Hcn); [unfold RCTX in TC2 |- *; exact TC2| cbn; unfold RCTX; lia]).
    assert (MI3 : mem_inv rsegs m3) by (apply (mem_inv_zeros rsegs m2 cur 8192 Hc1 Hn1 Hcn MI2); intros y Hy; apply ref_ro_addr_false; lia).
    assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (apply (rw_cells_zeros_other rsegs m2 cur 8192 Hc1 Hn1 Hcn); [exact FR2| cbn; lia]).
    assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -64)) by (apply (stk_zeros rsegs m2 cur 8192 Hc1 Hn1 Hcn); exact ST2).
    assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 e1]) by (apply (rw_cells_zeros_other rsegs m2 cur 8192 Hc1 Hn1 Hcn); [exact ERR2| cbn; rewrite rETP'; lia]).
    pose proof (rw_cells_zeros_new rsegs m2 cur 8192 Hc1 Hn1 Hcn) as ZN. fold m3 in ZN.
    assert (M23 : magree (rFP stI) m2 m3).
    { intros y Hy Hc. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia.
      destruct (Z.lt_ge_cases y cur); [lia|]. destruct (Z.lt_ge_cases y (cur + 8192)); [| lia].
      exfalso. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| rceilb; lia| lia]. }
    (* [comment removed for export] *)
    assert (E23 : forall y, 0 <= y < 2^64 -> ~ (cur <= y < cur + 8192) -> m3 (wa y) = m2 (wa y)).
    { intros y Hy Hn. unfold m3. apply (zeros_outside m2 cur 8192 Hc1 Hn1 Hcn). rewrite wa_unsigned by lia. lia. }
    clearbody m3.
    (* [comment removed for export] *)
    eapply rimplT_evt.
    { eapply (ram_bu_ok _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m3 cur);
        first [exact TC3 | lia]. }
    intros ms6 ->.
    pose proof MI3 as MI4. pose proof FR3 as FR4. pose proof ST3 as ST4. pose proof TC3 as TC4. pose proof HC3 as HC4. pose proof ERR3 as ERR4.
    eapply (rimplT_mmap_fixed o cur PGSZ _ (set_brk_ps (cur + 8192) (set_brk_ps cur s))).
    { unfold PGSZ. eapply (rmmap_fixed_spec (dec_mmap_fixed cur 4096) (fx_rel cur)) with (lo := lo) (errv := e1);
        [ intros rsp fa Hd; exact (dec_mmap_fixed_shape cur 4096 rsp fa Hd)
        | rewrite unsigned_lit by lia; exact ST4 | exact ERR4 | exact MI4 | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ..];
        rewrite ?A2.mmap_len_round_up, ?rETP', ?TPv, ?unsigned_lit by lia; try (change (round_up_pg 4096) with 4096); try lia. }
    intros fa ms7 MP. unfold rmmap_fixed_post in MP.
    ddestruct MP as (rr & u & u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m5 & REL & -> & MU5 & WM5 & MI5 & ST5 & ERR5).
    rewrite A2.mmap_len_round_up in MU5. change (round_up_pg 4096) with 4096 in MU5. rewrite unsigned_lit in MU5, ST5 by lia.
    replace (ret_pc (Z_to_bv 64 0x4041c)) with (Z_to_bv 64 0x4041c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    replace (mmap_fixed_answer_ok cur (fixed_val cur fa)) with true.
    2:{ symmetry. unfold mmap_fixed_answer_ok, is_errno_form, fixed_val, neg_errno, TWO64.
        destruct fa as [e|  |e]; cbn in REL.
        - destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
        - apply orb_true_iff. right. apply Z.eqb_refl.
        - destruct REL as [RE _]. destruct (errno_of_Some _ _ RE) as [_ HE]. apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
    cbn [negb].
    unfold new_region. cbv beta iota zeta delta [fst snd].
    set (rid := s_next_rid stI).
    dpose (rAMI_new_region st stI RKBrk cur 8192 AI ltac:(discriminate) ltac:(lia)) as (AI1 & RG1 & CQ1 & CN1).
    unfold new_region in AI1, RG1, CQ1, CN1. cbn [fst snd] in AI1, RG1, CQ1, CN1. fold rid in AI1, RG1, CQ1, CN1 |- *.
    set (st1 := set_next_rid (N.succ rid) _) in AI1, RG1, CQ1, CN1 |- *.
    rewrite (am_after_brk_false_eq st1 _ (rid, 4096) k bail) by (cbn; first [lia | reflexivity]).
    rewrite am_carve_took, carve_st_brk_irrel.
    set (stX := upd_ctx _ st1).
    (* [comment removed for export] *)
    assert (E45 : forall y, 0 <= y < 2^64 -> ~ (bv_unsigned sp - 64 - 80 <= y < bv_unsigned sp - 64) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 4096) -> m5 (wa y) = m3 (wa y)).
    { intros y Hy N1 N2 N3. apply MU5. rewrite wa_unsigned by lia. cbn. rewrite ?rETP' in *. repeat split; lia. }
    assert (HC5 : rw_cells rsegs m5 RCTX ltac:(lazymatch type of HX1 with rw_cells _ _ _ ?cs => exact cs end)).
    { eapply RA2.rrw_cells_agree; [exact HC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
    assert (TC5 : rw_cells rsegs m5 (RCTX + 912) [C1 (b8 (c_seq (ctx stI))); CB 7 (zeros 7); C8 (Z_to_bv 64 cur)]).
    { eapply RA2.rrw_cells_agree; [exact TC4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; unfold RCTX in *; lia. }
    assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)).
    { eapply RA2.rrw_cells_agree; [exact FR4|]. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
    eapply rimplT_evt.
    { eapply (ram_b_store _ gp tp u0 u1 u2 _ u3 u4 u5 u6 u7 u8 u9 s4x s5 s6 s7 s8 s9 s10 s11 u10 u11 u12 u13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m5 (cur + 8192));
        first [exact HC5 | exact TC5 | exact MI5 | lia]. }
    (intros ms8 dd_H; ddestruct dd_H as (m6 & -> & MU6 & WM6 & MI6 & HC6 & TC6)). replace (cur + 8192 - 4096) with (cur + 4096) by lia.
    assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)) by (eapply rw_cells_transport; [exact FR5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
    destruct (ami_fresh _ _ AI rid ltac:(unfold rid; lia)) as [FRr FRs].
    (* [comment removed for export] *)
    assert (E16 : forall y, 0 <= y < 2^64 ->
              ~ (RCTX + 40 <= y < RCTX + 48) -> ~ (RCTX + 920 <= y < RCTX + 928) -> ~ (lo <= y < bv_unsigned sp) -> ~ (errno_addr tp <= y < errno_addr tp + 4) -> ~ (cur <= y < cur + 8192) ->
              m6 (wa y) = m1 (wa y)).
    { intros y Hy N0 N1 N2 N3 N4.
      rewrite (MU6 (wa y)) by (rewrite wa_unsigned by lia; cbn; unfold RCTX in *; lia).
      rewrite (E45 y Hy) by (rewrite ?rETP' in *; lia).
      rewrite (E23 y Hy) by lia.
      apply MU2. rewrite wa_unsigned by lia. cbn. unfold RCTX in *. lia. }
    assert (MRn1 : rmrep st1 m1).
    { unfold st1. apply (RA2.rmrep_new_region stI m1 m1 cur 8192 RKBrk);
        first [ exact MR1
              | eapply ptrs_in_mono; [| exact PTRI]; intros q Hq; cbn in Hq; intros ->; unfold rid in Hq; lia
              | exact FRr | exact FRs
              | rceilb; change (round_up_pg 8192) with 8192; lia
              | change (round_up_pg 8192) with 8192; exact RF
              | intros; reflexivity
              | intros; discriminate
              | lia ]. }
    assert (CQX : forall q, fst q <> rid -> conc stX q = conc stI q) by (intros q Hq; change (conc stX q) with (conc st1 q); apply CQ1; exact Hq).
    dpose PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
    assert (PWX : forall q, optr_in (fun r => (r < s_next_rid stI)%N) q -> pw stX q = pw stI q).
    { intros [q|] Hq; unfold pw, oconc; [rewrite CQX; [reflexivity|]|reflexivity]. cbn in Hq. unfold rid. lia. }
    assert (MRX : rmrep stX m6).
    { apply (rmrep_agree_but_ctx st1 stX m1 m6 MRn1); try reflexivity.
      - intros y Hy. apply E16; rewrite ?rETP'; unfold RMLOCK, RCTX in *; lia.
      - intros y Hy. apply E16; rewrite ?rETP'; unfold RLIBC, RCTX in *; lia.
      - intros y Hy. apply E16; rewrite ?rETP'; unfold RGOT_SSP, RCTX in *; lia.
      - intros y Hy. apply E16; rewrite ?rETP'; unfold RSSP_GUARD, RCTX in *; lia.
      - intros a ar Ha y Hy. change (s_areas st1) with (s_areas stI) in Ha.
        ddestruct (rarea_conc stI a ar WF1 Ha) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RBa & RBAa & RBCa).
        destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as (Da1 & _ & Da23 & Da2). rceilb.
        rewrite (CQ1 a) in Hy by (intros E; rewrite E, FRr in Hra; discriminate).
        apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. eapply rrepfoot_area; [exact Ha| lia].
      - intros b gh Hb y Hy. change (s_groups st1) with (s_groups stI) in Hb.
        ddestruct (rgroup_conc stI b gh WF1 Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Alb & RBb & RBCb).
        destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). destruct (rreserved_disjoint _ _ RFb) as (Db1 & _ & Db23 & Db2). rceilb.
        pose proof (round_up_pg_ge (r_len rb)).
        rewrite (CQ1 b) in Hy by (intros E; rewrite E, FRr in Hrb; discriminate).
        apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). left. do 5 right. left. dexists b, gh. split; [exact Hb| lia].
      - intros q rq Hq Kq y Hy.
        assert (Hq' : (s_regions stI) !! q = Some rq).
        { change (s_regions st1) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)) in Hq.
          destruct (decide (q = rid)) as [->|NE]; [rewrite lookup_insert_eq in Hq; inversion Hq; subst; discriminate| rewrite lookup_insert_ne in Hq by congruence; exact Hq]. }
        destruct (WR _ _ Hq') as (RB0 & _ & _ & RBC & RFq). destruct (rreserved_disjoint _ _ RFq) as (Dq1 & _ & Dq23 & Dq2). rceilb.
        apply E16; rewrite ?rETP'; unfold RCTX; try lia. apply (rrepfoot_clear stI m1 cur 8192 y MR1 RF). right. dexists q, rq. auto.
      - (* [comment removed for export] *)
        ddestruct (rmrep_ctx_mid_agree st1 stX m1 m6 MRn1 ltac:(right; repeat split; reflexivity) eq_refl) as (X2 & X3 & X4 & X5).
        { intros y Hy. apply E16; rewrite ?rETP'; unfold RCTX in *; lia. }
        split; [| split; [exact X2| split; [exact X3| split; [exact X4| split; [exact X5|]]]]].
        + unfold ctx_head_cells. rewrite !PWX by assumption.
          cbn [ctx stX st1 upd_ctx s_ctx set_next_rid set_regions set_avail_meta_area_count set_brk c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
               c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
          change (s_ctx stI) with (ctx stI). unfold pw in HC6 |- *. cbn [oconc] in HC6 |- *. unfold wz. exact HC6.
        + unfold ctx_tail_cells, brk_word. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk c_seq].
          change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. change (s_ctx st1) with (ctx stI). unfold wz. exact TC6. }
    (* [comment removed for export] *)
    assert (ZP3 : rw_cells rsegs m3 (cur + 4096) [CB 4096 (zeros 4096)]).
    { destruct ZN as [[_ ZB0] ZW0]. cbn [cells_bytes cbytes cells_size csize app] in ZB0, ZW0. rewrite app_nil_r in ZB0. rewrite Nat.add_0_r in ZW0.
      eapply (rrw_cells_of_zeros m3 cur 8192 4096); [exact ZB0| exact ZW0| split; [exact (zeros_length 4096)| exact I]| cbn [cells_bytes cbytes cells_size csize]; rewrite app_nil_r, Nat.add_0_r; reflexivity| lia| cbv; discriminate]. }
    assert (ZP6 : rw_cells rsegs m6 (cur + 4096) [CB 4096 (zeros 4096)]).
    { eapply rw_cells_transport; [| exact MU6| exact WM6| cbn [cells_size csize]; rewrite ?Nat.add_0_r; cbn; unfold RCTX; lia].
      eapply RA2.rrw_cells_agree; [exact ZP3|].
      cbn [cells_size csize]. rewrite ?Nat.add_0_r. cbn. intros y Hy. apply E45; rewrite ?rETP'; lia. }
    destruct ZP6 as [[_ ZB] ZW]. cbn [cells_bytes cbytes cells_size csize app] in ZB, ZW. rewrite app_nil_r in ZB. rewrite Nat.add_0_r in ZW.
    assert (ST6 : stk rsegs m6 lo (bv_unsigned sp + -64)) by (eapply stk_transport_disjoint; [exact ST5| exact MU6| exact WM6|]; cbn; unfold RCTX; lia).
    assert (ERR6 : rw_cells rsegs m6 (errno_addr tp) [C4 (sysret_errno rr e1)]) by (eapply rw_cells_transport; [exact ERR5| exact MU6| exact WM6|]; cbn; rewrite rETP'; unfold RCTX; lia).
    assert (FPX : forall y, rFP stI y -> rFP stX y).
    { intros y X. eapply rFP_mono; [| exact X]. intros q rq Hq. exists rq.
      change (s_regions stX) with (<[rid := mkRegion RKBrk cur 8192]> (s_regions stI)).
      rewrite lookup_insert_ne by (intros ->; rewrite FRr in Hq; discriminate). repeat split; auto; lia. }
    assert (M16 : magree (rFP stX) m1 m6).
    { intros y Hy Hc.
      assert (~ (RCTX + 40 <= y < RCTX + 48)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
      assert (~ (RCTX + 920 <= y < RCTX + 928)) by (intros X; apply Hc; left; right; right; left; unfold RCTX in *; lia).
      assert (~ (lo <= y < bv_unsigned sp)) by (intros X; apply Hc; left; left; exact X).
      assert (~ (errno_addr tp <= y < errno_addr tp + 4)) by (intros X; apply Hc; left; right; left; rewrite <- TPv; exact X).
      assert (~ (cur <= y < cur + 8192)).
      { intros X. apply Hc. right. eapply (rfresh_of_ranges_free stI cur 8192); [exact RGI| exact (ami_reserved _ _ AI)| exact RF| rceilb; lia| exact X]. }
      apply E16; assumption. }
    replace (Z_to_bv 64 (cur + 4096)) with (Z_to_bv 64 (conc stX (rid, 4096))) by (change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)); rewrite CN1; reflexivity).
    eapply (rcarve_K stX (rid, 4096) (mkRegion RKBrk cur 8192) m6 _ _ (sysret_errno rr e1));
      first [exact RG1 | exact MRX | exact MI6 | exact FR6 | exact ST6 | exact ERR6 | reflexivity | idtac].
    all: try (cbn [snd fst r_len r_base r_kind]; unfold pgal, lr_lo; cbn [r_kind r_base]; change (round_up_pg 8192) with 8192; first [discriminate | lia]).
    + unfold stX. apply (rAMI_ctx st st1 _ AI1).
      * cbn. repeat split; reflexivity.
      * cbn. exact (ami_secretr _ _ AI1).
      * left. reflexivity.
      * right. right. dexists rid, 8192, (mkRegion RKBrk cur 8192). split; [reflexivity|]. split; [exact RG1|]. cbn. discriminate.
    + change (s_areas stX) with (s_areas stI). lazymatch goal with |- ?t = None => destruct t as [ar|] eqn:EA end; [| reflexivity].
      exfalso. destruct (WA _ _ EA) as (rr0 & Hrr & _). cbn [fst] in Hrr. rewrite FRr in Hrr. discriminate.
    + intros j Hj. change (s_metas stX) with (s_metas stI). lazymatch goal with |- ?t = None => destruct t as [mr|] eqn:EM end; [| reflexivity].
      exfalso. destruct (MKI _ _ EM) as (a & ar & kk & Ha & Hk & Eq). destruct (WA _ _ Ha) as (rr0 & Hrr & _).
      assert (Ef : fst a = rid) by (unfold aadd in Eq; cbn in Eq; inversion Eq; reflexivity). rewrite Ef, FRr in Hrr. discriminate.
    + intros tl Htl. change (s_areas stX) with (s_areas stI). apply TLI. exact Htl.
    + cbn. lia.
    + change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZB.
    + change (conc stX (rid, 4096)) with (conc st1 (rid, 4096)). rewrite CN1. exact ZW.
    + eapply rauxv_ok_magree; [exact AUX1| exact M16| intros y X; exact (rFP_below stX y (proj1 MRX) X)].
    + eapply magree_trans; [exact AG1| exact M16| exact FPX| intros y X; exact X].
    + unfold brk_link_ps. cbn [ctx stX upd_ctx s_ctx set_avail_meta_area_count set_brk c_brk ps_brk set_brk_ps].
      change (conc stX (rid, 8192)) with (conc st1 (rid, 8192)). rewrite CN1. reflexivity.
  - (* [comment removed for export] *)
    unfold brk_answer_ok. rewrite Z.eqb_refl.
    replace (cur =? cur + 8192) with false by (symmetry; apply Z.eqb_neq; lia). cbn [orb negb].
    eapply rimplT_evt.
    { eapply (ram_bu_fail _ gp tp t0 t1 t2 (Z_to_bv 64 0) a2' a3 a4 a5 a6 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ F fc m1 m2 stI cur);
        first [exact MR1 | exact MU2 | exact WM2 | exact ACNT | exact MI2 | reflexivity | exact TC2 | lia]. }
    (intros ms6 dd_H; ddestruct dd_H as (m3 & -> & MU3 & WM3 & MI3 & MRD)).
    assert (M23 : magree (rFP stI) m2 m3).
    { eapply magree_of_munch; [exact MU3|]. cbn. split; [| exact I]. intros y Hy. left. right. right. left. unfold RCTX in *. lia. }
    eapply (rmmap_path (upd_ctx (set_brk BrkDead) stI) m3 (set_brk_ps cur s) junk e1); first [exact MRD | exact MI3 | reflexivity | idtac].
    + apply (rAMI_ctx st stI _ AI); [cbn; repeat split; reflexivity| cbn; exact (ami_secretr _ _ AI)| left; reflexivity| right; left; reflexivity].
    + exact RGI.
    + exact ACNT.
    + change (ctx (upd_ctx (set_brk BrkDead) stI)) with (set_brk BrkDead (ctx stI)). cbn [c_meta_alloc_shift set_brk]. pose proof (amp_shift stI AMPI). lia.
    + exact TLI.
    + exact MKI.
    + dpose PTRI as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10). apply rptrs_in_upd_ctx; cbn; try assumption; try reflexivity; try exact I.
    + eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
    + eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. cbn. unfold RCTX. lia.
    + eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. cbn. rewrite rETP'. unfold RCTX. lia.
    + eapply rauxv_ok_magree; [exact AUX1| | intros y X; exact (rFP_below stI y WF1 X)].
      eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X].
    + eapply (magree_trans (rFP stI) (rFP stI) _ m m1 m3 AG1); [eapply magree_trans; [exact M12| exact M23| intros y X; exact X| intros y X; exact X] | |];
        intros y X; (eapply rFP_same; [| exact X]); reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L16073376009.89L16073574760.94L18246688654.94L22777989999.88L23338653334.94L26327372739.94L38041033028.98L38043096497.89L50460061748.94L51864552859.85L61361112624.84L6714072449.112L6714072449.121L67860849478.9600000800F00L00^00d01A01M01Y01l02302B02K02T02_S3stI2CRS3stI1p2P03ACRS1p2P0S3stI3CNT2kk2K12CRS1p2P0S3stI4ACNT1p1r2P03PHI3ACR3PALS2sp2lo4LOLES2sp2lo4LOLES3stI4ACNT1p2P03ACRS3stI1HS2st3stI1q2Hq1HS2tp1a2HaS2tp1a2HaS1p2P01j2Hj". (* [comment removed for export] *)
#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbody_spec : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "PstI,$10.Px1,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps1x,(=.&40.)Ps4x,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Pm1,$17.Pjunk,(3>.(=.&8.))Pe1,(=.&40.)P,(74.$73.R16.)P,(3?.Vst,R17.)P,(22.(32.$2>.$33.$34.$2?.)(36.R18.)(36.Vst,))P,(15.R19.Vs,)P,(19.VhRP,R1:.R7.)P,(1:.$1.R8.)P,(0.$1.R9.(7.(1<.&40.Vsp,)-40.)(5;.VhRP,R8.Vs4,Vs3,Vs2,Vs1,Vs0,Vra,))P,(1;.$1.R:.Vlo,(7.(1<.&40.Vsp,)-40.))P,(0.$1.R;.(7.(1<.&40.Vtp,)-:4.)(1=.$1>.(1?.R9.)(20.$1>.)))P,(>.VhRP,R<.(1<.&40.Vsp,))P,(2.(21.R20.)Vm,R=.)(16.VR,Vo,(75.VR,R21.Vk,Vbail,)Vs,VQ,(29.(2:.R20.(5>.&40.(7.(1<.&40.Vsp,)-40.))Vgp,Vtp,R1?.R1>.R1=.(5>.&40.+1000.)R1<.R1:.R19.R18.R17.R16.R15.R14.R13.(5>.&40.$5?.)(5>.&40.$60.)R1;.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R12.R11.R10.R?.)VF,(5>.&40.+40344.)Vfc,(2<.(=.&40.))R>.(2=.$1.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until e1. intros AMPI AI RGI BLI MR1 MI1 FR1 ST1 ERR1 AUX1 AG1.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof MR1 as (WF1 & _).
  unfold am_body.
  destruct (c_free_meta_head (ctx stI)) as [h|] eqn:FMH.
  - (* [comment removed for export] *)
    pose proof (amp_fmh stI AMPI h FMH) as [HN0 HM0].
    pose proof (amp_links stI AMPI) as [CLn CLp CLno CLs].
    pose proof (CLs h HN0) as MSh.
    dpose (amp_fml stI AMPI h HM0 HN0) as (CL0 & FMn & FMp).
    destruct (m_next (get_meta_rec stI h)) as [nx|] eqn:HN; [| exfalso; apply HN0; reflexivity].
    destruct (m_prev (get_meta_rec stI h)) as [pv|] eqn:HP.
    2:{ exfalso. pose proof (proj2 (CLno h) HP) as X. rewrite HN in X. discriminate. }
    destruct (CLn h nx HN) as [PVn MSn]. destruct (CLp h pv HP) as [NXp MSp].
    assert (SELF : nx = h <-> pv = h).
    { split; intros ->; [rewrite HP in PVn| rewrite HN in NXp]; congruence. }
    eapply rimplT_evt.
    { eapply (ram_deq sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI h nx pv);
        first [exact MR1 | exact MI1 | exact FMH | exact MSh | exact HN | exact HP | exact MSn | exact MSp | exact SELF | exact FR1 | exact ST1 | exact LO | lia]. }
    intros ms2 RP. unfold ram_ret_post in RP.
    ddestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
    eapply rfinish_K.
    + eapply (ram_rel_deq st stI h nx pv AI); try assumption.
      * rewrite <- FMH. symmetry. exact (proj1 (proj2 (ami_ctx _ _ AI))).
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HN.
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact HP.
      * eapply meta_slot_same_areas; [| exact MSh]. symmetry. exact (ami_areas _ _ AI).
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact CL0.
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMn nx eq_refl).
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). intros X. apply (proj1 (CLno nx)) in X. rewrite PVn in X. discriminate.
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). exact (FMp pv eq_refl).
      * unfold get_meta_rec. rewrite <- (ami_metas _ _ AI). rewrite NXp. discriminate.
    + exact MR2.
    + exact MI2.
    + exact ST2.
    + eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
    + eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
    + pose proof (sbl_regions _ _ (sbl_dequeue stI LFree h)) as RD.
      eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [exact RD| exact X] | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a RD)); exact X].
    + unfold brk_link_ps in *. rewrite (sbl_brk _ _ (sbl_dequeue stI LFree h)). destruct (c_brk (ctx stI)) as [| |rid off]; auto.
      unfold conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). exact BLI.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + unfold pw, oconc, wz, conc, get_region. rewrite (sbl_regions _ _ (sbl_dequeue stI LFree h)). reflexivity.
  - (* [comment removed for export] *)
    destruct (Z.eqb_spec (c_avail_meta_count (ctx stI)) 0) as [CNT|CNT]; cbn [negb].
    + (* [comment removed for export] *)
      eapply rimplT_evt.
      { eapply (ram_disp0 _ gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 RSSP_GUARD) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact FMH| exact CNT]. }
      intros ms2 ->.
      assert (TLI : forall tl, c_meta_area_tail (ctx stI) = Some tl -> is_Some ((s_areas stI) !! tl)) by (exact (amp_tail stI AMPI)).
      assert (MKI : forall q mr, (s_metas stI) !! q = Some mr -> meta_slot stI q) by (exact (amp_mkeys stI AMPI)).
      assert (PTRI : ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI).
      { apply (ami_ptrs _ _ AI); [| eapply ptrs_in_mono; [| exact (proj1 (amp_ptrs st AMP))]; intros q Hq; cbn in Hq; pose proof (ami_next _ _ AI); lia]. intros rid r Hr _.
        destruct (N.lt_ge_cases rid (s_next_rid stI)) as [L|G]; [exact L|]. destruct (ami_fresh _ _ AI rid G) as [X _]. rewrite X in Hr. discriminate. }
      destruct (Z.eqb_spec (c_avail_meta_area_count (ctx stI)) 0) as [ACNT|ACNT]; cbn [andb].
      * (* [comment removed for export] *)
        destruct (c_brk (ctx stI)) as [| |brid boff] eqn:BRK; cbn [negb].
        -- (* [comment removed for export] *)
           eapply (rbrk_untried_path stI m1 junk e1); first [exact AMPI | exact AI | exact RGI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | reflexivity].
        -- (* [comment removed for export] *)
           eapply rimplT_evt.
           { eapply (ram_disp_dead _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI); [exact MR1| exact ACNT| exact BRK]. }
           intros ms3 ->.
           eapply (rmmap_path stI m1 s junk e1); first [exact AI | exact RGI | exact ACNT | exact TLI | exact MKI | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
           pose proof (amp_shift stI AMPI). lia.
        -- (* [comment removed for export] *)
           eapply (rbrk_live_path stI brid boff m1 junk e1); first [exact AMPI | exact AI | exact RGI | exact BLI | exact ACNT | exact BRK | exact PTRI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1].
      * (* [comment removed for export] *)
        ddestruct (amp_avail_areas stI AMPI ACNT) as (p & r & AMA & Hr & NK & PAL & P0 & PLR & PHI & FRA).
        pose proof (amp_acount stI AMPI) as ACR.
        unfold am_after_brk. rewrite (proj2 (Z.eqb_neq _ _) ACNT).
        eapply rimplT_evt.
        { eapply (ram_disp_fin _ gp tp t0 t1 t2 s1x _ _ a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 stI p r);
            first [exact MR1 | exact ACNT | exact AMA | exact Hr | unfold pgal, PGSZ in *; exact PAL | lia | idtac]. unfold PGSZ in *. lia. }
        intros ms3 ->.
        eapply (rfinish_path stI p r m1 s junk e1); first [exact AI | exact AMA | exact Hr | exact NK | exact P0 | exact PLR | exact TLI | exact MR1 | exact MI1 | exact FR1 | exact ST1 | exact ERR1 | exact AUX1 | exact AG1 | exact BLI | reflexivity | idtac].
        -- unfold PGSZ in PHI. lia.
        -- unfold pgal. unfold PGSZ in PAL. exact PAL.
        -- apply (proj1 (FRA p eq_refl ltac:(lia))).
        -- intros j Hj. apply (proj2 (FRA (aadd p (AREA_HDR + META_SIZE * j)) eq_refl ltac:(cbn; unfold AREA_HDR, META_SIZE; lia))).
        -- lia.
    + (* [comment removed for export] *)
      ddestruct (amp_avail stI AMPI CNT) as (aa & ar & kk & Haa & AVM & K0 & K1 & MQ).
      pose proof (amp_count stI AMPI) as CR.
      assert (MSq : meta_slot stI (aadd aa (AREA_HDR + META_SIZE * kk))) by (exists aa, ar, kk; repeat split; auto; unfold NSLOTS in *; lia).
      rewrite (am_take_eq stI k bail _ AVM).
      eapply rimplT_evt.
      { eapply (ram_take_walk sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra s0 s1 s2 s3 s4 F fc m1 junk lo stI _);
          first [exact MR1 | exact MI1 | exact FMH | exact CNT | exact AVM | exact MSq | exact FR1 | exact ST1 | exact LO | unfold NSLOTS in CR; lia | lia]. }
      intros ms2 RP. unfold ram_ret_post in RP.
      ddestruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m2 & -> & PE2 & WM2 & MI2 & ST2 & MR2).
      eapply rfinish_K.
      * eapply (ram_rel_take st stI _ AI).
        -- rewrite <- AVM. symmetry. exact (proj1 (proj2 (proj2 (ami_ctx _ _ AI)))).
        -- rewrite <- (ami_metas _ _ AI). exact MQ.
        -- eapply meta_slot_same_areas; [| exact MSq]. symmetry. exact (ami_areas _ _ AI).
      * exact MR2.
      * exact MI2.
      * exact ST2.
      * eapply rrw_cells_magree; [exact ERR1| apply rmagree_of_pres; exact PE2|]. cbn. intros a Ha X. apply (rerrno_not_amfp stI a WF1); [exact X| lia].
      * eapply rauxv_ok_magree; [exact AUX1| apply rmagree_of_pres; exact PE2|]. intros a X. apply (rFP_below stI _ WF1). apply rFP_am. exact X.
      * eapply magree_trans; [exact AG1| apply rmagree_of_pres; exact PE2| intros a X; eapply rFP_same; [| exact X]; reflexivity | intros a X; apply rFP_am; eapply (proj2 (ram_fp_same _ _ lo _ a ltac:(reflexivity))); exact X].
      * unfold brk_link_ps in *. unfold ctx in BLI. cbn. destruct (c_brk (s_ctx stI)) as [| |rid off]; auto.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * unfold pw, oconc, wz. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L25069424428.89L3712931473.90 L37310060433.90L38043196530.6200000H00N00_00kS3hRP2sp2lo4LOLE3RCB3LO'S1y2HyS2sp2lo4LOLE1y2HyS2sp2lo4LOLE". (* [comment removed for export] *)
#[using="hRP lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH"] Lemma ralloc_meta_main : ltac2:(CDefT.buildp (gd_tbl_HP_RF_alloc_meta ()) "Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Pa0,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)(16.VR,Vo,(76.VR,Vst,Vk,Vbail,)Vs,VQ,(29.(2:.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,R<.R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(5>.&40.$77.)Vfc,(2<.(=.&40.))Vm,(2=.$1.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros. pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. unfold RAM_STACK in LOLE.
  pose proof LO as LO'. rceilb. pose proof rETP as rETP'. pose proof TP as TPv.
  pose proof MR as (WF0 & _).
  rewrite alloc_meta_eq. unfold ralloc_meta_entry.
  eapply rimplT_evt.
  { eapply (ram_entry ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st);
      first [exact MR | exact MI | exact AUX | exact ST | exact LO | exact (amp_init st AMP) | exact (amp_s_secret st AMP) | exact (amp_secret st AMP) | lia]. }
  (intros ms1 dd_H; ddestruct dd_H as (x1 & u0 & u1 & u2 & s1x & s4x & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u9' & u10 & u11 & u12 & u13 & m1 & junk & -> & MU1 & WM1 & MI1 & FR1 & ST1 & MR1)).
  assert (M01 : magree (rFP (am_init_st st)) m m1).
  { eapply magree_of_munch; [exact MU1|]. cbn. split; [| split; [| exact I]]; intros y Hy.
    - left. left. lia.
    - left. right. right. left. unfold RCTX in *. lia. }
  eapply (rbody_spec (am_init_st st) x1 u0 u1 u2 s1x s4x u3 u4 u5 u6 u7 u8 u9 u9' u10 u11 u12 u13 m1 junk errv).
  - exact (rAMpre_init st AMP).
  - exact (rAMI_init st AMP).
  - exact (ram_init_regions st).
  - unfold brk_link_ps in *. rewrite ram_init_brk. destruct (c_brk (ctx st)) as [| |rid off]; auto. rewrite ram_init_conc. exact BL.
  - exact MR1.
  - exact MI1.
  - exact FR1.
  - exact ST1.
  - eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite rETP'. cbn. unfold RCTX. lia.
  - eapply rauxv_ok_magree; [exact AUX| exact M01| intros a X; exact (rFP_below (am_init_st st) a (proj1 MR1) X)].
  - exact M01.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End ASM.

#[using="Type"] Theorem ralloc_meta_spec : ralloc_meta_stmt ram_pre.
Proof. rceilb.
  unfold ralloc_meta_stmt. intros.
  eapply ralloc_meta_main; eassumption.
Qed.



End RP_1.
