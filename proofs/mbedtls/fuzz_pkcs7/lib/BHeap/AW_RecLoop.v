(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR AW_FreeRB AW_FreeFam.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_Munmap AW_Poison AW_Populate
     AW_DepotA AW_DepotB AW_DepotC AW_DepotInv AW_DepotTop AW_MallocA AW_AllocA AW_AllocB AW_MallocB AW_MallocC AW_ClassId AW_Combined AW_Refill AW_Large
     AW_CfgS AW_CfgDefs AW_PopulateCfgS AW_PoisonBig AW_PoisonBigCfg AW_SMalloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_QPut AW_Enqueue AW_CbRecycle AW_CbRecycleS AW_LCDealloc AW_RTA AW_LargeFree AW_MunmapCfg AW_LargeFreeCfg
     AW_RecLC AW_RecChunk AW_RecChunkS AW_DoRecycle AW_DoRecycle2 AW_RecStep AW_RecStepSec AW_RecStepBatch.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AW_FakeRep HMLib HM HMFrame AW_FreeHM AW_FreeHMS AW_FreeHMX AImgW.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_RecLoop () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.not"; "ARUN_1.in_qs"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.None"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_size"; "Stdlib.Lists.List.filter"; "Corelib.Init.Datatypes.andb"; "Corelib.Init.Datatypes.negb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "Stdlib.ZArith.BinInt.Z.eqb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_QUARANTINE"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.false"; "ARUN_1.qs_of"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.rm_ab"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.RIq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.bn_of"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.qc_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.S"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.last_addr"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bsum"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.batch_hdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_elems"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.hd_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bwf"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "Stdlib.Lists.List.incl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.WFR"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.HMq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_K"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_CS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHMX.fkeepR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "ARUN_1.wmono_ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.qcache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.depot"; "ARUN_1.Loop.LST"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DoRecycle.dr_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.HMLib.kept"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "ARUN_1.Loop.LINV"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_recp"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.fkeep"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.SH"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_recs"; "ARUN_1.rp_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MunmapCfg.wmono_out"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.h_recb"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_elems"; "Stdlib.Lists.List.tl"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DoRecycle.dr_regs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_count"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DoRecycle.A_DR_TAIL"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_hdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.carved"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_at"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Peano.le"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.sub"; "ARUN_1.Loop.tail_cont"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DoRecycle.A_DR_INNER"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_CB_RECYCLE"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.hgeom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "ARUN_1.Loop.LINVx"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.msr"; "ARUN_1.Loop.exit_cont"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DoRecycle.A_DR_HEAD"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ffam"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "Stdlib.ZArith.BinInt.Z.modulo"; "ARUN_1.exit_cont"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DoRecycle.A_DORECYCLE"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition in_qs (QS : list (Z * Z)) (x : Z) : Prop := exists q, In q QS /\ fst q <= x < fst q + snd q.

Definition wmono_ex (QS : list (Z * Z)) (m m' : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Px,(0.&40.)P,(1.(2.O3.(3.&40.R1.)))P,(1.(4.(5.(0.&8.))(6.$7.O2.R2.)(8.(0.&8.))))(1.(4.(5.(0.&8.))(6.$7.O1.R3.)(8.(0.&8.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma wmono_ex_trans : forall QS m1 m2 m3, wmono_ex QS m1 m2 -> wmono_ex QS m2 m3 -> wmono_ex QS m1 m3.
Proof. intros QS m1 m2 m3 A B x Hx H. apply B; [exact Hx|]. apply A; [exact Hx| exact H]. Qed.
#[using="Type"] Lemma wmono_ex_of_wmono : forall QS m m', wmono asegs m m' -> wmono_ex QS m m'.
Proof. intros QS m m' W x _ H. apply W. exact H. Qed.
#[using="Type"] Lemma wmono_ex_of_out : forall QS a n m m', wmono_out a n m m' -> In (a, n) QS -> wmono_ex QS m m'.
Proof.
  intros QS a n m m' W IN x Hx H. apply W; [| exact H].
  destruct (Z.lt_ge_cases (bv_unsigned x) a) as [L|G]; [left; exact L|]. destruct (Z.lt_ge_cases (bv_unsigned x) (a + n)) as [L2|G2]; [| right; exact G2].
  exfalso. apply Hx. exists (a, n). split; [exact IN| cbn; lia].
Qed.

(* [comment removed for export] *)
Definition qs_of (h : ahst) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "(9.$:.(;.$<.$<.)Lk,$:.(=.$<.$<.(>.R1.)(?.R1.))(10.$:.Lk,$:.(11.(12.(13.R1.))(14.(15.R1.)$16.))(17.O1.)))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition rp_of (h : ahst) : list (Z * Z) := map (fun sh => (s_map_beg sh, 32)) (s_chunks (h_sec h)).

#[using="Type"] Lemma qs_of_In : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pk,$:.P,(19.$:.R1.(17.R2.))P,(4.$1:.(13.R2.)$1;.)P,(4.$<.(15.R3.)$16.)(19.(;.$<.$<.)(=.$<.$<.(>.R4.)(?.R4.))(1<.R5.))")
(* [comment removed for export] *).
Proof.
  intros h k Hk P S. unfold qs_of. apply (in_map (fun k0 => (ck_map_beg k0, ck_map_size k0))). apply (proj2 (filter_In _ _ _)). split; [exact Hk|]. rewrite P, S. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint msr_l (bs : list batch) : nat := match bs with [] => 0 | b :: r => S (length (b_elems b) + msr_l r) end.
Definition msr (h : ahst) : nat := msr_l (q_batches (h_tq h)).

(* [comment removed for export] *)
#[using="Type"] Lemma blocks_of_chunks : forall h h', h_chunks h' = h_chunks h -> blocks h' = blocks h.
Proof. intros h h' E. unfold blocks, live. rewrite E. reflexivity. Qed.
#[using="Type"] Lemma blocks_rm_quar : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Ph',$18.Pk,$:.P,(4.(1=.$:.)(17.R2.)(1>.(1?.R1.)(17.R3.)))P,(19.$:.R2.(17.R4.))P,(4.$<.(15.R3.)$16.)P,(20.$<.(9.$:.$<.$1?.(17.R6.)))(4.(1=.(;.$<.$<.))(21.R6.)(21.R7.))")
(* [comment removed for export] *).
Proof.
  intros h h' k E Hk S ND. rewrite <- (blocks_rec_prim h k Hk S ND). unfold blocks, live. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma RIq_head_cells : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.PC,$<.Pm,P,(0.&40.)(5.(0.&8.))Pb0,$22.Ptb,(1=.$22.)P,(23.VhAR,R5.R4.(8.(;.$24.$25.))R3.)P,(4.(1=.$22.)(26.(27.R6.))(28.$22.R3.R2.))Ztbs,(1=.$24.)(9.$22.$24.$29.R3.)(2:.$<.Lnx,$<.(2;.(2<.$7.R7.R8.(2=.(2>.(2?.(30.$22.R5.)))(31.R6.)(32.=(28.$24.(29.R6.)R2.))(33.(34.R6.)(35.R2.))))(2;.(2<.$7.R7.(31.R6.)(36.R1.(34.R6.)(2>.(30.$<.(37.R6.)))))(2;.(38.$7.R7.(33.(31.R6.)+18.)(9.$<.(0.&40.)(39.&40.)(37.R6.)))(2;.(4.$<.R1.(3:.R2.))(3;.VhAR,(3<.$24.(9.$22.$24.$29.(26.(3=.R9.)))(28.$24.(29.R6.)R2.))))))))")
(* [comment removed for export] *).
Proof.
  intros h C m b0 tb R HB tbs. unfold RIq in R. cbn zeta in R. rewrite HB in R. cbn [map] in R.
  ddestruct R as (QT & QG & BLG & MTX & QC & BLT & BWF).
  destruct BLT as [N BLT']. ddestruct N as (N1 & N2 & N3). cbn [bn_of bn_addr bn_size bn_elems bn_count] in N1, N2, N3, QC.
  exists (hd_addrT tbs 0). cbn [length bsum hd_addr hd_addrT bn_of bn_addr bn_size] in QC. rewrite length_map in QC.
  split; [exact QC|]. split; [| split; [exact N2| split; [reflexivity| exact BWF]]].
  unfold batch_hdr. unfold bn_count in N1. cbn [bn_elems bn_of] in N1. rewrite length_map in N1. exact N1.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Loop.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Variable FF : ffam AL.

  (* [comment removed for export] *)
  Variables (h0 : ahst) (m0 : mem) (LF : list (Z * Z)) (C SP0 lo STK : Z) (j0 : list byte) (q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra : word)
            (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).   (* [comment removed for export] *)
  Hypothesis TP : tp = Z_to_bv 64 A_TP.
  Let L := h_L h0.
  Let T := l_T L.
  Let SP := SP0 - 112.
  Let QS := qs_of h0.
  Let RP := rp_of h0 ++ [(C, 32)].   (* [comment removed for export] *)

  Hypothesis WF0 : WFR h0.
  Hypothesis GEO0 : hgeom h0.
  Hypothesis C0 : SP0 <= C.
  Hypothesis C1 : C + 32 <= l_stk_hi L.
  Hypothesis LOL : l_stk_lo L <= lo.
  Hypothesis SPL : lo <= SP0 - 112 - 736.
  Hypothesis SPA : SP0 mod 16 = 0.
  Hypothesis STKB : 0 <= STK < 2^64.

  (* [comment removed for export] *)
  Definition LST (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "(2;.(4.$<.(3>.O1.)(3>.Vh0,))(2;.(4.$3?.(40.O1.)(40.Vh0,))(2;.(4.$1:.(41.O1.)(41.Vh0,))(2;.(4.$<.(42.O1.)(42.Vh0,))(2;.(4.$1:.(43.O1.)(43.Vh0,))(2;.Pc,$<.(4.$<.(44.(45.O1.R1.))(44.(45.Vh0,R1.)))(2;.(46.(;.$<.$<.)(47.(48.Vh0,))(47.(48.O1.)))(2;.Pk,$:.P,(19.$:.R1.(17.Vh0,))P,(4.$1:.(13.R2.)$1;.)(49.(19.$:.R3.(17.O1.))(19.(;.$<.$<.)(=.$<.$<.(>.R3.)(?.R3.))(47.(48.O1.))))Pg,(;.$<.$<.)P,(19.(;.$<.$<.)R1.(47.(48.O1.)))(49.(19.(;.$<.$<.)R2.(47.(48.Vh0,)))(2:.$:.Lk,$:.(2;.(19.$:.R1.(17.Vh0,))(2;.(4.$1:.(13.R1.)$1;.)(4.(;.$<.$<.)R3.(=.$<.$<.(>.R1.)(?.R1.)))))))))))))))")
(* [comment removed for export] *).
  #[using="Type"] Lemma LST0 : LST h0.
  Proof. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros c; reflexivity|]. split; [apply incl_refl|]. split; [intros k Hk _; left; exact Hk|]. intros g Hg. left. exact Hg. Qed.

  Definition LINV (h : ahst) (m : mem) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "(2;.(4:.VhAR,O3.)(2;.(4;.(3>.O3.)$4<.)(2;.(4.$1:.(43.O3.)$4=.)(2;.(4>.VhAR,O3.VLF,O2.)(2;.(4?.VhAR,VAL,VFF,O3.O1.)(2;.(50.O2.O1.)(2;.(51.$7.O2.)(2;.Pk,$:.P,(19.$:.R1.(17.O3.))(19.$:.R2.(17.Vh0,))(2;.Psh,$52.P,(19.$52.R1.(53.(54.O3.)))(19.$52.R2.(53.(54.Vh0,)))(2;.Px,$<.P,(55.VhAR,VAL,VFF,Vh0,R1.)P,(1.(2.VQS,R2.))(55.VhAR,VAL,VFF,O3.R3.)(2;.(56.VL,(21.Vh0,)VQS,VRP,(57.(58.Vh0,))(59.(58.Vh0,))Vlo,VSP0,Vm0,O2.)(2;.(5:.VQS,Vm0,O2.)(2;.(4.$5;.(5<.O3.)(5<.Vh0,))(2;.(4.$5=.(3=.O3.)(3=.Vh0,))(2;.(4.$5>.(58.O3.)(58.Vh0,))(2;.(4.(1=.(;.$<.$<.))(21.O3.)(21.Vh0,))(2;.(5?.O3.)(2;.Pk,$:.P,(19.$:.R1.(17.O3.))(60.(61.(62.R2.))(63.+2.+20.))(2;.(64.$7.O2.Vlo,VSP,)(65.O2.VSP0,VT,VSTK,Vj0,Vq9,Vq8,Vq7,Vq6,Vq5,Vq4,Vq3,Vq2,Vq1,Vq0,Vqra,))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="WF0"] Lemma L_facts : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "(2;.(4;.+10007???9000.(66.VL,))(2;.(2;.(2;.(2;.(4;.+1000.(67.VL,))(49.(4;.(33.(67.VL,)+1000.)+10000.)(4;.+65?000.(67.VL,))))(49.(4;.(33.(67.VL,)+1000.)+7???7000.)(4;.+10007???8000.(67.VL,))))(4;.(33.(67.VL,)+1000.)(68.VhAR,)))(2;.(4;.(68.VhAR,)(69.VL,))(4;.(6:.VL,)(63.+2.+2?.)))))")
(* [comment removed for export] *).
  Proof.
    dpose WF0 as ((WL & _) & _). destruct (L_GSB L WL) as (SB0 & _). ddestruct (L_GT L WL) as (T0 & T1 & _).
    dpose WL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STK0 & STKH & _).
    exact (conj SB0 (conj (conj T0 T1) (conj STK0 STKH))).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fkeepR_step : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Pm,P,(0.&40.)(5.(0.&8.))Pm',P,(0.&40.)(5.(0.&8.))PNB,(1=.$<.)PBL,(1=.$<.)PQS',(1=.(;.$<.$<.))PRP',(1=.(;.$<.$<.))P,(56.VL,(21.Vh0,)VQS,VRP,(57.(58.Vh0,))(59.(58.Vh0,))Vlo,VSP0,Vm0,R6.)P,(56.VL,(21.Vh0,)R3.R2.R5.R4.Vlo,VSP,R7.R6.)P,(46.(;.$<.$<.)R4.VQS,)P,(46.(;.$<.$<.)R4.VRP,)P,(4.(1=.$<.)R8.(57.(58.Vh0,)))P,(4.(1=.$<.)R8.(59.(58.Vh0,)))(56.VL,(21.Vh0,)VQS,VRP,(57.(58.Vh0,))(59.(58.Vh0,))Vlo,VSP0,Vm0,R;.)")
(* [comment removed for export] *).
  Proof.
    intros m m' NB BL QS' RP' K1 K2 IQ IR -> ->. eapply fkeepR_trans; [exact K1| | apply incl_refl| apply incl_refl].
    intros x. cbv zeta. intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. apply (fkeepR_mono _ _ _ _ _ _ _ _ _ _ _ _ K2 IQ IR x); try assumption.
    subst SP. clear -H1. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="hAR WF0 GEO0 C0 C1 LOL SPL"] Lemma stack_kept : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Pm,P,(0.&40.)(5.(0.&8.))Pm',P,(0.&40.)(5.(0.&8.))PNB,(1=.$<.)PBL,(1=.$<.)PQS',(1=.(;.$<.$<.))PRP',(1=.(;.$<.$<.))PA,$<.Pn,$<.P,(56.VL,(21.Vh0,)R4.R3.R6.R5.Vlo,VSP,R8.R7.)P,(46.(;.$<.$<.)R5.VQS,)P,(46.(;.$<.$<.)R5.VRP,)P,(4.(1=.$<.)R9.(57.(58.Vh0,)))P,(4.(1=.$<.)R9.(59.(58.Vh0,)))P,(4;.VSP,R7.)P,(4;.(33.R8.R7.)VSP0,)(6;.R?.R>.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    intros m m' NB BL QS' RP' A n K IQ IR -> -> HA HB0 x Hx. dpose L_facts as (SB0 & (T0 & T1) & STK0 & STKH). assert (HB : A + n <= l_stk_hi L) by (clear -HB0 C0 C1; lia).
    dpose WF0 as ((WL & _) & _). dpose WL as (_ & _ & _ & _ & _ & B6d & _).
    pose proof (z_T_stk h0 GEO0) as Y1. pose proof (z_hull_stk h0 GEO0) as Y2. pose proof (z_pa_stk h0 GEO0) as Y3.
    unfold zapart in Y1, Y2, Y3. cbn [fst snd] in Y1, Y2, Y3. fold L in Y1, Y2, Y3.
    apply (K x); cbv zeta.
    - subst SP. clear - Hx HA. lia.
    - clear - Hx HA HB Y1 LOL SPL; subst SP L; lia.
    - intros [IH _]. unfold in_hull in IH. clear - Hx HA HB Y2 LOL SPL IH; subst SP L; lia.
    - intros [SH _]. unfold shad in SH. clear - Hx HA HB SH LOL SPL STK0 B6d; subst SP L; pose proof aceil_bounds; lia.
    - (intros dd_H; ddestruct dd_H as (q & Hq & R)). apply IQ in Hq. unfold QS, qs_of in Hq. apply in_map_iff in Hq. ddestruct Hq as (kq & <- & Hkq). apply filter_In in Hkq as [Hkq Pq].
      apply andb_prop in Pq as [Pq _]. apply Bool.negb_true_iff in Pq. cbn [fst snd] in R.
      dpose WF0 as (_ & _ & _ & (WKF & _ & _) & _). pose proof (proj1 (Forall_forall _ _) WKF kq Hkq) as (_ & _ & _ & Xq). rewrite Pq in Xq.
      ddestruct Xq as (iq & Nq & _ & _ & CEILq & _). pose proof (z_sec_stk h0 GEO0 iq _ Nq) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. fold L in Y.
      unfold shad in R. clear - Hx HA HB R Y LOL SPL STK0 CEILq; subst SP L; pose proof aceil_bounds; lia.
    - unfold free_img_ranges, A_INSTANCE, A_IA, A_IA_INIT. cbn. clear - Hx HA LOL SPL STK0; subst SP L; pose proof aceil_bounds; lia.
    - (intros dd_H; ddestruct dd_H as (b & Hb & R)). destruct (In_nth_error _ _ Hb) as [jb Hjb]. pose proof (z_node_stk h0 GEO0 jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y. fold L in Y.
      clear - Hx HA HB R Y LOL SPL; subst SP L; lia.
    - (intros dd_H; ddestruct dd_H as (b & Hb & R)). destruct (In_nth_error _ _ Hb) as [jb Hjb]. pose proof (z_store_stk h0 GEO0 jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y. fold L in Y.
      clear - Hx HA HB R Y LOL SPL; subst SP L; lia.
    - clear - Hx HA HB Y3 LOL SPL; subst SP L; lia.
    - (intros dd_H; ddestruct dd_H as (r & Hr & R)). apply IR in Hr. unfold RP, rp_of in Hr. apply in_app_iff in Hr. destruct Hr as [Hr|Hr]; [| destruct Hr as [<-|[]]; cbn [fst snd] in R; clear - R Hx HB0 C0; lia].
      apply in_map_iff in Hr. ddestruct Hr as (sh & <- & Hsh). cbn [fst snd] in R.
      destruct (In_nth_error _ _ Hsh) as [ish Nsh]. pose proof (z_sec_stk h0 GEO0 ish _ Nsh) as Y. unfold zapart in Y. cbn [fst snd] in Y. fold L in Y.
      dpose WF0 as (_ & _ & _ & _ & _ & WS & _). dpose WS as (_ & _ & _ & _ & _ & _ & _ & WS8). pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & M4 & _).
      clear - Hx HA HB R Y LOL SPL M4; subst SP L; lia.
  Qed.

  #[using="Type"] Lemma dr_frame_kept : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Pm,P,(0.&40.)(5.(0.&8.))Pm',P,(0.&40.)(5.(0.&8.))P,(65.R2.VSP0,VT,VSTK,Vj0,Vq9,Vq8,Vq7,Vq6,Vq5,Vq4,Vq3,Vq2,Vq1,Vq0,Vqra,)P,(6;.R3.R2.VSP,+70.)(65.R3.VSP0,VT,VSTK,Vj0,Vq9,Vq8,Vq7,Vq6,Vq5,Vq4,Vq3,Vq2,Vq1,Vq0,Vqra,)")
(* [comment removed for export] *).
  Proof. intros m m' FR K. unfold dr_frame in *. eapply krw; [exact FR| subst SP; cbn [cells_size csize Nat.add]; replace (SP0 + -112) with (SP0 - 112) by lia; exact K]. Qed.

  (* [comment removed for export] *)
  #[using="WF0 GEO0 C0 C1 LOL SPL"] Lemma LINV_prim : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pm,P,(0.&40.)(5.(0.&8.))Pmo,$6<.Pk,$:.Pdr,$1:.Pdn,$25.Pf,(5.$1:.)Pm',P,(0.&40.)(5.(0.&8.))Pmo',$6<.P,(6=.R9.R8.R7.)P,(19.$:.R7.(17.R:.))P,(4.$<.(15.R8.)$16.)P,(4.$1:.(13.R9.)$4=.)P,(4:.VhAR,(6>.R=.R:.R9.R8.R7.))P,(4>.VhAR,(6>.R>.R;.R:.R9.R8.)VLF,R7.)P,(4?.VhAR,VAL,VFF,(6>.R?.R<.R;.R:.R9.)R7.)P,(50.R9.R8.)P,Px,$<.P,(55.VhAR,VAL,VFF,R12.R1.)(55.VhAR,VAL,VFF,(6>.R13.R10.R?.R>.R=.)R2.)P,(6?.(5<.R12.)(21.R12.)VQS,(57.(58.R12.))(59.(58.R12.))Vlo,VSP,R11.R;.)P,(70.$7.R12.R<.)P,(51.$7.R=.)P,(64.$7.R>.Vlo,VSP,)(6=.(6>.R16.R13.R12.R11.R10.)R?.R>.)")
(* [comment removed for export] *).
  Proof.
    (intros h m mo k dr dn f m' mo' dd_H; ddestruct dd_H as (WF & HV & CI & HMQ & HK & HJ & MI & SUBK & SUBS & CSR & FK & WMX & EL & EG & ED & EB & LS & H32 & ST & FR); intros Hk SQ PK WF' HMQ' HK' HJ' CSM FK' WM MI' ST').
    dpose WF as (_ & _ & _ & (_ & NDK & _) & _).
    assert (FK2 : fkeepR L (blocks h0) QS RP (d_nb (h_dep h0)) (d_bl (h_dep h0)) lo SP m m').
    { unfold L. rewrite <- EL, <- EB, <- ED. apply fkeep_fkeepR. exact FK'. }
    assert (LS' : LST (h_recp h k dr dn f)).
    { ddestruct LS as (V1 & V2 & V3 & V4 & V5 & VR & V6 & V7 & V8). unfold LST.
      rewrite (recp_havol h k dr dn f), (recp_fake h k dr dn f), (recp_ia h k dr dn f), (recp_pa h k dr dn f), (recp_cinit h k dr dn f), (recp_acct h k dr dn f), (recp_chunks h k dr dn f).
      split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|].
      split. { intros c0. rewrite (recp_reg h k dr dn f c0). destruct ((c0 =? ck_cls k) && dr) eqn:EC0; [| exact (VR c0)].
               apply andb_prop in EC0 as [EC0 _]. apply Z.eqb_eq in EC0. subst c0. cbn [r_mapped_user]. exact (VR (ck_cls k)). }
      split; [exact V6|]. split; [| exact V8].
      intros k0 Hk0 P0. destruct (V7 k0 Hk0 P0) as [I|G]; [left| right; exact G]. apply rm_ab_In. split; [exact I|].
      intros EA. rewrite (NoDup_map_inj ck_ab _ _ _ NDK I Hk EA) in P0. rewrite PK in P0. discriminate P0. }
    unfold LINV. rewrite (recp_L h k dr dn f), (recp_havol h k dr dn f), (recp_cinit h k dr dn f), (recp_chunks h k dr dn f), (recp_sec h k dr dn f), (recp_gq h k dr dn f), (recp_dep h k dr dn f).
    split; [exact WF'|]. split; [exact HV|]. split; [exact CI|]. split; [exact HMQ'|]. split; [exact HK'|]. split; [exact HJ'|]. split; [exact MI'|].
    split; [intros k' Hk'; apply rm_ab_In in Hk' as [Hk' _]; exact (SUBK k' Hk')|]. split; [exact SUBS|].
    split; [intros x Hx NQ; apply CSM; exact (CSR x Hx NQ)|].
    split; [exact (fkeepR_step m m' _ _ QS RP FK FK2 (incl_refl _) (incl_refl _) eq_refl eq_refl)|].
    split; [exact (wmono_ex_trans QS m0 m m' WMX (wmono_ex_of_wmono QS m m' WM))|].
    split; [exact EL|]. split; [exact EG|]. split; [exact ED|].
    split; [rewrite <- EB; apply (blocks_rm_quar h _ k (recp_chunks h k dr dn f) Hk SQ NDK)|]. split; [exact LS'|].
    split; [intros k' Hk'; apply rm_ab_In in Hk' as [Hk' _]; exact (H32 k' Hk')|].
    split; [exact ST'|]. apply (dr_frame_kept m m' FR). apply (stack_kept m m' _ _ QS RP SP 112 FK2 (incl_refl _) (incl_refl _) eq_refl eq_refl); [clear; lia| subst SP; clear; lia].
  Qed.

  #[using="WF0 GEO0 C0 C1 LOL SPL"] Lemma LINV_sec : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pm,P,(0.&40.)(5.(0.&8.))Pmo,$6<.Pk,$:.Psi,$25.Pm',P,(0.&40.)(5.(0.&8.))Pmo',$6<.P,(6=.R7.R6.R5.)P,(19.$:.R5.(17.R8.))P,(4.$<.(15.R6.)$16.)P,(4.$1:.(13.R7.)$1;.)P,(4.(5.$52.)(71.$52.(53.(54.R;.))R7.)(72.$52.(73.(>.R8.)(?.R8.)(74.(62.R8.)))))P,(4:.VhAR,(75.R<.R9.R8.))P,(4>.VhAR,(75.R=.R:.R9.)VLF,R8.)P,(4?.VhAR,VAL,VFF,(75.R>.R;.R:.)R8.)P,(50.R:.R9.)P,Px,$<.P,(55.VhAR,VAL,VFF,R11.R1.)P,(1.(2;.(4;.(>.R?.)R2.)(60.R2.(33.(>.R?.)(?.R?.)))))(55.VhAR,VAL,VFF,(75.R13.R10.R?.)R3.)P,(56.(5<.R11.)(21.R11.)VQS,(76.R11.)(57.(58.R11.))(59.(58.R11.))Vlo,VSP,R10.R<.)P,(77.(>.R?.)(?.R?.)R11.R=.)P,(51.$7.R>.)P,(64.$7.R?.Vlo,VSP,)(6=.(75.R15.R12.R11.)R10.R?.)")
(* [comment removed for export] *).
  Proof.
    (intros h m mo k si m' mo' dd_H; ddestruct dd_H as (WF & HV & CI & HMQ & HK & HJ & MI & SUBK & SUBS & CSR & FK & WMX & EL & EG & ED & EB & LS & H32 & ST & FR); intros Hk SQ P NTHS WF' HMQ' HK' HJ' CSM FK' WMO MI' ST').
    dpose WF as (_ & _ & _ & (_ & NDK & _) & _).
    assert (INQ : In (ck_map_beg k, ck_map_size k) QS) by (apply qs_of_In; [exact (SUBK k Hk)| exact P| exact SQ]).
    assert (IRP : incl (rp_of h) RP).
    { intros r Hr. unfold rp_of in Hr. apply in_map_iff in Hr. ddestruct Hr as (sh & <- & Hsh). unfold RP, rp_of. apply in_app_iff. left. apply (in_map (fun sh0 => (s_map_beg sh0, 32))). exact (SUBS sh Hsh). }
    assert (FK2 : fkeepR L (blocks h0) QS RP (d_nb (h_dep h0)) (d_bl (h_dep h0)) lo SP m m').
    { unfold L. rewrite <- EL, <- EB, <- ED. exact (fkeepR_mono _ _ _ _ _ _ _ _ _ _ _ _ FK' (incl_refl _) IRP). }
    assert (LS' : LST (h_recs h k si)).
    { ddestruct LS as (V1 & V2 & V3 & V4 & V5 & VR & V6 & V7 & V8). unfold LST.
      rewrite (recs_havol h k si), (recs_fake h k si), (recs_ia h k si), (recs_pa h k si), (recs_cinit h k si), (recs_acct h k si), (recs_chunks h k si).
      split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [intros c0; rewrite (recs_reg h k si c0); exact (VR c0)|]. split; [intros g Hg; right; exact (V6 g Hg)|].
      split; [| intros g [<-|Hg]; [right; exists k; split; [exact (SUBK k Hk)| split; [exact P| reflexivity]]| exact (V8 g Hg)]].
      intros k0 Hk0 P0. destruct (V7 k0 Hk0 P0) as [I|G]; [| right; right; exact G].
      destruct (Z.eq_dec (ck_ab k0) (ck_ab k)) as [EA|NA].
      - right. left. rewrite (NoDup_map_inj ck_ab _ _ _ NDK I Hk EA). reflexivity.
      - left. apply rm_ab_In. exact (conj I NA). }
    unfold LINV. rewrite (recs_L h k si), (recs_havol h k si), (recs_cinit h k si), (recs_chunks h k si), (recs_secl h k si), (recs_gq h k si), (recs_dep h k si).
    split; [exact WF'|]. split; [exact HV|]. split; [exact CI|]. split; [exact HMQ'|]. split; [exact HK'|]. split; [exact HJ'|]. split; [exact MI'|].
    split; [intros k' Hk'; apply rm_ab_In in Hk' as [Hk' _]; exact (SUBK k' Hk')|].
    split. { intros sh Hsh. apply SUBS. apply (Permutation_in sh (swap_remove_perm (s_chunks (h_sec h)) si _ NTHS)). right. exact Hsh. }
    split; [intros x Hx NQ; apply CSM; [exact (CSR x Hx NQ)| intros R; apply NQ; exists (ck_map_beg k, ck_map_size k); split; [exact INQ| exact R]]|].
    split; [exact (fkeepR_step m m' _ _ QS RP FK FK2 (incl_refl _) (incl_refl _) eq_refl eq_refl)|].
    split; [exact (wmono_ex_trans QS m0 m m' WMX (wmono_ex_of_out QS _ _ m m' WMO INQ))|].
    split; [exact EL|]. split; [exact EG|]. split; [exact ED|].
    split; [rewrite <- EB; apply (blocks_rm_quar h _ k (recs_chunks h k si) Hk SQ NDK)|]. split; [exact LS'|].
    split; [intros k' Hk'; apply rm_ab_In in Hk' as [Hk' _]; exact (H32 k' Hk')|].
    split; [exact ST'|]. apply (dr_frame_kept m m' FR). apply (stack_kept m m' _ _ QS RP SP 112 FK2 (incl_refl _) (incl_refl _) eq_refl eq_refl); [clear; lia| subst SP; clear; lia].
  Qed.

  #[using="WF0 GEO0 C0 C1 LOL SPL"] Lemma LINV_batch : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pm,P,(0.&40.)(5.(0.&8.))Pmo,$6<.Pdr,$1:.Pdn,$25.Pf,(5.$1:.)Pb0,$22.Ptb,(1=.$22.)Pm',P,(0.&40.)(5.(0.&8.))Pmo',$6<.P,(6=.R:.R9.R8.)P,(4.(1=.$22.)(26.(27.R;.))(28.$22.R5.R4.))P,(4:.VhAR,(78.R<.R9.R8.R7.))P,(4>.VhAR,(78.R=.R:.R9.R8.)VLF,R5.)P,(4?.VhAR,VAL,VFF,(78.R>.R;.R:.R9.)R5.)P,(50.R7.R6.)P,Px,$<.P,(55.VhAR,VAL,VFF,R11.R1.)(55.VhAR,VAL,VFF,(78.R12.R?.R>.R=.)R2.)P,(6?.(5<.R11.)(21.R11.)VQS,(57.(58.R11.))(59.(58.R11.))Vlo,VSP,R10.R9.)P,(70.$7.R11.R:.)P,(51.$7.R;.)P,(64.$7.R<.Vlo,VSP,)(6=.(78.R15.R12.R11.R10.)R=.R<.)")
(* [comment removed for export] *).
  Proof.
    (intros h m mo dr dn f b0 tb m' mo' dd_H; ddestruct dd_H as (WF & HV & CI & HMQ & HK & HJ & MI & SUBK & SUBS & CSR & FK & WMX & EL & EG & ED & EB & LS & H32 & ST & FR); intros HB WF' HMQ' HK' HJ' CSM FK' WM MI' ST').
    assert (FK2 : fkeepR L (blocks h0) QS RP (d_nb (h_dep h0)) (d_bl (h_dep h0)) lo SP m m').
    { unfold L. rewrite <- EL, <- EB, <- ED. apply fkeep_fkeepR. exact FK'. }
    unfold LINV. rewrite (recb_L h dr dn f), (recb_havol h dr dn f), (recb_cinit h dr dn f), (recb_chunks h dr dn f), (recb_sec h dr dn f), (recb_gq h dr dn f), (recb_dep h dr dn f).
    split; [exact WF'|]. split; [exact HV|]. split; [exact CI|]. split; [exact HMQ'|]. split; [exact HK'|]. split; [exact HJ'|]. split; [exact MI'|].
    split; [exact SUBK|]. split; [exact SUBS|].
    split; [intros x Hx NQ; apply CSM; exact (CSR x Hx NQ)|].
    split; [exact (fkeepR_step m m' _ _ QS RP FK FK2 (incl_refl _) (incl_refl _) eq_refl eq_refl)|].
    split; [exact (wmono_ex_trans QS m0 m m' WMX (wmono_ex_of_wmono QS m m' WM))|].
    split; [exact EL|]. split; [exact EG|]. split; [exact ED|].
    split; [rewrite <- EB; apply (blocks_of_chunks h); apply recb_chunks|].
    split. { ddestruct LS as (V1 & V2 & V3 & V4 & V5 & VR & V678). unfold LST. rewrite (recb_havol h dr dn f), (recb_fake h dr dn f), (recb_ia h dr dn f), (recb_pa h dr dn f), (recb_cinit h dr dn f), (recb_acct h dr dn f), (recb_chunks h dr dn f).
             split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [| exact V678].
             intros c0. rewrite (recb_reg h dr dn f b0 tb HB c0). destruct ((c0 =? kBatchClass) && dr) eqn:EC0; [| exact (VR c0)].
             apply andb_prop in EC0 as [EC0 _]. apply Z.eqb_eq in EC0. subst c0. cbn [r_mapped_user]. exact (VR kBatchClass). }
    split; [exact H32|].
    split; [exact ST'|]. apply (dr_frame_kept m m' FR). apply (stack_kept m m' _ _ QS RP SP 112 FK2 (incl_refl _) (incl_refl _) eq_refl eq_refl); [clear; lia| subst SP; clear; lia].
  Qed.

  (* [comment removed for export] *)
  Definition tail_cont (Q : config -> Prop) (bc : bnode) (tb : list batch) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pm,P,(0.&40.)(5.(0.&8.))Pmo,$6<.Pra',(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)P,(6=.R16.R15.R14.)P,(23.VhAR,R17.VC,(72.(;.$24.$25.)(=.$24.$25.O2.(30.(0.&40.)(79.O2.))))R16.)P,(4.(1=.$22.)(7:.$22.(26.(27.R18.)))O1.)(7;.$7.O3.(7<.(7=.(7>.VSP0,R16.Vgp,Vtp,R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.(39.&40.(7?.O2.))(39.&40.(80.O2.))R:.R9.R8.Vs10,Vs11,R7.R6.R5.R4.VC,)VF,(39.&40.$81.)Vfc,(8.(0.&40.))R18.(82.$7.))R17.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="Type"] Lemma cur_elem : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pm,P,(0.&40.)(5.(0.&8.))Pbc,$24.Pi,$25.Pe,(0.&40.)P,(4:.VhAR,R5.)P,(23.VhAR,R6.VC,(72.(;.$24.$25.)(=.$24.$25.R4.R3.))R5.)P,(4.(5.(0.&40.))(71.(0.&40.)(79.R5.)R4.)(72.(0.&40.)R3.))(2:.$:.Lk,$:.(2;.(19.$:.R1.(17.R9.))(2;.(4.$<.(15.R1.)$16.)(2;.(4.(0.&40.)R5.(39.&40.(83.R1.)))(2:.$22.Lb0,$22.(2:.(1=.$22.)Ltb,(1=.$22.)(2;.(4.(1=.$22.)(26.(27.R;.))(28.$22.R2.R1.))(4.$<.(31.R2.)(7?.R9.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros h m bc i e WF R NTH. pose proof R as R0. unfold RIq in R0. cbn zeta in R0.
    ddestruct R0 as (_ & _ & _ & _ & _ & _ & (_ & _ & b0 & all & E0 & EA & EE & EL & IL & _)).
    rewrite EE, nth_error_map in NTH. destruct (nth_error all i) as [a|] eqn:NA; [| discriminate NTH]. cbn in NTH. injection NTH as <-.
    dpose WF as (_ & _ & _ & _ & WQ & _). destruct WQ as (WT & _). rewrite E0 in WT. destruct WT as [(_ & B2 & _) _].
    rewrite EL, (skipn_cons_nth all i a NA) in B2. inversion B2 as [|? ? (k & Hk & Sk & Hd) _]; subst.
    exists k. split; [exact Hk|]. split; [exact Sk|]. split; [first [reflexivity | rewrite Hd; reflexivity | rewrite <- Hd; reflexivity]|]. dexists b0, (tl (q_batches (h_tq h))). split; [exact E0| exact EA].
  Qed.

  (* [comment removed for export] *)
  #[using="SP0 T SP"] Lemma cur_block : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pm,P,(0.&40.)(5.(0.&8.))Pbc,$24.Pi,$25.P,(4:.VhAR,R4.)P,(4.$5;.(5<.R5.)(5<.Vh0,))P,(23.VhAR,R6.VC,(72.(;.$24.$25.)(=.$24.$25.R4.R3.))R5.)(2;.(4;.+65?000.(7?.R5.))(2;.(4;.(33.(7?.R5.)+2000.)(68.VhAR,))(2;.(4;.(80.R5.)+3?=.)(2;.(2:.$<.Lnx,$<.(84.R7.R6.R1.))(2:.$<.Lib,$<.(2;.(2;.(4;.=R1.)(60.R1.(85.R8.$86.)))(4.$<.(7?.R6.)(87.VL,$86.R1.))))))))")
(* [comment removed for export] *).
  Proof.
    intros h m bc i WF EL R. pose proof R as R0. unfold RIq in R0. cbn zeta in R0.
    ddestruct R0 as (_ & _ & _ & _ & _ & _ & (N & BWF & b0 & all & E0 & EA & EE & ELm & IL & _)).
    pose proof BWF as [BOK _]. apply Forall_app in BOK as [_ B]. inversion B as [|? ? OK _]; subst. unfold bn_ok in OK.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact N|].
    ddestruct (batch_slot h b0 WF ltac:(rewrite E0; apply in_app_iff; left; left; reflexivity)) as (ib & Hib & EB). exists ib. rewrite <- EA. unfold L. rewrite <- EL. exact (conj Hib EB).
  Qed.

  #[using="IMG ALWF ASB TP WF0 GEO0 C0 C1 LOL SPL SPA"] Lemma dr_inner : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Pn,$25.PQ,P,$88.SpPbc,$24.Ptb,(1=.$22.)Ph,$18.Pm,P,(0.&40.)(5.(0.&8.))Pmo,$6<.Pi,$<.Pe,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)P,(89.(8:.(8;.(80.R14.)R?.))R16.)P,(6=.R13.R12.R11.)P,(23.VhAR,R14.VC,(72.(;.$24.$25.)(=.$24.$25.R16.(8:.R11.)))R13.)P,(2;.(4;.=R12.)(60.R12.(80.R17.)))P,(4.(5.(0.&40.))(71.(0.&40.)(79.R18.)(8:.R13.))(72.(0.&40.)R12.))P,(4.(1=.$22.)(7:.$22.(26.(27.R17.)))R18.)P,(8<.R1;.R1:.R19.)(7;.$7.R1<.(7<.(7=.(7>.VSP0,(39.&40.$8=.)Vgp,Vtp,R14.R13.R12.(39.&40.(33.VSP0,-68.))R15.R11.R10.R?.R>.R=.R<.(39.&40.(7?.R1;.))(39.&40.(80.R1;.))(39.&40.(33.(33.(7?.R1;.)+98.)(8>.+8.R16.)))(39.&40.(33.(80.R1;.)+10.))(39.&40.(33.+10.R16.))Vs10,Vs11,R;.R:.R9.R8.VC,)VF,(39.&40.$8?.)Vfc,(8.(0.&40.))R18.(82.$7.))R17.))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros Q bc tb h m mo i e t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MS LI RQ IB NTH TLQ TC.
    { exfalso. clear - MS IB. lia. }
    dpose LI as (WF & HV & CI & HMQ & HK & HJ & MI & SUBK & SUBS & CSR & FK & WMX & EL & EG & ED & EB & LS & H32 & ST & FR).
    dpose L_facts as (SB0 & (T0 & T1) & STK0 & STKH).
    ddestruct (cur_elem h m bc (Z.to_nat i) e WF RQ NTH) as (k & Hk & SQ & -> & b0 & tb0 & HB & EA). assert (ETB : tb0 = tb) by (rewrite HB in TLQ; exact TLQ). subst tb0.
    assert (CBC : ro_cells asegs m (SP0 + -104) [C8 (Z_to_bv 64 (l_T (h_L h) + 208))]).
    { rewrite EL. unfold dr_frame in FR. change ([CB 8 j0; C8 (w64 (T + 208)); C8 (w64 STK); C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra])
        with ([CB 8 j0] ++ [C8 (w64 (T + 208))] ++ [C8 (w64 STK); C8 q9; C8 q8; C8 q7; C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra]) in FR.
      apply rw_cells_app in FR as [_ FR]. apply rw_cells_app in FR as [FR _]. cbn [cells_size csize Nat.add] in FR.
      replace (SP0 + -112 + Z.of_nat 8) with (SP0 + -104) in FR by (clear; lia). exact (proj1 FR). }
    unfold dr_regs. replace (SP0 + -112) with SP by (unfold SP; clear; lia).
    assert (REP : ret_pc (Z_to_bv 64 A_DR_INNER) = Z_to_bv 64 A_DR_INNER) by (apply ret_pc_even; [unfold A_DR_INNER; clear; lia| reflexivity]).
    destruct (ck_prim k) eqn:P.
    - (* [comment removed for export] *)
      eapply (rec_prim_step AL IMG ALWF ASB FF Q _ gp tp t0 t1 t2 _ _ a2 a3 a4 a5 a6 a7 _ _ _ _ _ _ _ _ s10 s11 t3 t4 t5 t6 h LF QS bc (Z.to_nat i) k SP (SP0 + -104) C lo F fc m mo
                WF HV CI Hk SQ P NTH HMQ RQ CBC); [unfold SP; clear; lia| unfold SP; clear -C0; lia| rewrite EL; exact C1| exact ST| rewrite EL; exact LOL| unfold SP; clear -SPL; lia
                | unfold SP; clear -SPA; rewrite Zminus_mod, SPA; reflexivity| exact MI| exact TP| exact HK| exact HJ|].
      intros c4 P4. ddestruct P4 as (ms4 & mo4 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m4 & dr & dn & f & -> & -> & WF' & HMQ' & RQ' & HK' & HJ' & CSM & FK' & WM & MI' & ST').
      pose proof (LINV_prim h m mo k dr dn f m4 mo4 LI Hk SQ P WF' HMQ' HK' HJ' CSM FK' WM MI' ST') as LI'.
      rewrite REP.
      (* [comment removed for export] *)
      destruct (cur_block _ m4 bc _ WF' ltac:(rewrite (recp_L h k dr dn f); exact EL) RQ') as (B0 & B1 & BC & (nx & BN) & ib & Hib & EBb).
      dpose BN as (BN1 & BN2 & BN3).
      eapply (evtA_aevtS_KJ AL (ff_CS AL FF (h_recp h k dr dn f)) (ff_K AL FF (h_recp h k dr dn f)) _ Q _ mo4 (ff_kinv AL FF _) HK'); [exact HJ'| |].
      { replace (Z_to_bv 64 SP) with (Z_to_bv 64 (SP0 + -112)) by (unfold SP; f_equal; clear; lia).
        eapply (dr_inner_next AL IMG ALWF (ff_CS AL FF (h_recp h k dr dn f)) (ff_csok AL FF _) _ gp tp x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 s10 s11 x3 x4 x5 x6 SP0 C (bn_addr bc) (bn_count bc) i (bn_elems bc) F fc m4);
          [exact B0| pose proof aceil_bounds; clear -B1 H; lia| exact IB| exact BC| unfold bn_count; rewrite Nat2Z.id; reflexivity| exact BN2| | exact MI'].
        rewrite EBb. pose proof LI' as (WFx & _). pose proof (WFK_of_WFR _ WFx ltac:(rewrite (recp_havol h k dr dn f); exact HV)) as W0'.
        eapply crange_sub; [apply (ff_cs_user AL FF (h_recp h k dr dn f) kBatchClass W0' ltac:(unfold kBatchClass; clear; lia))| |].
        + rewrite (recp_L h k dr dn f), EL. destruct (slot_le _ kBatchClass ib ltac:(dpose WF' as (_ & _ & WR' & _); exact WR') ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 _].
          rewrite (recp_L h k dr dn f), EL in S1. exact S1.
        + rewrite (recp_L h k dr dn f), EL. destruct (slot_le _ kBatchClass ib ltac:(dpose WF' as (_ & _ & WR' & _); exact WR') ltac:(unfold kBatchClass; clear; lia) Hib) as [_ S2].
          rewrite (recp_L h k dr dn f), EL in S2. change (class_size kBatchClass) with 8192 in S2.
          dpose WF' as (_ & _ & WR' & _). pose proof (WR' kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
          unfold L in *. clear - S2 AUMU'. lia. }
      cbn beta. intros ms5 mo5 P5 HK5 _ HJ5.
      destruct P5 as [(MORE & e' & NTH' & ->)|(DONE & ->)].
      + apply (IH Q bc tb (h_recp h k dr dn f) m4 mo5 (i + 1) e'); [clear - MS MORE IB; lia| | | clear -MORE IB; lia| exact NTH'| rewrite (recp_tq h k dr dn f b0 tb HB); reflexivity| exact TC].
        * dpose LI' as (X1 & X2 & X3 & X4 & _ & _ & X6). cbn [ms_mem] in HJ5. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj HK5 (conj HJ5 X6)))))).
        * replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by (clear -IB; lia). exact RQ'.
      + unfold tail_cont in TC. unfold dr_regs in TC |- *.
        eapply (TC (h_recp h k dr dn f) m4 mo5).
        * dpose LI' as (X1 & X2 & X3 & X4 & _ & _ & X6). cbn [ms_mem] in HJ5. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj HK5 (conj HJ5 X6)))))).
        * replace (length (bn_elems bc)) with (S (Z.to_nat i)) by (unfold bn_count in DONE; clear -DONE IB; lia). exact RQ'.
        * rewrite (recp_tq h k dr dn f b0 tb HB). reflexivity.
    - (* [comment removed for export] *)
      dpose WF as (_ & _ & _ & (WKF & _ & _) & _). pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (_ & _ & _ & KX). rewrite P in KX. ddestruct KX as (si & NTHS & _).
      eapply (rec_sec_step AL IMG ALWF ASB FF Q _ gp tp t0 t1 t2 _ _ a2 a3 a4 a5 a6 a7 _ _ _ _ _ _ _ _ s10 s11 t3 t4 t5 t6 h LF QS bc (Z.to_nat i) k si SP (SP0 + -104) C lo F fc m mo
                WF HV Hk SQ P NTHS NTH (H32 k Hk) ltac:(apply qs_of_In; [exact (SUBK k Hk)| exact P| exact SQ]) HMQ RQ);
        [unfold SP; clear; lia| unfold SP; clear -C0; lia| rewrite EL; exact C1| exact ST| rewrite EL; exact LOL| unfold SP; clear -SPL; lia
        | unfold SP; clear -SPA; rewrite Zminus_mod, SPA; reflexivity| exact MI| exact TP| exact HK| exact HJ|].
      intros c4 P4. ddestruct P4 as (ms4 & mo4 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m4 & -> & -> & WF' & HMQ' & RQ' & HK' & HJ' & CSM & FK' & WMO & MI' & ST').
      pose proof (LINV_sec h m mo k si m4 mo4 LI Hk SQ P NTHS WF' HMQ' HK' HJ' CSM FK' WMO MI' ST') as LI'.
      rewrite REP.
      destruct (cur_block _ m4 bc _ WF' ltac:(rewrite (recs_L h k si); exact EL) RQ') as (B0 & B1 & BC & (nx & BN) & ib & Hib & EBb).
      dpose BN as (BN1 & BN2 & BN3).
      eapply (evtA_aevtS_KJ AL (ff_CS AL FF (h_recs h k si)) (ff_K AL FF (h_recs h k si)) _ Q _ mo4 (ff_kinv AL FF _) HK'); [exact HJ'| |].
      { replace (Z_to_bv 64 SP) with (Z_to_bv 64 (SP0 + -112)) by (unfold SP; f_equal; clear; lia).
        eapply (dr_inner_next AL IMG ALWF (ff_CS AL FF (h_recs h k si)) (ff_csok AL FF _) _ gp tp x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 s10 s11 x3 x4 x5 x6 SP0 C (bn_addr bc) (bn_count bc) i (bn_elems bc) F fc m4);
          [exact B0| pose proof aceil_bounds; clear -B1 H; lia| exact IB| exact BC| unfold bn_count; rewrite Nat2Z.id; reflexivity| exact BN2| | exact MI'].
        rewrite EBb. pose proof LI' as (WFx & _). pose proof (WFK_of_WFR _ WFx ltac:(rewrite (recs_havol h k si); exact HV)) as W0'.
        eapply crange_sub; [apply (ff_cs_user AL FF (h_recs h k si) kBatchClass W0' ltac:(unfold kBatchClass; clear; lia))| |].
        + rewrite (recs_L h k si), EL. destruct (slot_le _ kBatchClass ib ltac:(dpose WF' as (_ & _ & WR' & _); exact WR') ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 _].
          rewrite (recs_L h k si), EL in S1. exact S1.
        + rewrite (recs_L h k si), EL. destruct (slot_le _ kBatchClass ib ltac:(dpose WF' as (_ & _ & WR' & _); exact WR') ltac:(unfold kBatchClass; clear; lia) Hib) as [_ S2].
          rewrite (recs_L h k si), EL in S2. change (class_size kBatchClass) with 8192 in S2.
          dpose WF' as (_ & _ & WR' & _). pose proof (WR' kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
          unfold L in *. clear - S2 AUMU'. lia. }
      cbn beta. intros ms5 mo5 P5 HK5 _ HJ5.
      destruct P5 as [(MORE & e' & NTH' & ->)|(DONE & ->)].
      + apply (IH Q bc tb (h_recs h k si) m4 mo5 (i + 1) e'); [clear - MS MORE IB; lia| | | clear -MORE IB; lia| exact NTH'| rewrite (recs_tq h k si b0 tb HB); reflexivity| exact TC].
        * dpose LI' as (X1 & X2 & X3 & X4 & _ & _ & X6). cbn [ms_mem] in HJ5. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj HK5 (conj HJ5 X6)))))).
        * replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by (clear -IB; lia). exact RQ'.
      + unfold tail_cont in TC. unfold dr_regs in TC |- *.
        eapply (TC (h_recs h k si) m4 mo5).
        * dpose LI' as (X1 & X2 & X3 & X4 & _ & _ & X6). cbn [ms_mem] in HJ5. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj HK5 (conj HJ5 X6)))))).
        * replace (length (bn_elems bc)) with (S (Z.to_nat i)) by (unfold bn_count in DONE; clear -DONE IB; lia). exact RQ'.
        * rewrite (recs_tq h k si b0 tb HB). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma elems_range : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pb0,$22.Ptb,(1=.$22.)P,(4:.VhAR,R3.)P,(4.(1=.$22.)(26.(27.R4.))(28.$22.R3.R2.))(90.$<.Le,$<.(2;.(4;.+65?000.R1.)(4;.(33.R1.+10.)(68.VhAR,)))(37.R4.))")
(* [comment removed for export] *).
  Proof.
    intros h b0 tb WF HB. dpose WF as ((WL & _) & _ & WR & WK & WQ & _). destruct WQ as (WT & _). rewrite HB in WT. destruct WT as [(_ & B2 & _) _].
    apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B2 e He) as (k & Hk & _ & <-).
    ddestruct (chunk_ext' h k WL WR WK Hk) as (_ & E1 & E2 & E3 & E4 & E5 & E6 & _). clear - E1 E2 E3 E4 E5 E6. lia.
  Qed.

  #[using="L WF0 GEO0 C0 C1 LOL SPL"] Lemma RIq_enter : forall h m m' b0 tb,
    WFR h -> h_L h = h_L h0 -> RIq h C None m -> q_batches (h_tq h) = b0 :: tb ->
    munch [(lo, SP0); (C, C + 32)] m m' -> wmono asegs m m' ->
    rw_cells asegs m' C (qc_cells (Z.of_nat (S (length tb)) - 1) (hd_addr (map bn_of tb))
                           (if hd_addr (map bn_of tb) =? 0 then 0 else last_addr 0 (bn_of b0 :: map bn_of tb)) (b_size b0 + bsum (map bn_of tb) - b_size b0)) ->
    RIq h C (Some (bn_of b0, 0%nat)) m'.
  Proof.
    intros h m m' b0 tb WF EL R HB MU WM QC'. dpose L_facts as (SB0 & (T0 & T1) & STK0 & STKH). unfold L in *.
    dpose WF as ((WLh & _) & _ & WRh & _). dpose WLh as (_ & _ & _ & _ & _ & B6d & _). rewrite EL in B6d.
    assert (KT : kept m m' (l_T (h_L h) + 80) 32).
    { rewrite EL. intros x Hx. apply MU. cbn [outside]. pose proof (z_T_stk h0 GEO0) as Y. unfold zapart in Y. cbn [fst snd] in Y. clear - Hx Y LOL SPL C0 C1. split; [lia| split; [lia| exact I]]. }
    assert (KI : iagree quar_img_ranges m m').
    { intros x Hx. apply MU. cbn [outside]. cbn in Hx. pose proof aceil_bounds. clear - Hx LOL SPL C0 C1 STK0 H. split; [lia| split; [lia| exact I]]. }
    assert (KH : forall A n, l_b6 L <= A -> A + n <= l_b6 L + 0x2000011000 -> kept m m' A n).
    { intros A n H1 H2 x Hx. unfold L in *. apply MU. cbn [outside]. pose proof (z_hull_stk h0 GEO0) as Y. unfold zapart in Y. cbn [fst snd] in Y. clear - Hx Y H1 H2 LOL SPL C0 C1. split; [lia| split; [lia| exact I]]. }
    assert (KB : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> kept m m' (b_addr b) 8192).
    { intros b Hb. unfold L in *. ddestruct (batch_slot h b WF Hb) as (ib & Hib & EBb).
      destruct (slot_le h kBatchClass ib WRh ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2]. rewrite <- EBb in S1, S2.
      dpose (user_vs_ri h kBatchClass WLh WRh ltac:(unfold kBatchClass; clear; lia)) as (Q1 & Q2 & Q3 & Q4).
      pose proof (WRh kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
      rewrite EL in S1, S2, Q1, Q2, Q4. change (class_size kBatchClass) with 8192 in S2. apply KH; clear - S1 S2 Q1 Q2 Q4 AUMU'; lia. }
    assert (KBn : forall b, In b (map bn_of (q_batches (h_tq h))) \/ In b (map bn_of (q_batches (h_gq h))) -> kept m m' (bn_addr b) 8192).
    { intros b Hb. assert (Hb' : In b (map bn_of (q_batches (h_tq h) ++ q_batches (h_gq h)))) by (rewrite map_app; apply in_app_iff; exact Hb).
      apply in_map_iff in Hb'. ddestruct Hb' as (b1 & <- & Hb1). cbn. apply KB. exact Hb1. }
    unfold RIq in R |- *. cbn zeta in R |- *. rewrite HB in R |- *. rewrite HB in KBn. cbn [map tl] in R, KBn |- *.
    ddestruct R as (QT & QG & BLG & MTX & QC & BLT & BWF). destruct BLT as [N BLT'].
    pose proof BWF as [BOK _]. apply Forall_app in BOK as [BOKg BOKt]. inversion BOKt as [|? ? OK0 OKt]; subst.
    unfold A_Q_GLOBAL, A_Q_CMUTEX, A_INSTANCE in *. unfold hm_qhead in *.
    split; [eapply krw; [exact QT| exact KT]|].
    split; [eapply krw; [exact QG| eapply iagree_kept; [exact KI| vm_compute; reflexivity]]|].
    split; [eapply blistT_k; [exact BLG| exact BOKg| intros b Hb; apply KBn; right; exact Hb]|].
    split; [eapply krw; [exact MTX| eapply iagree_kept; [exact KI| vm_compute; reflexivity]]|].
    split. { replace (Z.of_nat (length (map bn_of tb))) with (Z.of_nat (S (length tb)) - 1) by (rewrite length_map; clear; lia).
             replace (bsum (map bn_of tb)) with (b_size b0 + bsum (map bn_of tb) - b_size b0) by (clear; lia).
             replace (last_addr 0 (map bn_of tb)) with (if hd_addr (map bn_of tb) =? 0 then 0 else last_addr 0 (bn_of b0 :: map bn_of tb)); [exact QC'|].
             destruct (map bn_of tb) as [|b1 r] eqn:Etb; [reflexivity|]. cbn [hd_addr hd_addrT].
             inversion OKt as [|? ? OK1 _]; subst. unfold bn_ok in OK1. destruct (Z.eqb_spec (bn_addr b1) 0) as [E0|NE]; [exfalso; clear -E0 OK1; lia|].
             cbn [last_addr]. reflexivity. }
    split; [eapply blistT_k; [exact BLT'| exact OKt| intros b Hb; apply KBn; left; right; exact Hb]|].
    split. { exists (hd_addrT (map bn_of tb) 0). eapply bnode_at_k; [exact N| unfold bn_ok in OK0; clear -OK0; lia| apply KBn; left; left; reflexivity]. }
    split; [exact BWF|].
    dexists b0, (b_elems b0). split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|].
    exact (elems_range h b0 tb WF HB).
  Qed.
  (* [comment removed for export] *)
  #[using="WF0"] Lemma HMq_stack : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pm,P,(0.&40.)(5.(0.&8.))Pm',P,(0.&40.)(5.(0.&8.))PW,(1=.$91.)P,(4:.VhAR,R4.)P,(92.R5.)P,(4.$5;.(5<.R6.)(5<.Vh0,))P,(4>.VhAR,R7.VLF,R6.)P,(93.R5.R7.R6.)P,(70.$7.R8.R7.)P,PA,$<.Pn,$<.P,(49.(4;.(33.R2.R1.)(69.VL,))(4;.(6:.VL,)R2.))(94.R:.R3.R2.)(4>.VhAR,R;.VLF,R9.)")
(* [comment removed for export] *).
  Proof.
    (intros h m m' W WF GEO EL dd_H; ddestruct dd_H as (G0 & G1 & G2 & G3 & G4 & G5 & G7 & G8 & G9 & GE); intros MU WM DJS). dpose L_facts as (SB0 & (T0 & T1) & STK0 & STKH). unfold L in *.
    dpose WF as ((WL & WL24 & WLD) & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG). rewrite EL in WL.
    dpose WL as (_ & B6a & B6b & _ & B6c & B6d & B6e & _).
    assert (KOM : forall A n, (A + n <= l_stk_lo (h_L h0) \/ l_stk_hi (h_L h0) <= A) -> kept m m' A n) by (intros A n D; exact (kept_of_munch W m m' A n MU (DJS A n D))).
    assert (IAG : forall RS, ranges_within_b RS 0x10000 0x65f000 = true -> iagree RS m m').
    { intros RS HRS x Hx. apply (KOM (bv_unsigned x) 1); [| clear; lia]. pose proof (ranges_within_b_sound RS _ _ _ HRS Hx). pose proof aceil_bounds. clear - H H0 STK0. lia. }
    pose proof (z_T_stk h GEO) as ZT. pose proof (z_ctx_stk h GEO) as ZC. pose proof (z_fs_stk h GEO) as ZF. pose proof (z_pa_stk h GEO) as ZP. pose proof (z_hull_stk h GEO) as ZH. pose proof (z_stk_dtls h GEO) as ZD.
    unfold zapart in ZT, ZC, ZF, ZP, ZH, ZD. cbn [fst snd] in ZT, ZC, ZF, ZP, ZH, ZD. rewrite EL in ZT, ZC, ZF, ZP, ZH, ZD.
    ddestruct (L_GCTX (h_L h0) WL) as (_ & _ & CXL). rewrite CXL in ZC.
    assert (KH : forall A n, l_b6 (h_L h0) <= A -> A + n <= l_b6 (h_L h0) + 0x2000011000 -> kept m m' A n) by (intros A n H1 H2; apply KOM; clear - H1 H2 ZH; lia).
    split; [exact (hm_maps_frame _ _ _ G0 WM)|].
    split. { rewrite EL in G1 |- *. apply (hm_statics_frame m m' WM _ G1); [apply IAG; vm_compute; reflexivity| apply IAG; vm_compute; reflexivity| | | |]; apply KOM; rewrite ?CXL; pose proof WLD as (DL & _); unfold lowhigh, kHighMemBeg in DL; clear - ZT ZC ZD DL; try lia.
             all: lia. }
    split. { apply (hm_thread_frame m m' WM h G2); rewrite ?EL; [apply KOM; clear -ZT; lia| intros c Hc; apply KOM; clear -ZT Hc; lia| apply KOM; clear -ZT; lia| ddestruct G0 as (_ & _ & _ & WT & _); rewrite EL in WT; exact WT| clear -T0; lia]. }
    split. { apply (hm_depot_frame h m m' G3 WM); [apply IAG; vm_compute; reflexivity| |].
             - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb]. pose proof (z_node_stk h GEO jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL in Y. apply KOM. clear -Y; lia.
             - intros b Hb. destruct (In_nth_error _ _ Hb) as [jb Hjb]. pose proof (z_store_stk h GEO jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL in Y. apply KOM. clear -Y; lia. }
    split. { unfold hm_chunks in *. apply Forall_forall. intros k' Hk'.
             ddestruct (chunk_geom' h k' ltac:(rewrite EL; exact WL) WR WK Hk') as (RZ' & N0' & U8').
             apply (hm_chunk_frame m m' WM k' (proj1 (Forall_forall _ _) G4 k' Hk') RZ' N0' U8').
             ddestruct (chunk_ext' h k' ltac:(rewrite EL; exact WL) WR WK Hk') as (_ & F1 & F2 & F3 & F4 & F5 & F6 & FC).
             assert (XAB : ext_lo k' <= ck_ab k') by (unfold ext_lo, ck_map_beg; destruct (ck_prim k'); clear; lia).
             assert (UIN : ck_ab k' + ck_rz k' = ck_user k') by reflexivity.
             assert (NFX' : 0 <= nfix (ck_n k') /\ nfix (ck_n k') <= Z.max (ck_n k') 8) by (unfold nfix; clear -N0'; lia).
             assert (KX : forall A n', ext_lo k' <= A -> A + n' <= ext_hi k' -> kept m m' A n').
             { intros A n' HA HB'. apply KOM. destruct FC as [(P' & C' & RL' & RH' & _)|(P' & i' & N' & EL' & EH')].
               - dpose (user_vs_ri h (ck_cls k') ltac:(rewrite EL; exact WL) WR ltac:(clear -C'; lia)) as (Q1 & Q2 & _ & Q4). rewrite EL in Q1, Q2, Q4, RL', RH'.
                 pose proof (WR (ck_cls k') ltac:(unfold kNumClasses; clear -C'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
                 unfold region_beg, kRegionSize in Q1, Q2, RL', RH'. clear - HA HB' RL' RH' Q1 Q2 Q4 AUMU' ZH; lia.
               - pose proof (z_sec_stk h GEO i' _ N') as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. rewrite EL in Y. clear - HA HB' Y EL' EH'; lia. }
             unfold chunk_kept. split; [apply KX; [exact XAB| clear - UIN F4; lia]|]. split.
             - intros AK. apply KOM. unfold shad. pose proof (Z.div_mod (ck_user k') 8 ltac:(clear; lia)) as D1.
               pose proof (Z.div_mod (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D2. pose proof (Z.mod_pos_bound (nfix (ck_n k') + 7) 8 ltac:(clear; lia)) as D3.
               pose proof aceil_bounds as ACB. clear - D1 D2 D3 F3 F5 F6 XAB UIN NFX' STK0 STKH ACB. unfold kHighMemBeg in F5. lia.
             - intros NAK. apply KX; [clear - XAB UIN RZ'; lia| clear - F3; lia]. }
    split. { intros c' Hc'. pose proof (WR c' ltac:(unfold kNumClasses; clear -Hc'; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _ & _ & MULIM' & _ & _ & MFB' & NF4c & _).
             apply (hm_region_frame m m' WM (h_L h) c' (h_reg h c') _ (G5 c' Hc') AUMU' NF4c).
             dpose (user_vs_ri h c' ltac:(rewrite EL; exact WL) WR Hc') as (Q1 & Q2 & Q3 & Q4). rewrite EL in Q1, Q2, Q3, Q4 |- *.
             unfold fa_beg, kFreeArrayOffset, kFreeArraySize, region_beg, kRegionSize in Q1, Q2, Q3. unfold kUserLimit in MULIM'. unfold kFreeArraySize in MFB'.
             unfold region_kept. split; [| split; [| split]].
             + apply KOM. unfold ri_addr. unfold ri_base, space_end, kSpaceSize in *. clear - Hc' Q4 ZH SB0 B6a B6b; lia.
             + apply KOM. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset. clear - Hc' Q3 Q4 Q2 ZH MFB'; lia.
             + apply KOM. unfold shad, region_beg, kRegionSize. pose proof aceil_bounds as ACB. clear - STK0 ACB Q1 Q2 Q4 AUMU' B6d; lia.
             + intros k0 Hk0. apply KOM. destruct (slot_le h c' k0 WR Hc' ltac:(unfold carved; exact Hk0)) as [S1 S2]. rewrite EL in S1, S2. unfold region_beg, kRegionSize in S1, S2.
               unfold shad. pose proof aceil_bounds as ACB. pose proof (class_size_range c' Hc') as CSR'. clear - STK0 ACB S1 S2 CSR' Q1 Q2 Q4 AUMU' B6d; lia. }
    split. { apply (hm_sec_frame m m' WM h G7 WS); [apply IAG; vm_compute; reflexivity| |].
             - apply KOM. dpose WS as (_ & _ & _ & S4 & S5 & _). rewrite S5, EL. clear - ZP S4; lia.
             - intros sh Hsh. destruct (In_nth_error _ _ Hsh) as [i' N']. apply KOM. pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 WS))))))) sh Hsh) as (_ & SZ & _).
               pose proof (z_sec_stk h GEO i' _ N') as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL in Y. clear - Y SZ; lia. }
    split. { unfold hm_fake in *. rewrite EL in G8 |- *. dpose WL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FS0 & FS1 & _). unfold lowhigh, kHighMemBeg in FS0.
             apply (fake_rep_frame m m' WM (l_fs (h_L h0)) LF G8); [clear -FS0; lia| apply KOM; unfold kFakeBytes in ZF; clear -ZF; lia|].
             intros FB nB HFB. ddestruct G8 as (_ & _ & _ & LFW & _). destruct (LFW _ HFB) as (kf & ii & Hkf & Hii & EFB).
             pose proof (fsk_frame_inside (l_fs (h_L h0)) kf ii Hkf Hii) as [I1 I2]. pose proof (fsk_sizes kf Hkf) as (SZ1 & _).
             assert (EF1 : FB = fsk_frame (l_fs (h_L h0)) kf ii) by (clear -EFB; congruence). assert (EF2 : nB = fsk_bytes kf) by (clear -EFB; congruence).
             rewrite EF1, EF2. apply KOM. unfold kFakeBytes in ZF, I2. clear - I1 I2 SZ1 ZF; lia. }
    split; [apply (hm_ia_frame m m' WM h G9); apply IAG; vm_compute; reflexivity|].
    apply (hm_emb_frame_i m m' WM h h GE); [reflexivity| reflexivity| apply IAG; vm_compute; reflexivity].   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  #[using="h0 SP0 L T SP"] Lemma stk_keep : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "PW,(1=.$91.)Pm,P,(0.&40.)(5.(0.&8.))Pm',P,(0.&40.)(5.(0.&8.))Plo',$<.Phi',$<.P,(64.$7.R4.R2.R1.)P,(93.R6.R5.R4.)P,(70.$7.R6.R5.)P,(4;.+65?000.R5.)(64.$7.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros W m m' lo' hi' ST MU WM LO. eapply stk_transport; [exact ST| exact MU| exact WM|].
    intros x Hx. right. dpose ST as (S0 & S1 & SS). destruct (SS x Hx) as [W1 _]. apply WM in W1.
    rewrite wview_high in W1 by (rewrite wa_unsigned by lia; lia). destruct (m' (wa x)) as [b|]; [exists b; reflexivity| exfalso; apply W1; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition LINVx (h : ahst) (m : mem) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "(2;.(4:.VhAR,O3.)(2;.(4;.(3>.O3.)$4<.)(2;.(4.$1:.(43.O3.)$4=.)(2;.(4>.VhAR,O3.VLF,O2.)(2;.(4?.VhAR,VAL,VFF,O3.O1.)(2;.(50.O2.O1.)(2;.(51.$7.O2.)(2;.Pk,$:.P,(19.$:.R1.(17.O3.))(19.$:.R2.(17.Vh0,))(2;.Psh,$52.P,(19.$52.R1.(53.(54.O3.)))(19.$52.R2.(53.(54.Vh0,)))(2;.Px,$<.P,(55.VhAR,VAL,VFF,Vh0,R1.)P,(1.(2.VQS,R2.))(55.VhAR,VAL,VFF,O3.R3.)(2;.(56.VL,(21.Vh0,)VQS,VRP,(57.(58.Vh0,))(59.(58.Vh0,))Vlo,VSP0,Vm0,O2.)(2;.(5:.VQS,Vm0,O2.)(2;.(4.$5;.(5<.O3.)(5<.Vh0,))(2;.(4.$5=.(3=.O3.)(3=.Vh0,))(2;.(4.$5>.(58.O3.)(58.Vh0,))(2;.(4.(1=.(;.$<.$<.))(21.O3.)(21.Vh0,))(2;.(5?.O3.)Pk,$:.P,(19.$:.R1.(17.O3.))(60.(61.(62.R2.))(63.+2.+20.)))))))))))))))))))")
(* [comment removed for export] *).
  Definition exit_cont (Q : config -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Ph,$18.Pm,P,(0.&40.)(5.(0.&8.))Pmo,$6<.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)P,(95.R11.R10.R?.)P,(4.(1=.$22.)(26.(27.R12.))(96.$22.))P,(23.VhAR,R13.VC,(8.(;.$24.$25.))R12.)P,(64.$7.R13.Vlo,VSP0,)(7;.$7.O1.(7<.(7=.(97.Vqra,(39.&40.VSP0,)Vgp,Vtp,R12.R11.R10.Vq0,Vq1,(39.&40.=)R?.R>.R=.R<.R;.R:.R9.Vq2,Vq3,Vq4,Vq5,Vq6,Vq7,Vq8,Vq9,Vs10,Vs11,R8.R7.R6.R5.)VF,(98.Vqra,)Vfc,(8.(0.&40.))R14.(82.$7.))R13.))")
(* [comment removed for export] *).

  #[using="Type"] Lemma msr_cons : forall h b0 tb, q_batches (h_tq h) = b0 :: tb -> msr h = S (length (b_elems b0) + msr_l tb).
  Proof. intros h b0 tb HB. unfold msr. rewrite HB. reflexivity. Qed.

  #[using="IMG ALWF ASB TP WF0 GEO0 C0 C1 LOL SPL SPA STKB"] Lemma dr_outer : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "Pn,$25.PQ,P,$88.SpPh,$18.Pm,P,(0.&40.)(5.(0.&8.))Pmo,$6<.Pra,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)P,(89.(99.R17.)R19.)P,(6=.R18.R17.R16.)P,(23.VhAR,R19.VC,(8.(;.$24.$25.))R18.)P,(1.(4.(1=.$22.)(26.(27.R1:.))(96.$22.)))P,(60.(35.(9.$22.$24.$29.(26.(27.R1;.))))(63.+2.+3>.))P,(9:.R1=.)(7;.$7.R1>.(7<.(7=.(7>.VSP0,R1:.Vgp,Vtp,R19.R18.R17.(39.&40.(2>.(30.$22.(26.(27.R1=.)))))R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.Vs10,Vs11,R:.R9.R8.R7.VC,)VF,(39.&40.$9;.)Vfc,(8.(0.&40.))R1<.(82.$7.))R1;.))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros Q h m mo ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 MS LI RQ NE TQB EC.
    { exfalso. destruct (q_batches (h_tq h)) as [|b tb] eqn:E; [exact (NE eq_refl)|]. unfold msr in MS. rewrite E in MS. cbn in MS. clear -MS. lia. }
    destruct (q_batches (h_tq h)) as [|b0 tb] eqn:HB; [exact (False_ind _ (NE eq_refl))|]. clear NE.
    dpose LI as (WF & HV & CI & HMQ & HK & HJ & MI & SUBK & SUBS & CSR & FK & WMX & EL & EG & ED & EB & LS & H32 & ST & FR).
    dpose L_facts as (SB0 & (T0 & T1) & STK0 & STKH). dpose WF as ((WLh & _) & _ & WRh & _).
    ddestruct (RIq_head_cells h C m b0 tb RQ HB) as (nx & QC & BH & BE & -> & BWF).
    pose proof BWF as [BOK _]. apply Forall_app in BOK as [BOKg BOKt]. inversion BOKt as [|? ? OK0 OKt]; subst. pose proof OK0 as OK0'. unfold bn_ok, bn_count in OK0. cbn [bn_of bn_addr bn_size bn_elems] in OK0. rewrite length_map in OK0.
    cbn [map bsum bn_of bn_size] in TQB.
    pose proof (bsum_nonneg (map bn_of tb) OKt) as BS0.
    (* [comment removed for export] *)
    ddestruct (batch_slot h b0 WF ltac:(rewrite HB; apply in_app_iff; left; left; reflexivity)) as (ib & Hib & EBb).
    destruct (slot_le h kBatchClass ib WRh ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2]. rewrite <- EBb in S1, S2. change (class_size kBatchClass) with 8192 in S2.
    dpose (user_vs_ri h kBatchClass WLh WRh ltac:(unfold kBatchClass; clear; lia)) as (Q1 & Q2 & Q3 & Q4).
    pose proof (WRh kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU' & _).
    rewrite EL in S1, S2, Q1, Q2, Q4. pose proof (z_hull_stk h0 GEO0) as ZH. unfold zapart in ZH. cbn [fst snd] in ZH.
    pose proof WF as (WFRh & _). pose proof (WFK_of_WFR h WF HV) as W0.
    assert (BHULL : l_b6 (h_L h0) <= b_addr b0 /\ b_addr b0 + 8192 <= l_b6 (h_L h0) + 0x2000011000) by (unfold region_beg, kRegionSize in *; clear - S1 S2 Q1 Q2 Q4 AUMU'; lia).
    assert (CSB : crange (ff_CS AL FF h) (b_addr b0) 8192).
    { eapply crange_sub; [apply (ff_cs_user AL FF h kBatchClass W0 ltac:(unfold kBatchClass; clear; lia))| rewrite EL; exact S1| rewrite EL; clear - S2 AUMU'; lia]. }
    assert (CSC : crange (ff_CS AL FF h) C 32) by (apply (ff_cs_stack AL FF h C 32 W0); rewrite EL; unfold L in *; [clear - C0 SPL LOL; lia| exact C1]).
    assert (CSS : crange (ff_CS AL FF h) lo (SP0 - lo)) by (apply (ff_cs_stack AL FF h lo (SP0 - lo) W0); rewrite EL; unfold L in *; [exact LOL| clear - C0 C1; lia]).
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo (ff_kinv AL FF h) HK); [exact HJ| |].
    { eapply (dr_head' AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra
                SP0 C (b_addr b0) (Z.of_nat (S (length tb))) (hd_addr (map bn_of tb)) (last_addr 0 (bn_of b0 :: map bn_of tb)) (b_size b0 + bsum (map bn_of tb)) (b_size b0)
                (Z.of_nat (length (b_elems b0))) lo T STK j0 (map (Z_to_bv 64) (b_elems b0)) F fc m m FR);
        first [ exact QC | exact BH | exact BE | exact CSB | exact CSC | exact CSS | exact MI | apply munch_refl | apply wmono_refl
              | (rewrite length_map; rewrite Nat2Z.id; reflexivity)
              | match goal with |- ?G => idtac end ].
      all: pose proof aceil_bounds as ACB; unfold L in *.
      all: match goal with
           | |- 1 <= Z.of_nat _ < _ => pose proof (bsum_ge (map bn_of tb) OKt) as BG; rewrite length_map in BG; clear - BG TQB OK0; lia
           | |- 0 <= hd_addr _ < _ => destruct (map bn_of tb) as [|b1 r] eqn:Etb; cbn [hd_addr hd_addrT]; [clear; lia|]; inversion OKt as [|? ? OK1 X1]; subst; unfold bn_ok in OK1; clear - OK1 ACB; lia
           | |- 0 <= last_addr _ _ < _ => apply last_addr_bound; [constructor; [exact OK0'| exact OKt]| clear; lia]
           | |- _ => clear - OK0 OKt BS0 TQB BHULL ZH STK0 STKH LOL SPL C0 C1 ACB; lia
           end. }
    cbn beta. intros ms1 mo1 P1 HK1 _ HJ1.
    ddestruct P1 as (m1 & MU1 & WM1 & MI1 & FR1 & QC1 & REST).
    (* [comment removed for export] *)
    assert (HMQ1 : HMq h LF m1).
    { apply (HMq_stack h m m1 _ WF (ff_geom AL FF h mo W0 HK) EL HMQ MU1 WM1). intros A n' D. cbn [disjoint_from]. unfold L in *. clear - D LOL C0 C1 SPL. repeat split; lia. }
    assert (RQ1 : RIq h C (Some (bn_of b0, 0%nat)) m1) by (exact (RIq_enter h m m1 b0 tb WF EL RQ HB MU1 WM1 QC1)).
    assert (ST1 : stk asegs m1 lo SP) by (apply (stk_keep _ m m1 lo SP ST MU1 WM1); pose proof aceil_bounds; unfold L in *; clear - LOL STK0 H; lia).
    assert (HJ1' : J m1 mo1).
    { destruct REST as [(_ & E)|(_ & ? & ? & ? & ? & ? & E)]; rewrite E in HJ1; exact HJ1. }
    assert (LI1 : LINV h m1 mo1).
    { unfold LINV. split; [exact WF|]. split; [exact HV|]. split; [exact CI|]. split; [exact HMQ1|]. split; [exact HK1|]. split; [exact HJ1'|]. split; [exact MI1|].
      split; [exact SUBK|]. split; [exact SUBS|]. split; [exact CSR|].
      split. { eapply fkeepR_trans; [exact FK| | apply incl_refl| apply incl_refl]. apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m m1 MU1).
               apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; exact Ha|].
               apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; do 9 right; exists (C, 32); split; [unfold RP; apply in_app_iff; right; left; reflexivity| cbn [fst snd]; exact Ha]|].
               apply Forall_nil. }
      split; [exact (wmono_ex_trans QS m0 m m1 WMX (wmono_ex_of_wmono QS m m1 WM1))|].
      split; [exact EL|]. split; [exact EG|]. split; [exact ED|]. split; [exact EB|]. split; [exact LS|]. split; [exact H32|]. exact (conj ST1 FR1). }
    (* [comment removed for export] *)
    assert (TC : tail_cont Q (bn_of b0) tb).
    { intros h2 m2 mo2 ra' x0 x1 x2 z0 z1 z2 z3 z4 z5 z6 z7 r7 r8 r9 x3 x4 x5 x6 LI2 RQ2 TL2.
      dpose LI2 as (WF2 & HV2 & CI2 & HMQ2 & HK2 & HJ2 & MI2 & SUBK2 & SUBS2 & CSR2 & FK2 & WMX2 & EL2 & EG2 & ED2 & EB2 & LS2 & H322 & ST2 & FR2).
      pose proof RQ2 as R2. unfold RIq in R2. cbn zeta in R2. ddestruct R2 as (_ & _ & _ & _ & _ & _ & (_ & _ & b2 & all2 & E02 & EA2 & EE2 & EL2' & IL2 & _)).
      assert (HE2 : b_elems b2 = []).
      { rewrite EL2'. apply skipn_all2 || apply skipn_all. cbn [bn_elems bn_of] in EE2 |- *. rewrite <- (length_map (Z_to_bv 64) all2), <- EE2, length_map. clear; lia. }
      rewrite TL2 in E02. cbn [bn_addr bn_of] in EA2.
      pose proof (WFK_of_WFR h2 WF2 HV2) as W02. dpose WF2 as ((WL2 & _) & _ & WR2 & _).
      (* [comment removed for export] *)
      ddestruct (batch_slot h2 b2 WF2 ltac:(rewrite E02; apply in_app_iff; left; left; reflexivity)) as (ib2 & Hib2 & EBb2). rewrite EA2 in EBb2.
      pose proof (WR2 kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU2 & AUCS2 & _ & MULIM2 & _).
      pose proof (class_size_range kBatchClass ltac:(unfold kBatchClass; clear; lia)) as CSR24. change (class_size kBatchClass) with 8192 in CSR24, AUCS2.
      assert (CKB : 0 <= ib2 * 512 < 268435456).
      { unfold carved in Hib2. change (class_size kBatchClass) with 8192 in Hib2. unfold kUserLimit in MULIM2.
        pose proof (Z.mul_div_le (r_alloc_user (h_reg h2 kBatchClass)) 8192 ltac:(clear; lia)). clear - Hib2 AUMU2 MULIM2 H. nia. }
      pose proof HMQ2 as HMQ2c. ddestruct HMQ2c as (_ & [RO2 _] & _). pose proof RO2 as RO2'. unfold hm_ro in RO2'. cbn zeta in RO2'.
      ddestruct RO2' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SBC2 & _).
      eapply (evtA_aevtS_KJ AL (ff_CS AL FF h2) (ff_K AL FF h2) _ Q _ mo2 (ff_kinv AL FF h2) HK2); [exact HJ2| |].
      { eapply (dr_tail AL IMG ALWF (ff_CS AL FF h2) (ff_csok AL FF h2) ra' gp tp x0 x1 x2 z0 z1 z2 z3 z4 z5 z6 z7 _ r7 r8 r9 s10 s11 x3 x4 x5 x6 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra
                  SP0 C T STK (l_sb (h_L h2)) (b_addr b0) (ib2 * 512) lo j0 F fc m2);
          first [ exact FR2 | exact ST2 || (unfold SP in ST2; replace (SP0 + -112) with (SP0 - 112) by (clear; lia); exact ST2) | exact MI2 | exact SBC2 | exact CKB | exact STKB | idtac ].
        all: ddestruct (L_GSB (h_L h2) WL2) as (SB02 & _ & HRI2 & RI12); ddestruct (L_GT (h_L h2) WL2) as (T02 & T12 & _).
        all: match goal with
             | |- evtA _ _ _ _ _ => idtac
             | |- b_addr _ = _ => rewrite EBb2; unfold chunk_at, region_beg, kRegionSize, kBatchClass; change (class_size 24) with 8192; clear; lia
             | |- crange _ _ _ => apply (ff_cs_stack AL FF h2 lo (SP0 - lo) W02); rewrite EL2; unfold L in *; [exact LOL| clear - C0 C1; lia]
             | |- ?G => first [(rewrite ?EL2 in *; unfold T, L in *; pose proof aceil_bounds as ACB; clear - SB02 HRI2 RI12 T02 T12 STK0 STKH LOL SPL C0 C1 ACB; lia) | idtac "TGOAL" G]
             end.
      }
      cbn beta. intros ms3 mo3 P3 HK3 _ HJ3. ddestruct P3 as (a0x & a1x & -> & _ & _). unfold dr_regs.
      rewrite <- EA2. replace (Z_to_bv 64 (SP0 + -112)) with (Z_to_bv 64 SP) by (unfold SP; f_equal; clear; lia).
      assert (REB : ret_pc (Z_to_bv 64 A_DR_BACK) = Z_to_bv 64 A_DR_BACK) by (apply ret_pc_even; [unfold A_DR_BACK; clear; lia| reflexivity]).
      unfold T. unfold L. rewrite <- EL2.
      eapply (rec_batch_step AL IMG ALWF ASB FF Q _ gp tp x0 x1 x2 _ _ z4 z5 z6 z7 _ _ _ _ _ r7 r8 r9 s10 s11 x3 x4 x5 x6 h2 LF QS (bn_of b0) (length (bn_elems (bn_of b0))) b2 tb SP C lo F fc m2 mo3
                WF2 HV2 CI2 E02 HE2 HMQ2 RQ2); [unfold SP; clear -C0; lia| rewrite EL2; exact C1| exact ST2| rewrite EL2; exact LOL| unfold SP; clear -SPL; lia
                | unfold SP; clear -SPA; rewrite Zminus_mod, SPA; reflexivity| exact MI2| exact TP| exact HK3| exact HJ3|].
      intros c4 P4. ddestruct P4 as (ms4 & mo4 & w0 & w1 & w2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & m4 & dr & dn & f & -> & -> & WF3 & HMQ3 & RQ3 & HK4 & HJ4 & CSM3 & FK3 & WM3 & MI3 & ST3).
      pose proof (LINV_batch h2 m2 mo2 dr dn f b2 tb m4 mo4 LI2 E02 WF3 HMQ3 HK4 HJ4 CSM3 FK3 WM3 MI3 ST3) as LI3.
      set (h3 := h_recb h2 dr dn f) in *.
      dpose LI3 as (_ & HV3 & CI3 & _ & _ & _ & _ & SUBK3 & SUBS3 & CSR3 & FKR3 & WMX3 & EL3 & EG3 & ED3 & EB3 & LS3 & H323 & ST3' & FR3).
      assert (TQ3 : q_batches (h_tq h3) = tb) by (exact (recb_tq h2 dr dn f b2 tb E02)).
      rewrite REB.
      (* [comment removed for export] *)
      pose proof RQ3 as R3. unfold RIq in R3. cbn zeta in R3. rewrite TQ3 in R3. ddestruct R3 as (_ & _ & _ & _ & QC3 & _ & BWF3).
      pose proof (WFK_of_WFR h3 WF3 HV3) as W03.
      eapply (evtA_aevtS_KJ AL (ff_CS AL FF h3) (ff_K AL FF h3) _ Q _ mo4 (ff_kinv AL FF h3) HK4); [exact HJ4| |].
      { replace (Z_to_bv 64 SP) with (Z_to_bv 64 (SP0 + -112)) by (unfold SP; f_equal; clear; lia).
        eapply (dr_back AL IMG ALWF (ff_CS AL FF h3) (ff_csok AL FF h3) gp tp w0 w1 w2 _ _ _ _ v4 v5 v6 v7 _ _ r7 r8 r9 s10 s11 w3 w4 w5 w6 q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra
                  SP0 C (l_T (h_L h2)) STK (Z.of_nat (length (map bn_of tb))) (hd_addr (map bn_of tb)) (last_addr 0 (map bn_of tb)) (bsum (map bn_of tb)) lo j0 F fc m4 m4 []);
          first [ exact QC3 | exact MI3 | apply munch_refl | apply wmono_refl | (rewrite EL2; exact FR3) | (unfold SP in ST3'; replace (SP0 - 112) with (SP0 + -112) in ST3' by (clear; lia); exact ST3') | idtac ].
        all: pose proof (bsum_ge (map bn_of tb) OKt) as BG; rewrite length_map in BG; rewrite ?length_map.
        all: match goal with
             | |- crange _ C 32 => apply (ff_cs_stack AL FF h3 C 32 W03); rewrite EL3; unfold L in *; [clear - C0 SPL LOL; lia| exact C1]
             | |- crange _ lo _ => apply (ff_cs_stack AL FF h3 lo (SP0 - lo) W03); rewrite EL3; unfold L in *; [exact LOL| clear - C0 C1; lia]
             | |- ?G => first [(unfold L in *; pose proof aceil_bounds as ACB; clear - BG TQB OK0 STK0 STKH LOL SPL C0 C1 ACB; lia) | idtac "BGOAL" G]
             end. }
      cbn beta. intros ms5 mo5 P5 HK5 _ HJ5.
      destruct P5 as [(LNZ & ->)|(LZ & m5 & -> & MU5 & WM5 & MI5 & QC5 & ST5)].
      - (* [comment removed for export] *)
        rewrite length_map. rewrite <- TQ3. apply (IH Q h3 m4 mo5); [| | exact RQ3| | | exact EC].
        + rewrite (msr_cons h b0 tb HB) in MS. unfold msr. rewrite TQ3. clear -MS. lia.
        + dpose LI3 as (X1 & X2 & X3 & X4 & _ & _ & X6). cbn [ms_mem] in HJ5. exact (conj X1 (conj X2 (conj X3 (conj X4 (conj HK5 (conj HJ5 X6)))))).
        + rewrite TQ3. intros E. rewrite E in LNZ. cbn in LNZ. exact (LNZ eq_refl) || (rewrite length_map in LNZ; cbn in LNZ; exact (LNZ eq_refl)).
        + rewrite TQ3. clear - TQB OK0. lia.
      - (* [comment removed for export] *)
        replace (Z.of_nat (length (map bn_of tb))) with 0 by (clear -LZ; lia).
        apply (EC h3 m5 mo5).
        + dpose LI3 as (X1 & X2 & X3 & X4 & _ & _ & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & _). unfold LINVx. cbn [ms_mem] in HJ5.
          split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
          split. { apply (HMq_stack h3 m4 m5 _ X1 (ff_geom AL FF h3 mo4 W03 HK4) EL3 X4 MU5 WM5). intros A n' D. cbn [disjoint_from]. unfold L in *. clear - D LOL C0 C1 SPL. repeat split; lia. }
          split; [exact HK5|]. split; [exact HJ5|]. split; [exact MI5|]. split; [exact X7|]. split; [exact X8|]. split; [exact X9|].
          split. { eapply fkeepR_trans; [exact X10| | apply incl_refl| apply incl_refl]. apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m4 m5 MU5).
                   apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; exact Ha| apply Forall_nil]. }
          split; [exact (wmono_ex_trans QS m0 m4 m5 X11 (wmono_ex_of_wmono QS m4 m5 WM5))| exact (conj X12 (conj X13 (conj X14 (conj X15 (conj X16 X17)))))].
        + rewrite TQ3. destruct tb; [reflexivity| cbn in LZ; clear -LZ; lia].
        + apply (RIq_k m4 m5 h3 C None RQ3).
          * intros x Hx. apply MU5. cbn [outside]. rewrite EL3 in Hx. pose proof (z_T_stk h0 GEO0) as Y. unfold zapart in Y. cbn [fst snd] in Y. unfold L in *. clear - Hx Y LOL SPL C0 C1. split; [lia| exact I].
          * intros x Hx. apply MU5. cbn [outside]. cbn in Hx. pose proof aceil_bounds. unfold L in *. clear - Hx LOL SPL C0 STK0 H. split; [lia| exact I].
          * intros x Hx. apply MU5. cbn [outside]. clear - Hx C0. split; [lia| exact I].
          * intros b Hb. pose proof LI3 as (WFb & _). ddestruct (batch_slot h3 b WFb Hb) as (ib3 & Hib3 & EBb3). dpose WFb as ((WL3 & _) & _ & WR3 & _).
            destruct (slot_le h3 kBatchClass ib3 WR3 ltac:(unfold kBatchClass; clear; lia) Hib3) as [S13 S23]. rewrite <- EBb3 in S13, S23. change (class_size kBatchClass) with 8192 in S23.
            dpose (user_vs_ri h3 kBatchClass WL3 WR3 ltac:(unfold kBatchClass; clear; lia)) as (Q13 & Q23 & Q33 & Q43).
            pose proof (WR3 kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU3 & _).
            rewrite EL3 in S13, S23, Q13, Q23, Q43. intros x Hx. apply MU5. cbn [outside]. pose proof (z_hull_stk h0 GEO0) as Y. unfold zapart in Y. cbn [fst snd] in Y. unfold L in *.
            unfold region_beg, kRegionSize in *. clear - Hx Y LOL SPL C0 C1 S13 S23 Q13 Q23 Q43 AUMU3. split; [lia| exact I].
          * exact I.
        + exact ST5. }
    (* [comment removed for export] *)
    destruct REST as [(CNZ & ->)|(CZ & a0' & a1' & s7' & s8' & s9' & ->)].
    - pose proof (eq_refl (b_elems b0)) as HE0. destruct (b_elems b0) as [|e0 er] eqn:HE1 in |- ; [exfalso; rewrite HE1 in CNZ; cbn in CNZ; exact (CNZ eq_refl)|]. clear HE0. rewrite ?HE1. cbn [map].
      rewrite Z_to_bv_bv_unsigned.
      replace (Z_to_bv 64 (b_addr b0 + 152)) with (Z_to_bv 64 (bn_addr (bn_of b0) + 152 + 8 * 0)) by (cbn [bn_addr bn_of]; f_equal; clear; lia).
      replace (Z_to_bv 64 16) with (Z_to_bv 64 (16 + 0)) by (f_equal; clear; lia).
      change (b_addr b0) with (bn_addr (bn_of b0)).
      replace (Z.of_nat (length (e0 :: er))) with (bn_count (bn_of b0)) by (unfold bn_count; cbn [bn_elems bn_of]; rewrite HE1, length_map; reflexivity).
      apply (dr_inner (length (e0 :: er)) Q (bn_of b0) tb h m1 mo1 0 (Z_to_bv 64 e0)); [| exact LI1| exact RQ1| | | rewrite HB; reflexivity| exact TC].
      + unfold bn_count. cbn [bn_elems bn_of]. rewrite HE1, length_map. clear; lia.
      + unfold bn_count. cbn [bn_elems bn_of]. rewrite HE1, length_map. cbn. clear; lia.
      + cbn [bn_elems bn_of]. rewrite HE1. reflexivity.
    - unfold tail_cont in TC. unfold dr_regs in TC |- *.
      replace (Z_to_bv 64 (Z.of_nat (length (b_elems b0)))) with (Z_to_bv 64 (bn_count (bn_of b0))) by (unfold bn_count; cbn [bn_elems bn_of]; rewrite length_map; reflexivity).
      change (b_addr b0) with (bn_addr (bn_of b0)).
      apply (TC h m1 mo1); [exact LI1| | rewrite HB; reflexivity].
      replace (length (bn_elems (bn_of b0))) with 0%nat by (cbn [bn_elems bn_of]; rewrite length_map; clear -CZ; lia). exact RQ1.
  Qed.
End Loop.

(* [comment removed for export] *)
#[using="Type"] Theorem do_recycle : ltac2:(CDefT.buildp (gd_tbl_AW_RecLoop ()) "PAL,$9<.PIMG,(9=.R1.)PALWF,(9>.R2.)PASB,(4.$<.(9?.R3.)+7???8000.)PFF,(:0.VhAR,R4.)Ph0,$18.Pm0,P,(0.&40.)(5.(0.&8.))PLF,(1=.(;.$<.$<.))PC,$<.PSP0,$<.Plo,$<.PSTK,$<.Pq9,(0.&40.)Pq8,(0.&40.)Pq7,(0.&40.)Pq6,(0.&40.)Pq5,(0.&40.)Pq4,(0.&40.)Pq3,(0.&40.)Pq2,(0.&40.)Pq1,(0.&40.)Pq0,(0.&40.)Pqra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)PF,(:1.&5.(0.&40.))Pfc,(0.&20.)PQ,P,$88.SpPmo,$6<.Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)P,(4.(0.&40.)R13.(39.&40.$:2.))P,(4:.VhAR,R27.)P,(92.R28.)P,(4;.R25.R26.)P,(4;.(33.R27.+20.)(6:.(5<.R2:.)))P,(4;.(69.(5<.R2;.))R26.)P,(4;.R27.(8;.(8;.R28.+70.)+2>0.))P,(4.$<.(:3.R29.+10.)=)P,(2;.(4;.=R28.)(60.R28.(63.+2.+40.)))P,(4;.(3>.R2?.)$4<.)P,(4.$1:.(43.R30.)$4=.)P,(4>.VhAR,R31.R2?.R30.)P,(23.VhAR,R32.R2?.(8.(;.$24.$25.))R31.)P,(4?.VhAR,R38.R34.R33.R1<.)P,(50.R33.R1=.)P,(51.$7.R34.)P,(64.$7.R35.R31.R32.)P,Pk,$:.P,(19.$:.R1.(17.R38.))(60.(61.(62.R2.))(63.+2.+20.))P,(60.(35.(9.$22.$24.$29.(26.(27.R38.))))(63.+2.+3>.))P,(:4.R3>.R3:.R39.R38.R37.R36.R35.R34.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R19.R18.R25.R24.R23.)(7;.$7.R24.(7<.(7=.(97.R29.(39.&40.R36.)R28.R27.R22.R21.R20.R2:.R2;.R1?.(39.&40.R37.)(39.&40.(33.(67.(5<.R3:.))+=0.))(39.&40.R34.)R1>.R1=.R1<.R1;.R2<.R2=.R2>.R2?.R30.R31.R32.R33.R1:.R19.R18.R17.R16.R15.)R26.(39.&40.$:5.)R25.(8.(0.&40.))R39.(82.$7.))R23.))")
(* [comment removed for export] *).
Proof.
  intros AL IMG ALWF ASB FF h0 m0 LF C SP0 lo STK q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra gp tp F fc Q mo t0 t1 t2 a0 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6
    TP WF0 GEO0 C0 C1 LOL SPL SPA STKB HV CI HMQ RQ HK HJ MI ST H32 TQB EC.
  dpose (L_facts h0 WF0) as (SB0 & (T0 & T1) & STK0 & STKH). pose proof (WFK_of_WFR h0 WF0 HV) as W00.
  pose proof RQ as R0. unfold RIq in R0. cbn zeta in R0. ddestruct R0 as (_ & _ & _ & _ & QC0 & _ & BWF0). pose proof BWF0 as [BOK0 _]. apply Forall_app in BOK0 as [_ BOKt].
  pose proof (bsum_ge (map bn_of (q_batches (h_tq h0))) BOKt) as BG. rewrite length_map in BG.
  eapply (evtA_aevtS_KJ AL (ff_CS AL FF h0) (ff_K AL FF h0) _ Q _ mo (ff_kinv AL FF h0) HK); [exact HJ| |].
  { eapply (dr_entry AL IMG ALWF (ff_CS AL FF h0) (ff_csok AL FF h0) qra gp tp t0 t1 t2 q0 q1 a0 a4 a5 a6 a7 q2 q3 q4 q5 q6 q7 q8 q9 s10 s11 t3 t4 t5 t6
              SP0 C (l_T (h_L h0)) STK (Z.of_nat (length (map bn_of (q_batches (h_tq h0))))) _ _ _ lo F fc m0);
      first [ exact QC0 | exact ST | exact MI | exact STKB
            | (apply (ff_cs_stack AL FF h0 C 32 W00); [clear - C0 SPL LOL; lia| exact C1])
            | (apply (ff_cs_stack AL FF h0 lo (SP0 - lo) W00); [exact LOL| clear - C0 C1; lia])
            | (pose proof aceil_bounds as ACB; rewrite ?length_map; clear - BG TQB STK0 STKH LOL SPL C0 C1 ACB T0 T1; lia) ]. }
  cbn beta. intros ms1 mo1 P1 HK1 _ HJ1.
  ddestruct P1 as (m1 & jk & MU1 & WM1 & MI1 & QC1 & [(LNZ & a1' & -> & FR1 & ST1)|(LZ & a1' & a2' & a3' & -> & ST1)]).
  - (* [comment removed for export] *)
    assert (HMQ1 : HMq h0 LF m1).
    { apply (HMq_stack h0 LF WF0 h0 m0 m1 _ WF0 GEO0 eq_refl HMQ MU1 WM1). intros A n' D. cbn [disjoint_from]. clear - D LOL C0 C1. split; [lia| exact I]. }
    assert (RQ1 : RIq h0 C None m1).
    { apply (RIq_k m0 m1 h0 C None RQ); [| | | | exact I].
      - intros x Hx. apply MU1. cbn [outside]. pose proof (z_T_stk h0 GEO0) as Y. unfold zapart in Y. cbn [fst snd] in Y. clear - Hx Y LOL SPL C0 C1. split; [lia| exact I].
      - intros x Hx. apply MU1. cbn [outside]. cbn in Hx. pose proof aceil_bounds. clear - Hx LOL STK0 H. split; [lia| exact I].
      - intros x Hx. apply MU1. cbn [outside]. clear - Hx C0. split; [lia| exact I].
      - intros b Hb. ddestruct (batch_slot h0 b WF0 Hb) as (ib & Hib & EBb). dpose WF0 as ((WL & _) & _ & WR & _).
        destruct (slot_le h0 kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2]. rewrite <- EBb in S1, S2. change (class_size kBatchClass) with 8192 in S2.
        dpose (user_vs_ri h0 kBatchClass WL WR ltac:(unfold kBatchClass; clear; lia)) as (Q1 & Q2 & Q3 & Q4).
        pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU & _).
        intros x Hx. apply MU1. cbn [outside]. pose proof (z_hull_stk h0 GEO0) as Y. unfold zapart in Y. cbn [fst snd] in Y.
        unfold region_beg, kRegionSize in *. clear - Hx Y LOL SPL C0 C1 S1 S2 Q1 Q2 Q4 AUMU. split; [lia| exact I]. }
    rewrite length_map.
    apply (dr_outer AL IMG ALWF ASB FF h0 m0 LF C SP0 lo STK jk q9 q8 q7 q6 q5 q4 q3 q2 q1 q0 qra gp tp s10 s11 F fc TP WF0 GEO0 C0 C1 LOL SPL SPA STKB (msr h0) Q h0 m1 mo1);
      [apply le_n| | exact RQ1| intros E; rewrite E, length_map in LNZ; cbn in LNZ; exact (LNZ eq_refl)| exact TQB| exact EC].
    unfold LINV. cbn [ms_mem] in HJ1. split; [exact WF0|]. split; [exact HV|]. split; [exact CI|]. split; [exact HMQ1|]. split; [exact HK1|]. split; [exact HJ1|]. split; [exact MI1|].
    split; [intros k Hk; exact Hk|]. split; [intros sh Hsh; exact Hsh|]. split; [intros x Hx _; exact Hx|].
    split. { apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m0 m1 MU1). apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; exact Ha| apply Forall_nil]. }
    split; [exact (wmono_ex_of_wmono _ m0 m1 WM1)|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply LST0|]. split; [exact H32|]. exact (conj ST1 FR1).
  - (* [comment removed for export] *)
    replace (Z_to_bv 64 (Z.of_nat (length (map bn_of (q_batches (h_tq h0)))))) with (Z_to_bv 64 0) by (f_equal; clear -LZ; lia).
    apply (EC h0 m1 mo1).
    + unfold LINVx. split; [exact WF0|]. split; [exact HV|]. split; [exact CI|].
      split. { apply (HMq_stack h0 LF WF0 h0 m0 m1 _ WF0 GEO0 eq_refl HMQ MU1 WM1). intros A n' D. cbn [disjoint_from]. clear - D LOL C0 C1. split; [lia| exact I]. }
      split; [exact HK1|]. split; [cbn [ms_mem] in HJ1; exact HJ1|]. split; [exact MI1|]. split; [intros k Hk; exact Hk|]. split; [intros sh Hsh; exact Hsh|]. split; [intros x Hx _; exact Hx|].
      split. { apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m0 m1 MU1). apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; exact Ha| apply Forall_nil]. }
      split; [exact (wmono_ex_of_wmono _ m0 m1 WM1)|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply LST0|]. exact H32.
    + destruct (q_batches (h_tq h0)); [reflexivity| rewrite length_map in LZ; cbn in LZ; clear -LZ; lia].
    + apply (RIq_k m0 m1 h0 C None RQ); [| | | | exact I].
      * intros x Hx. apply MU1. cbn [outside]. pose proof (z_T_stk h0 GEO0) as Y. unfold zapart in Y. cbn [fst snd] in Y. clear - Hx Y LOL SPL C0 C1. split; [lia| exact I].
      * intros x Hx. apply MU1. cbn [outside]. cbn in Hx. pose proof aceil_bounds. clear - Hx LOL STK0 H. split; [lia| exact I].
      * intros x Hx. apply MU1. cbn [outside]. clear - Hx C0. split; [lia| exact I].
      * intros b Hb. ddestruct (batch_slot h0 b WF0 Hb) as (ib & Hib & EBb). dpose WF0 as ((WL & _) & _ & WR & _).
        destruct (slot_le h0 kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2]. rewrite <- EBb in S1, S2. change (class_size kBatchClass) with 8192 in S2.
        dpose (user_vs_ri h0 kBatchClass WL WR ltac:(unfold kBatchClass; clear; lia)) as (Q1 & Q2 & Q3 & Q4).
        pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU & _).
        intros x Hx. apply MU1. cbn [outside]. pose proof (z_hull_stk h0 GEO0) as Y. unfold zapart in Y. cbn [fst snd] in Y.
        unfold region_beg, kRegionSize in *. clear - Hx Y LOL SPL C0 C1 S1 S2 Q1 Q2 Q4 AUMU. split; [lia| exact I].
    + exact ST1.
Qed.

End ARUN_1.
