(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_DepotA AW_DepotB AW_DepotC AW_DepotF AW_DepotCfg AW_DepotInv AW_DepotTop
     AW_MallocA AW_AllocA AW_Poison AW_AllocB AW_MallocB AW_MallocC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_Populate AW_Large AW_CfgDefs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Blist AW_FakeDefs AW_MmapFixedNR AW_PoisonBig AW_SFree5 AW_SMalloc HMLib HM AImgW HMFrame AW_FreeHM AW_MunmapCfg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_FreeHMS () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.HMLib.kept"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode_at"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_count"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.blistT"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_ok"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_maps"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctxlen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.iagree"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.ro_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.rwstat_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_errno"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pcl"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_pclass"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_thread"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cache"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dnodes"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotInv.sblks"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_inv"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.dep_zone"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_depot"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.depot"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_rz"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_user"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.chunk_kept"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_alloc_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_nfreed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.region_kept"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fake_rep"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_esz"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.emb_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section KeepK.
  Variables (m m' : mem).

  #[using="Type"] Lemma wview_eq_at : forall x, m' x = m x -> wview asegs m' x = wview asegs m x.
  Proof. intros x E. unfold wview. rewrite E. reflexivity. Qed.
  #[using="Type"] Lemma mrd_eq_at : forall x, m' x = m x -> mrd asegs m' x = mrd asegs m x.
  Proof. intros x E. unfold mrd. rewrite E. reflexivity. Qed.

  #[using="Type"] Lemma kwr : forall A n, wr_at asegs m A n -> kept m m' A n -> wr_at asegs m' A n.
  Proof.
    (intros A n dd_H; ddestruct dd_H as (H0 & H1 & H); intros K). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite (wview_eq_at (wa (A + i))); [apply H; exact Hi|]. apply K. rewrite wa_unsigned by lia. lia.
  Qed.

  #[using="Type"] Lemma krw : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "PA,$0.Pcs,(1.$2.)P,(3.$4.Vm,R2.R1.)P,(5.Vm,Vm',R3.(6.(7.R2.)))(3.$4.Vm',R4.R3.)")
(* [comment removed for export] *).
  Proof. intros A cs [C W] K. split; [exact (keep_ro m m' A cs C K)| exact (kwr _ _ W K)]. Qed.

  #[using="Type"] Lemma kbytes : forall A bs, bytes_at asegs m A bs -> kept m m' A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
  Proof.
    intros A bs B K. dpose B as (B0 & B1 & _).
    eapply bytes_at_transport; [exact B| apply kept_munch; [exact B0| exact K]| cbn; repeat split; lia].
  Qed.

  #[using="Type"] Lemma ku32 : forall A ws, u32arr asegs m A ws -> kept m m' A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
  Proof.
    intros A ws [B W] K. split; [| exact (kwr _ _ W K)].
    eapply kbytes; [exact B|]. rewrite u32s_length, Nat2Z.inj_mul. exact K.
  Qed.
  #[using="Type"] Lemma ku64 : forall A ws, u64arr asegs m A ws -> kept m m' A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
  Proof.
    intros A ws [B W] K. split; [| exact (kwr _ _ W K)].
    eapply kbytes; [exact B|]. rewrite u64s_length, Nat2Z.inj_mul. exact K.
  Qed.
  #[using="Type"] Lemma ku8 : forall A bs, u8arr asegs m A bs -> kept m m' A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
  Proof. intros A bs [B W] K. split; [exact (kbytes _ _ B K)| exact (kwr _ _ W K)]. Qed.

  #[using="Type"] Lemma kstk : forall lo hi, stk asegs m lo hi -> kept m m' lo (hi - lo) -> stk asegs m' lo hi.
  Proof.
    (intros lo hi dd_H; ddestruct dd_H as (H0 & H1 & H); intros K). split; [exact H0|]. split; [exact H1|]. intros a Ha.
    assert (E : m' (wa a) = m (wa a)) by (apply K; rewrite wa_unsigned by lia; lia).
    rewrite (wview_eq_at _ E), (mrd_eq_at _ E). apply H. exact Ha.
  Qed.

  #[using="Type"] Lemma bnode_at_k : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "Pb,$8.Pnx,$0.P,(9.Vm,R2.R1.)P,(:.(;.R3.)+3?=.)P,(5.Vm,Vm',(<.R4.)+2000.)(9.Vm',R5.R4.)")
(* [comment removed for export] *).
  Proof.
    (intros b nx dd_H; ddestruct dd_H as (H1 & H2 & H3); intros CNT K). unfold bn_count in CNT. split; [| split].
    - eapply krw; [exact H1| eapply kept_sub; [exact K| lia| cbn; lia]].
    - eapply ku64; [exact H2| eapply kept_sub; [exact K| lia| lia]].
    - exact (kwr _ _ H3 K).
  Qed.

  #[using="Type"] Lemma blistT_k : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "Pbs,(1.$8.)Pt,$0.P,(=.Vm,R2.R1.)P,(>.$8.(?.VhAR,)R3.)P,Pb,$8.P,(10.$8.R1.R5.)(5.Vm,Vm',(<.R2.)+2000.)(=.Vm',R5.R4.)")
(* [comment removed for export] *).
  Proof.
    induction bs as [|b r IH]; intros t BL F K; [exact I|]. destruct BL as [N BL]. inversion F; subst. split.
    - apply bnode_at_k; [exact N| unfold bn_ok in *; lia| apply K; left; reflexivity].
    - apply IH; auto. intros b' Hb'. apply K. right. exact Hb'.
  Qed.
End KeepK.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Hole.
  Variables (m m' : mem) (ha hn : Z).
  Hypothesis WMO : wmono_out ha hn m m'.

  Local Notation apart A n := (A + n <= ha \/ ha + hn <= A).

  #[using="WMO"] Lemma wro : forall A n, wr_at asegs m A n -> apart A n -> wr_at asegs m' A n.
  Proof. intros A n W AP. exact (wr_at_transport_out ha hn m m' A n W WMO AP). Qed.

  (* [comment removed for export] *)
  #[using="WMO"] Lemma hm_maps_o : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "PL,$11.P,(12.R1.Vm,)P,(13.(:.(14.+7???7000.+10000000.)Vha,)(:.(14.Vha,Vhn,)+7???7000.))P,(13.(:.(14.+2008???7000.+=???0001000.)Vha,)(:.(14.Vha,Vhn,)+2008???7000.))P,(13.(:.(14.(15.R4.)(16.(17.R4.)(15.R4.)))Vha,)(:.(14.Vha,Vhn,)(15.R4.)))P,(13.(:.(14.(18.R5.)+1000.)Vha,)(:.(14.Vha,Vhn,)(18.R5.)))P,(13.(:.(14.(19.R6.)(1:.R6.))Vha,)(:.(14.Vha,Vhn,)(19.R6.)))P,(13.(:.(14.(1;.R7.)$1<.)Vha,)(:.(14.Vha,Vhn,)(1;.R7.)))(12.R8.Vm',)")
(* [comment removed for export] *).
  Proof.
    (intros L dd_H; ddestruct dd_H as (W1 & W2 & W3 & W4 & W5 & W6); intros A1 A2 A3 A4 A5 A6).
    split; [exact (wro _ _ W1 A1)|]. split; [exact (wro _ _ W2 A2)|]. split; [exact (wro _ _ W3 A3)|].
    split; [exact (wro _ _ W4 A4)|]. split; [exact (wro _ _ W5 A5)| exact (wro _ _ W6 A6)].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hm_rwstat_k : hm_rwstat m -> iagree rwstat_ranges m m' -> hm_rwstat m'.
  Proof.
    (intros dd_H; ddestruct dd_H as ((e & ERR) & (o & OOM) & FBM); intros AG). unfold A_ERRNO, A_OOM, A_FB_MUTEX, A_INSTANCE in *.
    split; [| split].
    - exists e. eapply krw; [exact ERR| eapply iagree_kept; [exact AG| vm_compute; reflexivity]].
    - exists o. eapply krw; [exact OOM| eapply iagree_kept; [exact AG| vm_compute; reflexivity]].
    - eapply krw; [exact FBM| eapply iagree_kept; [exact AG| vm_compute; reflexivity]].
  Qed.
  #[using="Type"] Lemma hm_statics_k : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "PL,$11.P,(1=.R1.Vm,)P,(1>.$1?.Vm,Vm',)P,(1>.$20.Vm,Vm',)P,(5.Vm,Vm',(18.R4.)+50.)P,(5.Vm,Vm',(14.(19.R5.)+8.)+4.)P,(5.Vm,Vm',(14.(19.R6.)+98.)+8.)P,(5.Vm,Vm',(14.(21.R7.)+18.)+8.)(1=.R8.Vm',)")
(* [comment removed for export] *).
  Proof. intros L [RO RW] A1 A2 K1 K2 K3 K4. split; [eapply hm_ro_frame; eauto| eapply hm_rwstat_k; eauto]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hm_pclass_k : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "PT,$0.Pci,$22.Pc,$0.Pp,$23.Pds,(1.(24.&40.))P,(25.Vm,R5.R4.R3.R2.R1.)P,(5.Vm,Vm',(14.(14.R6.+=0.)(26.+50.R4.))+50.)(25.Vm',R7.R6.R5.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    (intros T ci c p ds dd_H; ddestruct dd_H as (PC & ARR & LEN & FST & CI); intros K). split; [| split; [| split; [exact LEN| split; [exact FST| exact CI]]]].
    - eapply krw; [exact PC| eapply kept_sub; [exact K| lia| cbn; lia]].
    - eapply ku32; [exact ARR| eapply kept_sub; [exact K| lia| rewrite LEN; cbn; lia]].
  Qed.
    (* [comment removed for export] *)
  #[using="WMO"] Lemma hm_thread_o : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "Ph,$27.P,(28.R1.Vm,)P,(5.Vm,Vm',(14.(18.(29.R2.))+<60.)+1.)P,Pc,$0.P,(2:.(:.+1.R1.)(:.R1.+1?.))(5.Vm,Vm',(14.(14.(18.(29.R5.))+=0.)(26.+50.R2.))+50.)P,(5.Vm,Vm',(14.(18.(29.R4.))+:=0.)+10.)P,(2;.$4.Vm,(18.(29.R5.))+1000.)P,(2:.(:.+1000.(18.(29.R6.)))(13.(:.(14.(18.(29.R6.))+1000.)+10000.)(:.+65?000.(18.(29.R6.)))))P,(13.(:.(14.(18.(29.R7.))+1000.)Vha,)(:.(14.Vha,Vhn,)(18.(29.R7.))))Ph',$27.P,(2<.$11.(29.R1.)(29.R9.))P,(2<.$22.(2=.R2.)(2=.R:.))P,Pc,$0.(2<.$23.(2>.R4.R1.)(2>.R<.R1.))(28.R4.Vm',)")
(* [comment removed for export] *).
  Proof.
    (intros h dd_H; ddestruct dd_H as (UNW & (ds & PCL) & (j0 & j1 & J) & _); intros K1 KC K2 WT HT AT h' EL EI EC).
    unfold hm_thread. rewrite EL, EI. split; [| split; [| split]].
    - eapply krw; [exact UNW| exact K1].
    - exists ds. intros c Hc. rewrite EC. eapply hm_pclass_k; [exact (PCL c Hc)| exact (KC c Hc)].
    - dexists j0, j1. eapply krw; [exact J| exact K2].
    - apply hm_tstats_of_wr; [exact (wro _ _ WT AT)| exact HT].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma dtab_k : forall N, dtab m N -> iagree dep_zone m m' -> dtab m' N.
  Proof.
    intros N DT AG i Hi. ddestruct (DT i Hi) as (v & TC & VB). exists v. split; [| exact VB].
    eapply krw; [exact TC|]. eapply iagree_kept; [exact AG|]. unfold A_DEP, dep_zone, A_SS, A_DEP_END. cbn [cells_size csize Nat.add].
    cbn -[Z.leb Z.add Z.mul]. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma dmap1_k : forall nb, dmap1 m nb -> iagree dep_zone m m' -> dmap1 m' nb.
  Proof.
    (intros nb dd_H; ddestruct dd_H as (DM & DF & DL); intros AG). split; [| split; [exact DF| exact DL]].
    intros k Hk. eapply krw; [exact (DM k Hk)|]. eapply iagree_kept; [exact AG|]. unfold A_DEP_MAP1, A_DEP, dep_zone, A_SS, A_DEP_END. cbn [cells_size csize Nat.add].
    cbn -[Z.leb Z.add Z.mul]. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma dnodes_k : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "Pnb,(1.$0.)PN,$0.P,(2?.Vm,R2.R1.)P,(>.$0.Lb,$0.(2:.(:.+65?000.R1.)(2:.(:.(14.R1.(30.+2.+14.))(31.VhAR,))(2<.$0.(32.R1.+1000.)=)))R3.)P,Pb,$0.P,(10.$0.R1.R5.)(5.Vm,Vm',R2.(30.+2.+14.))(2?.Vm',R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros nb N DN HF K s Hs. ddestruct (DN s Hs) as (hsh & sid & lnk & NC & L0 & LS).
    dexists hsh, sid, lnk. split; [| split; [exact L0| exact LS]].
    ddestruct (dnode_range nb s HF Hs) as (R0 & R1 & _ & R3 & _).
    assert (IN : In (dblk nb (s / 65536)) nb).
    { unfold dblk. apply nth_In. assert (0 <= s / 65536 < Z.of_nat (length nb)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia. }
    eapply krw; [exact NC|]. eapply kept_sub; [exact (K _ IN)| exact R0| cbn; lia].
  Qed.
  #[using="Type"] Lemma dblocks_k : forall bl, dblocks m bl -> iagree dep_zone m m' -> dblocks m' bl.
  Proof.
    (intros bl dd_H; ddestruct dd_H as (DB & DF & DL); intros AG). split; [| split; [exact DF| exact DL]].
    intros j Hj. destruct (DB j Hj) as [stored R]. exists stored. eapply krw; [exact R|].
    eapply iagree_kept; [exact AG|]. unfold dep_zone, A_SS, A_DEP_END. cbn [cells_size csize Nat.add].
    cbn -[Z.leb Z.add Z.mul]. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.
  #[using="Type"] Lemma sblks_k : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "Pbl,(1.$0.)P,(33.Vm,R1.)P,(>.$0.Lb,$0.(2:.(:.+65?000.R1.)(2:.(:.(14.R1.(30.+2.+17.))(31.VhAR,))(2<.$0.(32.R1.+1000.)=)))R2.)P,Pb,$0.P,(10.$0.R1.R4.)(5.Vm,Vm',R2.(30.+2.+17.))(33.Vm',R4.)")
(* [comment removed for export] *).
  Proof.
    intros bl SB HF K j Hj.
    assert (IN : In (sblk bl j) bl) by (unfold sblk; apply nth_In; lia).
    eapply kstk; [exact (SB j Hj)|]. replace (sblk bl j + 2 ^ 23 - sblk bl j) with (2^23) by lia. exact (K _ IN).
  Qed.
  #[using="Type"] Lemma depot_inv_k : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "PN,$0.Pnb,(1.$0.)Ptf,$0.Pbl,(1.$0.)P,(34.VhAR,Vm,R4.R3.R2.R1.)P,(1>.$35.Vm,Vm',)P,Pb,$0.P,(10.$0.R1.R6.)(5.Vm,Vm',R2.(30.+2.+14.))P,Pb,$0.P,(10.$0.R1.R5.)(5.Vm,Vm',R2.(30.+2.+17.))(34.VhAR,Vm',R8.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    intros N nb tf bl DI AG KN KS.
    ddestruct DI as (NC & DT & DM & DNO & WF & MX & (alloc & SSX) & DB & SB & TF0 & BL & BA).
    dpose DM as (DM1 & DMF & DML). dpose DB as (DB1 & DBF & DBL).
    assert (KZ : forall A n, A_SS <= A -> A + n <= A_DEP_END -> kept m m' A n).
    { intros A n H1 H2. eapply iagree_kept; [exact AG|]. cbn -[Z.leb Z.add].
      rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity. }
    unfold A_SS, A_DEP_END in KZ.
    split. { eapply krw; [exact NC| apply KZ; unfold A_DEP_N; cbn; lia]. }
    split; [exact (dtab_k N DT AG)|]. split; [exact (dmap1_k nb DM AG)|].
    split; [exact (dnodes_k nb N DNO DMF KN)|]. split; [exact WF|].
    split. { eapply krw; [exact MX| apply KZ; unfold A_DEP_NODES; cbn; lia]. }
    split. { exists alloc. eapply krw; [exact SSX| apply KZ; unfold A_SS; cbn; lia]. }
    split; [exact (dblocks_k bl DB AG)|]. split; [exact (sblks_k bl SB DBF KS)|].
    split; [exact TF0|]. split; [exact BL| exact BA].
  Qed.
  #[using="Type"] Lemma hm_depot_k : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "Ph,$27.P,(36.VhAR,R1.Vm,)P,(1>.$35.Vm,Vm',)P,Pb,$0.P,(10.$0.R1.(37.(38.R4.)))(5.Vm,Vm',R2.(30.+2.+14.))P,Pb,$0.P,(10.$0.R1.(39.(38.R5.)))(5.Vm,Vm',R2.(30.+2.+17.))Ph',$27.P,(2<.$3:.(38.R1.)(38.R6.))(36.VhAR,R2.Vm',)")
(* [comment removed for export] *).
  Proof. intros h D AG KN KS h' ED. unfold hm_depot in *. rewrite ED. eapply depot_inv_k; eauto. Qed.

  (* [comment removed for export] *)
  #[using="WMO"] Lemma hm_chunk_o : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "Pk,$3;.P,(3<.Vm,R1.)P,(:.+10.(3=.R2.))P,(:.=(3>.R3.))P,(2<.$0.(32.(3?.R4.)+8.)=)P,(40.Vm,Vm',R5.)P,P,(41.(2<.$0.(42.R6.)$43.))(13.(:.(14.(3?.R7.)(44.(3>.R7.)))Vha,)(:.(14.Vha,Vhn,)(3?.R7.)))(3<.Vm',R7.)")
(* [comment removed for export] *).
  Proof.
    (intros k dd_H; ddestruct dd_H as (HD & MG & US); intros RZ N0 U8 dd_H; ddestruct dd_H as (K1 & K2 & K3); intros AQ).
    assert (EH : ck_hdr k = ck_user k - 16) by reflexivity. assert (EU : ck_user k = ck_ab k + ck_rz k) by reflexivity.
    pose proof (Z.div_mod (nfix (ck_n k)) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (nfix (ck_n k)) 8 ltac:(lia)) as MB.
    assert (NF : 1 <= nfix (ck_n k)) by (unfold nfix; lia).
    split; [| split].
    - ddestruct HD as (b1 & id & HC & B13 & B1R & IDR). dexists b1, id. split; [| auto].
      eapply krw; [exact HC|]. eapply kept_sub; [exact K1| rewrite EH, EU; lia| rewrite EH, EU; cbn; lia].
    - intros HRZ. eapply krw; [exact (MG HRZ)|]. eapply kept_sub; [exact K1| lia| cbn; lia].
    - destruct (Z.eqb_spec (ck_st k) CHUNK_ALLOCATED) as [E|NE].
      + destruct US as [Z0 PG]. specialize (K2 E).
        assert (CEIL : (nfix (ck_n k) + 7) / 8 = nfix (ck_n k) / 8 + (if nfix (ck_n k) mod 8 =? 0 then 0 else 1)).
        { pose proof (Z.div_mod (nfix (ck_n k) + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nfix (ck_n k) + 7) 8 ltac:(lia)).
          destruct (Z.eqb_spec (nfix (ck_n k) mod 8) 0); lia. }
        split.
        * eapply krw; [exact Z0|]. eapply kept_sub; [exact K2| lia|].
          cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. rewrite CEIL. destruct (_ =? 0); lia.
        * intros HM8. eapply krw; [exact (PG HM8)|]. eapply kept_sub; [exact K2| |].
          -- unfold shad. replace ((ck_user k + nfix (ck_n k) / 8 * 8) / 8) with (ck_user k / 8 + nfix (ck_n k) / 8) by (rewrite Z.div_add by lia; lia). lia.
          -- cbn [cells_size csize]. unfold shad. replace ((ck_user k + nfix (ck_n k) / 8 * 8) / 8) with (ck_user k / 8 + nfix (ck_n k) / 8) by (rewrite Z.div_add by lia; lia).
             rewrite CEIL. destruct (Z.eqb_spec (nfix (ck_n k) mod 8) 0); lia.
      + ddestruct US as (fc & UC & UW). specialize (K3 NE). exists fc. split; [| exact (wro _ _ UW (AQ NE))].
        eapply krw; [exact UC| exact K3].
  Qed.

  (* [comment removed for export] *)
  #[using="WMO"] Lemma hm_region_o : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "PL,$11.Pc,$0.Pr,$45.Pe,$22.P,(46.Vm,R4.R3.R2.R1.)P,(2:.(:.=(47.R3.))(:.(47.R3.)(48.R3.)))P,(:.(26.+4.(49.R4.))(4:.R4.))P,(4;.Vm,Vm',R7.R6.R5.)P,(13.(:.(14.(4<.R8.R7.)(48.R6.))Vha,)(:.(14.Vha,Vhn,)(4<.R8.R7.)))(46.Vm',R9.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    (intros L c r e HR AUMU NF4 dd_H; ddestruct dd_H as (K1 & K2 & K3 & K4); intros AU). unfold hm_region in *. cbn zeta in *.
    ddestruct HR as (RMX & RNF & RMFA & RAU & R40 & RMU & R56 & R68 & (stw & R72) & (s80 & s88 & R80) & RFA & (js & RJS & JSL) & WRU & SHT & SHF).   (* [comment removed for export] *)
    pose proof (Z.div_mod (r_mapped_user r - r_alloc_user r) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (r_mapped_user r - r_alloc_user r) 8 ltac:(lia)) as MB.
    unfold r_nfreed in *.
    Ltac rk K1 := eapply krw; [eassumption| eapply kept_sub; [exact K1| lia| cbn; lia]].
    split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|]. split; [rk K1|].
    split; [exists stw; rk K1|]. split; [dexists s80, s88; rk K1|].
    split. { eapply ku32; [exact RFA| eapply kept_sub; [exact K2| lia| rewrite length_map; lia]]. }
    split. { exists js. split; [| exact JSL]. eapply ku32; [exact RJS| eapply kept_sub; [exact K2| lia| lia]]. }
    split; [exact (wro _ _ WRU AU)|].
    split. { eapply krw; [exact SHT| eapply kept_sub; [exact K3| lia|]]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
    intros k Hk. eapply krw; [exact (SHF k Hk)| exact (K4 k Hk)].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fake_rep_k : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "PFS,$0.PLF,(1.$4=.)P,(4>.R2.R1.Vm,)P,(:.=R3.)P,(5.Vm,Vm',R4.+9000.)P,PFB,$0.Pn,$0.P,(10.(4?.$0.$0.)(50.$0.$0.R2.R1.)R6.)(5.Vm,Vm',(16.(14.R3.R2.)+8.)+8.)(4>.R6.R5.Vm',)")
(* [comment removed for export] *).
  Proof.
    (intros FS LF dd_H; ddestruct dd_H as (HD & HI & FL & WF & ND); intros F0 K KL). split; [| split; [| split; [| split; [exact WF| exact ND]]]].
    - eapply keep_ro; [exact HD| eapply kept_sub; [exact K| lia| cbn; lia]].
    - intros k Hk. destruct (HI k Hk) as [hh R]. exists hh. pose proof (fsk_geom FS k Hk).
      eapply krw; [exact R| eapply kept_sub; [exact K| lia| cbn; lia]].
    - intros k Hk. ddestruct (FL k Hk) as (fl & U & L & SL). exists fl. pose proof (fsk_geom FS k Hk). split; [| split; [exact L|]].
      + eapply ku8; [exact U|]. rewrite L. eapply kept_sub; [exact K| lia| lia].
      + intros i Hi. ddestruct (SL i Hi) as (b & NTH & Z0 & NZ). exists b. split; [exact NTH|]. split; [exact Z0|].
        intros Hb. destruct (NZ Hb) as [IN R]. split; [exact IN|].
        eapply keep_ro; [exact R| apply (KL _ _ IN)].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hm_ia_k : forall h, hm_ia h m -> iagree ia_ranges m m' -> forall h', h_ia h' = h_ia h -> hm_ia h' m'.
  Proof.
    intros h HI AG h' EI. unfold hm_ia in *. rewrite EI. cbn zeta in *.
    ddestruct HI as (H1 & H2 & H3 & (cs2 & H4 & S4) & (p0 & p1 & H5 & P5) & (cs4 & H6 & S6) & (cs5 & H7 & S7)).
    assert (KZ : forall a n, A_IA <= a -> a + n <= A_IA + 0x81030 -> kept m m' a n).
    { intros a n Ha Hn x Hx. apply AG. unfold A_IA, A_IA_INIT in *. cbn. lia. }
    assert (KI : kept m m' A_IA_INIT 4) by (intros x Hx; apply AG; unfold A_IA, A_IA_INIT in *; cbn; lia).
    unfold A_IA, A_IA_INIT in *.
    split. { eapply krw; [exact H1| exact KI || (apply KZ; cbn; lia)]. }
    split. { eapply krw; [exact H2| first [apply KZ; cbn; lia | exact KI]]. }
    split. { eapply krw; [exact H3| first [apply KZ; cbn [cells_size csize]; rewrite ?Nat.add_0_r, ?Z2Nat.id; lia | exact KI]]. }
    split. { exists cs2. split; [| exact S4]. eapply krw; [exact H4| apply KZ; lia]. }
    split. { dexists p0, p1. split; [| exact P5]. eapply krw; [exact H5| apply KZ; cbn; lia]. }
    split. { exists cs4. split; [| exact S6]. eapply krw; [exact H6| apply KZ; lia]. }
    exists cs5. split; [| exact S7]. eapply krw; [exact H7| apply KZ; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="WMO"] Lemma hm_emb_o : ltac2:(CDefT.buildp (gd_tbl_AW_FreeHMS ()) "Ph,$27.Ph',$27.P,(51.R2.Vm,)P,(2<.$0.(52.(53.R2.))(52.(53.R3.)))P,(2<.$0.(54.(53.R3.))(54.(53.R4.)))P,(1>.$55.Vm,Vm',)P,P,(41.(2<.$0.(52.(53.R6.))=))(13.(:.(14.(52.(53.R7.))$56.)Vha,)(:.(14.Vha,Vhn,)(52.(53.R7.))))(51.R6.Vm',)")
(* [comment removed for export] *).
  Proof.
    (intros h h' dd_H; ddestruct dd_H as (E1 & E2 & E3 & E4); intros EA ES AG AP). unfold hm_emb. rewrite EA, ES. unfold emb_cells.
    assert (K : kept m m' A_EMB 56) by (eapply iagree_kept; [exact AG| vm_compute; reflexivity]).
    split; [eapply krw; [exact E1| eapply kept_sub; [exact K| cbn; lia| cbn; lia]]|].
    split; [eapply krw; [exact E2| eapply kept_sub; [exact K| cbn; lia| cbn; lia]]|].
    split; [eapply krw; [exact E3| eapply kept_sub; [exact K| cbn; lia| cbn; lia]]|].
    intros D0. exact (wro _ _ (E4 D0) (AP D0)).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma RIq_k : forall h C cur,
    RIq h C cur m ->
    kept m m' (l_T (h_L h) + 80) 32 -> iagree quar_img_ranges m m' -> kept m m' C 32 ->
    (forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> kept m m' (b_addr b) 8192) ->
    (match cur with None => True | Some (bc, _) => kept m m' (bn_addr bc) 8192 end) ->
    RIq h C cur m'.
  Proof.
    intros h C cur R KT AG KC KB KBC. unfold RIq in *. cbn zeta in *.
    ddestruct R as (QT & QG & BLG & MTX & QC & BLT & REST).
    assert (KBn : forall b, In b (map bn_of (q_batches (h_tq h))) \/ In b (map bn_of (q_batches (h_gq h))) -> kept m m' (bn_addr b) 8192).
    { intros b Hb. assert (Hb' : In b (map bn_of (q_batches (h_tq h) ++ q_batches (h_gq h)))) by (rewrite map_app; apply in_app_iff; exact Hb).
      apply in_map_iff in Hb'. ddestruct Hb' as (b0 & <- & Hb0). cbn. apply KB. exact Hb0. }
    unfold A_Q_GLOBAL, A_Q_CMUTEX, A_INSTANCE in *. unfold hm_qhead in *.
    split; [eapply krw; [exact QT| exact KT]|].
    split; [eapply krw; [exact QG| eapply iagree_kept; [exact AG| vm_compute; reflexivity]]|].
    split.
    { destruct cur as [[bc i]|].
      - ddestruct REST as (_ & [BOK _] & _). eapply blistT_k; [exact BLG| apply Forall_app in BOK as [B _]; exact B| intros b Hb; apply KBn; right; exact Hb].
      - destruct REST as [BOK _]. eapply blistT_k; [exact BLG| apply Forall_app in BOK as [B _]; exact B| intros b Hb; apply KBn; right; exact Hb]. }
    split; [eapply krw; [exact MTX| eapply iagree_kept; [exact AG| vm_compute; reflexivity]]|].
    split; [eapply krw; [exact QC| eapply kept_sub; [exact KC| lia| cbn; lia]]|].
    destruct cur as [[bc i]|].
    - ddestruct REST as ((nx & N) & BWF & b0 & all & E0 & EA & EE & EL & IL & RNG). pose proof BWF as [BOK _].
      split. { eapply blistT_k; [exact BLT| | intros b Hb; apply KBn; left; rewrite E0; cbn; right; exact Hb].
               apply Forall_app in BOK as [_ B]. inversion B; assumption. }
      split. { exists nx. eapply bnode_at_k; [exact N| apply Forall_app in BOK as [_ B]; inversion B; unfold bn_ok in *; lia| exact KBC]. }
      split; [exact BWF|]. dexists b0, all. repeat split; assumption.
    - destruct REST as [BOK BAP].
      split. { eapply blistT_k; [exact BLT| apply Forall_app in BOK as [_ B]; exact B| intros b Hb; apply KBn; left; exact Hb]. }
      exact (conj BOK BAP).
  Qed.
End Hole.

End ARUN_1.
