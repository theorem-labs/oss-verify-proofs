(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR AW_FreeRB AW_FreeFam AW_FreeRM.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AW_Unwind AW_Unwind2 AW_MmapFixed AW_DepotB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_QPut AW_Enqueue AW_Drain AW_Blist AW_DoRecycle AW_DoRecycle2 AW_Merge AW_Recycle AW_RecLoop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_FakeDefs AW_FakeRep HMLib HM HMFrame AW_FreeHM AW_FreeHMS AW_FreeHMX AW_FreeHMQ AW_MunmapCfg AW_RecStep.
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
Ltac2 gd_tbl_AW_RecTop () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHMX.fkeepR"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.awf'"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.HMq"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_quar"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_K"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_CS"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.in_qs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.qs_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.rp_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.wmono_ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.depot"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "Stdlib.Lists.List.incl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_size"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "ARUN_1.RecTop.rec_post"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.in_blk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeP.WFR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.hgeom"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.BHeap.HMLib.kept"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "Stdlib.Lists.List.flat_map"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_elems"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_addr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bwf"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeRM.bP"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bsum"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMax"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_qhead"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.hd_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.last_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.blist"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.qc_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Drain.qmutex_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Recycle.rec_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "ARUN_1.WRf"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Recycle.A_REC_C"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_base"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMin"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Recycle.A_REC_B"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_Q_GLOBAL"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_Q_CMUTEX"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Drain.A_RECYCLE"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Wn (bs : list bnode) : list (Z * Z) := map (fun b => (bn_addr b, bn_addr b + 8192)) bs.
(* [comment removed for export] *)
Definition WRf (lo SP : Z) (bs : list bnode) : list (Z * Z) := (lo, SP) :: (A_INSTANCE + 880, A_INSTANCE + 920) :: Wn bs.

#[using="Type"] Lemma Wn_outside : forall bs y, outside (Wn bs) y <-> (forall b, In b bs -> ~ (bn_addr b <= y < bn_addr b + 8192)).
Proof.
  intros bs y. unfold Wn. induction bs as [|b bs IH]; cbn.
  - split; [intros _ b F; destruct F| intros _; exact I].
  - split.
    + intros [A B] b' [<-|Hb']; [lia| exact (proj1 IH B b' Hb')].
    + intros H. split; [pose proof (H b ltac:(left; reflexivity)); lia| apply (proj2 IH); intros b' Hb'; apply H; right; exact Hb'].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fkeepR_up : ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "PL,$0.PLBK,(1.(2.$3.$3.))PQS,(1.(2.$3.$3.))PRP,(1.(2.$3.$3.))PNB,(1.$3.)PBL,(1.$3.)Plo,$3.PSP,$3.PSP',$3.PC,$3.Pm,P,(4.&40.)(5.(4.&8.))Pm',P,(4.&40.)(5.(4.&8.))P,(6.R<.R;.R:.(7.(2.$3.$3.)R9.(8.(2.$3.$3.)(9.$3.$3.R3.+20.)(:.(2.$3.$3.))))R8.R7.R6.R5.R2.R1.)P,(;.R6.R5.)P,(;.R8.R5.)P,(;.(<.R6.+20.)R7.)(6.R10.R?.R>.R=.R<.R;.R:.R8.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros L LBK QS RP NB BL lo SP SP' C m m' K LE C0 C1 x. cbv zeta. intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  apply (K x); try assumption.
  - intros R. apply H1. lia.
  - (intros dd_H; ddestruct dd_H as (r & Hr & R)). apply in_app_iff in Hr as [Hr|[<-|[]]]; [apply H10; exists r; exact (conj Hr R)|]. cbn [fst snd] in R. apply H1. lia.
Qed.

Section RecTop.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Variable FF : ffam AL.

  (* [comment removed for export] *)
  Definition rec_post (h : ahst) (m : mem) (lo SP : Z) (LF : list (Z * Z)) (h' : ahst) (m' : mem) (mo' : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "(=.(>.VhAR,O3.)(=.(?.(1.$10.)(11.(12.O3.))(:.$10.))(=.(13.VhAR,O3.O4.O2.)(=.(14.VhAR,O3.O2.)(=.(15.VhAR,VAL,VFF,O3.O1.)(=.(16.O2.O1.)(=.(17.$18.O2.)(=.(19.$18.O2.O6.O5.)(=.Px,$3.P,(1:.VhAR,VAL,VFF,O8.R1.)P,(1;.(1<.(1=.O8.)R2.))(1:.VhAR,VAL,VFF,O3.R3.)(=.(6.(1>.O8.)(1?.O8.)(1=.O8.)(20.O8.)(21.(22.O8.))(23.(22.O8.))O6.O5.O7.O2.)(=.(24.(1=.O8.)O7.O2.)(=.(?.$0.(1>.O3.)(1>.O8.))(=.(?.$25.(22.O3.)(22.O8.))(=.(?.(1.(2.$3.$3.))(1?.O3.)(1?.O8.))(=.(?.$3.(26.O3.)(26.O8.))(=.(?.$27.(28.O3.)(28.O8.))(=.(?.$29.(2:.O3.)(2:.O8.))(=.(?.$3.(2;.O3.)(2;.O8.))(=.(?.$29.(2<.O3.)(2<.O8.))(=.Pc,$3.(?.$3.(2=.(2>.O3.R1.))(2=.(2>.O8.R1.)))(=.Pk,$2?.P,(30.$2?.R1.(31.O3.))(30.$2?.R2.(31.O8.))(=.Psh,$32.P,(30.$32.R1.(33.(34.O3.)))(30.$32.R2.(33.(34.O8.)))(=.(35.(2.$3.$3.)(36.(37.O8.))(36.(37.O3.)))(=.Pk,$2?.P,(30.$2?.R1.(31.O8.))P,(?.$29.(38.R2.)$39.)(3:.(30.$2?.R3.(31.O3.))(30.(2.$3.$3.)(9.$3.$3.(3;.R3.)(3<.R3.))(36.(37.O3.))))Pg,(2.$3.$3.)P,(30.(2.$3.$3.)R1.(36.(37.O3.)))(3:.(30.(2.$3.$3.)R2.(36.(37.O8.)))(3=.$2?.Lk,$2?.(=.(30.$2?.R1.(31.O8.))(=.(?.$29.(38.R1.)$39.)(?.(2.$3.$3.)R3.(9.$3.$3.(3;.R1.)(3<.R1.)))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Section R.
    (* [comment removed for export] *)
    Variables (h : ahst) (ct cg : Z) (m0 : mem) (LF : list (Z * Z)) (SP lo STK : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (Q : config -> Prop)
              (qra q0 q1 q2 q3 q4 s5 s6 s7 s8 s9 s10 s11 : word).
    Let L := h_L h.
    Let T := l_T L.
    Let SPR := SP - 80.
    Let gbs := map bn_of (q_batches (h_gq h)).
    Hypothesis TP : tp = Z_to_bv 64 A_TP.
    Hypothesis WF : WFC h ct cg.
    Hypothesis TQ0 : q_batches (h_tq h) = [].
    Hypothesis HV : h_havol h <= AVOL_MAX.
    Hypothesis H32 : forall k, In k (h_chunks h) -> nfix (ck_n k) < 2^32.
    Hypothesis BWF0 : bwf gbs.
    Hypothesis GB40 : bsum gbs < 2^40.
    Hypothesis LOL : l_stk_lo L <= lo.
    Hypothesis SPL : lo <= SP - 80 - 112 - 736.
    Hypothesis SPH : SP <= l_stk_hi L.
    Hypothesis SPA : SP mod 16 = 0.
    Hypothesis STKB : 0 <= STK < 2^64.
    Hypothesis GEO : hgeom h.
    Hypothesis GNE : q_batches (h_gq h) <> [].
    Hypothesis EXIT : ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "Ph',$3>.Pm',P,(4.&40.)(5.(4.&8.))Pmo',$3?.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa0,(4.&40.)Pa1,(4.&40.)Pa2,(4.&40.)Pa3,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(40.Vh,Vm0,Vlo,VSP,VLF,R12.R11.R10.)(41.$18.VQ,(42.(43.(44.Vqra,(45.&40.VSP,)Vgp,Vtp,R10.R?.R>.Vq0,Vq1,R=.R<.R;.R:.R9.R8.R7.R6.Vq2,Vq3,Vq4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(46.Vqra,)Vfc,(47.(4.&40.))R12.(48.$18.))R11.))")
(* [comment removed for export] *).

    #[using="ct cg WF"] Lemma WL : wf_L L. Proof. ddestruct WF as ((A & _) & _). exact A. Qed.
    #[using="ct cg WF"] Lemma Lf : ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "(=.(;.+10007???9000.(49.VL,))(=.(=.(=.(;.+1000.VT,)(3:.(;.(<.VT,+1000.)+10000.)(;.+65?000.VT,)))(3:.(;.(<.VT,+1000.)+7???7000.)(;.+10007???8000.VT,)))(=.(;.(<.VT,+1000.)(4:.VhAR,))(=.(;.(4:.VhAR,)(4;.VL,))(;.(4<.VL,)(4=.+2.+2?.))))))")
(* [comment removed for export] *).
    Proof.
      pose proof WL as W. destruct (L_GSB L W) as (SB0 & _). ddestruct (L_GT L W) as (T0 & T1 & _).
      dpose W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STK0 & STKH & _).
      exact (conj SB0 (conj T0 (conj T1 (conj STK0 STKH)))).
    Qed.
    #[using="ct cg WF HV"] Lemma WFKh : WFK h. Proof. exact (WFK_of_WFC h ct cg WF HV). Qed.

    (* [comment removed for export] *)
    #[using="hAR ct cg WF TQ0 GEO"] Lemma batches_not_blocks : ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "Pb,$10.Pa,$3.P,(30.$10.R2.(11.(4>.Vh,)))P,(4?.(1?.Vh,)R2.)(1;.(=.(;.(50.R4.)R3.)(51.R3.(<.(50.R4.)+2000.))))")
(* [comment removed for export] *).
    Proof.
      (intros b a Hb dd_H; ddestruct dd_H as (bk & Hbk & Ra); intros R). destruct bk as [B N]. cbn [fst snd] in Ra.
      dpose WF as (WL' & WC & WR & WK & (WT & WGQ & _) & _). pose proof (proj1 WL') as W.
      ddestruct (in_blk_chunk h a B N W WR WK Hbk Ra) as (kb & Hkb & STb & -> & -> & Xb & _).
      assert (Hb' : In b (q_batches (h_tq h) ++ q_batches (h_gq h))) by (apply in_app_iff; right; exact Hb).
      assert (BS : forall b0, In b0 (q_batches (h_tq h) ++ q_batches (h_gq h)) -> exists i, 0 <= i < carved h kBatchClass /\ b_addr b0 = chunk_at (h_L h) kBatchClass i).
      { intros b0 Hb0. rewrite TQ0 in Hb0. cbn [app] in Hb0. destruct WGQ as (G1 & _). destruct (proj1 (Forall_forall _ _) G1 b0 Hb0) as (_ & _ & _ & B4). exact B4. }
      destruct (ext_cases h kb W WR WK Hkb) as [(c' & P' & EC' & C' & RL' & RH' & AUMU')|(i' & sh & P' & N' & EL' & EH')].
      - pose proof (batch_vs_chunk' h WR WK BS kb b Hkb P' Hb') as AP. unfold ext_lo, ext_hi, ck_end in Xb. rewrite P' in Xb. clear - AP Xb R. lia.
      - ddestruct (BS b Hb') as (ib & Hib & EBb). destruct (slot_le h kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2].
        dpose (user_vs_ri h kBatchClass W WR ltac:(unfold kBatchClass; clear; lia)) as (U1 & U2 & _ & U4).
        pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU & _).
        (* [comment removed for export] *)
        pose proof (z_sec_hull h GEO i' _ N') as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y.
        change (class_size kBatchClass) with 8192 in S2. clear - Y EL' EH' Xb R S1 S2 U1 U2 U4 AUMU EBb. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="hAR ct cg SP L T SPR gbs WF BWF0 GB40 GNE"] Lemma cinit_true : q_batches (h_gq h) <> [] -> h_cinit h = true.
    Proof.
      intros NE. destruct (h_cinit h) eqn:CI; [reflexivity| exfalso].
      dpose WF as (_ & _ & _ & _ & (_ & (G1 & _) & _) & _ & _ & _ & _ & (_ & _ & WX3 & _) & _).
      destruct (q_batches (h_gq h)) as [|b l] eqn:E; [exact (NE eq_refl)|].
      destruct (proj1 (Forall_forall _ _) G1 b ltac:(left; reflexivity)) as (_ & _ & _ & (i & Hi & _)).
      unfold carved in Hi. rewrite (WX3 CI kBatchClass ltac:(unfold kBatchClass, kNumClasses; lia)) in Hi.
      change (class_size kBatchClass) with 8192 in Hi. rewrite Z.div_0_l in Hi by (clear; lia). clear - Hi. lia.
    Qed.

    (* [comment removed for export] *)
    #[using="ct cg T WF LOL SPL SPH"] Lemma above_kept : ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "Ph3,$3>.Pm,P,(4.&40.)(5.(4.&8.))Pm',P,(4.&40.)(5.(4.&8.))PRP,(1.(2.$3.$3.))P,(52.VhAR,R4.)P,(53.R5.)P,(?.$0.(1>.R6.)VL,)P,(6.VL,(1?.R7.)(1=.R7.)(7.(2.$3.$3.)(20.R7.)R4.)(21.(22.R7.))(23.(22.R7.))Vlo,VSPR,R6.R5.)P,Pr,(2.$3.$3.)P,(30.(2.$3.$3.)R1.R6.)(;.(<.(54.$3.$3.R2.)(55.$3.$3.R2.))(<.VSPR,+20.))(56.R8.R7.(<.VSPR,+20.)+30.)")
(* [comment removed for export] *).
    Proof.
      intros h3 m m' RP WF3 GEO3 EL3 K HRP x Hx. dpose Lf as (SB0 & (T0 & T1) & T2 & STK0 & STKH).
      dpose WF3 as ((WL3 & _) & _ & _ & (WKF & _ & _) & _ & WS3 & _). rewrite EL3 in WL3. dpose WL3 as (_ & _ & _ & _ & _ & B6d & _).
      pose proof (z_T_stk h3 GEO3) as Y1. pose proof (z_hull_stk h3 GEO3) as Y2. pose proof (z_pa_stk h3 GEO3) as Y3.
      unfold zapart in Y1, Y2, Y3. cbn [fst snd] in Y1, Y2, Y3. rewrite EL3 in Y1, Y2, Y3. pose proof aceil_bounds as ACB.
      apply (K x); cbv zeta.
      - subst SPR. clear - Hx. lia.
      - clear - Hx Y1 LOL SPL SPH; subst SPR L; lia.
      - intros [IH _]. unfold in_hull in IH. clear - Hx Y2 LOL SPL SPH IH; subst SPR L; lia.
      - intros [SH _]. unfold shad in SH. clear - Hx SH LOL SPL SPH STK0 B6d ACB; subst SPR L; lia.
      - (intros dd_H; ddestruct dd_H as (q & Hq & R)). unfold qs_of in Hq. apply in_map_iff in Hq. ddestruct Hq as (kq & <- & Hkq). apply filter_In in Hkq as [Hkq Pq].
        apply andb_prop in Pq as [Pq _]. apply Bool.negb_true_iff in Pq. cbn [fst snd] in R.
        pose proof (proj1 (Forall_forall _ _) WKF kq Hkq) as (_ & _ & _ & Xq). rewrite Pq in Xq.
        ddestruct Xq as (iq & Nq & _ & _ & CEILq & _). pose proof (z_sec_stk h3 GEO3 iq _ Nq) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. rewrite EL3 in Y.
        unfold shad in R. clear - Hx R Y LOL SPL SPH STK0 CEILq ACB; subst SPR L; lia.
      - unfold free_img_ranges, A_INSTANCE, A_IA, A_IA_INIT. cbn. clear - Hx LOL SPL STK0 ACB; subst SPR L; lia.
      - (intros dd_H; ddestruct dd_H as (b & Hb & R)). destruct (In_nth_error _ _ Hb) as [jb Hjb]. pose proof (z_node_stk h3 GEO3 jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL3 in Y.
        clear - Hx R Y LOL SPL SPH; subst SPR L; lia.
      - (intros dd_H; ddestruct dd_H as (b & Hb & R)). destruct (In_nth_error _ _ Hb) as [jb Hjb]. pose proof (z_store_stk h3 GEO3 jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL3 in Y.
        clear - Hx R Y LOL SPL SPH; subst SPR L; lia.
      - clear - Hx Y3 LOL SPL SPH; subst SPR L; lia.
      - (intros dd_H; ddestruct dd_H as (r & Hr & R)). apply in_app_iff in Hr. destruct Hr as [Hr|Hr]; [| pose proof (HRP r Hr) as X; clear - R Hx X; subst SPR; lia].
        unfold rp_of in Hr. apply in_map_iff in Hr. ddestruct Hr as (sh & <- & Hsh). cbn [fst snd] in R.
        destruct (In_nth_error _ _ Hsh) as [ish Nsh]. pose proof (z_sec_stk h3 GEO3 ish _ Nsh) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL3 in Y.
        dpose WS3 as (_ & _ & _ & _ & _ & _ & _ & WS8). pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & M4 & _).
        clear - Hx R Y LOL SPL SPH M4; subst SPR L; lia.
    Qed.

    (* [comment removed for export] *)
    #[using="IMG ALWF ASB ct cg TP WF TQ0 HV H32 BWF0 GB40 LOL SPL SPH SPA STKB GEO GNE EXIT"] Lemma rec_from_C : ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "PG,(1.$57.)PX,(1.$57.)Pgs1,(1.$57.)Pgs2,(1.$57.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$3?.PMIN,$3.Pra,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(?.(1.(4.&40.))(58.$57.(4.&40.)$59.R18.)(58.$57.(4.&40.)$59.Vgbs,))P,(?.(1.(4.&40.))(58.$57.(4.&40.)$59.R18.)(:.(4.&40.)))P,Pb',$57.P,(30.$57.R1.(7.$57.R1:.R1;.))(3=.$57.Lb,$57.(=.(30.$57.R1.Vgbs,)(?.$3.(5:.R3.)(5:.R1.))))P,(?.$5;.(5<.$57.(7.$57.R1:.R1;.))(5<.$57.Vgbs,))P,(5=.VhAR,(7.$57.R1;.R1<.))P,(5>.$57.(5?.Vh,)R1=.)P,(?.(1.$57.)R1>.(7.$57.R1<.R1;.))P,(;.(60.R1<.)$61.)P,(?.$3.(<.(60.R1?.)(60.R20.))(60.Vgbs,))P,(15.VhAR,VAL,VFF,Vh,R1<.)P,(16.R1>.R1=.)P,(17.$18.R1?.)P,(13.VhAR,Vh,VLF,R20.)P,(62.R21.(<.VT,+50.)(:.$57.))P,(63.$18.R22.(<.$64.+378.)(8.$65.(66.(45.&40.(67.(5<.$57.R23.))))(8.$65.(66.(45.&40.(68.R23.)))(8.$65.(66.(45.&40.(69.=R23.)))(8.$65.(66.(45.&40.(60.R23.)))(:.$65.))))))P,(6:.R23.R24.)P,(6:.R24.(7.$57.R27.R26.))P,(63.$18.R25.VSPR,(6;.(67.(5<.$57.(7.$57.R28.R27.)))(68.(7.$57.R28.R27.))(69.=(7.$57.R28.R27.))(60.(7.$57.R28.R27.))))P,(63.$18.R26.(<.$64.+370.)(6<.+1.+1.))P,(6=.R27.VSPR,Vq4,Vq3,Vq2,Vq1,Vq0,Vqra,)P,(19.$18.R28.Vlo,VSPR,)P,(6>.(6?.Vlo,VSP,Vgbs,)Vm0,R29.)P,(70.$18.Vm0,R2:.)(41.$18.VQ,(42.(43.(44.R28.(45.&40.VSPR,)Vgp,Vtp,R22.R21.R20.R27.R26.(45.&40.(<.$64.+2=8.))(45.&40.R29.)(45.&40.(<.VT,+=0.))(45.&40.VSTK,)R1?.R1>.R1=.R1<.R25.R24.R23.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1;.R1:.R19.R18.)VF,(45.&40.$71.)Vfc,(47.(4.&40.))R2;.(48.$18.))R2:.))")
(* [comment removed for export] *).
    Proof.
      intros G X gs1 gs2 m mo MIN ra s0 s1 s2 s3 s4 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6
        FM FT ADDR LEN BWF PG EG CAP SUM HK HJ MI HMQ QT QG BLG BLT TMP MTX FR ST MU0 WM0.
      dpose Lf as (SB0 & (T0 & T1) & T2 & STK0 & STKH). pose proof aceil_bounds as ACB.
      dpose WF as (WL' & WC & WR & WK & (WT & WGQ & NDA & UQ) & WS & WD & WB & WBIG & WX & WG). pose proof (proj1 WL') as W.
      set (h3 := h_rq h X gs1 gs2).
      pose proof (WFR_rq h ct cg G X gs1 gs2 WF TQ0 FM FT ADDR LEN BWF PG EG CAP) as WF3. fold h3 in WF3.
      assert (GEO3 : hgeom h3) by (unfold hgeom; unfold h3; rewrite (rq_hzones h X gs1 gs2); exact GEO).
      pose proof (cinit_true GNE) as CI.
      assert (SPRA : SPR mod 16 = 0).
      { subst SPR. replace (SP - 80) with (SP + (-5) * 16) by (clear; lia). rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by (clear; lia). exact SPA. }
      pose proof (bwf_app_l _ _ BWF) as BWFX. pose proof (bwf_app_r _ _ BWF) as BWFG. rewrite EG in BWFG. pose proof (bwf_app_r _ _ BWFG) as BWF2. pose proof (bwf_app_l _ _ BWFG) as BWF1.
      pose proof (bsum_nonneg _ (proj1 BWFX)) as X0. pose proof (bsum_nonneg _ (proj1 BWF1)) as G10. pose proof (bsum_nonneg _ (proj1 BWF2)) as G20.
      pose proof SUM as SUM'. rewrite EG, bsum_app in SUM'.
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo (ff_kinv AL FF h) HK); [exact HJ| |].
      { eapply (rec_C AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 STK) a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SPR MIN F fc m); [subst SPR; clear - SPL LOL STK0 ACB; lia| subst SPR; clear - SPH STKH; lia| exact MTX| exact MI]. }
      cbn beta. intros ms1 mo1 P1 HK1 MM1 HJ1. ddestruct P1 as (m1 & MU1 & WM1 & MI1 & MTX1 & ->).
      assert (KO1 : forall A n, (A + n <= A_INSTANCE + 880 \/ A_INSTANCE + 884 <= A) -> kept m m1 A n).
      { intros A n D. apply (kept_of_munch _ m m1 A n MU1). cbn. split; [exact D| exact I]. }
      (* [comment removed for export] *)
      assert (QT1 : hm_qhead m1 (T + 80) []).
      { unfold hm_qhead in *. eapply krw; [exact QT| apply KO1; cbn; unfold A_INSTANCE; subst T L; clear - T0; lia]. }
      assert (QG1 : rw_cells asegs m1 (A_INSTANCE + 888) [C8 (Z_to_bv 64 (Z.of_nat (length gs2))); C8 (Z_to_bv 64 (hd_addr gs2)); C8 (Z_to_bv 64 (last_addr 0 gs2)); C8 (Z_to_bv 64 (bsum gs2))]).
      { eapply krw; [exact QG| apply KO1; cbn; clear; lia]. }
      assert (NODEK : forall b, In b (X ++ G) -> kept m m1 (bn_addr b) 8192).
      { intros b Hb. pose proof (bwf_ok_in _ _ BWF Hb) as OK. unfold bn_ok in OK. apply KO1. unfold A_INSTANCE. clear - OK; lia. }
      assert (BLG1 : blist m1 gs2).
      { unfold blist in *. eapply blistT_k; [exact BLG| exact (proj1 BWF2)| intros b Hb; apply NODEK; rewrite EG; apply in_app_iff; right; apply in_app_iff; right; exact Hb]. }
      assert (BLT1 : blist m1 (X ++ gs1)).
      { unfold blist in *. eapply blistT_k; [exact BLT| rewrite EG, app_assoc in BWF; exact (proj1 (bwf_app_l _ _ BWF))| intros b Hb; apply NODEK; rewrite EG, app_assoc; apply in_app_iff; left; exact Hb]. }
      assert (TMP1 : rw_cells asegs m1 SPR (qc_cells (Z.of_nat (length (X ++ gs1))) (hd_addr (X ++ gs1)) (last_addr 0 (X ++ gs1)) (bsum (X ++ gs1)))).
      { eapply krw; [exact TMP| apply KO1; cbn; unfold A_INSTANCE; subst SPR; clear - SPL LOL STK0 ACB; lia]. }
      assert (FR1 : rec_frame m1 SPR q4 q3 q2 q1 q0 qra).
      { unfold rec_frame in *. eapply krw; [exact FR| apply KO1; cbn; unfold A_INSTANCE; subst SPR; clear - SPL LOL STK0 ACB; lia]. }
      assert (ST1 : stk asegs m1 lo SPR) by (apply (stk_keep h 0 _ m m1 lo SPR ST MU1 WM1); clear - LOL STK0 ACB; lia).
      assert (HMQ1 : HMq h3 LF m1).
      { assert (HMQ1' : HMq h LF m1); [| exact HMQ1'].
        assert (BS : forall b0, In b0 (q_batches (h_tq h) ++ q_batches (h_gq h)) -> exists i, 0 <= i < carved h kBatchClass /\ b_addr b0 = chunk_at (h_L h) kBatchClass i).
        { intros b0 Hb0. rewrite TQ0 in Hb0. cbn [app] in Hb0. destruct WGQ as (G1 & _). destruct (proj1 (Forall_forall _ _) G1 b0 Hb0) as (_ & _ & _ & B4). exact B4. }
        apply (HMq_keepQ h m m1 LF WL' WR WK WS WD GEO BS WM1); [| exact HMQ].
        intros A n NZ x Hx. apply MU1. cbn. split; [| exact I]. intros R. apply (NZ (bv_unsigned x) Hx). right; left.
        unfold quar_img_ranges, A_INSTANCE in *. cbn. clear - R; lia. }
      assert (RQ1 : RIq h3 SPR None m1).
      { unfold RIq. cbn zeta. unfold h3. rewrite (rq_L h X gs1 gs2), (rq_gq_bn h X gs1 gs2), (rq_tq_bn h X gs1 gs2). fold L T.
        split; [exact QT1|]. split; [unfold hm_qhead, A_Q_GLOBAL; exact QG1|]. split; [exact BLG1|].
        split; [unfold A_Q_CMUTEX; unfold qmutex_cells in MTX1; exact MTX1|]. split; [exact TMP1|]. split; [exact BLT1|].
        eapply bwf_of_perm; [exact BWF| | ].
        - rewrite EG, !map_app. rewrite app_assoc. apply Permutation_app_comm.
        - rewrite Forall_app. split; [exact (proj1 BWF2)| rewrite EG, app_assoc in BWF; exact (proj1 (bwf_app_l _ _ BWF))]. }
      (* [comment removed for export] *)
      replace (Z_to_bv 64 (T + 208)) with (Z_to_bv 64 (l_T (h_L h3) + 208)) by (unfold h3; rewrite (rq_L h X gs1 gs2); reflexivity).
      apply (do_recycle AL IMG ALWF ASB FF h3 m1 LF SPR SPR lo STK s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (Z_to_bv 64 A_REC_D) gp tp F fc Q mo1
               t0 t1 t2 (Z_to_bv 64 (A_INSTANCE + 728)) a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 TP WF3 GEO3).
      - clear; lia.
      - unfold h3. rewrite (rq_L h X gs1 gs2). fold L. subst SPR. clear - SPH; lia.
      - unfold h3. rewrite (rq_L h X gs1 gs2). exact LOL.
      - subst SPR. clear - SPL; lia.
      - exact SPRA.
      - exact STKB.
      - unfold h3. rewrite (rq_havol h X gs1 gs2). exact HV.
      - unfold h3. rewrite (rq_cinit h X gs1 gs2). exact CI.
      - exact HMQ1.
      - exact RQ1.
      - exact (ff_view_K AL FF h h3 mo1 (kview_rq h X gs1 gs2) HK1).
      - cbn [ms_mem] in HJ1. exact HJ1.
      - exact MI1.
      - exact ST1.
      - unfold h3. rewrite (rq_chunks h X gs1 gs2). exact H32.
      - unfold h3. rewrite (rq_tq_bn h X gs1 gs2). rewrite bsum_app. clear - SUM' GB40 X0 G10 G20. lia.
      - (* [comment removed for export] *)
        unfold exit_cont. intros hE mE moE x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 LIX TQE RQE STE.
        dpose LIX as (WFE & HVE & CIE & HMQE & HKE & HJE & MIE & SUBK & SUBS & CSR & FK & WMX & ELE & EGE & EDE & EBE & LSE & H32E).
        ddestruct LSE as (V1 & V2 & V3 & V4 & V5 & VR & V6 & V7 & V8).
        assert (ELE' : h_L hE = L) by (rewrite ELE; unfold h3; apply (rq_L h X gs1 gs2)).
        assert (GEOE : hgeom hE) by (exact (ff_geom AL FF hE moE (WFK_of_WFR hE WFE HVE) HKE)).
        pose proof RQE as R. unfold RIq in R. cbn zeta in R. rewrite TQE, ELE' in R. cbn [map length Z.of_nat hd_addr hd_addrT last_addr bsum] in R.
        ddestruct R as (QTE & QGE & BLGE & MTXE & QCE & _ & BWFE).
        assert (FRE : rec_frame mE SPR q4 q3 q2 q1 q0 qra).
        { unfold rec_frame in *. eapply krw; [exact FR1|]. cbn [cells_size csize Nat.add].
          apply (above_kept h3 m1 mE [(SPR, 32)] WF3 GEO3 ltac:(unfold h3; apply (rq_L h X gs1 gs2))).
          - exact FK.
          - intros r [<-|[]]. cbn. clear; lia. }
        replace (ret_pc (Z_to_bv 64 A_REC_D)) with (Z_to_bv 64 A_REC_D) by (symmetry; apply ret_pc_even; [unfold A_REC_D; clear; lia| reflexivity]).
        eapply (evtA_aevtS_KJ AL (ff_CS AL FF hE) (ff_K AL FF hE) _ Q _ moE (ff_kinv AL FF hE) HKE); [exact HJE| |].
        { eapply (rec_D AL IMG ALWF (ff_CS AL FF hE) (ff_csok AL FF hE) gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 0) y1 y2 y3 y4 y5 y6 y7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6
                    q4 q3 q2 q1 q0 qra _ _ _ _ SPR lo F fc mE);
            [subst SPR; clear - SPL LOL STK0 ACB; lia| subst SPR; clear - SPH STKH; lia| unfold qc_cells in QCE; exact QCE| exact FRE| exact STE
            | clear - LOL STK0; lia| subst SPR; clear - SPL; lia| | exact MIE].
          apply (ff_cs_stack AL FF hE lo (SPR + 80 - lo) (WFK_of_WFR hE WFE HVE)); rewrite ELE'; [exact LOL| subst SPR; clear - SPH; lia]. }
        cbn beta. intros ms2 mo2 P2 HK2 MM2 HJ2. ddestruct P2 as (m2 & MU2 & WM2 & MI2 & ST2 & ->).
        replace (SPR + 80) with SP in * by (subst SPR; clear; lia).
        assert (KO2 : forall A n, (A + n <= lo \/ SP <= A) -> kept mE m2 A n).
        { intros A n D. apply (kept_of_munch _ mE m2 A n MU2). cbn. split; [exact D| exact I]. }
        dpose WFE as (WLE' & _ & WRE & WKE & WQE & WSE & WDE & _). pose proof (proj1 WLE') as WLE.
        assert (BSE : forall b0, In b0 (q_batches (h_tq hE) ++ q_batches (h_gq hE)) -> exists i, 0 <= i < carved hE kBatchClass /\ b_addr b0 = chunk_at (h_L hE) kBatchClass i).
        { intros b0 Hb0. exact (batch_slot hE b0 WFE Hb0). }
        (* [comment removed for export] *)
        pose proof (z_hull_stk hE GEOE) as ZHE. pose proof (z_T_stk hE GEOE) as ZTE. unfold zapart in ZHE, ZTE. cbn [fst snd] in ZHE, ZTE. rewrite ELE' in ZHE, ZTE.
        assert (GQK : forall b, In b (map bn_of (q_batches (h_gq hE))) -> kept mE m2 (bn_addr b) 8192).
        { intros b Hb. apply in_map_iff in Hb as (b0 & <- & Hb0). cbn [bn_addr bn_of].
          ddestruct (BSE b0 ltac:(apply in_app_iff; right; exact Hb0)) as (ib & Hib & EBb). rewrite ELE' in EBb.
          pose proof WRE as WRE'. destruct (slot_le hE kBatchClass ib WRE ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2]. rewrite ELE' in S1, S2.
          dpose (user_vs_ri hE kBatchClass WLE WRE ltac:(unfold kBatchClass; clear; lia)) as (U1 & U2 & _ & U4). rewrite ELE' in U1, U2, U4.
          pose proof (WRE kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as XX. cbn zeta in XX. ddestruct XX as (_ & AUMU & _).
          change (class_size kBatchClass) with 8192 in S2.
          apply KO2. clear - EBb S1 S2 U1 U2 U4 AUMU ZHE LOL SPH. lia. }
        apply (EXIT (h_rx hE) m2 mo2).
        split; [exact (awf'_rx hE WFE TQE)|]. split; [reflexivity|].
        split. { change (HMq (h_rx hE) LF m2) with (HMq hE LF m2).
                 apply (HMq_keepQ hE mE m2 LF WLE' WRE WKE WSE WDE GEOE BSE WM2); [| exact HMQE].
                 intros A n NZ x Hx. apply MU2. cbn. split; [| exact I]. intros R. apply (NZ (bv_unsigned x) Hx). left. rewrite ELE'. clear - R LOL SPH; lia. }
        split. { unfold hm_quar. cbn zeta. change (h_L (h_rx hE)) with (h_L hE). change (h_gq (h_rx hE)) with (h_gq hE). cbn [h_rx set_tq h_tq q_batches q_bytes qcache0 map].
                 rewrite ELE'. rewrite app_nil_r in BWFE.
                 split. { unfold hm_qhead in *. eapply krw; [exact QTE|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
                          apply KO2. subst T L. clear - ZTE LOL SPH. lia. }
                 split; [exact I|].
                 split; [unfold hm_qhead, A_Q_GLOBAL, A_INSTANCE in *; eapply krw; [exact QGE| apply KO2; cbn; clear - LOL STK0 ACB; lia]|].
                 split; [unfold blist in *; eapply blistT_k; [exact BLGE| exact (proj1 BWFE)| exact GQK]|].
                 split; [cbn [app]; exact BWFE|].
                 split; [unfold A_Q_CMUTEX, A_INSTANCE in *; eapply krw; [exact MTXE| apply KO2; cbn; clear - LOL STK0 ACB; lia]|].
                 split; [reflexivity|].
                 rewrite EGE. unfold h3. rewrite (rq_gqb h X gs1 gs2), (rq_gq_bn h X gs1 gs2). reflexivity. }
        split; [exact (ff_view_K AL FF hE (h_rx hE) mo2 (kview_rx hE) HK2)|].
        split; [cbn [ms_mem] in HJ2; exact HJ2|].
        split; [exact MI2|]. split; [exact ST2|].
        split. { intros x Hx NQ. apply (ff_view_CS AL FF hE (h_rx hE) x (kview_rx hE)). apply CSR; [exact (ff_view_CS AL FF h h3 x (kview_rq h X gs1 gs2) Hx)| exact NQ]. }
        split. { (* [comment removed for export] *)
          assert (FK' : fkeepR L (blocks h) (qs_of h) (rp_of h) (d_nb (h_dep h)) (d_bl (h_dep h)) lo SP m1 mE).
          { apply (fkeepR_up L (blocks h) (qs_of h) (rp_of h) (d_nb (h_dep h)) (d_bl (h_dep h)) lo SPR SP SPR m1 mE); [exact FK| subst SPR; clear; lia| subst SPR; clear - SPL; lia| subst SPR; clear; lia]. }
          eapply fkeepR_trans; [| eapply fkeepR_trans; [| eapply fkeepR_trans; [exact FK'| | apply incl_refl| apply incl_refl]| apply incl_refl| apply incl_refl]| apply incl_refl| apply incl_refl].
          - (* [comment removed for export] *)
            apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m0 m MU0). unfold WRf. apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; exact Ha|].
            apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; do 5 right; left; unfold free_img_ranges; cbn; clear - Ha; lia|].
            unfold Wn. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & Hb). intros a Ha. cbn [fst snd] in Ha.
            unfold gbs in Hb. apply in_map_iff in Hb as (b0 & <- & Hb0). cbn [bn_addr bn_of] in Ha.
            do 2 right; left. split.
            + destruct WGQ as (G1 & _). destruct (proj1 (Forall_forall _ _) G1 b0 Hb0) as (_ & _ & _ & (ib & Hib & EBb)).
              destruct (slot_le h kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2].
              dpose (user_vs_ri h kBatchClass W WR ltac:(unfold kBatchClass; clear; lia)) as (U1 & U2 & _ & U4).
              pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as XX. cbn zeta in XX. ddestruct XX as (_ & AUMU & _).
              change (class_size kBatchClass) with 8192 in S2. unfold in_hull. subst L. clear - Ha EBb S1 S2 U1 U2 U4 AUMU. lia.
            + intros IB. exact (batches_not_blocks b0 a Hb0 IB Ha).
          - apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m m1 MU1). apply Forall_cons; [| apply Forall_nil]. intros a Ha. cbn [fst snd] in Ha. do 5 right; left. unfold free_img_ranges; cbn; clear - Ha; lia.
          - apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ mE m2 MU2). apply Forall_cons; [| apply Forall_nil]. intros a Ha. cbn [fst snd] in Ha. left. exact Ha. }
        split. { eapply wmono_ex_trans; [exact (wmono_ex_of_wmono _ m0 m WM0)|]. eapply wmono_ex_trans; [exact (wmono_ex_of_wmono _ m m1 WM1)|].
                 eapply wmono_ex_trans; [exact WMX| exact (wmono_ex_of_wmono _ mE m2 WM2)]. }
        split; [cbn; exact ELE'|]. split; [cbn; rewrite EDE; reflexivity|].
        split; [rewrite (blocks_of_chunks hE (h_rx hE) eq_refl), EBE; reflexivity|].
        split; [cbn; rewrite V1; reflexivity|]. split; [cbn; rewrite V2; reflexivity|]. split; [cbn; rewrite V3; reflexivity|].
        split; [cbn; rewrite V4; reflexivity|]. split; [cbn; rewrite V5; reflexivity|].
        split; [intros c0; cbn; exact (VR c0)|].
        split; [intros k Hk; exact (SUBK k Hk)|]. split; [intros sh Hsh; exact (SUBS sh Hsh)|].
        split; [exact V6|]. split; [exact V7| exact V8].
    Qed.

    (* [comment removed for export] *)
    #[using="ct cg WF HV"] Lemma node_cs : ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "PG,(1.$57.)PX,(1.$57.)Pb,$57.P,Pb',$57.P,(30.$57.R1.(7.$57.R3.R4.))(3=.$57.Lb0,$57.(=.(30.$57.R1.Vgbs,)(?.$3.(5:.R3.)(5:.R1.))))P,(30.$57.R2.(7.$57.R3.R4.))(=.(72.(1:.VhAR,VAL,VFF,Vh,)(5:.R3.)+2000.)(=.(;.(73.VL,)(5:.R3.))(;.(<.(5:.R3.)+2000.)(74.VL,))))")
(* [comment removed for export] *).
    Proof.
      intros G X b ADDR Hb. ddestruct (ADDR b Hb) as (b1 & Hb1 & E). unfold gbs in Hb1. apply in_map_iff in Hb1 as (b0 & <- & Hb0). cbn [bn_addr bn_of] in E.
      dpose WF as (WL' & WC & WR & WK & (WT & (G1 & _) & _) & _).
      destruct (proj1 (Forall_forall _ _) G1 b0 Hb0) as (_ & _ & _ & (ib & Hib & EBb)).
      destruct (slot_le h kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2].
      dpose (user_vs_ri h kBatchClass (proj1 WL') WR ltac:(unfold kBatchClass; clear; lia)) as (U1 & U2 & _ & U4).
      pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as XX. cbn zeta in XX. ddestruct XX as (_ & AUMU & _).
      change (class_size kBatchClass) with 8192 in S2. rewrite E, EBb.
      split; [| subst L; clear - S1 S2 U1 U2 U4 AUMU; lia].
      eapply crange_sub; [apply (ff_cs_user AL FF h kBatchClass WFKh); unfold kBatchClass; clear; lia| clear - S1; lia| clear - S2 AUMU; lia].
    Qed.

    (* [comment removed for export] *)
    #[using="IMG ALWF ASB ct cg TP WF TQ0 HV H32 BWF0 GB40 LOL SPL SPH SPA STKB GEO GNE EXIT"] Lemma rec_from_B : ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "PG,(1.$57.)PX,(1.$57.)Pm,P,(4.&40.)(5.(4.&8.))Pmo,$3?.PTL,$3.Ptf,(4.&40.)Pra,(4.&40.)Ps0,(4.&40.)Ps1,(4.&40.)Ps2,(4.&40.)Ps3,(4.&40.)Ps4,(4.&40.)Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(?.(1.(4.&40.))(58.$57.(4.&40.)$59.R16.)(58.$57.(4.&40.)$59.Vgbs,))P,(?.(1.(4.&40.))(58.$57.(4.&40.)$59.R16.)(:.(4.&40.)))P,Pb',$57.P,(30.$57.R1.(7.$57.R18.R19.))(3=.$57.Lb,$57.(=.(30.$57.R1.Vgbs,)(?.$3.(5:.R3.)(5:.R1.))))P,(?.$5;.(5<.$57.(7.$57.R18.R19.))(5<.$57.Vgbs,))P,(5=.VhAR,(7.$57.R19.R1:.))P,(5>.$57.(5?.Vh,)R1;.)P,(?.$3.(<.(60.R1;.)(60.R1<.))(60.Vgbs,))P,(15.VhAR,VAL,VFF,Vh,R1:.)P,(16.R1<.R1;.)P,(17.$18.R1=.)P,(13.VhAR,Vh,VLF,R1>.)P,(62.R1?.(<.VT,+50.)(:.$57.))P,(63.$18.R20.(<.$64.+378.)(8.$65.(66.(45.&40.(67.(5<.$57.R22.))))(8.$65.(66.(45.&40.(68.R22.)))(8.$65.(66.(45.&40.(69.=R22.)))(8.$65.(66.(45.&40.(60.R22.)))(:.$65.))))))P,(6:.R21.R23.)P,(6:.R22.R23.)P,(63.$18.R23.VSPR,(8.$65.(66.(45.&40.(67.(5<.$57.R24.))))(8.$65.(66.R20.)(8.$65.(66.(45.&40.R21.))(8.$65.(66.(45.&40.(60.R24.)))(:.$65.))))))P,P,(1;.(?.(1.$57.)R25.(:.$57.)))(=.(?.$3.R23.(69.=R26.))(?.(4.&40.)R22.(45.&40.(68.R26.))))P,P,(?.(1.$57.)R26.(:.$57.))(=.(?.$3.R24.=)(?.(4.&40.)R23.(45.&40.=)))P,(=.(;.=R24.)(51.R24.(4=.+2.+40.)))P,(63.$18.R27.(<.$64.+370.)(6<.+1.+1.))P,(6=.R28.VSPR,Vq4,Vq3,Vq2,Vq1,Vq0,Vqra,)P,(19.$18.R29.Vlo,VSPR,)P,(6>.(6?.Vlo,VSP,Vgbs,)Vm0,R2:.)P,(70.$18.Vm0,R2;.)(41.$18.VQ,(42.(43.(44.R28.(45.&40.VSPR,)Vgp,Vtp,R22.R21.R20.R27.R26.(45.&40.(<.$64.+2=8.))(45.&40.$75.)(45.&40.(<.VT,+=0.))(45.&40.VSTK,)R1?.R1>.(45.&40.(67.(5<.$57.R2>.)))R1=.R25.R24.R23.Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R1<.R1;.R1:.R19.)VF,(45.&40.$76.)Vfc,(47.(4.&40.))R2<.(48.$18.))R2;.))")
(* [comment removed for export] *).
    Proof.
      intros G X m mo TL tf ra s0 s1 s2 s3 s4 t0 t1 t2 a4 a5 a7 t3 t4 t5 t6
        FM FT ADDR LEN BWF PG SUM HK HJ MI HMQ QT QG BLG BLX TMP TLD TL0 TLB MTX FR ST MU0 WM0.
      dpose Lf as (SB0 & (T0 & T1) & T2 & STK0 & STKH). pose proof aceil_bounds as ACB.
      dpose WF as (WL' & WC & WR & WK & (WT & WGQ & NDA & UQ) & WS & WD & WB & WBIG & WX & WG). pose proof (proj1 WL') as W.
      pose proof (bwf_app_l _ _ BWF) as BWFX. pose proof (bwf_app_r _ _ BWF) as BWFG.
      pose proof (bsum_nonneg _ (proj1 BWFX)) as X0. pose proof (bsum_nonneg _ (proj1 BWFG)) as G0.
      assert (LENB : Z.of_nat (length (X ++ G)) < 2^40).
      { pose proof GB40 as GB. pose proof (bsum_ge gbs (proj1 BWF0)) as BG. rewrite LEN. unfold gbs in GB, BG |- *. rewrite length_map in *. clear - BG GB. lia. }
      assert (HDG : 0 <= hd_addr G < 2^64).
      { destruct G as [|g0 gr]; [cbn; clear; lia|]. pose proof (bwf_ok_in _ _ BWFG ltac:(left; reflexivity)) as OK. unfold bn_ok in OK. cbn. clear - OK ACB. lia. }
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo (ff_kinv AL FF h) HK); [exact HJ| |].
      { eapply (rec_B AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) ra gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 STK) a4 a5 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 tf (Z_to_bv 64 (last_addr 0 G)) SPR kQuarantineMin (Z.of_nat (length G)) (hd_addr G) (bsum G)
                  (Z.of_nat (length X)) TL (bsum X) F fc m);
          [unfold kQuarantineMin; clear; lia| clear - G0 X0 SUM GB40; lia| exact HDG| rewrite length_app, Nat2Z.inj_add in LENB; clear - LENB; lia| exact TLB
          | subst SPR; clear - SPL LOL STK0 ACB; lia| subst SPR; clear - SPH STKH; lia| exact QG| exact TMP| | exact MI].
        apply (ff_cs_stack AL FF h SPR 80 WFKh); [subst SPR L; clear - SPL LOL; lia| subst SPR L; clear - SPH; lia]. }
      cbn beta. intros ms1 mo1 P1 HK1 MM1 HJ1.
      destruct P1 as [(LT & t1' & t2' & ->)|(GE & t0' & u1' & u2' & a4' & a5' & a6' & a7' & ->)].
      - (* [comment removed for export] *)
        eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo1 (ff_kinv AL FF h) HK1); [exact HJ1| |].
        { eapply (rec_pop AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) G X ra gp tp t1' t2' s0 s1 (Z_to_bv 64 (T + 208)) (Z_to_bv 64 STK) (Z_to_bv 64 (bsum G))
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 (last_addr 0 G)) (Z_to_bv 64 (Z.of_nat (length X))) tf (Z_to_bv 64 TL)
                    SPR kQuarantineMin (Z.of_nat (length X)) TL (Z.of_nat (length G)) (bsum G) (bsum X) lo (Wn gbs) F fc m m);
            first [ reflexivity | exact BWF | exact QG | exact BLG | exact BLX | exact TMP | exact ST | exact MI | apply munch_refl | apply wmono_refl
                  | idtac ].
          + unfold kQuarantineMin in *. clear - LT; lia.
          + pose proof GB40 as GB. unfold gbs in GB, SUM. clear - G0 X0 SUM GB; lia.
          + exact LENB.
          + exact TLB.
          + intros b Hb. exact (proj1 (node_cs G X b ADDR Hb)).
          + intros b x Hb OUT R. ddestruct (ADDR b Hb) as (b1 & Hb1 & E). apply (proj1 (Wn_outside gbs x) OUT b1 Hb1). rewrite <- E. clear - R; lia.
          + intros NZ. apply TLD. intros E. apply NZ. rewrite E. reflexivity.
          + clear - STK0 LOL; lia.
          + subst SPR; clear - SPL; lia.
          + subst SPR; clear - SPH STKH; lia.
          + apply (ff_cs_stack AL FF h lo (SPR + 80 - lo) WFKh); [exact LOL| subst SPR L; clear - SPH; lia]. }
        cbn beta. intros ms2 mo2 P2 HK2 MM2 HJ2. unfold pop_post in P2.
        ddestruct P2 as (m2 & gs1 & gs2 & x0 & x1 & x2 & y4 & y5 & y6 & y7 & EG & NE1 & CAP & MU2 & WM2 & MI2 & QG2 & BLG2 & BLT2 & TMP2 & ST2 & ->).
        (* [comment removed for export] *)
        assert (GBND : forall b, In b gbs -> l_b6 L <= bn_addr b /\ bn_addr b + 8192 <= ri_base L).
        { intros b Hb. unfold gbs in Hb. apply in_map_iff in Hb as (b0 & <- & Hb0). cbn [bn_addr bn_of].
          destruct WGQ as (G1 & _). destruct (proj1 (Forall_forall _ _) G1 b0 Hb0) as (_ & _ & _ & (ib & Hib & EBb)).
          destruct (slot_le h kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2].
          dpose (user_vs_ri h kBatchClass W WR ltac:(unfold kBatchClass; clear; lia)) as (U1 & U2 & _ & U4).
          pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as XX. cbn zeta in XX. ddestruct XX as (_ & AUMU & _).
          change (class_size kBatchClass) with 8192 in S2. rewrite EBb. subst L. clear - S1 S2 U1 U2 U4 AUMU. lia. }
        assert (KOP : forall A n, (A + n <= lo \/ SPR + 32 <= A) -> (A + n <= A_INSTANCE + 888 \/ A_INSTANCE + 920 <= A) -> (A + n <= l_b6 L \/ ri_base L <= A) -> kept m m2 A n).
        { intros A n D1 D2 D3 x Hx. apply MU2. unfold pop_W. cbn [outside]. split; [clear - Hx D1; lia|]. split; [clear - Hx D2; lia|].
          apply (proj2 (Wn_outside gbs (bv_unsigned x))). intros b Hb. destruct (GBND b Hb) as [B1 B2]. clear - Hx D3 B1 B2. lia. }
        pose proof (z_T_hull h GEO) as ZTH. pose proof (z_hull_stk h GEO) as ZHS. pose proof (z_T_stk h GEO) as ZTS. unfold zapart in ZTH, ZHS, ZTS. cbn [fst snd] in ZTH, ZHS, ZTS. fold L in ZTH, ZHS, ZTS.
        ddestruct (L_GSB L W) as (_ & _ & RIE & RIH). dpose W as (_ & B6a & B6b & _ & B6c & _). unfold kHighMemBeg in B6c. unfold ri_base, space_end, kSpaceSize in RIH, KOP.
        assert (QT2 : hm_qhead m2 (T + 80) []).
        { unfold hm_qhead in *. eapply krw; [exact QT|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
          apply KOP; subst T L SPR; unfold A_INSTANCE; unfold ri_base, space_end, kSpaceSize in *; [clear - ZTS LOL SPH; lia| clear - T0; lia| clear - ZTH B6b; lia]. }
        assert (MTX2 : rw_cells asegs m2 (A_INSTANCE + 880) (qmutex_cells 1 1)).
        { unfold qmutex_cells in *. eapply krw; [exact MTX|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4.
          apply KOP; subst L SPR; unfold A_INSTANCE; [clear - LOL STK0 ACB; lia| clear; lia| clear - B6c B6a; lia]. }
        assert (FR2 : rec_frame m2 SPR q4 q3 q2 q1 q0 qra).
        { unfold rec_frame in *. eapply krw; [exact FR|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 48) with 48.
          apply KOP; subst L SPR; unfold A_INSTANCE; [clear; lia| clear - SPL LOL STK0 ACB; lia| clear - ZHS LOL SPL SPH B6b; lia]. }
        assert (HMQ2 : HMq h LF m2).
        { assert (BS : forall b0, In b0 (q_batches (h_tq h) ++ q_batches (h_gq h)) -> exists i, 0 <= i < carved h kBatchClass /\ b_addr b0 = chunk_at (h_L h) kBatchClass i).
          { intros b0 Hb0. rewrite TQ0 in Hb0. cbn [app] in Hb0. destruct WGQ as (G1 & _). destruct (proj1 (Forall_forall _ _) G1 b0 Hb0) as (_ & _ & _ & B4). exact B4. }
          apply (HMq_keepQ h m m2 LF WL' WR WK WS WD GEO BS WM2); [| exact HMQ].
          intros A n NZ x Hx. apply MU2. unfold pop_W. cbn [outside]. split; [| split].
          - intros R. apply (NZ (bv_unsigned x) Hx). left. fold L. subst SPR. clear - R LOL SPH; lia.
          - intros R. apply (NZ (bv_unsigned x) Hx). right; left. unfold quar_img_ranges, A_INSTANCE in *. cbn. clear - R; lia.
          - apply (proj2 (Wn_outside gbs (bv_unsigned x))). intros b Hb R. apply (NZ (bv_unsigned x) Hx). do 3 right.
            unfold gbs in Hb. apply in_map_iff in Hb as (b0 & <- & Hb0). exists b0. split; [apply in_app_iff; right; exact Hb0| exact R]. }
        assert (EL2 : Z_to_bv 64 (last_addr 0 gs2) = match gs2 with [] => Z_to_bv 64 0 | _ :: _ => Z_to_bv 64 (last_addr 0 G) end).
        { rewrite EG. destruct gs2 as [|g r]; [reflexivity|]. rewrite last_addr_app. rewrite (last_addr_cons_ne (last_addr 0 gs1) 0). reflexivity. }
        rewrite <- EL2 in QG2.
        apply (rec_from_C G X gs1 gs2 m2 mo2 kQuarantineMin ra s0 s1 s2 s3 s4 x0 x1 x2 y4 y5 y6 y7 t3 t4 t5 t6 FM FT ADDR LEN BWF PG EG);
          [unfold kQuarantineMin, kQuarantineMax in *; clear - CAP; lia| exact SUM| exact HK2| cbn [ms_mem] in HJ2; exact HJ2| exact MI2| exact HMQ2| exact QT2| exact QG2| exact BLG2| exact BLT2
          | unfold qc_cells; exact TMP2| exact MTX2| exact FR2| exact ST2| | exact (wmono_trans asegs _ _ _ WM0 WM2)].
        eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU2]. intros x OUT. unfold WRf, pop_W in *. cbn [outside] in OUT |- *.
        ddestruct OUT as (O1 & O2 & O3). split; [subst SPR; clear - O1; lia|]. split; [clear - O2; lia| exact O3].
      - (* [comment removed for export] *)
        assert (ETF : TL = last_addr 0 X /\ tf = Z_to_bv 64 (hd_addr X)).
        { destruct X as [|x0 xr]; [destruct (TL0 eq_refl) as [-> ->]; split; reflexivity| apply TLD; discriminate]. }
        destruct ETF as [ETL Etf]. rewrite ETL, Etf in TMP.
        apply (rec_from_C G X [] G m mo1 kQuarantineMin ra s0 s1 s2 s3 s4 t0' u1' u2' a4' a5' a6' a7' t3 t4 t5 t6 FM FT ADDR LEN BWF PG eq_refl);
          [unfold kQuarantineMin, kQuarantineMax in *; clear - GE; lia| exact SUM| exact HK1| cbn [ms_mem] in HJ1; exact HJ1| exact MI| exact HMQ| exact QT| exact QG| exact BLG| rewrite app_nil_r; exact BLX
          | rewrite app_nil_r; unfold qc_cells; exact TMP| exact MTX| exact FR| exact ST| exact MU0| exact WM0].
    Qed.

    #[using="hAR ct cg WF"] Lemma PG0 : Forall (bP h) gbs.
    Proof.
      dpose WF as (WL' & WC & WR & WK & (WT & (G1 & _) & _) & _). unfold gbs. apply Forall_forall. intros b Hb.
      apply in_map_iff in Hb as (b0 & <- & Hb0). pose proof (proj1 (Forall_forall _ _) G1 b0 Hb0) as WB0.
      exact (bP_orig h b0 WB0 (batch_elems_range h b0 (proj1 WL') WR WK WB0)).
    Qed.

    (* [comment removed for export] *)
    #[using="IMG ALWF ASB ct cg SPR TP WF TQ0 HV H32 BWF0 GB40 LOL SPL SPH SPA STKB GEO GNE EXIT"] Theorem recycle_top : ltac2:(CDefT.buildp (gd_tbl_AW_RecTop ()) "Pmo,$3?.Pt0,(4.&40.)Pt1,(4.&40.)Pt2,(4.&40.)Pa4,(4.&40.)Pa5,(4.&40.)Pa6,(4.&40.)Pa7,(4.&40.)Pt3,(4.&40.)Pt4,(4.&40.)Pt5,(4.&40.)Pt6,(4.&40.)P,(15.VhAR,VAL,VFF,Vh,R<.)P,(16.Vm0,R=.)P,(17.$18.Vm0,)P,(13.VhAR,Vh,VLF,Vm0,)P,(62.Vm0,(<.VT,+50.)(:.$57.))P,(62.Vm0,$77.Vgbs,)P,(6:.Vm0,Vgbs,)P,(63.$18.Vm0,$78.(6<.=+1.))P,(51.$61.(60.Vgbs,))P,(19.$18.Vm0,Vlo,VSP,)(41.$18.VQ,(42.(43.(44.Vqra,(45.&40.VSP,)Vgp,Vtp,R15.R14.R13.Vq0,Vq1,(45.&40.(<.$64.+2=8.))(45.&40.$75.)(45.&40.(<.VT,+=0.))(45.&40.VSTK,)R12.R11.R10.R?.Vq2,Vq3,Vq4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(45.&40.$79.)Vfc,(47.(4.&40.))Vm0,(48.$18.))R16.))")
(* [comment removed for export] *).
    Proof.
      intros mo t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 HK HJ MI HMQ QT QG BLG MTX GMAX ST.
      dpose Lf as (SB0 & (T0 & T1) & T2 & STK0 & STKH). pose proof aceil_bounds as ACB.
      dpose WF as (WL' & WC & WR & WK & (WT & WGQ & NDA & UQ) & WS & WD & WB & WBIG & WX & WG). pose proof (proj1 WL') as W.
      pose proof (bsum_nonneg _ (proj1 BWF0)) as G0. pose proof (bsum_ge _ (proj1 BWF0)) as GLEN.
      dpose W as (_ & B6a & B6b & _ & B6c & _). unfold kHighMemBeg in B6c.
      ddestruct (L_GSB L W) as (_ & _ & RIE & RIH). unfold ri_base, space_end, kSpaceSize in RIH.
      pose proof (z_T_hull h GEO) as ZTH. pose proof (z_hull_stk h GEO) as ZHS. pose proof (z_T_stk h GEO) as ZTS. unfold zapart in ZTH, ZHS, ZTS. cbn [fst snd] in ZTH, ZHS, ZTS. fold L in ZTH, ZHS, ZTS.
      assert (BS : forall b0, In b0 (q_batches (h_tq h) ++ q_batches (h_gq h)) -> exists i, 0 <= i < carved h kBatchClass /\ b_addr b0 = chunk_at (h_L h) kBatchClass i).
      { intros b0 Hb0. rewrite TQ0 in Hb0. cbn [app] in Hb0. destruct WGQ as (G1 & _). destruct (proj1 (Forall_forall _ _) G1 b0 Hb0) as (_ & _ & _ & B4). exact B4. }
      assert (GBND : forall b, In b gbs -> l_b6 L <= bn_addr b /\ bn_addr b + 8192 <= ri_base L).
      { intros b Hb. exact (proj2 (node_cs gbs [] b ltac:(intros b' Hb'; exists b'; split; [exact Hb'| reflexivity]) Hb)). }
      assert (ADDR0 : forall b', In b' ([] ++ gbs) -> exists b, In b gbs /\ bn_addr b' = bn_addr b) by (intros b' Hb'; exists b'; split; [exact Hb'| reflexivity]).
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo (ff_kinv AL FF h) HK); [exact HJ| |].
      { eapply (rec_A AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) qra gp tp t0 t1 t2 q0 q1 a4 a5 a6 a7 q2 q3 q4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  (Z_to_bv 64 (hd_addr gbs)) (Z_to_bv 64 (last_addr 0 gbs)) SP T STK kQuarantineMin (Z.of_nat (length gbs)) (bsum gbs) lo F fc m0);
          [exact T0| subst T L; clear - T2 ACB; lia| exact STKB| unfold kQuarantineMin; clear; lia| clear; lia| clear - GLEN; lia| exact GB40
          | unfold A_Q_CMUTEX in MTX; exact MTX| unfold hm_qhead, A_Q_GLOBAL in QG; exact QG| exact ST| clear - LOL STK0; lia| clear - SPL; lia| clear - SPH STKH; lia| exact SPA| | exact MI].
        apply (ff_cs_stack AL FF h lo (SP - lo) WFKh); [exact LOL| subst L; clear - SPH; lia]. }
      cbn beta. intros ms1 mo1 P1 HK1 MM1 HJ1.
      ddestruct P1 as (m1 & x5 & x6 & x14 & x15 & x17 & MU1 & WM1 & MI1 & MTX1 & QG1 & TMP1 & FR1 & ST1 & ARM).
      replace (SP + -80) with SPR in * by (subst SPR; clear; lia).
      assert (KO1 : forall A n, (A + n <= lo \/ SP <= A) -> (A + n <= A_INSTANCE + 880 \/ A_INSTANCE + 884 <= A) -> kept m0 m1 A n).
      { intros A n D1 D2. apply (kept_of_munch _ m0 m1 A n MU1). cbn. split; [exact D1|]. split; [exact D2| exact I]. }
      assert (QT1 : hm_qhead m1 (T + 80) []).
      { unfold hm_qhead in *. eapply krw; [exact QT|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
        apply KO1; subst T L; unfold A_INSTANCE; [clear - ZTS LOL SPH; lia| clear - T0; lia]. }
      assert (BLG1 : blist m1 gbs).
      { unfold blist in *. eapply blistT_k; [exact BLG| exact (proj1 BWF0)|]. intros b Hb. destruct (GBND b Hb) as [B1 B2]. unfold ri_base, space_end, kSpaceSize in B2.
        apply KO1; subst L; unfold A_INSTANCE; [clear - B1 B2 ZHS LOL SPH B6b; lia| clear - B1 B6c; lia]. }
      assert (MU01 : munch (WRf lo SP gbs) m0 m1).
      { eapply munch_weaken; [| exact MU1]. intros x OUT. unfold WRf in OUT. cbn [outside] in OUT |- *. ddestruct OUT as (O1 & O2 & _). split; [exact O1|]. split; [clear - O2; lia| exact I]. }
      assert (HMQ1 : HMq h LF m1).
      { apply (HMq_keepQ h m0 m1 LF WL' WR WK WS WD GEO BS WM1); [| exact HMQ].
        intros A n NZ x Hx. apply MU1. cbn [outside]. split; [| split; [| exact I]].
        - intros R. apply (NZ (bv_unsigned x) Hx). left. fold L. clear - R LOL SPH; lia.
        - intros R. apply (NZ (bv_unsigned x) Hx). right; left. unfold quar_img_ranges, A_INSTANCE in *. cbn. clear - R; lia. }
      destruct ARM as [(MC1 & MC2 & ->)|(NM & ->)].
      - (* [comment removed for export] *)
        replace (Z_to_bv 64 AW_Recycle.A_MERGEB) with (Z_to_bv 64 AW_Merge.A_MERGEB) by reflexivity.
        eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo1 (ff_kinv AL FF h) HK1); [exact HJ1| |].
        { eapply (merge_spec AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) gbs [] (Z_to_bv 64 A_REC_MB_BACK) gp tp x5 x6 t2
                    (Z_to_bv 64 (A_INSTANCE + 888)) (Z_to_bv 64 kQuarantineMin) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 STK) x14 x15 (Z_to_bv 64 (Z.of_nat (length gbs))) x17
                    (Z_to_bv 64 (A_INSTANCE + 728)) (Z_to_bv 64 STK) (Z_to_bv 64 (T + 208)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (Z_to_bv 64 0) SPR 0 lo (Wn gbs) F fc m1);
            cbn [app bsum length Z.of_nat]; first [exact BWF0 | exact QG1 | exact BLG1 | exact I | exact TMP1 | exact ST1 | exact MI1 | idtac].
          + pose proof GB40 as GB. unfold gbs in GB, GLEN |- *. rewrite length_map in *. clear - GB GLEN; lia.
          + pose proof GB40 as GB. unfold gbs in GB, GLEN |- *. rewrite length_map in *. clear - GB GLEN; lia.
          + clear; lia.
          + intros b Hb. exact (proj1 (node_cs gbs [] b ADDR0 Hb)).
          + intros b y Hb OUT. exact (proj1 (Wn_outside gbs y) OUT b Hb).
          + intros y Hy. apply (proj2 (Wn_outside gbs y)). intros b Hb. destruct (GBND b Hb) as [B1 B2]. unfold ri_base, space_end, kSpaceSize in B2. subst SPR L. clear - Hy B1 B2 B6b ZHS LOL SPH; lia.
          + intros NE. exfalso. exact (NE eq_refl).
          + clear - LOL STK0; lia.
          + subst SPR; clear - SPL; lia.
          + subst SPR; clear - SPH STKH; lia.
          + apply (ff_cs_stack AL FF h lo (SPR + 32 - lo) WFKh); [exact LOL| subst SPR L; clear - SPH; lia]. }
        cbn beta. intros ms2 mo2 P2 HK2 MM2 HJ2. unfold merge_post in P2.
        ddestruct P2 as (m2 & gs' & ts' & TL' & tf' & y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30
                        & MU2 & WM2 & MI2 & QG2 & BLG2 & BLT2 & BWF2 & HD2 & TMP2 & TLD2 & TLB2 & TE2 & FM2 & FT2 & ADDR2 & LEN2 & SUM2 & ST2 & EGS & ETS & ->).
        cbn [app] in ETS, ADDR2, LEN2, FT2, SUM2. cbn [bsum] in SUM2.
        replace (ret_pc (Z_to_bv 64 A_REC_MB_BACK)) with (Z_to_bv 64 A_REC_MB_BACK) by (symmetry; apply ret_pc_even; [unfold A_REC_MB_BACK; clear; lia| reflexivity]).
        (* [comment removed for export] *)
        eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo2 (ff_kinv AL FF h) HK2); [exact HJ2| |].
        { eapply (rec_MB_back AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) (Z_to_bv 64 A_REC_MB_BACK) gp tp y5 y6 y7 (Z_to_bv 64 (A_INSTANCE + 888)) y11 y12 y13 y14 y15 y16 y17
                    s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 t6 (Z_to_bv 64 (hd_addr gs')) (Z_to_bv 64 (last_addr 0 gs')) SPR T STK kQuarantineMin (Z.of_nat (length gs')) (bsum gs') F fc m2);
            [| exact QG2| exact MI2].
          pose proof (bsum_ge _ (proj1 (bwf_app_r _ _ BWF2))) as GL2. pose proof (bsum_nonneg _ (proj1 (bwf_app_l _ _ BWF2))) as TB2. clear - GL2 TB2 SUM2 GB40. lia. }
        cbn beta. intros ms3 mo3 -> HK3 MM3 HJ3.
        (* [comment removed for export] *)
        assert (KO2 : forall A n, (A + n <= lo \/ SPR + 32 <= A) -> (A + n <= A_INSTANCE + 888 \/ A_INSTANCE + 920 <= A) -> (A + n <= l_b6 L \/ ri_base L <= A) -> kept m1 m2 A n).
        { intros A n D1 D2 D3 x Hx. apply MU2. cbn [outside]. split; [subst SPR; clear - Hx D1; lia|]. split; [clear - Hx D2; lia|]. split; [subst SPR; clear - Hx D1 SPL; lia|].
          apply (proj2 (Wn_outside gbs (bv_unsigned x))). intros b Hb. destruct (GBND b Hb) as [B1 B2]. clear - Hx D3 B1 B2. lia. }
        unfold ri_base, space_end, kSpaceSize in KO2.
        assert (QT2 : hm_qhead m2 (T + 80) []).
        { unfold hm_qhead in *. eapply krw; [exact QT1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32.
          apply KO2; subst T L SPR; unfold A_INSTANCE; [clear - ZTS LOL SPH; lia| clear - T0; lia| clear - ZTH B6b; lia]. }
        assert (MTX2 : rw_cells asegs m2 (A_INSTANCE + 880) (qmutex_cells 1 1)).
        { unfold qmutex_cells in *. eapply krw; [exact MTX1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4.
          apply KO2; subst L SPR; unfold A_INSTANCE; [clear - LOL STK0 ACB; lia| clear; lia| clear - B6c B6a; lia]. }
        assert (FR2 : rec_frame m2 SPR q4 q3 q2 q1 q0 qra).
        { unfold rec_frame in *. eapply krw; [exact FR1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 48) with 48.
          apply KO2; subst L SPR; unfold A_INSTANCE; [clear; lia| clear - SPL LOL STK0 ACB; lia| clear - ZHS LOL SPL SPH B6b; lia]. }
        assert (HMQ2 : HMq h LF m2).
        { apply (HMq_keepQ h m1 m2 LF WL' WR WK WS WD GEO BS WM2); [| exact HMQ1].
          intros A n NZ x Hx. apply MU2. cbn [outside]. split; [| split; [| split]].
          - intros R. apply (NZ (bv_unsigned x) Hx). left. fold L. subst SPR. clear - R LOL SPH; lia.
          - intros R. apply (NZ (bv_unsigned x) Hx). right; left. unfold quar_img_ranges, A_INSTANCE in *. cbn. clear - R; lia.
          - intros R. apply (NZ (bv_unsigned x) Hx). left. fold L. subst SPR. clear - R LOL SPH SPL; lia.
          - apply (proj2 (Wn_outside gbs (bv_unsigned x))). intros b Hb R. apply (NZ (bv_unsigned x) Hx). do 3 right.
            unfold gbs in Hb. apply in_map_iff in Hb as (b0 & <- & Hb0). exists b0. split; [apply in_app_iff; right; exact Hb0| exact R]. }
        assert (PG' : Forall (bP h) gs').
        { rewrite EGS. exact (proj1 (merge_out_inv (bP h) (fun b => bn_elems b = [] /\ bn_size b = kBatchSize) (bP_mnode h) (bQ_xnode h) gbs PG0)). }
        apply (rec_from_B gs' ts' m2 mo3 TL' tf' (Z_to_bv 64 A_REC_MB_BACK) (Z_to_bv 64 (A_INSTANCE + 888)) (Z_to_bv 64 kQuarantineMin)
                 (Z_to_bv 64 (A_INSTANCE + 728)) (Z_to_bv 64 STK) (Z_to_bv 64 (T + 208)) y5 y6 y7 y14 y15 y17 y28 y29 y30 t6 FM2 FT2 ADDR2 LEN2 BWF2 PG');
          [clear - SUM2; lia| exact HK3| cbn [ms_mem] in HJ3; exact HJ3| exact MI2| exact HMQ2| exact QT2| exact QG2| exact BLG2| exact BLT2| exact TMP2| exact TLD2| | exact TLB2| exact MTX2| exact FR2| exact ST2| | exact (wmono_trans asegs _ _ _ WM1 WM2)].
        + intros E. destruct (TE2 E) as [A1 A2]. split; [exact A1| exact A2].
        + eapply munch_trans; [exact MU01|]. eapply munch_weaken; [| exact MU2]. intros x OUT. unfold WRf in OUT |- *. cbn [outside] in OUT |- *.
          ddestruct OUT as (O1 & O2 & O3). split; [subst SPR; clear - O1; lia|]. split; [clear - O2; lia|]. split; [subst SPR; clear - O1 SPL; lia| exact O3].
      - (* [comment removed for export] *)
        apply (rec_from_B gbs [] m1 mo1 0 (Z_to_bv 64 0) qra q0 q1 q2 q3 q4 x5 x6 t2 x14 x15 x17 t3 t4 t5 t6 eq_refl eq_refl ADDR0 eq_refl BWF0 PG0);
          [clear; cbn; lia| exact HK1| cbn [ms_mem] in HJ1; exact HJ1| exact MI1| exact HMQ1| exact QT1| exact QG1| exact BLG1| exact I| exact TMP1| intros NE; exfalso; exact (NE eq_refl)| intros _; split; reflexivity| clear; lia
          | exact MTX1| exact FR1| exact ST1| exact MU01| exact WM1].
    Qed.
  End R.
End RecTop.
End ARUN_1.
