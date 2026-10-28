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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_QPut AW_Enqueue AW_Drain AW_Blist AW_DoRecycle AW_DoRecycle2 AW_Merge AW_Recycle AW_RecLoop AW_RecTop.
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
Ltac2 gd_tbl_AW_FreePhD () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_ro"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_Q_MAX"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMax"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineMin"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kQuarantineCache"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHMX.fkeepR"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_region"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.hgeom"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.batch"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_batches"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.carved"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kBatchClass"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.b_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_quar"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.awf'"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHM.HMq"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_K"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.ff_CS"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.in_qs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.qs_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.rp_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.wmono_ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.depot"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "Stdlib.Lists.List.incl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_sech"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_size"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "ARUN_1.PhD.dpost"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_base"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeRM.WFC"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.q_bytes"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_chunks'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_sec"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.HMLib.kept"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.put_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_QPut.A_QPUT_RA1"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"].

Section ARUN_1. Context {hAR : arun}.

#[using="Type"] Lemma hm_ro_qmax : ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "PL,$0.Pm,P,(1.&40.)(2.(1.&8.))P,(3.R2.R1.)(4.$5.R2.$6.(7.$8.(9.(:.&40.$;.))(7.$8.(9.(:.&40.$<.))(7.$8.(9.(:.&40.$=.))(>.$8.)))))")
(* [comment removed for export] *).
Proof. intros L m H. dpose H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QM & _). exact QM. Qed.

#[using="Type"] Lemma fkeepR_sp_mono : ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "PL,$0.PLBK,(?.(10.$11.$11.))PQS,(?.(10.$11.$11.))PRP,(?.(10.$11.$11.))PNB,(?.$11.)PBL,(?.$11.)Plo,$11.PSP,$11.PSP',$11.Pm,P,(1.&40.)(2.(1.&8.))Pm',P,(1.&40.)(2.(1.&8.))P,(12.R;.R:.R9.R8.R7.R6.R5.R4.R2.R1.)P,(13.R5.R4.)(12.R=.R<.R;.R:.R9.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros L LBK QS RP NB BL lo SP SP' m m' K LE x. cbv zeta. intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  apply (K x); try assumption. intros R. apply H1. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hm_quar_keepS : ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "Phq,$14.Pm,P,(1.&40.)(2.(1.&8.))Pm',P,(1.&40.)(2.(1.&8.))Plo,$11.PSP,$11.P,(15.VhAR,(16.R5.))P,(17.R6.)P,(18.R7.)P,Pb,$19.P,(1:.$19.R1.(1;.$19.(1<.(1=.R9.))(1<.(1>.R9.))))(1?.$11.Li,$11.(20.(20.(13.=R1.)(21.R1.(22.R;.$23.)))(24.$11.(25.R3.)(26.(16.R;.)$23.R1.))))P,(13.(27.(16.R9.))R6.)P,(13.R6.(28.(16.R:.)))P,(29.VhAR,R;.R:.)P,(2:.(7.(10.$11.$11.)(2;.$11.$11.R9.R8.)(>.(10.$11.$11.)))R;.R:.)P,(2<.$5.R<.R;.)(29.VhAR,R>.R<.)")
(* [comment removed for export] *).
Proof.
  intros hq m m' lo SP WL WR GEO BS LOL SPH HQ MU WM.
  dpose WL as (_ & B6a & B6b & _ & B6c & B6d & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STK0 & STKH & _). unfold kHighMemBeg in B6c.
  destruct (L_GT _ WL) as ((T0 & T1) & T2 & _). destruct (L_GSB _ WL) as (SB0 & _ & RIE & RIH). unfold ri_base, space_end, kSpaceSize in RIH. pose proof aceil_bounds as ACB.
  pose proof (z_T_stk hq GEO) as ZTS. pose proof (z_hull_stk hq GEO) as ZHS. unfold zapart in ZTS, ZHS. cbn [fst snd] in ZTS, ZHS.
  assert (KO : forall A n, (A + n <= lo \/ SP <= A) -> kept m m' A n).
  { intros A n D. apply (kept_of_munch _ m m' A n MU). cbn. split; [exact D| exact I]. }
  assert (NK : forall b, In b (map bn_of (q_batches (h_tq hq)) ++ map bn_of (q_batches (h_gq hq))) -> kept m m' (bn_addr b) 8192).
  { intros b Hb. rewrite <- map_app in Hb. apply in_map_iff in Hb as (b0 & <- & Hb0). cbn [bn_addr bn_of].
    ddestruct (BS b0 Hb0) as (ib & Hib & EBb). destruct (slot_le hq kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2].
    dpose (user_vs_ri hq kBatchClass WL WR ltac:(unfold kBatchClass; clear; lia)) as (U1 & U2 & _ & U4).
    pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as XX. cbn zeta in XX. ddestruct XX as (_ & AUMU & _).
    change (class_size kBatchClass) with 8192 in S2. rewrite EBb. apply KO. unfold ri_base, space_end, kSpaceSize in U1, U4. clear - S1 S2 U1 U2 U4 AUMU ZHS LOL SPH B6b. lia. }
  unfold hm_quar in *. cbn zeta in *. ddestruct HQ as (QT & BLT & QG & BLG & BWF & MTX & EB1 & EB2). unfold hm_qhead, A_Q_GLOBAL, A_Q_CMUTEX, A_INSTANCE in *.
  split. { eapply krw; [exact QT|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 32) with 32. apply KO. clear - ZTS LOL SPH; lia. }
  split. { unfold blist in *. eapply blistT_k; [exact BLT| exact (proj1 (bwf_app_l _ _ BWF))| intros b Hb; apply NK; apply in_app_iff; left; exact Hb]. }
  split. { eapply krw; [exact QG|]. apply KO. cbn. clear - LOL STK0 ACB; lia. }
  split. { unfold blist in *. eapply blistT_k; [exact BLG| exact (proj1 (bwf_app_r _ _ BWF))| intros b Hb; apply NK; apply in_app_iff; right; exact Hb]. }
  split; [exact BWF|]. split. { eapply krw; [exact MTX|]. apply KO. cbn. clear - LOL STK0 ACB; lia. }
  exact (conj EB1 EB2).
Qed.

Section PhD.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Variable FF : ffam AL.

  (* [comment removed for export] *)
  Definition dpost (h : ahst) (m : mem) (lo SP : Z) (LF : list (Z * Z)) (h' : ahst) (m' : mem) (mo' : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "(20.(2=.VhAR,O3.)(20.(2>.VhAR,O3.O4.O2.)(20.(29.VhAR,O3.O2.)(20.(2?.VhAR,VAL,VFF,O3.O1.)(20.(30.O2.O1.)(20.(31.$5.O2.)(20.(32.$5.O2.O6.O5.)(20.Px,$11.P,(33.VhAR,VAL,VFF,O8.R1.)P,(34.(35.(36.O8.)R2.))(33.VhAR,VAL,VFF,O3.R3.)(20.(12.(16.O8.)(37.O8.)(36.O8.)(38.O8.)(39.(3:.O8.))(3;.(3:.O8.))O6.O5.O7.O2.)(20.(3<.(36.O8.)O7.O2.)(20.(24.$0.(16.O3.)(16.O8.))(20.(24.$3=.(3:.O3.)(3:.O8.))(20.(24.(?.(10.$11.$11.))(37.O3.)(37.O8.))(20.(24.$11.(3>.O3.)(3>.O8.))(20.(24.$3?.(40.O3.)(40.O8.))(20.(24.$41.(42.O3.)(42.O8.))(20.(24.$11.(43.O3.)(43.O8.))(20.(24.$41.(44.O3.)(44.O8.))(20.Pc,$11.(24.$11.(45.(46.O3.R1.))(45.(46.O8.R1.)))(20.Pk,$47.P,(1:.$47.R1.(48.O3.))(1:.$47.R2.(48.O8.))(20.Psh,$49.P,(1:.$49.R1.(4:.(4;.O3.)))(1:.$49.R2.(4:.(4;.O8.)))(20.(4<.(10.$11.$11.)(4=.(4>.O8.))(4=.(4>.O3.)))(20.Pk,$47.P,(1:.$47.R1.(48.O8.))P,(24.$41.(4?.R2.)$50.)(51.(1:.$47.R3.(48.O3.))(1:.(10.$11.$11.)(2;.$11.$11.(52.R3.)(53.R3.))(4=.(4>.O3.))))Pg,(10.$11.$11.)P,(1:.(10.$11.$11.)R1.(4=.(4>.O3.)))(51.(1:.(10.$11.$11.)R2.(4=.(4>.O8.)))(1?.$47.Lk,$47.(20.(1:.$47.R1.(48.O8.))(20.(24.$41.(4?.R1.)$50.)(24.(10.$11.$11.)R3.(2;.$11.$11.(52.R1.)(53.R1.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  
  Section D.
    (* [comment removed for export] *)
    Variables (h : ahst) (ct : Z) (m0 : mem) (LF : list (Z * Z)) (SP lo STK p n : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (Q : config -> Prop)
              (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
    Let L := h_L h.
    Let T := l_T L.
    Let tbs := map bn_of (q_batches (h_tq h)).
    Let gbs := map bn_of (q_batches (h_gq h)).
    Hypothesis TP : tp = Z_to_bv 64 A_TP.
    Hypothesis WF : WFC h ct kQuarantineMax.
    Hypothesis HV : h_havol h <= AVOL_MAX.
    Hypothesis H32 : forall k, In k (h_chunks h) -> nfix (ck_n k) < 2^32.
    Hypothesis TNE : q_batches (h_tq h) <> [].
    Hypothesis TB30 : bsum tbs < 2^39.   (* [comment removed for export] *)
    Hypothesis LOL : l_stk_lo L <= lo.
    Hypothesis SPL : lo <= SP - 80 - 80 - 112 - 736.
    Hypothesis SPH : SP <= l_stk_hi L.
    Hypothesis SPA : SP mod 16 = 0.
    Hypothesis STKB : 0 <= STK < 2^64.
    Hypothesis GEO : hgeom h.
    Hypothesis EXIT : ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "Ph',$14.Pm',P,(1.&40.)(2.(1.&8.))Pmo',$54.Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)P,(55.Vh,Vm0,Vlo,VSP,VLF,R12.R11.R10.)(56.$5.VQ,(57.(58.(59.Vra,(:.&40.VSP,)Vgp,Vtp,R10.R?.R>.Vs0,Vs1,R=.R<.R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(5:.Vra,)Vfc,(5;.(1.&40.))R12.(5<.$5.))R11.))")
(* [comment removed for export] *).

    #[using="ct WF"] Lemma WL : wf_L L. Proof. ddestruct WF as ((A & _) & _). exact A. Qed.
    #[using="ct WF"] Lemma Lf : ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "(20.(13.+10007???9000.(5=.VL,))(20.(20.(20.(13.+1000.VT,)(51.(13.(5>.VT,+1000.)+10000.)(13.+65?000.VT,)))(51.(13.(5>.VT,+1000.)+7???7000.)(13.+10007???8000.VT,)))(20.(13.(5>.VT,+1000.)(5?.VhAR,))(20.(13.(5?.VhAR,)(27.VL,))(13.(28.VL,)(60.+2.+2?.))))))")
(* [comment removed for export] *).
    Proof.
      pose proof WL as W. destruct (L_GSB L W) as (SB0 & _). ddestruct (L_GT L W) as (T0 & T1 & _).
      dpose W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STK0 & STKH & _).
      exact (conj SB0 (conj T0 (conj T1 (conj STK0 STKH)))).
    Qed.
    #[using="ct WF HV"] Lemma WFKh : WFK h. Proof. exact (WFK_of_WFC h ct kQuarantineMax WF HV). Qed.
    #[using="hAR ct WF"] Lemma BS : ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "Pb0,$19.P,(1:.$19.R1.(1;.$19.(1<.(1=.Vh,))(1<.(1>.Vh,))))(1?.$11.Li,$11.(20.(20.(13.=R1.)(21.R1.(22.Vh,$23.)))(24.$11.(25.R3.)(26.(16.Vh,)$23.R1.))))")
(* [comment removed for export] *).
    Proof.
      intros b0 Hb0. dpose WF as (_ & _ & _ & _ & ((T1 & _) & (G1 & _) & _) & _).
      apply in_app_iff in Hb0 as [Hb0|Hb0]; [destruct (proj1 (Forall_forall _ _) T1 b0 Hb0) as (_ & _ & _ & B4)| destruct (proj1 (Forall_forall _ _) G1 b0 Hb0) as (_ & _ & _ & B4)]; exact B4.
    Qed.
    (* [comment removed for export] *)
    #[using="ct WF HV"] Lemma node_facts : ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "Pb,$61.P,(1:.$61.R1.(1;.$61.Vtbs,Vgbs,))(20.(62.(33.VhAR,VAL,VFF,Vh,)(63.R2.)+2000.)(20.(13.(64.VL,)(63.R2.))(20.(13.(5>.(63.R2.)+2000.)(65.VL,))(20.(13.(5>.(63.R2.)+2000.)(5?.VhAR,))(13.+65?000.(63.R2.))))))")
(* [comment removed for export] *).
    Proof.
      intros b Hb. assert (Hb' : exists b0, In b0 (q_batches (h_tq h) ++ q_batches (h_gq h)) /\ b = bn_of b0).
      { unfold tbs, gbs in Hb. rewrite <- map_app in Hb. apply in_map_iff in Hb as (b0 & <- & Hb0). exists b0. auto. }
      ddestruct Hb' as (b0 & Hb0 & ->). cbn [bn_addr bn_of].
      dpose WF as (WL' & WC & WR & WK & _). ddestruct (BS b0 Hb0) as (ib & Hib & EBb).
      destruct (slot_le h kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2].
      dpose (user_vs_ri h kBatchClass (proj1 WL') WR ltac:(unfold kBatchClass; clear; lia)) as (U1 & U2 & _ & U4).
      pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as XX. cbn zeta in XX. ddestruct XX as (_ & AUMU & _).
      pose proof (proj1 WL') as W. dpose W as (_ & _ & _ & _ & B6c & B6d & _). unfold kHighMemBeg in B6c. ddestruct (L_GSB L W) as (_ & _ & RIE & RIH).
      change (class_size kBatchClass) with 8192 in S2. rewrite EBb.
      split; [| subst L; unfold ri_base, space_end, kSpaceSize in *; clear - S1 S2 U1 U2 U4 AUMU B6c B6d RIH; lia].
      eapply crange_sub; [apply (ff_cs_user AL FF h kBatchClass WFKh); unfold kBatchClass; clear; lia| clear - S1; lia| clear - S2 AUMU; lia].
    Qed.

    (* [comment removed for export] *)
    #[using="ct T WF LOL SPL SPH"] Lemma put_frame_kept : ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "Ph1,$14.Pm,P,(1.&40.)(2.(1.&8.))Pm',P,(1.&40.)(2.(1.&8.))P,(51.(66.VhAR,R3.=(67.(1>.R3.)))$68.)P,(24.$0.(16.R4.)VL,)P,(18.R5.)P,(69.VhAR,R6.)P,(6:.R7.)P,(12.VL,(37.R8.)(36.R8.)(38.R8.)(39.(3:.R8.))(3;.(3:.R8.))Vlo,(6;.VSP,+50.)R7.R6.)(6<.R8.R7.(6;.VSP,+50.)+50.)")
(* [comment removed for export] *).
    Proof.
      intros h1 m m' _ EL1 GEO1 WK1 WS1 K x Hx. dpose Lf as (SB0 & (T0 & T1) & T2 & STK0 & STKH). pose proof WL as W0. dpose W0 as (_ & _ & _ & _ & _ & B6d & _).
      dpose WK1 as (WKF & _ & _).
      pose proof (z_T_stk h1 GEO1) as Y1. pose proof (z_hull_stk h1 GEO1) as Y2. pose proof (z_pa_stk h1 GEO1) as Y3.
      unfold zapart in Y1, Y2, Y3. cbn [fst snd] in Y1, Y2, Y3. rewrite EL1 in Y1, Y2, Y3. pose proof aceil_bounds as ACB.
      apply (K x); cbv zeta.
      - clear - Hx. lia.
      - clear - Hx Y1 LOL SPL SPH; subst L; lia.
      - intros [IH _]. unfold in_hull in IH. clear - Hx Y2 LOL SPL SPH IH; subst L; lia.
      - intros [SH _]. unfold shad in SH. clear - Hx SH LOL SPL SPH STK0 B6d ACB; subst L; lia.
      - (intros dd_H; ddestruct dd_H as (q & Hq & R)). unfold qs_of in Hq. apply in_map_iff in Hq. ddestruct Hq as (kq & <- & Hkq). apply filter_In in Hkq as [Hkq Pq].
        apply andb_prop in Pq as [Pq _]. apply Bool.negb_true_iff in Pq. cbn [fst snd] in R.
        pose proof (proj1 (Forall_forall _ _) WKF kq Hkq) as (_ & _ & _ & Xq). rewrite Pq in Xq.
        ddestruct Xq as (iq & Nq & _ & _ & CEILq & _). pose proof (z_sec_stk h1 GEO1 iq _ Nq) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. rewrite EL1 in Y.
        unfold shad in R. clear - Hx R Y LOL SPL SPH STK0 CEILq ACB; subst L; lia.
      - unfold free_img_ranges, A_INSTANCE, A_IA, A_IA_INIT. cbn. clear - Hx LOL SPL STK0 ACB; subst L; lia.
      - (intros dd_H; ddestruct dd_H as (b & Hb & R)). destruct (In_nth_error _ _ Hb) as [jb Hjb]. pose proof (z_node_stk h1 GEO1 jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL1 in Y.
        clear - Hx R Y LOL SPL SPH; subst L; lia.
      - (intros dd_H; ddestruct dd_H as (b & Hb & R)). destruct (In_nth_error _ _ Hb) as [jb Hjb]. pose proof (z_store_stk h1 GEO1 jb b Hjb) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL1 in Y.
        clear - Hx R Y LOL SPL SPH; subst L; lia.
      - clear - Hx Y3 LOL SPL SPH; subst L; lia.
      - (intros dd_H; ddestruct dd_H as (r & Hr & R)). unfold rp_of in Hr. apply in_map_iff in Hr. ddestruct Hr as (sh & <- & Hsh). cbn [fst snd] in R.
        destruct (In_nth_error _ _ Hsh) as [ish Nsh]. pose proof (z_sec_stk h1 GEO1 ish _ Nsh) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL1 in Y.
        dpose WS1 as (_ & _ & _ & _ & _ & _ & _ & WS8). pose proof (proj1 (Forall_forall _ _) WS8 sh Hsh) as (_ & M4 & _).
        clear - Hx R Y LOL SPL SPH M4; subst L; lia.
    Qed.

    (* [comment removed for export] *)
    #[using="hAR ct WF GEO"] Lemma nodes_not_blocks : forall b a, In b (tbs ++ gbs) -> in_blk (blocks h) a -> ~ (bn_addr b <= a < bn_addr b + 8192).
    Proof.
      (intros b a Hb dd_H; ddestruct dd_H as (bk & Hbk & Ra); intros R). destruct bk as [B N]. cbn [fst snd] in Ra.
      assert (Hb' : exists b0, In b0 (q_batches (h_tq h) ++ q_batches (h_gq h)) /\ b = bn_of b0).
      { unfold tbs, gbs in Hb. rewrite <- map_app in Hb. apply in_map_iff in Hb as (b0 & <- & Hb0). exists b0. auto. }
      ddestruct Hb' as (b0 & Hb0 & ->). cbn [bn_addr bn_of] in R.
      dpose WF as (WL' & WC & WR & WK & _). pose proof (proj1 WL') as W.
      ddestruct (in_blk_chunk h a B N W WR WK Hbk Ra) as (kb & Hkb & STb & -> & -> & Xb & _).
      destruct (ext_cases h kb W WR WK Hkb) as [(c' & P' & EC' & C' & RL' & RH' & AUMU')|(i' & sh & P' & N' & EL' & EH')].
      - pose proof (batch_vs_chunk' h WR WK BS kb b0 Hkb P' Hb0) as AP. unfold ext_lo, ext_hi, ck_end in Xb. rewrite P' in Xb. clear - AP Xb R. lia.
      - ddestruct (BS b0 Hb0) as (ib & Hib & EBb). destruct (slot_le h kBatchClass ib WR ltac:(unfold kBatchClass; clear; lia) Hib) as [S1 S2].
        dpose (user_vs_ri h kBatchClass W WR ltac:(unfold kBatchClass; clear; lia)) as (U1 & U2 & _ & U4).
        pose proof (WR kBatchClass ltac:(unfold kBatchClass, kNumClasses; clear; lia)) as X. cbn zeta in X. ddestruct X as (_ & AUMU & _).
        pose proof (z_sec_hull h GEO i' _ N') as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y.
        change (class_size kBatchClass) with 8192 in S2. clear - Y EL' EH' Xb R S1 S2 U1 U2 U4 AUMU EBb. lia.
    Qed.

    #[using="IMG ALWF ASB ct tbs gbs TP WF HV H32 TNE TB30 LOL SPL SPH SPA STKB GEO EXIT"] Theorem phase_D : ltac2:(CDefT.buildp (gd_tbl_AW_FreePhD ()) "Pmo,$54.Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)P,(2?.VhAR,VAL,VFF,Vh,R10.)P,(30.Vm0,R11.)P,(31.$5.Vm0,)P,(2>.VhAR,Vh,VLF,Vm0,)P,(29.VhAR,Vh,Vm0,)P,(6=.Vm0,VSP,VT,VSTK,Vs6,Vs5,Vs4,Vs3,Vs2,Vs1,Vs0,Vra,)P,(32.$5.Vm0,Vlo,(6;.VSP,+50.))(56.$5.VQ,(57.(58.(59.(:.&40.$6>.)(:.&40.(5>.VSP,-50.))Vgp,Vtp,R16.R15.R14.(:.&40.(5>.$6?.+2=8.))(:.&40.(5>.VT,+50.))R13.R12.R11.R10.R?.R>.R=.R<.(:.&40.Vn,)(:.&40.VSTK,)(:.&40.(5>.VT,+=0.))(:.&40.(5>.Vp,-10.))(:.&40.$=.)Vs7,Vs8,Vs9,Vs10,Vs11,R;.R:.R9.R8.)VF,(:.&40.$6>.)Vfc,(5;.(1.&40.))Vm0,(5<.$5.))R17.))")
(* [comment removed for export] *).
    Proof.
      intros mo t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HK HJ MI HMQ HQ PF ST.
      dpose Lf as (SB0 & (T0 & T1) & T2 & STK0 & STKH). pose proof aceil_bounds as ACB. pose proof WL as W.
      dpose WF as (WL' & WC & WR & WK & ((WT1 & WT2 & WT3) & (WG1 & WG2 & WG3) & NDA & UQ) & WS & WD & WB & WBIG & WX & WG).
      pose proof HQ as HQ'. unfold hm_quar in HQ'. cbn zeta in HQ'. fold L tbs gbs in HQ'. ddestruct HQ' as (QT & BLT & QG & BLG & BWF & MTX & ETB & EGB).
      pose proof (bsum_nonneg _ (proj1 (bwf_app_l _ _ BWF))) as TB0. pose proof (bsum_nonneg _ (proj1 (bwf_app_r _ _ BWF))) as GB0.
      pose proof (bsum_ge _ (proj1 (bwf_app_l _ _ BWF))) as TLEN. pose proof (bsum_ge _ (proj1 (bwf_app_r _ _ BWF))) as GLEN.
      assert (GMAX : bsum gbs <= kQuarantineMax) by (rewrite <- EGB; clear - WG3; lia).
      pose proof (z_T_stk h GEO) as ZTS. pose proof (z_hull_stk h GEO) as ZHS. unfold zapart in ZTS, ZHS. cbn [fst snd] in ZTS, ZHS. fold L in ZTS, ZHS.
      destruct (Z_le_gt_dec (bsum tbs) kQuarantineCache) as [SMALL|BIG].
      - (* [comment removed for export] *)
        eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo (ff_kinv AL FF h) HK); [exact HJ| |].
        { unfold hm_qhead in QT.
          eapply (put_B_ret AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 s6 s5 s4 s3 s2 s1 s0 ra
                    _ _ _ SP p n STK T (bsum tbs) lo F fc m0 m0 []);
            [clear - SMALL TB0; lia| exact T0| subst T L; clear - T2 ACB; lia| exact QT| apply (ff_cs_T AL FF h WFKh)| exact PF| replace (SP + -80) with (SP - 80) by (clear; lia); exact ST
            | clear - LOL STK0; lia| clear - SPL; lia| clear - SPH STKH; lia| apply munch_refl| apply wmono_refl| exact MI|].
          apply (ff_cs_stack AL FF h lo (SP - lo) WFKh); [exact LOL| subst L; clear - SPH; lia]. }
        cbn beta. intros ms1 mo1 P1 HK1 MM1 HJ1. ddestruct P1 as (x10 & m1 & -> & MU1 & WM1 & MI1 & QT' & ST1).
        apply (EXIT h m1 mo1).
        assert (KO1 : forall A n', (A + n' <= lo \/ SP <= A) -> kept m0 m1 A n').
        { intros A n' D. apply (kept_of_munch _ m0 m1 A n' MU1). cbn. split; [exact D| exact I]. }
        split. { apply (proj2 (awf'_iff_WFC h)). apply (WFC_cap h ct kQuarantineMax); [exact WF| rewrite ETB; exact SMALL| clear - WG3; lia]. }
        assert (NODEK : forall b, In b (tbs ++ gbs) -> kept m0 m1 (bn_addr b) 8192).
        { intros b Hb. ddestruct (node_facts b Hb) as (_ & B1 & B2 & _). dpose W as (_ & _ & B6b & _).
          apply KO1. subst L. unfold ri_base, space_end, kSpaceSize in B2. clear - B1 B2 B6b ZHS LOL SPH. lia. }
        split. { apply (HMq_keepQ h m0 m1 LF WL' WR WK WS WD GEO BS WM1); [| exact HMQ].
                 intros A n' NZ x Hx. apply MU1. cbn [outside]. split; [| exact I]. intros R. apply (NZ (bv_unsigned x) Hx). left. fold L. clear - R LOL SPH; lia. }
        split. { unfold hm_quar. cbn zeta. fold L tbs gbs. unfold hm_qhead in *.
                 split; [exact QT'|]. split; [unfold blist in *; eapply blistT_k; [exact BLT| exact (proj1 (bwf_app_l _ _ BWF))| intros b Hb; apply NODEK; apply in_app_iff; left; exact Hb]|].
                 split; [unfold A_Q_GLOBAL, A_INSTANCE in *; eapply krw; [exact QG| apply KO1; cbn; clear - LOL STK0 ACB; lia]|].
                 split; [unfold blist in *; eapply blistT_k; [exact BLG| exact (proj1 (bwf_app_r _ _ BWF))| intros b Hb; apply NODEK; apply in_app_iff; right; exact Hb]|].
                 split; [exact BWF|]. split; [unfold A_Q_CMUTEX, A_INSTANCE in *; eapply krw; [exact MTX| apply KO1; cbn; clear - LOL STK0 ACB; lia]|].
                 exact (conj ETB EGB). }
        split; [exact HK1|]. split; [cbn [ms_mem] in HJ1; exact HJ1|]. split; [exact MI1|]. split; [exact ST1|]. split; [intros x Hx _; exact Hx|].
        split; [apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m0 m1 MU1); apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; exact Ha| apply Forall_nil]|].
        split; [exact (wmono_ex_of_wmono _ m0 m1 WM1)|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [intros c; reflexivity|].
        split; [intros k Hk; exact Hk|]. split; [intros sh Hsh; exact Hsh|]. split; [apply incl_refl|]. split; [intros k Hk _; left; exact Hk|]. intros g Hg; left; exact Hg.
      - (* [comment removed for export] *)
        assert (TB64 : bsum tbs < 2^64) by (clear - TB30; lia).
        eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo (ff_kinv AL FF h) HK); [exact HJ| |].
        { unfold hm_qhead in QT.
          eapply (put_B_drain AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 s6 s5 s4 s3 s2 s1 s0 ra
                    _ _ _ SP p n STK T (bsum tbs) lo F fc m0 m0 []);
            [clear - BIG TB64; lia| exact T0| subst T L; clear - T2 ACB; lia| exact STKB| exact QT| apply (ff_cs_T AL FF h WFKh)| exact PF
            | replace (SP + -80) with (SP - 80) by (clear; lia); exact ST
            | clear - LOL STK0; lia| clear - SPL; lia| clear - SPH STKH; lia| apply munch_refl| apply wmono_refl| exact MI|].
          apply (ff_cs_stack AL FF h lo (SP - lo) WFKh); [exact LOL| subst L; clear - SPH; lia]. }
        cbn beta. intros ms1 mo1 -> HK1 MM1 HJ1.
        (* [comment removed for export] *)
        assert (GL : Z.of_nat (length gbs) <> 0 ->
                  rw_cells asegs m0 (last_addr 0 gbs) [C8 (Z_to_bv 64 0)] /\ crange (ff_CS AL FF h) (last_addr 0 gbs) 8 /\ 0x65f000 <= last_addr 0 gbs /\ last_addr 0 gbs + 8192 <= 2^47
                  /\ (T + 4096 <= last_addr 0 gbs \/ last_addr 0 gbs + 8192 <= T) /\ (SP - 80 <= last_addr 0 gbs \/ last_addr 0 gbs + 8192 <= lo)).
        { intros NZ. destruct (snoc_or_nil gbs) as [E|(g0 & gl & E)]; [exfalso; apply NZ; rewrite E; reflexivity|].
          assert (Hgl : In gl (tbs ++ gbs)) by (apply in_app_iff; right; rewrite E; apply in_app_iff; right; left; reflexivity).
          ddestruct (node_facts gl Hgl) as (CSg & B1 & B2 & B3 & B4). rewrite E, last_addr_snoc.
          unfold blist in BLG. rewrite E, blistT_snoc in BLG. destruct BLG as [_ (N1 & N2 & N3)].
          apply (proj1 (rw_cells_app asegs m0 (bn_addr gl) [C8 _] [C8 _; C8 _])) in N1 as [N1 _].
          pose proof (z_T_hull h GEO) as ZTH. unfold zapart in ZTH. cbn [fst snd] in ZTH. fold L in ZTH.
          dpose W as (_ & B6a & B6b & _). ddestruct (L_GSB L W) as (_ & _ & RIE & RIH). unfold ri_base, space_end, kSpaceSize in B2, RIH.
          split; [exact N1|]. split; [eapply crange_sub; [exact CSg| clear; lia| clear; lia]|]. split; [exact B4|]. split; [clear - B3 ACB; lia|].
          split; [subst T L; clear - ZTH B1 B2 B6b; lia| subst L; clear - ZHS B1 B2 B6b LOL SPH SPL; lia]. }
        dpose HMQ as (G0h & G1h & _). pose proof (hm_ro_qmax _ _ (proj1 G1h)) as QMX.
        assert (HDT : 0 <= hd_addr tbs < 2^64).
        { destruct tbs as [|b0 r] eqn:Et; [cbn; clear; lia|]. ddestruct (node_facts b0 ltac:(rewrite Et; apply in_app_iff; left; left; reflexivity)) as (_ & _ & _ & B3 & B4). cbn. clear - B3 B4 ACB; lia. }
        assert (HDG : 0 <= hd_addr gbs < 2^64).
        { destruct gbs as [|b0 r] eqn:Eg; [cbn; clear; lia|]. ddestruct (node_facts b0 ltac:(rewrite Eg; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & B3 & B4). cbn. clear - B3 B4 ACB; lia. }
        pose proof (last_addr_bound 0 tbs (proj1 (bwf_app_l _ _ BWF)) ltac:(clear; lia)) as LAT.
        assert (TLEN1 : 1 <= Z.of_nat (length tbs)).
        { destruct tbs as [|b0 r] eqn:Et; [exfalso; apply TNE; unfold tbs in Et; destruct (q_batches (h_tq h)); [reflexivity| discriminate Et]| cbn; clear; lia]. }
        (* [comment removed for export] *)
        eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo1 (ff_kinv AL FF h) HK1); [exact HJ1| |].
        { unfold hm_qhead in QT, QG. replace (SP + -80) with (SP - 80) by (clear; lia).
          eapply (drain_spec AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) (Z_to_bv 64 A_QPUT_RA2) gp tp t0 t1 t2 (Z_to_bv 64 (A_INSTANCE + 728)) (Z_to_bv 64 (T + 80))
                    a4 a5 a6 a7 (Z_to_bv 64 n) (Z_to_bv 64 STK) (Z_to_bv 64 (T + 208)) (Z_to_bv 64 (p + -16)) (Z_to_bv 64 kQuarantineCache) s7 s8 s9 s10 s11 t3 t4 t5 t6
                    (Z_to_bv 64 0) (SP - 80) T STK (Z.of_nat (length tbs)) (hd_addr tbs) (last_addr 0 tbs) (bsum tbs) (Z.of_nat (length gbs)) (hd_addr gbs) (last_addr 0 gbs) (bsum gbs) lo F fc m0);
            [exact T0| subst T L; clear - T2 ACB; lia| exact STKB| exact TLEN1| clear; lia| clear - TLEN GLEN TB30 GMAX; unfold kQuarantineMax in *; lia| exact HDT| exact LAT| exact HDG
            | exact TB0| exact GB0| unfold kQuarantineMax in GMAX; clear - GMAX TB30 TB0 GB0; lia
            | unfold qc_cells; exact QT| apply (ff_cs_T AL FF h WFKh)| unfold qmutex_cells, A_Q_CMUTEX in *; exact MTX| unfold qc_cells, A_Q_GLOBAL in *; exact QG| exact QMX
            | exact GL| exact ST| clear - LOL STK0; lia| clear - SPL; lia| clear - SPH STKH; lia| subst T L; clear - ZTS LOL SPH SPL; lia| | exact MI].
          apply (ff_cs_stack AL FF h lo (SP - 80 - lo) WFKh); [exact LOL| subst L; clear - SPH; lia]. }
        cbn beta. intros ms2 mo2 P2 HK2 MM2 HJ2. unfold drain_post in P2.
        ddestruct P2 as (m2 & MU2 & WM2 & MI2 & QG2 & QT2 & GLN & ST2 & ARM).
        (* [comment removed for export] *)
        set (h3 := h_drainq h).
        pose proof (WFC_drainq h ct kQuarantineMax WF) as WF3. fold h3 in WF3.
        dpose W as (_ & B6a & B6b & _ & B6c & _). unfold kHighMemBeg in B6c. ddestruct (L_GSB L W) as (_ & _ & RIE & RIH). unfold ri_base, space_end, kSpaceSize in RIH.
        pose proof (z_T_hull h GEO) as ZTH. unfold zapart in ZTH. cbn [fst snd] in ZTH. fold L in ZTH.
        (* [comment removed for export] *)
        assert (GLB : Z.of_nat (length gbs) <> 0 -> exists gl, In gl gbs /\ last_addr 0 gbs = bn_addr gl /\ l_b6 L <= bn_addr gl /\ bn_addr gl + 8192 <= l_sb L + 2^37).
        { intros NZ. ddestruct (last_addr_in 0 gbs ltac:(intros E; apply NZ; rewrite E; reflexivity)) as (gl & Hgl & Egl).
          ddestruct (node_facts gl ltac:(apply in_app_iff; right; exact Hgl)) as (_ & B1 & B2 & _). unfold ri_base, space_end, kSpaceSize in B2.
          exists gl. exact (conj Hgl (conj Egl (conj B1 B2))). }
        assert (KO2 : forall A k, (A + k <= lo \/ SP - 80 <= A) -> (A + k <= A_INSTANCE + 880 \/ A_INSTANCE + 920 <= A) -> (A + k <= T + 80 \/ T + 112 <= A) ->
                      (A + k <= l_b6 L \/ l_sb L + 2^37 <= A) -> kept m0 m2 A k).
        { intros A k D1 D2 D3 D4 x Hx. apply MU2. cbn [outside app]. split; [clear - Hx D1; lia|]. split; [clear - Hx D2; lia|]. split; [clear - Hx D2; lia|]. split; [clear - Hx D3; lia|].
          destruct (Z.eqb_spec (Z.of_nat (length gbs)) 0) as [E0|NE]; cbn [outside]; [exact I|]. split; [| exact I].
          ddestruct (GLB NE) as (gl & Hgl & Egl & B1 & B2). rewrite Egl. clear - Hx D4 B1 B2. lia. }
        assert (PF2 : put_frame m2 SP T STK s6 s5 s4 s3 s2 s1 s0 ra).
        { unfold put_frame in *. eapply krw; [exact PF|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 80) with 80.
          apply KO2; subst T L; unfold A_INSTANCE; [clear; lia| clear - SPL LOL STK0 ACB; lia| clear - ZTS LOL SPH SPL; lia| clear - ZHS LOL SPH SPL B6b; lia]. }
        assert (HMQ2 : HMq h3 LF m2).
        { change (HMq h3 LF m2) with (HMq h LF m2). apply (HMq_keepQ h m0 m2 LF WL' WR WK WS WD GEO BS WM2); [| exact HMQ].
          intros A k NZ x Hx. apply MU2. cbn [outside app]. split; [| split; [| split; [| split]]].
          - intros R. apply (NZ (bv_unsigned x) Hx). left. fold L. clear - R LOL SPH SPL; lia.
          - intros R. apply (NZ (bv_unsigned x) Hx). right; left. unfold quar_img_ranges, A_INSTANCE in *. cbn. clear - R; lia.
          - intros R. apply (NZ (bv_unsigned x) Hx). right; left. unfold quar_img_ranges, A_INSTANCE in *. cbn. clear - R; lia.
          - intros R. apply (NZ (bv_unsigned x) Hx). right; right; left. fold L T. clear - R; lia.
          - destruct (Z.eqb_spec (Z.of_nat (length gbs)) 0) as [E0|NE]; cbn [outside]; [exact I|]. split; [| exact I]. intros R. apply (NZ (bv_unsigned x) Hx). do 3 right.
            ddestruct (GLB NE) as (gl & Hgl & Egl & _). unfold gbs in Hgl. apply in_map_iff in Hgl as (b0 & <- & Hb0). exists b0. split; [apply in_app_iff; right; exact Hb0| rewrite Egl in R; cbn [bn_addr bn_of] in R; clear - R; lia]. }
        assert (BWF3 : bwf (gbs ++ tbs)).
        { eapply bwf_of_perm; [exact BWF| rewrite !map_app; apply Permutation_app_comm| rewrite Forall_app; split; [exact (proj1 (bwf_app_r _ _ BWF))| exact (proj1 (bwf_app_l _ _ BWF))]]. }
        assert (QG2' : hm_qhead m2 A_Q_GLOBAL (gbs ++ tbs)).
        { unfold hm_qhead, A_Q_GLOBAL. unfold qc_cells in QG2.
          replace (Z.of_nat (length (gbs ++ tbs))) with (Z.of_nat (length gbs) + Z.of_nat (length tbs)) by (rewrite length_app; clear; lia).
          replace (hd_addr (gbs ++ tbs)) with (if Z.of_nat (length gbs) =? 0 then hd_addr tbs else hd_addr gbs) by (destruct gbs; reflexivity).
          replace (last_addr 0 (gbs ++ tbs)) with (last_addr 0 tbs) by (rewrite last_addr_app; destruct tbs as [|tb0 tr] eqn:Et; [exfalso; clear - TLEN1; cbn in TLEN1; lia| apply last_addr_cons_ne]).
          rewrite bsum_app. exact QG2. }
        assert (BL2 : blist m2 (gbs ++ tbs)).
        { unfold blist in *. apply (proj2 (blistT_app m2 gbs tbs 0)). split.
          - destruct (snoc_or_nil gbs) as [E|(g0 & gl & E)]; [rewrite E; exact I|].
            assert (NZ : Z.of_nat (length gbs) <> 0) by (rewrite E, length_app; cbn; clear; lia).
            rewrite E in BLG |- *. apply (proj1 (blistT_snoc m0 g0 gl 0)) in BLG as [B0 (N1 & N2 & N3)]. apply (proj2 (blistT_snoc m2 g0 gl _)).
            assert (Hgl : In gl (tbs ++ gbs)) by (apply in_app_iff; right; rewrite E; apply in_app_iff; right; left; reflexivity).
            pose proof (bwf_ok_in _ _ BWF Hgl) as OKgl. pose proof OKgl as OK'. unfold bn_ok in OK'.
            assert (EGL : last_addr 0 gbs = bn_addr gl) by (rewrite E, last_addr_snoc; reflexivity).
            split.
            + eapply blistT_k; [exact B0| rewrite E in BWF; exact (proj1 (bwf_app_l _ _ (bwf_app_r _ _ BWF)))|].
              intros b Hb. ddestruct (node_facts b ltac:(apply in_app_iff; right; rewrite E; apply in_app_iff; left; exact Hb)) as (_ & B1 & B2 & _). unfold ri_base, space_end, kSpaceSize in B2.
              assert (AP : bn_addr b + 8192 <= bn_addr gl \/ bn_addr gl + 8192 <= bn_addr b).
              { apply (bapart_in _ _ _ BWF ltac:(apply in_app_iff; right; rewrite E; apply in_app_iff; left; exact Hb) Hgl). intros EA.
                rewrite E in BWF. pose proof (bwf_app_r _ _ BWF) as [_ [ND _]]. rewrite map_app in ND. cbn [map] in ND. apply NoDup_remove_2 in ND. apply ND. rewrite <- EA. apply in_or_app. left. apply in_map. exact Hb. }
              intros x Hx. apply MU2. unfold A_INSTANCE. cbn [outside app]. rewrite (proj2 (Z.eqb_neq _ _) NZ). cbn [outside]. rewrite EGL.
              split; [subst L; clear - Hx B1 B2 ZHS LOL SPH SPL B6b; lia|]. split; [clear - Hx B1 B6c; lia|]. split; [clear - Hx B1 B6c; lia|]. split; [subst T L; clear - Hx B1 B2 ZTH B6b; lia|]. split; [clear - Hx AP; lia| exact I].
            + ddestruct (node_facts gl Hgl) as (_ & B1 & B2 & _). unfold ri_base, space_end, kSpaceSize in B2.
              assert (KG : kept m0 m2 (bn_addr gl + 8) (8192 - 8)).
              { intros x Hx. apply MU2. unfold A_INSTANCE. cbn [outside app]. rewrite (proj2 (Z.eqb_neq _ _) NZ). cbn [outside]. rewrite EGL.
                split; [subst L; clear - Hx B1 B2 ZHS LOL SPH SPL B6b; lia|]. split; [clear - Hx B1 B6c; lia|]. split; [clear - Hx B1 B6c; lia|]. split; [subst T L; clear - Hx B1 B2 ZTH B6b; lia|]. split; [clear - Hx; lia| exact I]. }
              split; [| split].
              * apply (proj2 (rw_cells_app asegs m2 (bn_addr gl) [C8 _] [C8 _; C8 _])). split.
                -- rewrite <- EGL. replace (hd_addrT tbs 0) with (hd_addr tbs) by reflexivity. exact (GLN NZ).
                -- apply (proj1 (rw_cells_app asegs m0 (bn_addr gl) [C8 _] [C8 _; C8 _])) in N1 as [_ N1b]. eapply krw; [exact N1b|]. cbn [cells_size csize Nat.add].
                   eapply kept_sub; [exact KG| clear; lia| cbn; clear; lia].
              * eapply ku64; [exact N2|]. eapply kept_sub; [exact KG| clear; lia| unfold bn_count in OK'; clear - OK'; lia].
              * eapply wr_at_transport; [exact N3| exact WM2].
          - eapply blistT_k; [exact BLT| exact (proj1 (bwf_app_l _ _ BWF))|].
            intros b Hb. ddestruct (node_facts b ltac:(apply in_app_iff; left; exact Hb)) as (_ & B1 & B2 & _). unfold ri_base, space_end, kSpaceSize in B2.
            intros x Hx. apply MU2. unfold A_INSTANCE. cbn [outside app].
            split; [subst L; clear - Hx B1 B2 ZHS LOL SPH SPL B6b; lia|]. split; [clear - Hx B1 B6c; lia|]. split; [clear - Hx B1 B6c; lia|]. split; [subst T L; clear - Hx B1 B2 ZTH B6b; lia|].
            destruct (Z.eqb_spec (Z.of_nat (length gbs)) 0) as [E0|NE]; cbn [outside]; [exact I|]. split; [| exact I].
            ddestruct (GLB NE) as (gl & Hgl & Egl & _). rewrite Egl.
            assert (AP : bn_addr b + 8192 <= bn_addr gl \/ bn_addr gl + 8192 <= bn_addr b).
            { apply (bapart_in _ _ _ BWF ltac:(apply in_app_iff; left; exact Hb) ltac:(apply in_app_iff; right; exact Hgl)). intros EA.
              pose proof BWF as [_ [ND _]]. rewrite map_app in ND. apply (NoDup_app_l_r _ _ (bn_addr b) ND); [apply in_map; exact Hb| rewrite EA; apply in_map; exact Hgl]. }
            clear - Hx AP; lia. }
        assert (QT2' : hm_qhead m2 (T + 80) []) by (unfold hm_qhead; unfold qc_cells in QT2; exact QT2).
        assert (BS3 : forall b0, In b0 (q_batches (h_tq h3) ++ q_batches (h_gq h3)) -> exists i, 0 <= i < carved h3 kBatchClass /\ b_addr b0 = chunk_at (h_L h3) kBatchClass i).
        { intros b0 Hb0. apply BS. apply in_app_iff. cbn in Hb0. apply in_app_iff in Hb0 as [Hb0|Hb0]; [right| left]; exact Hb0. }
        assert (GQ3 : map bn_of (q_batches (h_gq h3)) = gbs ++ tbs) by (unfold h3, h_drainq, q_transfer; cbn; rewrite map_app; reflexivity).
        assert (FK02 : fkeepR L (blocks h) (qs_of h) (rp_of h) (d_nb (h_dep h)) (d_bl (h_dep h)) lo SP m0 m2).
        { apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m0 m2 MU2).
          apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; clear - Ha; lia|].
          apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; do 5 right; left; unfold free_img_ranges; cbn; clear - Ha; lia|].
          apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; do 5 right; left; unfold free_img_ranges; cbn; clear - Ha; lia|].
          apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; right; left; subst T L; clear - Ha; lia|].
          destruct (Z.eqb_spec (Z.of_nat (length gbs)) 0) as [E0|NE]; [apply Forall_nil|]. apply Forall_cons; [| apply Forall_nil].
          intros a Ha. cbn [fst snd] in Ha. ddestruct (GLB NE) as (gl & Hgl & Egl & B1 & B2). rewrite Egl in Ha. do 2 right; left. split.
          - unfold in_hull. subst L. clear - Ha B1 B2 B6b. lia.
          - intros IB. exact (nodes_not_blocks gl a ltac:(apply in_app_iff; right; exact Hgl) IB ltac:(clear - Ha; lia)). }
        destruct ARM as [(LE & MTX2 & x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & ->)|(GT & MTX2 & x0 & x1 & x2 & y4 & y5 & y6 & y7 & ->)].
        + (* [comment removed for export] *)
          assert (HQ3 : hm_quar h3 m2).
          { unfold hm_quar. cbn zeta. change (h_L h3) with (h_L h). rewrite GQ3. cbn [h3 h_drainq set_tq h_tq q_batches map q_bytes qcache0 set_gq h_gq q_transfer]. fold L T.
            split; [exact QT2'|]. split; [exact I|]. split; [exact QG2'|]. split; [exact BL2|]. split; [cbn [app]; exact BWF3|].
            split; [unfold A_Q_CMUTEX; unfold qmutex_cells in MTX2; exact MTX2|]. split; [reflexivity|]. rewrite bsum_app, <- EGB, <- ETB. reflexivity. }
          replace (ret_pc (Z_to_bv 64 A_QPUT_RA2)) with (Z_to_bv 64 A_QPUT_RA2) by (symmetry; apply ret_pc_even; [unfold A_QPUT_RA2; clear; lia| reflexivity]).
          eapply (evtA_aevtS_KJ AL (ff_CS AL FF h) (ff_K AL FF h) _ Q _ mo2 (ff_kinv AL FF h) HK2); [exact HJ2| |].
          { eapply (put_C AL IMG ALWF (ff_CS AL FF h) (ff_csok AL FF h) gp tp x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 _ _ _ _ _ _ _ s7 s8 s9 s10 s11 t3 t4 t5 t6
                      s6 s5 s4 s3 s2 s1 s0 ra SP STK T lo F fc m2 m2 []);
              [exact PF2| replace (SP + -80) with (SP - 80) by (clear; lia); exact ST2| clear - LOL STK0; lia| clear - SPL; lia| clear - SPH STKH; lia
              | apply munch_refl| apply wmono_refl| exact MI2|].
            apply (ff_cs_stack AL FF h lo (SP - lo) WFKh); [exact LOL| subst L; clear - SPH; lia]. }
          cbn beta. intros ms3 mo3 P3 HK3 MM3 HJ3. ddestruct P3 as (m3 & -> & MU3 & WM3 & MI3 & ST3).
          apply (EXIT h3 m3 mo3).
          split. { apply (proj2 (awf'_iff_WFC h3)). apply (WFC_cap h3 0 (q_bytes (h_gq h) + q_bytes (h_tq h)) _ _ WF3); [cbn; unfold kQuarantineCache; clear; lia|].
                   cbn. rewrite ETB, EGB. exact LE. }
          split. { change (HMq h3 LF m3) with (HMq h LF m3). apply (HMq_keepQ h m2 m3 LF WL' WR WK WS WD GEO BS WM3); [| exact HMQ2].
                   intros A k NZ x Hx. apply MU3. cbn [outside]. split; [| exact I]. intros R. apply (NZ (bv_unsigned x) Hx). left. fold L. clear - R LOL SPH; lia. }
          split. { dpose WF3 as (_ & _ & WR3 & _). apply (hm_quar_keepS h3 m2 m3 lo SP W WR3 GEO BS3 LOL SPH HQ3 MU3 WM3). }
          split; [exact (ff_view_K AL FF h h3 mo3 (kview_dq h) HK3)|]. split; [cbn [ms_mem] in HJ3; exact HJ3|]. split; [exact MI3|]. split; [exact ST3|].
          split; [intros x Hx _; exact (ff_view_CS AL FF h h3 x (kview_dq h) Hx)|].
          split. { eapply fkeepR_trans; [exact FK02| | apply incl_refl| apply incl_refl].
                   apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m2 m3 MU3). apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; exact Ha| apply Forall_nil]. }
          split; [exact (wmono_ex_trans _ m0 m2 m3 (wmono_ex_of_wmono _ m0 m2 WM2) (wmono_ex_of_wmono _ m2 m3 WM3))|].
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
          split; [intros c; reflexivity|].
          split; [intros k Hk; exact Hk|]. split; [intros sh Hsh; exact Hsh|]. split; [apply incl_refl|]. split; [intros k Hk _; left; exact Hk|]. intros g Hg; left; exact Hg.
        + (* [comment removed for export] *)
          replace (Z_to_bv 64 (SP + -80)) with (Z_to_bv 64 (SP - 80)) by (f_equal; clear; lia).
          replace (Z_to_bv 64 (T + 208)) with (Z_to_bv 64 (l_T (h_L h3) + 208)) by reflexivity.
          assert (SPA' : (SP - 80) mod 16 = 0).
          { replace (SP - 80) with (SP + (-5) * 16) by (clear; lia). rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by (clear; lia). exact SPA. }
          apply (recycle_top AL IMG ALWF ASB FF h3 0 (q_bytes (h_gq h) + q_bytes (h_tq h)) m2 LF (SP - 80) lo STK gp tp F fc Q
                   (Z_to_bv 64 A_QPUT_RA2) (Z_to_bv 64 (A_INSTANCE + 728)) (Z_to_bv 64 (T + 80)) (Z_to_bv 64 n) (Z_to_bv 64 STK) (Z_to_bv 64 (T + 208))
                   (Z_to_bv 64 (p + -16)) (Z_to_bv 64 kQuarantineCache) s7 s8 s9 s10 s11 TP WF3 eq_refl HV H32);
            rewrite ?GQ3; [exact BWF3| | exact LOL| clear - SPL; lia| change (l_stk_hi (h_L h3)) with (l_stk_hi L); subst L; clear - SPH; lia| exact SPA'| exact STKB| exact GEO
            | unfold h3, h_drainq, q_transfer; cbn; intros E; apply TNE; apply app_eq_nil in E as [_ E]; exact E| | exact (ff_view_K AL FF h h3 mo2 (kview_dq h) HK2)| cbn [ms_mem] in HJ2; exact HJ2| exact MI2| exact HMQ2| exact QT2'| exact QG2'| exact BL2
            | unfold A_Q_CMUTEX; unfold qmutex_cells in MTX2 |- *; exact MTX2| rewrite bsum_app; exact GT| exact ST2].
          * rewrite bsum_app. unfold kQuarantineMax in GMAX. clear - GMAX TB30 TB0 GB0. lia.
          * (* [comment removed for export] *)
            intros h' m' mo' x0' x1' x2' z0 z1 z2 z3 z4 z5 z6 z7 x3' x4' x5' x6' RP.
            dpose RP as (AWF' & TQ' & HMQ' & HQ' & HK' & HJ' & MI' & ST' & CSR' & FK' & WMX' & EL' & ED' & EB' & EHV' & EFK' & EIA' & EPA' & ECI' & ERU' & SUBK' & SUBS' & GH1 & GH2 & GH3).
            pose proof (WFR_of_awf' h' AWF') as WFR'. dpose WFR' as (WLh' & WCh' & WRh' & WKh' & WQh' & WSh' & WDh' & _).
            assert (ELh : h_L h' = L) by (rewrite EL'; reflexivity).
            assert (HVh : h_havol h' <= AVOL_MAX) by (rewrite EHV'; exact HV).
            pose proof (ff_geom AL FF h' mo' (WFK_of_WFR h' WFR' HVh) HK') as GEOh.
            assert (PF' : put_frame m' SP T STK s6 s5 s4 s3 s2 s1 s0 ra).
            { unfold put_frame in *. eapply krw; [exact PF2|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 80) with 80. replace (SP + -80) with (SP - 80) by (clear; lia).
              dpose WF3 as (_ & _ & _ & WK3 & _ & WS3 & _).
              exact (put_frame_kept h3 m2 m' (or_intror I) eq_refl GEO WK3 WS3 FK'). }
            replace (ret_pc (Z_to_bv 64 A_QPUT_RA2)) with (Z_to_bv 64 A_QPUT_RA2) by (symmetry; apply ret_pc_even; [unfold A_QPUT_RA2; clear; lia| reflexivity]).
            eapply (evtA_aevtS_KJ AL (ff_CS AL FF h') (ff_K AL FF h') _ Q _ mo' (ff_kinv AL FF h') HK'); [exact HJ'| |].
            { eapply (put_C AL IMG ALWF (ff_CS AL FF h') (ff_csok AL FF h') gp tp x0' x1' x2' z0 z1 z2 z3 z4 z5 z6 z7 _ _ _ _ _ _ _ s7 s8 s9 s10 s11 x3' x4' x5' x6'
                        s6 s5 s4 s3 s2 s1 s0 ra SP STK T lo F fc m' m' []);
                [exact PF'| replace (SP + -80) with (SP - 80) by (clear; lia); exact ST'| clear - LOL STK0; lia| clear - SPL; lia| clear - SPH STKH; lia
                | apply munch_refl| apply wmono_refl| exact MI'|].
              apply (ff_cs_stack AL FF h' lo (SP - lo) (WFK_of_WFR h' WFR' HVh)); rewrite ELh; [exact LOL| subst L; clear - SPH; lia]. }
            cbn beta. intros ms4 mo4 P4 HK4 MM4 HJ4. ddestruct P4 as (m4 & -> & MU4 & WM4 & MI4 & ST4).
            assert (BSh : forall b0, In b0 (q_batches (h_tq h') ++ q_batches (h_gq h')) -> exists i, 0 <= i < carved h' kBatchClass /\ b_addr b0 = chunk_at (h_L h') kBatchClass i).
            { intros b0 Hb0. exact (batch_slot h' b0 WFR' Hb0). }
            apply (EXIT h' m4 mo4).
            split; [exact AWF'|].
            split. { apply (HMq_keepQ h' m' m4 LF WLh' WRh' WKh' WSh' WDh' GEOh BSh WM4); [| exact HMQ'].
                     intros A k NZ x Hx. apply MU4. cbn [outside]. split; [| exact I]. intros R. apply (NZ (bv_unsigned x) Hx). left. rewrite ELh. clear - R LOL SPH; lia. }
            split. { apply (hm_quar_keepS h' m' m4 lo SP (proj1 WLh') WRh' GEOh BSh); rewrite ?ELh; [exact LOL| exact SPH| exact HQ'| exact MU4| exact WM4]. }
            split; [exact HK4|]. split; [cbn [ms_mem] in HJ4; exact HJ4|]. split; [exact MI4|]. split; [exact ST4|].
            split; [intros x Hx NQ; apply CSR'; [exact (ff_view_CS AL FF h h3 x (kview_dq h) Hx)| exact NQ]|].
            split. { eapply fkeepR_trans; [exact FK02| | apply incl_refl| apply incl_refl].
                     eapply fkeepR_trans; [exact (fkeepR_sp_mono _ _ _ _ _ _ lo (SP - 80) SP m2 m' FK' ltac:(clear; lia))| | apply incl_refl| apply incl_refl].
                     apply (fkeepR_of_munch _ _ _ _ _ _ _ _ _ m' m4 MU4). apply Forall_cons; [intros a Ha; cbn [fst snd] in Ha; left; exact Ha| apply Forall_nil]. }
            split. { eapply wmono_ex_trans; [exact (wmono_ex_of_wmono _ m0 m2 WM2)|]. eapply wmono_ex_trans; [exact WMX'| exact (wmono_ex_of_wmono _ m' m4 WM4)]. }
            split; [exact EL'|]. split; [exact ED'|]. split; [exact EB'|]. split; [exact EHV'|]. split; [exact EFK'|]. split; [exact EIA'|]. split; [exact EPA'|]. split; [exact ECI'|]. split; [exact ERU'|].
            split; [exact SUBK'|]. split; [exact SUBS'|]. split; [exact GH1|]. split; [exact GH2| exact GH3].
    Qed.
  End D.
End PhD.
End ARUN_1.
