(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanPlanCore AsanPlan AsanPlanSound AsanAcct AsanInit AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AH0Spec0 AH0Base AH0Layout AH0Pure AH0Vwf.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APS.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ahx.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_AH0K () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.pagedown"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.pageup"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.zpb"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Vwf.AL0"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Stdlib.Lists.List.In"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.zB"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.zE"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanAcct.page_allowedb"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.me_allow"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.node_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Base.PG"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dnodes"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.store_tr"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dstore"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.ri_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Spec0.L0_of"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.TR"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_thr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KEager"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_treg"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_fstk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dtls"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_len"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.csranges"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vgood"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.winst"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WAlu"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WLit"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WVar"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_prim"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_pslack"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Layout.SB"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_s1"; "LinuxProcessSemantics.Riscv.Instr.ALU_SRL"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_s2"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sh_window_good : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "Pb,$0.Pn,$0.PB,$0.PN,$0.Ppg,$0.P,(1.=R3.)P,(1.R4.R6.)P,(2.=R6.)P,(1.(3.R8.R7.)(3.R6.R5.))P,(1.(4.(3.+7???8000.(5.R9.+8.)))R5.)P,(1.(3.R6.+1000.)(6.(3.+7???8000.(5.(3.R:.R9.)+8.))))P,(7.$0.(8.R7.+1000.)=)(9.(1.(:.(;.$<.R:.))R8.)(1.R8.(:.(;.$<.(=.(3.R:.R9.)+1.)))))")
(* [comment removed for export] *).
Proof.
  intros b n B N pg HB0 HB Hn HN W1 W2 AL. unfold zpb, shadow_of, AL0. cbn [al_sb]. unfold pagedown, pageup in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  split; [nia|].
  (* [comment removed for export] *)
  assert ((b + n) / 8 <= (B + N - 1) / 8 + 1) by (apply Z.le_trans with ((B + N) / 8); [apply Z.div_le_mono; lia| nia]).
  nia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma own_window : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "Pb,$0.Pn,$0.Ppg,$0.P,(7.$0.(8.R3.+1000.)=)P,(7.$0.(8.R3.+1000.)=)P,(1.(4.R5.)R3.)P,(1.(3.R4.+1000.)(6.(3.R6.R5.)))(9.(1.R7.R5.)(1.(3.R5.+1000.)(3.R7.R6.)))")
(* [comment removed for export] *).
Proof.
  intros b n pg Hb Hn W1 W2. unfold pagedown, pageup in *.
  pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.div_mod n 4096 ltac:(lia)). rewrite Hb in *. rewrite Hn in *.
  replace (b + n + 4095) with (4095 + (b / 4096 + n / 4096) * 4096) in W2 by lia.
  rewrite Z_div_plus_full in W2 by lia. change (4095 / 4096) with 0 in W2. lia.
Qed.

Section K.
  Context {hAR : arun}.
  Variables (sp : word) (fs : Fs.Fs).
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Variable STKHI : Z.
  Variable FOG : list (Z * Z).
  Variable TF : Z.
  Variable md : Model.
  Hypothesis HMOD : me_model sp fs p md.
  (* [comment removed for export] *)
  Hypothesis HAC : ACEIL = STKPG p - 0x800000.
  Hypothesis HSP : bv_unsigned sp = SP p.
  Hypothesis STKHI_gt : SP p < STKHI.
  Hypothesis STKHI_47 : STKHI <= 2 ^ 47.

  Let bp := bp_of p STKHI FOG TF.
  Let h0 := h0_of bp.
  Let v0 := vst_of h0.
  Local Ltac pv := cbn; first [clear; tauto | tauto]. (* [comment removed for export] *)

  (* [comment removed for export] *)
  Let M := vm_maps (m_vmmaps md).
  Let N := vm_noaccess (m_vmmaps md).
  Let Lz := m_vm_lazy md.

  (* [comment removed for export] *)
  Local Ltac mm X :=
    pose proof HMOD as X; unfold me_model in X;
    destruct X as (Mhalt & Mfds & Mfs & Mres & Mlim & Mfog & Mseps & Mwf & Mbounds & Mlazyb & Mnasub & MNsecv & MNgap
                   & MAdstore & MAhigh & MAlow & Mtot & Misp & Mbrk & Msbrk & Meager & Mabytes & Mminv & MNcov & MLcov
                   & Ndivec & Ngvec & Ndstore & Ndnodes & Nfstk & Ndtls & Ntvec & Ntreg & Nthr & Nictx & Nlla & Nhigh & Nlow
                   & Ldivec & Lgvec & Ldnodes & Lfstk & Ldtls & Ltvec & Ltreg & Lthr & Lictx & Llla & Mri & K5secv & K5prim & K5gap).   (* [comment removed for export] *)

  #[using="sp fs HMOD"] Lemma MM_minv : MInv (me_allow p) md.
  Proof. mm X. exact Mminv. Qed.
    #[using="sp fs p HMOD"] Lemma MM_Lzcov : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "Pe,(>.(?.&40.)(?.&40.))P,(10.(>.(?.&40.)(?.&40.))R1.VLz,)(9.(2.=(11.&40.(12.(?.&40.)(?.&40.)R2.)))(13.(>.(?.&40.)(?.&40.))Liv,(>.(?.&40.)(?.&40.))(9.(10.(>.(?.&40.)(?.&40.))R1.VM,)(9.(1.(14.R1.)(14.R3.))(1.(15.R3.)(15.R1.))))))")
(* [comment removed for export] *).
  Proof. mm X. exact MLcov. Qed.

  (* [comment removed for export] *)
  #[using="sp fs HMOD"] Lemma mat_facts : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "Ppg,(?.&40.)P,(10.(?.&40.)R1.(16.Vmd,))(9.(7.$0.(8.(11.&40.R2.)+1000.)=)(9.(13.(>.(?.&40.)(?.&40.))Le,(>.(?.&40.)(?.&40.))(9.(10.(>.(?.&40.)(?.&40.))R1.VLz,)(9.(1.(14.R1.)(11.&40.R3.))(1.(3.(11.&40.R3.)+1000.)(15.R1.)))))(7.$17.(18.(19.Vp,)R2.)$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros pg Hpg. destruct MM_minv as [N1 N2 N3 N4 N5].
    split; [exact (N2 pg Hpg)|]. split; [| exact (N3 pg Hpg)].
    pose proof (N4 pg Hpg) as L. apply page_in_ranges_true in L as (e & He & E1 & E2). exists e. unfold zB, zE, page_size in *. auto.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma cs_gsh : forall r, In r (GSH p) -> In r (csranges v0).
  Proof. intros r Hr. unfold csranges. right. right. apply in_app_iff. right. cbn [v0 vst_of v_ghost h0 h0_of h_acct a_sech h_L L0_of l_gsh bp bp_of bp_gsh app]. exact Hr. Qed.
  #[using="Type"] Lemma cs_img : In (0x10000, 0x64f000) (csranges v0).
  Proof. unfold csranges. right. left. reflexivity. Qed.
  #[using="Type"] Lemma cs_tr : forall t, In t (tr_of h0) -> t_cs t = true -> In (t_lo t, t_len t) (csranges v0).
  Proof. intros t Ht TC. unfold csranges. right. right. apply in_app_iff. left. apply in_map_iff. exists t. split; [reflexivity|]. apply filter_In. auto. Qed.

  #[using="Type"] Lemma cs_trk : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "Pt,$1;.P,(10.$1;.R1.(1<.$1;.(1=.$1;.(1>.(1?.Vp,$20.))(1=.$1;.(21.(1?.Vp,$22.))(1=.$1;.(23.(24.Vbp,))(25.$1;.))))(1=.$1;.(26.(1?.Vp,$27.)+1000.$28.$1:.$1:.)(1=.$1;.(26.(1?.Vp,$29.)+10000.$28.$1:.$1:.)(1=.$1;.(26.(1?.Vp,$2:.)$2;.$28.$1:.$1:.)(1=.$1;.(26.(1?.Vp,$2<.)+1000.$28.$1:.$1:.)(25.$1;.)))))))(10.(>.$0.$0.)(2=.$0.$0.(2>.R2.)(2?.R2.))(30.Vv0,))")
(* [comment removed for export] *).
  Proof.
    intros t Ht. destruct (tr_of_h0 p STKHI FOG TF) as [K E]. apply cs_tr.
    - unfold h0, bp. rewrite E. apply in_app_iff in Ht as [Ht|Ht]; apply in_app_iff; [left; exact Ht | right; apply in_app_iff; left; exact Ht].
    - apply in_app_iff in Ht as [Ht|Ht]; [destruct Ht as [<-|[<-|[<-|[]]]] | destruct Ht as [<-|[<-|[<-|[<-|[]]]]]]; reflexivity.
  Qed.

  #[using="Type"] Lemma good_sh : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "PR,(>.$0.$0.)Pb,$0.Pn,$0.Ppg,(?.&40.)P,(10.(>.$0.$0.)R4.(30.Vv0,))P,(1.=(31.$0.$0.R5.))P,(1.(31.$0.$0.R6.)R5.)P,(2.=R5.)P,(1.(3.R7.R6.)(3.(31.$0.$0.R8.)(12.$0.$0.R8.)))P,(1.(4.(3.+7???8000.(5.R8.+8.)))(11.&40.R6.))P,(1.(3.(11.&40.R7.)+1000.)(6.(3.+7???8000.(5.(3.R9.R8.)+8.))))P,(7.$0.(8.(11.&40.R8.)+1000.)=)(32.$<.Vv0,R9.)")
(* [comment removed for export] *).
  Proof.
    intros R b n pg HR R0 R1 Hn R2 W1 W2 AL. unfold vgood, vgood_b. apply Bool.orb_true_iff. left. apply existsb_exists. exists R. split; [exact HR|].
    destruct (sh_window_good b n (fst R) (snd R) (bv_unsigned pg) R0 R1 Hn R2 W1 W2 AL) as [G1 G2].
    unfold pg_shadow_b. rewrite !andb_true_iff. repeat split; [apply Z.leb_le; exact G1 | apply Z.leb_le; exact G2 | apply Z.eqb_eq; exact AL].
  Qed.
  #[using="Type"] Lemma good_store : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "Ppg,(?.&40.)P,(1.(1?.Vp,$22.)(11.&40.R1.))P,(1.(3.(11.&40.R2.)+1000.)(3.(1?.Vp,$22.)(33.+2.+17.)))P,(7.$0.(8.(11.&40.R3.)+1000.)=)(32.$<.Vv0,R4.)")
(* [comment removed for export] *).
  Proof.
    intros pg H1 H2 AL. unfold vgood, vgood_b. apply Bool.orb_true_iff. right. apply existsb_exists. exists (PG p v_dstore, 2 ^ 23). split.
    - unfold lazyranges. apply in_map_iff. exists (store_tr (PG p v_dstore)). split; [reflexivity|]. apply filter_In. split; [| reflexivity].
      unfold v0, h0. cbn [vst_of v_tr]. unfold tr_of. apply in_app_iff. right. apply in_app_iff. left. cbn. left. reflexivity.
    - unfold pg_inside_b. cbn [fst snd]. rewrite !andb_true_iff. repeat split; [apply Z.leb_le | apply Z.leb_le | apply Z.eqb_eq]; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma u_wlit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (winst p (WLit z)) = z.
  Proof. intros z Hz. cbn [winst]. rewrite Z_to_bv_unsigned. cbn [bv_wrap bv_modulus]. change (2 ^ Z.of_N 64) with (2 ^ 64). apply Z.mod_small. exact Hz. Qed.

  (* [comment removed for export] *)
  #[using="HCN"] Lemma u_divec : bv_unsigned (winst p (#0x1000 * v_divec)%tm) = PG p v_divec. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_gvec : bv_unsigned (winst p (#0x1000 * v_gvec)%tm) = PG p v_gvec. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_dstore : bv_unsigned (winst p (#0x1000 * v_dstore)%tm) = PG p v_dstore. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_dnodes : bv_unsigned (winst p (#0x1000 * v_dnodes)%tm) = PG p v_dnodes. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_fstk : bv_unsigned (winst p (#0x1000 * v_fstk)%tm) = PG p v_fstk. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_dtls : bv_unsigned (winst p (#0x1000 * v_dtls)%tm) = PG p v_dtls. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_tvec : bv_unsigned (winst p (#0x1000 * v_tvec)%tm) = PG p v_tvec. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_treg : bv_unsigned (winst p (#0x1000 * v_treg)%tm) = PG p v_treg. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_thr : bv_unsigned (winst p (#0x1000 * v_thr)%tm) = PG p v_thr. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_ictx : bv_unsigned (winst p (#0x1000 * v_ictx)%tm) = PG p v_ictx. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_lla : bv_unsigned (winst p (#0x1000 * v_lla)%tm) = PG p v_lla. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_tmpv : bv_unsigned (winst p (#0x1000 * v_tmpv)%tm) = PG p v_tmpv. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_mus1 : bv_unsigned (winst p (#0x1000 * v_mus1)%tm) = PG p v_mus1. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_mus2 : bv_unsigned (winst p (#0x1000 * v_mus2)%tm) = PG p v_mus2. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_prim : bv_unsigned (winst p (#0x1000 * v_prim)%tm) = PG p v_prim. Proof. apply (u_page p HCN); pv. Qed.
  #[using="HCN"] Lemma u_secv : bv_unsigned (winst p (#0x1000 * v_secv)%tm) = PG p v_secv. Proof. apply (u_page p HCN); pv. Qed.
  #[using="hAR HCN"] Lemma u_brk0pg : bv_unsigned (winst p (#0x1000 * v_brk0pg)%tm) = PG p v_brk0pg.
  Proof. pose proof (r_brk0pg p HCN). unfold PG. rewrite zev_exact; cbn [zev]; lia. Qed.
  #[using="hAR HCN"] Lemma u_mus1p : bv_unsigned (winst p ((#0x1000 * v_mus1) + #0x1000)%tm) = PG p v_mus1 + 4096.
  Proof. pose proof (proj1 (PG_range p HCN v_mus1 ltac:(pv))). unfold PG in *. rewrite zev_exact; cbn [zev]; lia. Qed.
  #[using="hAR HCN"] Lemma u_ri : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "(7.$0.(11.&40.(34.Vp,(35.$36.(35.$36.(37.$38.(39.+1000.)(3:.$3;.))(37.$38.(39.-1000.)(3:.$3<.)))(39.+2000010000.))))(3.(3=.Vp,)(33.+2.+25.)))")
(* [comment removed for export] *).
  Proof. pose proof (r_prim p HCN). pose proof (r_pslack p HCN). unfold SB, PG in *. rewrite zev_exact; cbn [zev]; lia. Qed.
  #[using="HCN HAC"] Lemma u_stkb : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "(7.$0.(11.&40.(34.Vp,(35.$36.(35.$36.(37.$38.(39.+8000.)(3:.$3>.))(37.$38.(39.+1000.)(35.$3?.(3:.$40.)(39.+8.))))(39.-800000.))))(41.VhAR,))")
(* [comment removed for export] *).
  Proof.
    pose proof (r_s1 p HCN) as S1. pose proof (r_s2 p HCN) as S2. rewrite HAC.
    pose proof (zev_STKPG p (proj2 S2)) as ZS. unfold W_STKPG in ZS.
    pose proof (Z.div_pos (uv p v_s2) 256 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (uv p v_s2) 256 8 ltac:(lia) ltac:(lia)).
    rewrite zev_exact; cbn [zev]; cbn [zev] in ZS; rewrite ZS; unfold STKPG; lia.
  Qed.
  #[using="HCN HAC"] Lemma u_stkn : ltac2:(CDefT.buildp (gd_tbl_AH0K ()) "(7.$0.(11.&40.(34.Vp,(35.$36.(35.$36.(37.$38.(39.-8000.)(3:.$3>.))(37.$38.(39.-1000.)(35.$3?.(3:.$40.)(39.+8.))))(39.+800000800000.))))(=.(33.+2.+2?.)(41.VhAR,)))")
(* [comment removed for export] *).
  Proof.
    pose proof (r_s1 p HCN) as S1. pose proof (r_s2 p HCN) as S2. rewrite HAC.
    pose proof (zev_STKPG p (proj2 S2)) as ZS. unfold W_STKPG in ZS. cbn [zev] in ZS.
    pose proof (Z.div_pos (uv p v_s2) 256 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (uv p v_s2) 256 8 ltac:(lia) ltac:(lia)).
    assert (E : zev p (((#(-0x8000) * v_s1) + (#(-0x1000) * (WAlu Instr.ALU_SRL v_s2 #8))) + #0x800000800000)%tm = 0x800000800000 - STKPG p).
    { cbn [zev]. match type of ZS with ?a + 4096 * ?q = _ => replace (-4096 * q) with (- (4096 * q)) by lia end. unfold STKPG in *. lia. }
    rewrite zev_exact; rewrite E; unfold STKPG; lia.
  Qed.
  Local Ltac uvals := rewrite ?u_divec, ?u_gvec, ?u_dstore, ?u_dnodes, ?u_fstk, ?u_dtls, ?u_tvec, ?u_treg, ?u_thr, ?u_ictx, ?u_lla, ?u_tmpv, ?u_mus1, ?u_mus2,
    ?u_prim, ?u_secv, ?u_brk0pg, ?u_mus1p, ?u_ri, ?u_stkb, ?u_stkn in *; rewrite ?u_wlit in * by lia.
  (* [comment removed for export] *)
  Local Ltac shcase R W1 W2 HAL :=
    lazymatch type of W2 with _ + 4096 <= pageup (2147450880 + (?b + ?n) / 8) =>
      apply (good_sh R b n);
      [ first [apply cs_gsh; cbn; tauto | apply cs_img
              | apply (cs_trk (store_tr b)); cbn; tauto | apply (cs_trk (node_tr b)); cbn; tauto
              | apply (cs_trk (TR b n KEager true true)); cbn; tauto ]
      | cbn [fst snd] | cbn [fst snd] | | cbn [fst snd] | exact W1 | exact W2 | exact HAL ]
    end.

  #[using="sp fs HCN HMOD HAC HSP M Lz"] Theorem h0_mat_good : forall pg, In pg (m_vm_materialized md) -> vgood AL0 v0 pg.
  Proof.
    intros pg Hpg. ddestruct (mat_facts pg Hpg) as (AL & (e & He & E1 & E2) & HA). mm X.
    clear Mhalt Mfds Mfs Mres Mlim Mfog Mseps Mwf Mlazyb Mnasub MNsecv MNgap MAdstore MAhigh MAlow Mtot Misp Mbrk Msbrk Meager Mabytes Mminv MNcov MLcov
          Ndivec Ngvec Ndstore Ndnodes Nfstk Ndtls Ntvec Ntreg Nthr Nictx Nlla Nhigh Nlow.
    pose proof (u64_range pg) as Rpg.
    unfold me_allow, page_allowedb in HA. apply existsb_exists in HA as (iv & Hiv & Hb). apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. unfold page_size in Hb2.
    apply in_app_iff in Hiv as [Hiv|Hiv].
    - (* [comment removed for export] *)
      unfold me_vis in Hiv. apply in_flat_map in Hiv as (r & Hr & Hiv). apply in_map_iff in Hr as (tpl & <- & Htpl).
      unfold allow1w, pinst in Hiv. cbn [fst snd] in Hiv.
      cbn in Htpl.
      destruct Htpl as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; cbn [fst snd] in Hiv;
        destruct Hiv as [<-|[<-|[]]]; cbn [fst snd] in Hb1, Hb2.
      all: pose proof aceil_bounds as AB; pose proof (r_s1 p HCN) as S1; pose proof (r_s2 p HCN) as S2; pose proof (r_prim p HCN) as PR; pose proof (r_pslack p HCN) as PS.
      all: pose proof (PG_range p HCN v_divec ltac:(pv)) as [Gdivec Adivec]; pose proof (PG_range p HCN v_gvec ltac:(pv)) as [Ggvec Agvec];
           pose proof (PG_range p HCN v_dstore ltac:(pv)) as [Gdstore Adstore]; pose proof (PG_range p HCN v_dnodes ltac:(pv)) as [Gdnodes Adnodes];
           pose proof (PG_range p HCN v_fstk ltac:(pv)) as [Gfstk Afstk]; pose proof (PG_range p HCN v_dtls ltac:(pv)) as [Gdtls Adtls];
           pose proof (PG_range p HCN v_tvec ltac:(pv)) as [Gtvec Atvec]; pose proof (PG_range p HCN v_treg ltac:(pv)) as [Gtreg Atreg];
           pose proof (PG_range p HCN v_thr ltac:(pv)) as [Gthr Athr]; pose proof (PG_range p HCN v_ictx ltac:(pv)) as [Gictx Aictx];
           pose proof (PG_range p HCN v_lla ltac:(pv)) as [Glla Alla].
      all: uvals.
      (* [comment removed for export] *)
      all: try (exfalso;
                lazymatch type of Hb2 with _ + 4096 <= pageup (?b + ?n) =>
                  lazymatch goal with
                  | Lv : forall e0, In e0 (m_vm_lazy md) -> zE e0 <= b \/ b + n <= zB e0 |- _ =>
                      destruct (own_window b n (bv_unsigned pg) ltac:(assumption || reflexivity) ltac:(reflexivity) Hb1 Hb2) as [O1 O2];
                      destruct (Lv e He); unfold zB, zE in *; lia
                  end
                end).
      + (* [comment removed for export] *) shcase (PG p v_divec, 0x1000) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *) shcase (PG p v_gvec, 0x1000) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *)
        destruct (own_window (PG p v_dstore) 8388608 (bv_unsigned pg) Adstore eq_refl Hb1 Hb2) as [O1 O2]. apply good_store; lia.
      + (* [comment removed for export] *) shcase (PG p v_dstore, 2 ^ 23) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *) shcase (PG p v_dnodes, 2 ^ 20) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *) shcase (PG p v_fstk, kFakeBytes) Hb1 Hb2 AL; unfold kFakeBytes; lia.
      + (* [comment removed for export] *) shcase (PG p v_dtls, 4096) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *) shcase (PG p v_tvec, 0x1000) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *) shcase (PG p v_treg, 0x10000) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *) shcase (PG p v_thr, 4096) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *)
        exfalso. ddestruct Mri as (_ & _ & _ & RL).
        assert (RIA : (SB p + 2 ^ 37) mod 4096 = 0).
        { unfold SB, PG. replace (4096 * uv p v_prim - 4096 * uv p v_pslack + 0x10000 + 2 ^ 37) with ((uv p v_prim - uv p v_pslack + 16 + 2 ^ 25) * 4096) by lia.
          apply Z_mod_mult. }
        destruct (own_window (SB p + 2 ^ 37) 4096 (bv_unsigned pg) RIA eq_refl Hb1 Hb2) as [O1 O2].
        destruct (RL e He); unfold zB, zE in *; lia.
      + (* [comment removed for export] *) shcase (SB p + 2 ^ 37, 4096) Hb1 Hb2 AL; unfold SB, PG in *; lia.
      + (* [comment removed for export] *) shcase (PG p v_ictx, 0x38e000) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *) shcase (PG p v_lla, 0x10000) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *)
        exfalso. destruct (own_window 0x10000 0x64f000 (bv_unsigned pg) eq_refl eq_refl Hb1 Hb2) as [O1 O2].
        ddestruct (MM_Lzcov e He) as (_ & iv & Hiv & C1 & C2). pose proof (proj1 (Forall_forall _ _) Mbounds iv Hiv) as (_ & _ & _ & IMG & _).
        unfold zB, zE in *. lia.
      + (* [comment removed for export] *) shcase (0x10000, 0x64f000) Hb1 Hb2 AL; lia.
      + (* [comment removed for export] *)
        exfalso. pose proof ACEIL_pg as CP.
        assert (NP : (2 ^ 47 - ACEIL) mod 4096 = 0).
        { rewrite Zminus_mod, CP. reflexivity. }
        destruct (own_window ACEIL (2 ^ 47 - ACEIL) (bv_unsigned pg) CP NP Hb1 Hb2) as [O1 O2].
        ddestruct (MM_Lzcov e He) as (_ & iv & Hiv & C1 & C2). pose proof (proj1 (Forall_forall _ _) Mbounds iv Hiv) as (_ & B1 & B2 & _ & TOP & _).
        rewrite HSP in TOP. unfold zB, zE, SP, STKPG in *.
        pose proof (Z.div_mod (bv_unsigned (fst iv)) 4096 ltac:(lia)) as D1. pose proof (Z.div_mod (bv_unsigned (snd iv)) 4096 ltac:(lia)) as D2.
        rewrite B1, Z.add_0_r in D1. rewrite B2, Z.add_0_r in D2.
        pose proof (Z.div_mod (uv p v_s2) 256 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (uv p v_s2) 256 ltac:(lia)) as M3.
        clear - O1 O2 C1 C2 E1 E2 TOP D1 D2 D3 M3 HAC Rpg. lia.
      + (* [comment removed for export] *) shcase (ACEIL, 2 ^ 47 - ACEIL) Hb1 Hb2 AL; lia.
    - (* [comment removed for export] *)
      unfold me_ghost in Hiv. apply in_flat_map in Hiv as (r & Hr & Hiv). apply in_map_iff in Hr as (tpl & <- & Htpl).
      unfold allowshw, pinst in Hiv. cbn [fst snd] in Hiv. destruct Hiv as [<-|[]]. cbn [fst snd] in Hb1, Hb2.
      cbn in Htpl.
      pose proof aceil_bounds as AB.
      pose proof (proj1 (PG_range p HCN v_tmpv ltac:(pv))). pose proof (proj1 (PG_range p HCN v_mus1 ltac:(pv))). pose proof (proj1 (PG_range p HCN v_mus2 ltac:(pv))).
      pose proof (r_brk0pg p HCN).
      (* [comment removed for export] *)
      destruct Htpl as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd] in Hb1, Hb2; uvals.
      + shcase (PG p v_tmpv, 0x1000) Hb1 Hb2 AL; lia.
      + shcase (PG p v_brk0pg, 0x2000) Hb1 Hb2 AL; unfold PG in *; lia.
      + shcase (PG p v_mus1, 0x1000) Hb1 Hb2 AL; lia.
      + shcase (PG p v_mus1 + 0x1000, 0x1000) Hb1 Hb2 AL; lia.
      + shcase (PG p v_mus2, 0x1000) Hb1 Hb2 AL; lia.
      + shcase (PG p v_brk0pg, 0x2000) Hb1 Hb2 AL; unfold PG in *; lia.
      + shcase (PG p v_mus1, 0x1000) Hb1 Hb2 AL; lia.
      + shcase (PG p v_mus1 + 0x1000, 0x1000) Hb1 Hb2 AL; lia.
      + shcase (PG p v_mus2, 0x1000) Hb1 Hb2 AL; lia.
  Qed.
End K.
