(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst HMLib HM AW_Refill AW_FakeDefs AW_FakeRep AHeapR.
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
Ltac2 gd_tbl_AHeapB () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pclass"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sec_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.awf'"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "ARUN_1.B.ext_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_hdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_user"; "ARUN_1.B.ext_hi"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_cls"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_alloc_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.uunit_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.tr_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lit"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_n"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_bytes"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "ARUN_1.B.bapart"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "Corelib.Lists.ListDef.Forall"].

Section ARUN_1. Context {hAR : arun}.
Section B.
  Variable STKLO : Z.
  Local Notation hok := (hok STKLO).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma rounded_ge : forall n, Z.max n 8 <= rounded n.
  Proof. intros n. unfold rounded. pose proof (round_up_spec (Z.max n 8) 8 ltac:(lia)). lia. Qed.

  #[using="Type"] Lemma user_end_prim : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Pn,$0.P,(1.=R1.)P,(2.$3.(4.R2.)$5.)(6.(1.(7.(8.R3.)R3.)(9.(:.R3.)))(;.(8.R3.)(9.(:.R3.))))")
(* [comment removed for export] *).
  Proof.
    intros n Hn FP. pose proof (needed_le_class n Hn FP) as NC. unfold needed in NC. pose proof (rounded_ge n). lia.
  Qed.

  #[using="Type"] Lemma user_end_sec : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Pn,$0.P,(1.=R1.)P,(2.$3.(4.R2.)$<.)(6.(1.(7.(7.+1000.(8.R3.))R3.)(=.R3.))(;.(7.+1000.(8.R3.))(=.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros n Hn FP. unfold sec_map_size, needed2. rewrite FP. unfold needed.
    pose proof (round_up_spec (rounded n + rz_size n + rz_size n) 4096 ltac:(lia)). pose proof (rounded_ge n). pose proof (rz_size_bound' n). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma sec_map_big : forall n, 0 <= n -> from_primary n = false -> 0x10000 + 4096 < sec_map_size n.
  Proof.
    intros n Hn FP. unfold sec_map_size, needed2. rewrite FP. unfold from_primary, kMaxSize in FP. apply Z.leb_gt in FP.
    pose proof (round_up_spec (needed n + rz_size n) 4096 ltac:(lia)) as [R1 R2]. pose proof (rz_size_bound' n). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ext_lo (k : chunk) : Z := if ck_prim k then ck_ab k else ck_map_beg k.
  Definition ext_hi (k : chunk) : Z := ck_end k.

  #[using="Type"] Lemma chunk_ext : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.Pk,$?.P,(10.VhAR,R2.)P,(11.$?.R2.(12.R3.))(6.(1.=(13.R3.))(6.(1.(14.R3.)(15.R3.))(6.(2.$0.(7.(15.R3.)+10.)(16.R3.))(6.(1.(7.(16.R3.)(13.R3.))(17.R3.))(6.(;.(16.R3.)(17.R3.))(6.(6.(1.+65?000.(14.R3.))(18.(1.(17.R3.)+7???7000.)(1.$19.(14.R3.))))(6.(1.(17.R3.)(1:.VhAR,))(18.(6.(2.$3.(1;.R3.)$5.)(6.(6.(1.+1.(1<.R3.))(1.(1<.R3.)+1>.))(6.(1.(1=.(1>.R4.)(1<.R3.))(14.R3.))(6.(1.(17.R3.)(7.(1=.(1>.R4.)(1<.R3.))(1?.(20.R4.(1<.R3.)))))(21.$0.Li,$0.(6.(1.=R1.)(6.(2.$0.(14.R4.)(22.(1>.R5.)(1<.R4.)R1.))(2.$0.(17.R4.)(7.(22.(1>.R5.)(1<.R4.)R1.)(9.(1<.R4.)))))))))))(6.(2.$3.(1;.R3.)$<.)(21.$23.Lsh,$23.(6.(11.$23.R1.(24.(25.R5.)))(6.(2.$0.(14.R4.)(26.R1.))(2.$0.(17.R4.)(7.(26.R1.)(27.R1.)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros h k AW Hk. dpose AW as ([WL _] & WC & WR & (WKF & _ & _) & _).
    pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (WN & WST & WP & WX).
    unfold ext_lo, ext_hi, ck_end, ck_hdr, ck_user, ck_rz, kChunkHeaderSize. pose proof (rz_size_bound' (ck_n k)) as RZ.
    destruct (ck_prim k) eqn:PK.
    - ddestruct WX as (ECLS & C30 & i & Hi & EAB).
      pose proof (user_end_prim (ck_n k) ltac:(lia) ltac:(symmetry; exact WP)) as [UE UL]. rewrite <- ECLS in UE, UL.
      pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc.
      ddestruct WRc as (_ & AUMU & AUCS & MUAL & MULIM & _).
      pose proof (class_size_range (ck_cls k) ltac:(lia)) as CSR.
      unfold carved in Hi.
      assert (KCS : i * class_size (ck_cls k) + class_size (ck_cls k) <= r_alloc_user (h_reg h (ck_cls k))).
      { rewrite AUCS in Hi |- *. rewrite Z.mul_comm, Z.div_mul in Hi by lia. nia. }
      unfold wf_L in WL. unfold chunk_at, region_beg, kRegionSize, kUserLimit, kHighMemBeg, space_end, kSpaceSize in *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      assert (SBH : 0x10007fff8000 <= l_sb (h_L h)) by (clear - WL; lia).
      split; [split; [clear - SBH EAB Hi CSR C30; nia| right; clear - SBH EAB Hi CSR C30; nia]|]. split; [clear - WL EAB KCS CSR C30 AUMU MULIM; nia|].
      left. split; [reflexivity|]. split; [exact C30|]. split; [clear - EAB Hi CSR; nia|]. split; [clear - EAB KCS; lia|].
      exists i. split; [lia|]. split; [exact EAB| rewrite EAB; reflexivity].
    - ddestruct WX as (i & NTH & MB4 & MB0 & MBH & MBL).
      pose proof (user_end_sec (ck_n k) ltac:(lia) ltac:(symmetry; exact WP)) as [UE UL].
      pose proof (sec_map_big (ck_n k) ltac:(lia) ltac:(symmetry; exact WP)) as BIG.
      pose proof (lowhigh_big _ _ MBL ltac:(unfold ck_map_size; clear - BIG; lia)) as M63. ddestruct MBL as (_ & _ & MBAND).
      unfold ck_map_beg, ck_map_size in *.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [clear - M63 MBAND; lia|]. split; [exact MBH|].
      right. split; [reflexivity|]. exists (SH (ck_ab k - 4096) (sec_map_size (ck_n k)) (needed2 (ck_n k))).
      split; [eapply nth_error_In; exact NTH|]. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ext_crange : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.Pk,$?.P,(28.VhAR,VSTKLO,R2.)P,(11.$?.R2.(12.R3.))(29.(2:.$2;.(2<.R4.))(14.R3.)(2=.(17.R3.)(14.R3.)))")
(* [comment removed for export] *).
  Proof.
    intros h k HOK Hk. dpose HOK as (EL & AW & VW). dpose AW as (_ & _ & WR & _).
    ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & [(PK & C30 & R1 & R2 & _)|(PK & sh & Hsh & S1 & S2)]).
    - pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & _ & MUAL & _).
      apply (crange_user AL0 h (ck_cls k)); [lia| exact MUAL| exact R1| lia| lia].
    - intros x Hx. apply (vcs_of_tr AL0 h (sec_tr sh)); [apply tr_of_sec; exact Hsh| reflexivity| unfold t_hi; cbn; lia].
  Qed.

  #[using="Type"] Lemma live_block : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.PA,$0.Pn,$0.P,(11.(2>.$0.$0.)(2?.$0.$0.R2.R1.)(30.R3.))(21.$?.Lk,$?.(6.(11.$?.R1.(12.R5.))(6.(2.$0.(31.R1.)$32.)(6.(2.$0.R4.(16.R1.))(2.$0.R3.(13.R1.))))))")
(* [comment removed for export] *).
  Proof.
    intros h A n HB. unfold AModel.blocks, live in HB. apply in_map_iff in HB. ddestruct HB as (k & E & Hk). apply filter_In in Hk. destruct Hk as [Hk ST].
    exists k. injection E as EA EN. split; [exact Hk|]. split; [apply Z.eqb_eq; exact ST|]. split; symmetry; assumption.
  Qed.

  #[using="Type"] Lemma block_crange : forall h A n, hok h -> In (A, n) (AModel.blocks h) -> crange (vcs AL0 (vst_of h)) A n.
  Proof.
    intros h A n HOK HB. dpose HOK as (EL & AW & VW). ddestruct (live_block h A n HB) as (k & Hk & _ & -> & ->).
    ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & _).
    eapply crange_sub; [exact (ext_crange h k HOK Hk)| lia| lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma user_point_unit : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.Pc,$0.Px,$0.P,(10.VhAR,R3.)P,(6.(1.+1.R3.)(1.R3.+1?.))P,(6.(1.(1=.(1>.R5.)R4.)R3.)(;.R3.(7.(1=.(1>.R5.)R4.)(33.(20.R5.R4.)))))(21.$0.Lj,$0.(6.(11.$34.(35.(1>.R7.)R6.R1.)(36.R7.))(6.(1.(37.(35.(1>.R7.)R6.R1.))R5.)(;.R5.(38.(35.(1>.R7.)R6.R1.))))))")
(* [comment removed for export] *).
  Proof.
    intros h c x AW Hc Hx. dpose AW as (_ & _ & WR & _).
    pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & _ & MUAL & _).
    set (RB := region_beg (h_L h) c) in *. set (j := (x - RB) / kUserMapSize). unfold kUserMapSize in *.
    pose proof (Z.div_mod (x - RB) (2^18) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (x - RB) (2^18) ltac:(lia)) as MB.
    assert (Hj : 0 <= j < r_mapped_user (h_reg h c) / 2^18).
    { subst j. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      pose proof (Z.div_mod (r_mapped_user (h_reg h c)) (2^18) ltac:(lia)). lia. }
    exists j. split; [apply tr_of_uunit; [exact Hc| exact Hj]|]. unfold t_hi, uunit_tr, kUserMapSize. cbn [t_lo t_len]. fold RB. subst j. lia.
  Qed.

  #[using="Type"] Lemma user_vs_lit : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.Pc,$0.Pt,$34.Px,$0.P,(28.VhAR,VSTKLO,R4.)P,(6.(1.+1.R4.)(1.R4.+1?.))P,(11.$34.R4.(36.R6.))P,(2.$3.(39.R5.)$5.)P,(6.(1.(1=.(1>.R8.)R7.)R5.)(;.R5.(7.(1=.(1>.R8.)R7.)(33.(20.R8.R7.)))))(3:.(6.(1.(37.R7.)R6.)(;.R6.(38.R7.))))")
(* [comment removed for export] *).
  Proof.
    (intros h c t x dd_H; ddestruct dd_H as (EL & AW & VW); intros Hc Ht TL Hx XT). dpose VW as (_ & APT & _).
    ddestruct (user_point_unit h c x AW Hc Hx) as (j & Hj & XJ).
    destruct (APT _ _ Hj Ht) as [E|[X|X]]; [| unfold t_hi in *; lia| unfold t_hi in *; lia].
    rewrite <- E in TL. cbn in TL. discriminate.
  Qed.

  #[using="Type"] Lemma sec_vs_sec : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.Psh1,$23.Psh2,$23.Px,$0.P,(28.VhAR,VSTKLO,R4.)P,(11.$23.R4.(24.(25.R5.)))P,(11.$23.R4.(24.(25.R6.)))P,(3:.(2.$0.(26.R6.)(26.R5.)))P,(6.(1.(26.R7.)R5.)(;.R5.(7.(26.R7.)(27.R7.))))(3:.(6.(1.(26.R7.)R6.)(;.R6.(7.(26.R7.)(27.R7.)))))")
(* [comment removed for export] *).
  Proof.
    (intros h sh1 sh2 x dd_H; ddestruct dd_H as (EL & AW & VW); intros H1 H2 NE X1 X2). dpose VW as (_ & APT & _).
    destruct (APT _ _ (tr_of_sec h sh1 H1) (tr_of_sec h sh2 H2)) as [E|[X|X]]; [| unfold t_hi in X; cbn in X; lia| unfold t_hi in X; cbn in X; lia].
    injection E as E1 E2. exact (NE E1).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ext_apart : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.Pk1,$?.Pk2,$?.Px,$0.P,(28.VhAR,VSTKLO,R4.)P,(11.$?.R4.(12.R5.))P,(11.$?.R4.(12.R6.))P,(3:.(2.$0.(3;.R6.)(3;.R5.)))P,(6.(1.(14.R7.)R5.)(;.R5.(17.R7.)))(3:.(6.(1.(14.R7.)R6.)(;.R6.(17.R7.))))")
(* [comment removed for export] *).
  Proof.
    intros h k1 k2 x HOK Hk1 Hk2 NE X1 X2. dpose HOK as (EL & AW & VW). dpose AW as ([WL _] & _ & WR & _).
    ddestruct (chunk_ext h k1 AW Hk1) as (_ & _ & _ & _ & _ & _ & _ & [(P1 & C1 & R1 & R1' & i1 & I1 & L1 & H1)|(P1 & sh1 & S1 & L1 & H1)]);
    ddestruct (chunk_ext h k2 AW Hk2) as (_ & _ & _ & _ & _ & _ & _ & [(P2 & C2 & R2 & R2' & i2 & I2 & L2 & H2)|(P2 & sh2 & S2 & L2 & H2)]).
    - (* [comment removed for export] *)
      unfold ext_lo in *. rewrite P1 in *. rewrite P2 in *.
      pose proof (WR (ck_cls k1) ltac:(unfold kNumClasses; lia)) as WRa. cbn zeta in WRa. ddestruct WRa as (_ & AUMU1 & _ & _ & MULIM1 & _).
      pose proof (WR (ck_cls k2) ltac:(unfold kNumClasses; lia)) as WRb. cbn zeta in WRb. ddestruct WRb as (_ & AUMU2 & _ & _ & MULIM2 & _).
      pose proof (class_size_range (ck_cls k1) ltac:(lia)) as CS1. pose proof (class_size_range (ck_cls k2) ltac:(lia)) as CS2.
      unfold chunk_at, region_beg, kRegionSize, kUserLimit in *.
      destruct (Z.eq_dec (ck_cls k1) (ck_cls k2)) as [EC|NC].
      + rewrite <- EC in *. assert (NI : i1 <> i2) by (intros ->; apply NE; lia).
        destruct (Z_lt_le_dec i1 i2) as [LT|LE].
        * pose proof (Z.mul_le_mono_nonneg_r (i1 + 1) i2 (class_size (ck_cls k1)) ltac:(lia) ltac:(lia)). clear - H X1 X2 L1 H1 L2 H2. lia.
        * pose proof (Z.mul_le_mono_nonneg_r (i2 + 1) i1 (class_size (ck_cls k1)) ltac:(lia) ltac:(lia)). clear - H X1 X2 L1 H1 L2 H2. lia.
      + clear - NC X1 X2 R1 R1' R2 R2' AUMU1 AUMU2 MULIM1 MULIM2 C1 C2. nia.
    - (* [comment removed for export] *)
      apply (user_vs_lit h (ck_cls k1) (sec_tr sh2) x HOK ltac:(lia) (tr_of_sec h sh2 S2) eq_refl).
      + pose proof (WR (ck_cls k1) ltac:(unfold kNumClasses; lia)) as WRa. cbn zeta in WRa. ddestruct WRa as (_ & AUMU1 & _). lia.
      + unfold t_hi. cbn. lia.
    - (* [comment removed for export] *)
      apply (user_vs_lit h (ck_cls k2) (sec_tr sh1) x HOK ltac:(lia) (tr_of_sec h sh1 S1) eq_refl).
      + pose proof (WR (ck_cls k2) ltac:(unfold kNumClasses; lia)) as WRb. cbn zeta in WRb. ddestruct WRb as (_ & AUMU2 & _). lia.
      + unfold t_hi. cbn. lia.
    - (* [comment removed for export] *)
      unfold ext_lo in *. rewrite P1 in *. rewrite P2 in *.
      apply (sec_vs_sec h sh1 sh2 x HOK S1 S2); [| lia| lia]. unfold ck_map_beg in *. intros E. apply NE. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma fs_tr_in : forall h, In (TR (l_fs (h_L h)) kFakeBytes KEager true true) (tr_of h).
  Proof. intros h. apply tr_of_fs. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma fs_vs_sec : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.Psh,$23.Px,$0.P,(28.VhAR,VSTKLO,R3.)P,(11.$23.R3.(24.(25.R4.)))P,(6.(1.(3<.(1>.R5.))R3.)(;.R3.(7.(3<.(1>.R5.))$3=.)))(3:.(6.(1.(26.R5.)R4.)(;.R4.(7.(26.R5.)(27.R5.)))))")
(* [comment removed for export] *).
  Proof.
    (intros h sh x dd_H; ddestruct dd_H as (EL & AW & VW); intros Hsh XF XS). dpose VW as (_ & APT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & _).
    destruct (APT _ _ (fs_tr_in h) (tr_of_sec h sh Hsh)) as [E|[X|X]]; [| unfold t_hi in X; cbn in X; lia| unfold t_hi in X; cbn in X; lia].
    (* [comment removed for export] *)
    cbn [vst_of v_tr] in ND. unfold tr_of in ND.
    apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND.
    eapply (NoDup_app_in _ _ (sec_tr sh) ND).
    - apply in_map. exact Hsh.
    - rewrite <- E. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
      unfold fixed_of. apply in_app_iff. left. right. right. left. reflexivity.
  Qed.

  #[using="Type"] Lemma frame_ext : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.PLF,(3>.(2>.$0.$0.))Pm,P,(3?.&40.)(40.(3?.&8.))Pfb,(2>.$0.$0.)P,(10.VhAR,R4.)P,(41.R5.R4.R3.)P,(11.(2>.$0.$0.)R3.R5.)(21.$0.Lk,$0.(21.$0.Li,$0.(6.(6.(1.=R2.)(1.R2.+:.))(6.(6.(1.=R1.)(;.R1.(42.R2.)))(6.(2.(2>.$0.$0.)R6.(2?.$0.$0.(43.(3<.(1>.R9.))R2.R1.)(44.R2.)))(6.(1.(7.(3<.(1>.R9.))+9000.)(45.$0.$0.R6.))(6.(1.(7.(45.$0.$0.R6.)(46.$0.$0.R6.))(7.(3<.(1>.R9.))$3=.))(1.+40.(46.$0.$0.R6.)))))))))")
(* [comment removed for export] *).
  Proof.
    (intros h LF m fb AW dd_H; ddestruct dd_H as (_ & _ & _ & WF & _); intros Hfb). ddestruct (WF fb Hfb) as (k & i & Hk & Hi & E).
    dexists k, i. split; [exact Hk|]. split; [exact Hi|]. split; [exact E|]. subst fb. cbn [fst snd].
    pose proof (fsk_frame_inside (l_fs (h_L h)) k i Hk Hi). pose proof (fsk_sizes k Hk). lia.
  Qed.

  #[using="Type"] Lemma frame_crange : forall h LF m A n, hok h -> hm_fake h LF m -> In (A, n) LF -> crange (vcs AL0 (vst_of h)) A n.
  Proof.
    (intros h LF m A n dd_H; ddestruct dd_H as (EL & AW & VW); intros HF HIn). ddestruct (frame_ext h LF m (A, n) AW HF HIn) as (k & i & Hk & Hi & E & F1 & F2 & F3). cbn [fst snd] in F1, F2, F3.
    intros x Hx. apply (vcs_of_tr AL0 h _ x (fs_tr_in h)); [reflexivity|]. unfold t_hi, kFakeBytes in *. cbn. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ext_vs_frame : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.PLF,(3>.(2>.$0.$0.))Pm,P,(3?.&40.)(40.(3?.&8.))Pk,$?.Pfb,(2>.$0.$0.)Px,$0.P,(28.VhAR,VSTKLO,R6.)P,(41.R7.R6.R5.)P,(11.$?.R5.(12.R8.))P,(11.(2>.$0.$0.)R5.R8.)P,(6.(1.(14.R7.)R5.)(;.R5.(17.R7.)))(3:.(6.(1.(45.$0.$0.R7.)R6.)(;.R6.(7.(45.$0.$0.R7.)(46.$0.$0.R7.)))))")
(* [comment removed for export] *).
  Proof.
    intros h LF m k fb x HOK HF Hk Hfb XK XF. dpose HOK as (EL & AW & VW). dpose AW as (_ & _ & WR & _).
    ddestruct (frame_ext h LF m fb AW HF Hfb) as (kk & i & Hkk & Hi & E & F1 & F2 & F3).
    ddestruct (chunk_ext h k AW Hk) as (_ & _ & _ & _ & _ & _ & _ & [(P1 & C1 & R1 & R1' & _)|(P1 & sh1 & S1 & L1 & H1)]).
    - apply (user_vs_lit h (ck_cls k) _ x HOK ltac:(lia) (fs_tr_in h) eq_refl).
      + pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRa. cbn zeta in WRa. ddestruct WRa as (_ & AUMU1 & _). lia.
      + unfold t_hi. cbn. lia.
    - apply (fs_vs_sec h sh1 x HOK S1); lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bapart (a b : blk) : Prop := fst a + snd a <= fst b \/ fst b + snd b <= fst a.

  #[using="Type"] Lemma blocks_apart_app : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Pl1,(3>.$47.)Pl2,(3>.$47.)P,(48.R2.)P,(48.R2.)P,Pa,$47.Pb,$47.P,(11.$47.R2.R6.)P,(11.$47.R2.R6.)(49.R4.R3.)(48.(4:.$47.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    induction l1 as [|[A n] r IH]; intros l2 H1 H2 X; [exact H2|]. cbn. destruct H1 as [H1a H1b]. split.
    - intros B k HIn. apply in_app_iff in HIn. destruct HIn as [HIn|HIn]; [exact (H1a B k HIn)|].
      exact (X (A, n) (B, k) ltac:(left; reflexivity) HIn).
    - apply IH; [exact H1b| exact H2|]. intros a b Ha Hb. apply X; [right; exact Ha| exact Hb].
  Qed.

  #[using="Type"] Lemma blocks_apart_map : forall {X} (f : X -> blk) (key : X -> Z) (l : list X),
    List.NoDup (map key l) -> (forall a b, In a l -> In b l -> key a <> key b -> bapart (f a) (f b)) -> blocks_apart (map f l).
  Proof.
    intros X f key l. induction l as [|a r IH]; intros ND H; [exact I|]. cbn. cbn in ND. inversion ND as [|? ? NI ND']; subst.
    destruct (f a) as [A n] eqn:EF. split.
    - intros B k HIn. apply in_map_iff in HIn. ddestruct HIn as (b & EB & Hb).
      assert (NK : key a <> key b) by (intros E; apply NI; rewrite E; apply in_map; exact Hb).
      pose proof (H a b ltac:(left; reflexivity) ltac:(right; exact Hb) NK) as AP. rewrite EF, EB in AP. exact AP.
    - apply IH; [exact ND'|]. intros x y Hx Hy. apply H; right; assumption.
  Qed.

  #[using="Type"] Lemma NoDup_map_filter : forall {X} (g : X -> Z) (p : X -> bool) l, List.NoDup (map g l) -> List.NoDup (map g (List.filter p l)).
  Proof.
    intros X g p l. induction l as [|a r IH]; intros ND; [constructor|]. cbn in ND. inversion ND as [|? ? NI ND']; subst. cbn.
    destruct (p a); [| exact (IH ND')]. cbn. constructor; [| exact (IH ND')].
    intros HIn. apply NI. apply in_map_iff in HIn. ddestruct HIn as (b & E & Hb). apply filter_In in Hb. rewrite <- E. apply in_map. exact (proj1 Hb).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma apart_of_ext : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "PA,$0.Pn,$0.PB,$0.Pj,$0.PloA,$0.PhiA,$0.PloB,$0.PhiB,$0.P,(1.R4.R8.)P,(1.(7.R9.R8.)R4.)P,(;.R:.R5.)P,(1.=R:.)P,(1.R6.R:.)P,(1.(7.R;.R:.)R6.)P,(;.R<.R7.)P,(1.=R<.)P,Px,$0.P,(6.(1.R=.R1.)(;.R1.R<.))(3:.(6.(1.R<.R2.)(;.R2.R;.)))(18.(1.(7.R11.R10.)R?.)(1.(7.R?.R>.)R11.))")
(* [comment removed for export] *).
  Proof.
    intros A n B j loA hiA loB hiB H1 H2 H3 H4 H5 H6 H7 H8 DJ.
    destruct (Z_lt_le_dec A B) as [AB|BA].
    - left. destruct (Z_lt_le_dec B (A + n)) as [X|X]; [| exact X]. exfalso. apply (DJ B); lia.
    - right. destruct (Z_lt_le_dec A (B + j)) as [X|X]; [| exact X]. exfalso. apply (DJ A); lia.
  Qed.

  #[using="Type"] Theorem hm_apart_c : ltac2:(CDefT.buildp (gd_tbl_AHeapB ()) "Ph,$>.PLB,(3>.(2>.$0.$0.))PLF,(3>.(2>.$0.$0.))Pm,P,(3?.&40.)(40.(3?.&8.))P,(28.VhAR,VSTKLO,R4.)P,(4;.VhAR,R5.R4.R3.R2.)(6.(4<.(2>.$0.$0.)Lb,(2>.$0.$0.)(6.(;.=(45.$0.$0.R1.))(6.(1.=(46.$0.$0.R1.))(6.(1.(7.(45.$0.$0.R1.)(46.$0.$0.R1.))(1:.VhAR,))(18.(1.(7.(45.$0.$0.R1.)(46.$0.$0.R1.))+10000.)(1.+65?000.(45.$0.$0.R1.))))))(4:.(2>.$0.$0.)R5.R4.))(48.(4:.(2>.$0.$0.)R5.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m HOK HM0. dpose HOK as (EL & AW & VW). dpose HM0 as ((_ & HLB) & _ & _ & _ & _ & _ & _ & _ & _ & GF & _).
    dpose AW as ([WL _] & _ & _ & (_ & NDAB & _) & _). dpose GF as (_ & _ & _ & _ & NDF).
    assert (FSB : lowhigh (l_fs (h_L h)) kFakeBytes /\ l_fs (h_L h) + kFakeBytes <= ACEIL) by (unfold wf_L in WL; clear - WL; tauto).
    destruct FSB as [FSL FSB]. apply lowhigh_big in FSL; [| unfold kFakeBytes; clear; lia]. aceilb. 
    split.
    - apply Forall_app. split.
      + apply Forall_forall. intros [A n] HB. rewrite HLB in HB. ddestruct (live_block h A n HB) as (k & Hk & _ & -> & ->). cbn [fst snd].
        ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _). unfold kHighMemBeg in E5. clear - N0 E1 E2 E3 E4 E5 E6. lia.
      + apply Forall_forall. intros fb Hfb. ddestruct (frame_ext h LF m fb AW GF Hfb) as (kk & i & _ & _ & _ & F1 & F2 & F3). clear - F1 F2 F3 FSL FSB. lia.
    - apply blocks_apart_app.
      + (* [comment removed for export] *)
        rewrite HLB. unfold AModel.blocks, live. apply (blocks_apart_map _ ck_ab); [apply NoDup_map_filter; exact NDAB|].
        intros a b Ha Hb NK. apply filter_In in Ha. apply filter_In in Hb. destruct Ha as [Ha _]. destruct Hb as [Hb _]. unfold bapart. cbn [fst snd].
        ddestruct (chunk_ext h a AW Ha) as (Na & A1 & A2 & A3 & A4 & _). ddestruct (chunk_ext h b AW Hb) as (Nb & B1 & B2 & B3 & B4 & _).
        apply (apart_of_ext _ _ _ _ (ext_lo a) (ext_hi a) (ext_lo b) (ext_hi b)); try lia.
        intros x Hx. exact (ext_apart h a b x HOK Ha Hb NK Hx).
      + (* [comment removed for export] *)
        rewrite <- (map_id LF). apply (blocks_apart_map (fun x : blk => x) fst); [exact NDF|].
        intros a b Ha Hb NK. unfold bapart.
        ddestruct (frame_ext h LF m a AW GF Ha) as (ka & ia & Hka & Hia & -> & _). ddestruct (frame_ext h LF m b AW GF Hb) as (kb & ib & Hkb & Hib & -> & _).
        cbn [fst snd] in *. apply fsk_frames_apart; [exact Hka| exact Hia| exact Hkb| exact Hib|].
        destruct (Z.eq_dec ka kb) as [<-|NEk]; [| left; exact NEk]. right. intros <-. exact (NK eq_refl).
      + (* [comment removed for export] *)
        intros a fb Ha Hfb. rewrite HLB in Ha. destruct a as [A n]. ddestruct (live_block h A n Ha) as (k & Hk & _ & -> & ->).
        unfold bapart. cbn [fst snd].
        ddestruct (chunk_ext h k AW Hk) as (Na & A1 & A2 & A3 & A4 & _). ddestruct (frame_ext h LF m fb AW GF Hfb) as (kk & i & _ & _ & _ & F1 & F2 & F3).
        apply (apart_of_ext _ _ _ _ (ext_lo k) (ext_hi k) (fst fb) (fst fb + snd fb)); try lia.
        intros x Hx. exact (ext_vs_frame h LF m k fb x HOK GF Hk Hfb Hx).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem hcs_block_c : forall h LB LF m A n, hok h -> HMc h LB LF m -> In (A, n) LB -> crange (hcsA h) A n.
  Proof.
    intros h LB LF m A n HOK HM0 HIn. dpose HM0 as ((_ & HLB) & _). rewrite HLB in HIn. intros x Hx. left. exact (block_crange h A n HOK HIn x Hx).
  Qed.

  #[using="Type"] Theorem hcs_fake_c : forall h LB LF m A n, hok h -> HMc h LB LF m -> In (A, n) LF -> crange (hcsA h) A n.
  Proof.
    intros h LB LF m A n HOK HM0 HIn. dpose HM0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GF & _). intros x Hx. left. exact (frame_crange h LF m A n HOK GF HIn x Hx).
  Qed.
End B.

End ARUN_1.
