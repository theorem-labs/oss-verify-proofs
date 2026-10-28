(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Asn1Aux CellsX HeapIface Frame Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop APopGen APopEmb. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AVstT AVstE AInstGen
     HMLib HM HMFrame AW_DepotB AW_DepotTop AW_MallocB AW_AllocB AW_Refill AW_Populate AW_EmbCfg
     AW_FakeDefs AW_FakeRep AHeapR AHeapB AHeapZ AHeapZW AMallocPost AHeapL AInstMallocG AInstEmb.
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
Ltac2 gd_tbl_AHeapExh () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.ranges_apart_b"; "ARUN_1.xzone"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.in_rangesZ"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.ro_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.rwstat_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.dep_zone"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.quar_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.sec_img_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.ia_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.emb_ranges"; "RocqVerifyHarness.AgentSubmission.BHeap.HMFrame.iagree"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapZ.rzone"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.HMLib.kept"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_exh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocB.A_ERRNO"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.A_OOM"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.emb_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.emb_P"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.emb_cap"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.awf'"; "RocqVerifyHarness.AgentSubmission.BHeap.APopEmb.emb_h"; "RocqVerifyHarness.AgentSubmission.BHeap.APopGen.null_h"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.hm_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.HK"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.AL0"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArrayMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArraySize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_htop"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_OOM_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.emb_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.Kfx"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstMallocG.KhF"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstEmb.KxF"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.emb_step"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_esz"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_EmbCfg.emb_fresh"; "RocqVerifyHarness.AgentSubmission.BHeap.AInstGen.CSh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.vst_of"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AMallocPost.img_keep"].

Section ARUN_1. Context {hAR : arun}.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ZEmb.
  Variable STKLO : Z.
  Local Notation hok := (hok STKLO).
  Variables (h : ahst) (LB LF : list blk) (m : mem).
  Hypothesis HOK : hok h.
  Hypothesis HM0 : HMc h LB LF m.
  (* [comment removed for export] *)
  Variable d : Z.
  Hypothesis DT : forall t, In t (tr_base h) -> t_hi t <= d \/ d + kEmbBytes <= t_lo t.
  Hypothesis DH1 : d + kEmbBytes <= l_b6 (h_L h) \/ l_b6 (h_L h) + kPrimHullLen <= d.
  Hypothesis DH2 : d + kEmbBytes <= l_pa (h_L h) \/ l_pa (h_L h) + kPaHullLen <= d.
  Hypothesis D63 : 0x65f000 <= d.
  Hypothesis DBAND : Pband d kEmbBytes.

  #[using="hAR STKLO HOK DT DH1 DH2 D63 DBAND"] Theorem rzone_not_emb : forall a, rzone h a -> ~ (d <= a < d + kEmbBytes).
  Proof.
    intros a Z0 FS. dpose HOK as (EL & AW & VW). pose proof (Lfacts STKLO h HOK) as LF0.
    dpose AW as ([WL _] & WC & WR & (WKF & NDAB & WKS) & WQ & WS & WD & WB & WBIG & WX & WG).
    assert (FSL : forall t, In t (tr_base h) -> ~ (t_lo t <= a < t_hi t)).
    { intros t Ht Hx. destruct (DT t Ht) as [X|X]; unfold t_hi in *; clear - X Hx FS; lia. }
    assert (HBE : forall x, l_b6 (h_L h) <= x < l_b6 (h_L h) + kPrimHullLen -> ~ (d <= x < d + kEmbBytes)) by (intros x HB HF; clear - HB HF DH1; lia).
    assert (EXT : forall k, In k (h_chunks h) -> ext_lo k <= a < ext_hi k -> False).
    { intros k Hk XE. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & _)|(P & sh & Hsh & Q1 & Q2)]).
      - pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _).
        destruct (user_in_HB STKLO h HOK (ck_cls k) a ltac:(lia) ltac:(lia)) as [HB _]. exact (HBE a HB FS).
      - apply (FSL _ (trb_sec h sh Hsh)). unfold sec_tr, t_hi. cbn [t_lo t_len]. clear - XE Q1 Q2. lia. }
    unfold rzone in Z0. unfold kEmbBytes, kHighMemBeg in *.
    destruct Z0 as [Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|[Z0|Z0]]]]]]]]]]]]]]].
    - unfold IMGZ, RT in Z0. cbn in Z0. clear - Z0 FS D63 DBAND. lia.
    - apply (FSL _ (trb_T h)). unfold t_hi; cbn; clear - Z0; lia.
    - apply (FSL _ (trb_ctx h)). unfold t_hi; cbn; clear - Z0; lia.
    - ddestruct Z0 as (b & Hb & Rb). apply (FSL _ (trb_node h b Hb)). unfold t_hi; cbn; clear - Rb; lia.
    - ddestruct Z0 as (b & Hb & Rb). apply (FSL _ (trb_store h b Hb)). unfold t_hi; cbn; clear - Rb; lia.
    - ddestruct Z0 as (k & Hk & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & _).
      apply (EXT k Hk). unfold ck_hdr, ck_user, kChunkHeaderSize in *. unfold ext_lo in *. destruct (ck_prim k); unfold ck_map_beg in *; clear - Rk E1 E2 E3 E4; lia.
    - ddestruct Z0 as (k & Hk & ST & Rk). ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _).
      unfold shad, kHighMemBeg in *. pose proof (Z.div_mod (ck_user k) 8 ltac:(lia)). pose proof (Z.div_mod (nfix (ck_n k) + 7) 8 ltac:(lia)). unfold nfix in *.
      pose proof aceil_bounds. clear - Rk FS D63 DBAND E1 E2 E3 E5 E6 H H0 H1 N0. lia.
    - ddestruct Z0 as (k & Hk & ST & Rk). destruct (ext_align STKLO h HOK k Hk) as [U16 E16]. ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & _).
      pose proof (Z.div_mod (ck_user k) 16 ltac:(lia)) as DU16. pose proof (Z.div_mod (ext_hi k) 16 ltac:(lia)) as DE16.
      apply (EXT k Hk). clear - Rk E1 E2 E4 U16 E16 DU16 DE16. lia.
    - ddestruct Z0 as (c & Hc & Rc). destruct (ri_in_HB STKLO h HOK a ltac:(unfold ri_addr in Rc; clear - Rc Hc; lia)) as [HB _]. exact (HBE a HB FS).
    - ddestruct Z0 as (c & Hc & Rc). destruct (fa_in_HB STKLO h HOK c a Hc Rc) as (HB & _). exact (HBE a HB FS).
    - ddestruct Z0 as (c & Hc & Rc). cbn zeta in Rc. pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & _ & _ & MULIM & _).
      pose proof (Z.div_mod (region_beg (h_L h) c + r_alloc_user (h_reg h c)) 8 ltac:(lia)) as D1.
      pose proof (Z.div_mod (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as D2.
      pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as M2.
      assert (MU : r_alloc_user (h_reg h c) < r_mapped_user (h_reg h c)) by (unfold shad in Rc; clear - Rc D2 M2 AUMU; lia).
      destruct (user_in_HB STKLO h HOK c (region_beg (h_L h) c + r_mapped_user (h_reg h c) - 1) Hc ltac:(clear - MU AUMU; lia)) as [HB _].
      destruct (user_in_HB STKLO h HOK c (region_beg (h_L h) c + r_alloc_user (h_reg h c)) Hc ltac:(clear - MU AUMU; lia)) as [HBG _].
      unfold shad, kPrimHullLen, kHighMemBeg in *. pose proof aceil_bounds. clear - Rc FS LF0 D63 DBAND HB HBG D1 D2 M2 AUMU H. lia.
    - ddestruct Z0 as (c & k & Hc & Hk & ->). pose proof (WR c ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc.
      ddestruct WRc as (_ & AUMU & AUCS & _). pose proof (class_size_range c Hc) as CSR.
      assert (KC : k * class_size c + class_size c <= r_alloc_user (h_reg h c)).
      { rewrite AUCS in Hk |- *. rewrite Z.mul_comm, Z.div_mul in Hk by lia. clear - Hk CSR. nia. }
      destruct (user_in_HB STKLO h HOK c (chunk_at (h_L h) c k) Hc ltac:(unfold chunk_at; clear - Hk KC AUMU CSR; nia)) as [HB _].
      unfold shad, kPrimHullLen, kHighMemBeg in *. pose proof (Z.div_mod (chunk_at (h_L h) c k) 8 ltac:(lia)) as D1. pose proof aceil_bounds. clear - FS LF0 D63 DBAND HB D1 H. lia.
    - ddestruct Z0 as (b & Hb & Rb).
      assert (WBb : wf_batch h b).
      { dpose WQ as ((F1 & _) & (F2 & _) & _). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) F1 b Hb)| exact (proj1 (Forall_forall _ _) F2 b Hb)]. }
      ddestruct WBb as (_ & _ & _ & i & Hi & EB).
      pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & AUCS & _).
      assert (CS24 : class_size 24 = 8192) by reflexivity. unfold kBatchClass in Hi, EB. unfold carved in Hi. rewrite CS24 in Hi.
      pose proof AUCS as AU. unfold carved in AU. rewrite CS24 in AU.
      destruct (user_in_HB STKLO h HOK 24 a ltac:(lia)) as [HB _]; [| exact (HBE a HB FS)].
      rewrite EB in Rb. unfold chunk_at in Rb. rewrite CS24 in Rb. clear - Rb Hi AU AUMU. lia.
    - dpose WS as (S1 & _ & S3 & S4 & S5 & _). unfold kPaHullLen in *. clear - Z0 S3 S4 S5 FS DH2. lia.
    - ddestruct Z0 as (sh & Hsh & Rsh). dpose WS as (_ & _ & _ & _ & _ & _ & _ & SHW). pose proof (proj1 (Forall_forall _ _) SHW sh Hsh) as (_ & SM & _).
      apply (FSL _ (trb_sec h sh Hsh)). unfold sec_tr, t_hi. cbn [t_lo t_len]. clear - Rsh SM. lia.
    - apply (FSL _ (trb_dtls h)). unfold t_hi; cbn; clear - Z0; lia.
  Qed.
End ZEmb.
(* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_agree : ltac2:(CDefT.buildp (gd_tbl_AHeapExh ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$2.Pcs,(3.$4.)P,(5.$6.R4.R2.R1.)P,(5.$6.R4.R3.R2.)P,(7.(8.(9.R4.(:.(;.R3.)))+10000.)(8.+65?000.R4.))Pa,$2.P,(<.(8.R6.R1.)(=.R1.(9.R6.(:.(;.R5.)))))(>.(1.(0.&8.))A1.R8.(?.R2.)A1.R9.(?.R2.))")
(* [comment removed for export] *).
Proof.
  (intros m m' A cs dd_H; ddestruct dd_H as [[WF (A0 & A64' & B)] (_ & A64 & W)]; intros dd_H; ddestruct dd_H as [[_ (_ & _ & B')] (_ & _ & W')]; intros OFF a Ha).
  pose proof (cells_bytes_length cs WF) as LEN.
  specialize (B (Z.to_nat (a - A)) ltac:(rewrite LEN; clear - Ha; lia)). specialize (B' (Z.to_nat (a - A)) ltac:(rewrite LEN; clear - Ha; lia)).
  replace (A + Z.of_nat (Z.to_nat (a - A))) with a in B, B' by (clear - Ha; lia).
  specialize (W (a - A) ltac:(clear - Ha; lia)). specialize (W' (a - A) ltac:(clear - Ha; lia)). replace (A + (a - A)) with a in W, W' by (clear; lia).
  destruct (wr_off_byte m a ltac:(clear - A0 Ha; lia) ltac:(clear - OFF Ha; lia) ltac:(clear - A64 Ha; lia) W) as [b E].
  destruct (wr_off_byte m' a ltac:(clear - A0 Ha; lia) ltac:(clear - OFF Ha; lia) ltac:(clear - A64 Ha; lia) W') as [b' E'].
  unfold mrd in B, B'. rewrite E in B. rewrite E' in B'. rewrite E, E'. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xzone : list (Z * Z) := [(0x18bc60, 0x18bc61); (0x63c9ec, 0x63c9f0); (0x109268, 0x1092a0)].

Section ZFrameExh.
  Variable STKLO : Z.
  Local Notation hok := (hok STKLO).
  Variables (h : ahst) (m m' : mem) (c : Z).
  Hypothesis HOK : hok h.
  Hypothesis WM : wmono asegs m m'.
  Hypothesis Hc : 1 <= c <= 31.
  Local Notation Rc := (ri_addr (h_L h) c).
  (* [comment removed for export] *)
  Hypothesis AG : zagree (fun a => rzone h a /\ ~ in_rangesZ xzone a /\ a <> Rc + 68) m m'.

  #[using="hAR STKLO h c HOK Hc AG"] Lemma zimg_sub_x : ltac2:(CDefT.buildp (gd_tbl_AHeapExh ()) "PRS,(3.(10.$2.$2.))P,(>.$11.(12.R1.$13.)$14.)P,Pa,$2.P,(15.R3.R1.)(15.(16.(10.$2.$2.)$17.(16.(10.$2.$2.)$18.(16.(10.$2.$2.)$19.(16.(10.$2.$2.)$1:.(16.(10.$2.$2.)$1;.(16.(10.$2.$2.)$1<.$1=.))))))R2.)(1>.R3.Vm,Vm',)")
(* [comment removed for export] *).
  Proof.
    intros RS AP SUB. eapply (iagree_of_zagree _ RS m m' AG). intros a Ha.
    assert (IZ : in_rangesZ IMGZ a) by (apply (ranges_cover_b_sound _ IMGZ a hm_img_cover); apply SUB, Ha).
    split; [left; exact IZ|]. split; [exact (ranges_apart_b_sound RS xzone a AP Ha)|].
    pose proof (Lfacts STKLO h HOK) as LF0. unfold IMGZ, RT in IZ. cbn in IZ. unfold ri_addr, ri_base, space_end, kSpaceSize, kHighMemBeg in *. clear - IZ LF0 Hc. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG"] Lemma kzx : ltac2:(CDefT.buildp (gd_tbl_AHeapExh ()) "PA,$2.Pn,$2.P,Pa,$2.P,(<.(8.R3.R1.)(=.R1.(9.R3.R2.)))(<.(1?.Vh,R2.)(<.(7.(=.R2.+10000.)(8.+65?000.R2.))(20.(>.$2.R2.(9.(21.(22.Vh,)Vc,)+44.)))))(23.Vm,Vm',R3.R2.)")
(* [comment removed for export] *).
  Proof.
    intros A n H. eapply kept_of_zagree; [exact AG|]. intros a Ha. ddestruct (H a Ha) as (Z1 & Z2 & Z3).
    split; [exact Z1|]. split; [unfold xzone; cbn; clear - Z2; lia| exact Z3].
  Qed.

  (* [comment removed for export] *)
  #[using="Hc"] Lemma ri_byte : forall a, ~ (ri_base (h_L h) <= a < ri_base (h_L h) + 4096) -> a <> Rc + 68.
  Proof. intros a N E. apply N. unfold ri_addr in E. clear - E Hc. lia. Qed.

  #[using="STKLO HOK WM Hc AG"] Theorem HMc_zframe_exh : ltac2:(CDefT.buildp (gd_tbl_AHeapExh ()) "PLB,(3.(10.$2.$2.))PLF,(3.(10.$2.$2.))Pdd,$2.Psz,$2.P,(24.VhAR,Vh,R4.R3.Vm,)P,(>.$11.(25.(26.Vh,)Vc,)$27.)P,(5.$6.Vm',(9.(21.(22.Vh,)Vc,)+44.)(28.$4.(29.(2:.&8.+1.))(2;.$4.)))P,(2<.(0.&40.)Le,(0.&40.)(5.$6.Vm',$2=.(28.$4.(2>.R1.)(2;.$4.))))P,(2<.(0.&8.)Lo,(0.&8.)(5.$6.Vm',$2?.(28.$4.(29.R1.)(2;.$4.))))P,(30.(31.R7.)R7.(32.R7.)R6.Vm',)P,(33.VhAR,(34.(35.Vh,Vc,=$14.)R8.R7.))P,(36.Vh,R:.Vm',)(24.VhAR,(34.(35.Vh,Vc,=$14.)R:.R9.)R<.R;.Vm',)")
(* [comment removed for export] *).
  Proof.
    intros LB LF dd sz HM0 EX0 EX' ERR' OOM' EMB' AWF' GF'. dpose HOK as (EL & AW & VW).
    dpose HM0 as (HP & GM & (GRO & GRW) & GT & GD & GC & GR & GQ & GS & GF & GI & GE).
    dpose AW as ([WL _] & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    pose proof (Lfacts STKLO h HOK) as LF0. unfold kHighMemBeg, kPrimHullLen, kPaHullLen, kFakeBytes in LF0.
    assert (TLO : Timg (l_T (h_L h)) /\ 0 <= l_fs (h_L h)) by (unfold wf_L, lowhigh, kHighMemBeg in WL; clear - WL; lia).
    pose proof (Limg STKLO h HOK) as [TI DI].
    dpose GM as (_ & _ & _ & WRT & _).
    (* [comment removed for export] *)
    assert (NRL : forall t a, In t (tr_of h) -> t_lit t = true -> t_lo t <= a < t_hi t -> a <> Rc + 68).
    { intros t a Ht TL Ha. apply ri_byte. intros RIx. destruct (ri_in_HB STKLO h HOK a RIx) as [HB _].
      exact (proj1 (lit_apart_hulls STKLO h HOK t a Ht TL Ha) HB). }
    assert (NRU : forall c' a, 1 <= c' <= 31 -> region_beg (h_L h) c' <= a < region_beg (h_L h) c' + r_mapped_user (h_reg h c') -> a <> Rc + 68).
    { intros c' a Hc' Ha. apply ri_byte. intros RIx. destruct (ri_in_HB STKLO h HOK a RIx) as [_ NU]. exact (NU c' Hc' Ha). }
    assert (NRS : forall a, a < 17594333495296 -> a <> Rc + 68).
    { intros a Ha. apply ri_byte. unfold ri_base, space_end, kSpaceSize. clear - Ha LF0. lia. }
    assert (NRP : forall a, l_pa (h_L h) <= a < l_pa (h_L h) + 8388608 -> a <> Rc + 68).
    { intros a Ha. apply ri_byte. intros RIx. destruct (ri_in_HB STKLO h HOK a RIx) as [HB _]. exact (hulls_apart STKLO h HOK a HB ltac:(unfold kPaHullLen; exact Ha)). }
    (* [comment removed for export] *)
    assert (K63 : forall k, In k (h_chunks h) -> 0x65f000 <= ck_ab k /\ 0x65f000 <= ck_user k /\ (ck_prim k = false -> 0x65f000 + 4096 <= ck_ab k)).
    { intros k Hk. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & _ & _ & [E5 _] & _).
      unfold ext_lo in E1, E5. unfold ck_hdr, ck_user, ck_map_beg, kChunkHeaderSize in *. pose proof (rz_size_bound' (ck_n k)) as RZ. unfold ck_rz in *.
      destruct (ck_prim k).
      - clear - E1 E2 E5 RZ. split; [lia|]. split; [lia|]. intros X; discriminate X.
      - clear - E1 E2 E5 RZ. split; [lia|]. split; [lia|]. intros _; lia. }
    assert (KNR : forall k a, In k (h_chunks h) -> ext_lo k <= a < ext_hi k -> a <> Rc + 68).
    { intros k a Hk XE. ddestruct (chunk_ext h k AW Hk) as (_ & E1 & E2 & E3 & E4 & _ & _ & [(P & C30 & R1 & R2 & _)|(P & sh & Hsh & Q1 & Q2)]).
      - pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRk. cbn zeta in WRk. ddestruct WRk as (_ & AUMU' & _).
        apply (NRU (ck_cls k)); [lia| lia].
      - apply (NRL (sec_tr sh) a (tr_of_sec h sh Hsh) eq_refl). unfold sec_tr, t_hi. cbn [t_lo t_len]. clear - XE Q1 Q2. lia. }
    assert (B63 : forall b, In b (q_batches (h_tq h) ++ q_batches (h_gq h)) -> 0x65f000 <= b_addr b
                  /\ region_beg (h_L h) 24 <= b_addr b /\ b_addr b + 8192 <= region_beg (h_L h) 24 + r_mapped_user (h_reg h 24)).
    { intros b Hb.
      assert (WBb : wf_batch h b).
      { dpose WQ as ((F1 & _) & (F2 & _) & _). apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) F1 b Hb)| exact (proj1 (Forall_forall _ _) F2 b Hb)]. }
      ddestruct WBb as (_ & _ & _ & i & Hi & EB).
      pose proof (WR 24 ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & AUCS & _).
      assert (CS24 : class_size 24 = 8192) by reflexivity. unfold kBatchClass in Hi, EB. unfold carved in Hi. rewrite CS24 in Hi.
      pose proof AUCS as AU. unfold carved in AU. rewrite CS24 in AU. rewrite EB. unfold chunk_at. rewrite CS24.
      unfold region_beg, kRegionSize. clear - Hi AU AUMU LF0. lia. }
    assert (TLIT : forall a, l_T (h_L h) <= a < l_T (h_L h) + 4096 -> a <> Rc + 68).
    { intros a Ha. apply (NRL _ a (tr_of_T h) eq_refl). unfold t_hi. cbn [t_lo t_len]. exact Ha. }
    assert (G1' : hm_statics (h_L h) m').
    { split.
      + eapply hm_ro_frame; [exact GRO| | | | |].
        * apply zimg_sub_x; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto.
        * apply kzx. intros a Ha. split; [right; left; clear - Ha; lia| split; [clear - Ha TI; lia| apply TLIT; clear - Ha; lia]].
        * apply kzx. intros a Ha. split; [right; right; left; unfold wf_L in WL; clear - Ha WL; lia| split; [clear - Ha LF0; lia|]].
          apply (NRL _ a (tr_of_ctx h) eq_refl). unfold t_hi. cbn [t_lo t_len]. clear - Ha LF0. lia.
        * apply kzx. intros a Ha. split; [right; right; left; unfold wf_L in WL; clear - Ha WL; lia| split; [clear - Ha LF0; lia|]].
          apply (NRL _ a (tr_of_ctx h) eq_refl). unfold t_hi. cbn [t_lo t_len]. clear - Ha LF0. lia.
        * apply kzx. intros a Ha. split; [do 15 right; clear - Ha; lia| split; [clear - Ha DI; lia|]].
          apply (NRL _ a (tr_of_dtls h) eq_refl). unfold t_hi. cbn [t_lo t_len]. clear - Ha. lia.
      + ddestruct GRW as (_ & _ & FBM). split; [exact ERR'| split; [exact OOM'|]].
        eapply keep_rw; [exact FBM| | exact WM]. eapply iagree_kept; [apply (zimg_sub_x [(0x106770, 0x106771)]); [vm_compute; reflexivity|]| vm_compute; reflexivity].
        intros a Ha. rewrite !in_rangesZ_app. right. left. unfold rwstat_ranges. cbn in Ha |- *. clear - Ha. lia. }
    assert (G2' : hm_thread h m').
    { eapply hm_thread_frame; [exact WM| exact GT| | | | exact WRT| clear - TLO; lia].
      + apply kzx. intros a Ha. split; [right; left; clear - Ha; lia| split; [clear - Ha TI; lia| apply TLIT; clear - Ha; lia]].
      + intros c' Hc'. apply kzx. intros a Ha. split; [right; left; clear - Ha Hc'; lia| split; [clear - Ha Hc' TI; lia| apply TLIT; clear - Ha Hc'; lia]].
      + apply kzx. intros a Ha. split; [right; left; clear - Ha; lia| split; [clear - Ha TI; lia| apply TLIT; clear - Ha; lia]]. }
    assert (G3' : hm_depot h m').
    { eapply hm_depot_frame; [exact GD| exact WM| | |].
      + apply zimg_sub_x; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto.
      + intros b Hb. dpose WD as (_ & _ & F & _). pose proof (proj1 (Forall_forall _ _) F b Hb) as (Hb63 & _).
        apply kzx. intros a Ha. split; [do 3 right; left; exists b; auto| split; [clear - Ha Hb63; lia|]].
        apply (NRL _ a (tr_of_node h b Hb) eq_refl). unfold node_tr, t_hi. cbn [t_lo t_len]. exact Ha.
      + intros b Hb. dpose WD as (_ & _ & _ & _ & _ & F & _). pose proof (proj1 (Forall_forall _ _) F b Hb) as (Hb63 & _).
        apply kzx. intros a Ha. split; [do 4 right; left; exists b; auto| split; [clear - Ha Hb63; lia|]].
        apply (NRL _ a (tr_of_store h b Hb) eq_refl). unfold store_tr, t_hi. cbn [t_lo t_len]. exact Ha. }
    assert (G4' : hm_chunks h m').
    { eapply hm_chunks_frame; [exact WM| exact GC| exact AW|]. intros k Hk. ddestruct (K63 k Hk) as (KA & KU & _).
      ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & _). destruct (ext_align STKLO h HOK k Hk) as [U16 E16].
      pose proof (Z.div_mod (ck_user k) 16 ltac:(lia)) as DU16. pose proof (Z.div_mod (ext_hi k) 16 ltac:(lia)) as DE16.
      split; [| split].
      + apply kzx. intros a Ha. split; [do 5 right; left; exists k; split; [exact Hk|]; unfold ck_user; clear - Ha; lia| split; [clear - Ha KA; lia|]].
        apply (KNR k a Hk). unfold ck_hdr, ck_user, kChunkHeaderSize in *. unfold ext_lo in *. destruct (ck_prim k); unfold ck_map_beg in *; clear - Ha E1 E2 E3 E4; lia.
      + intros ST. apply kzx. intros a Ha. split; [do 6 right; left; exists k; auto|]. unfold shad in Ha. pose proof (Z.div_mod (ck_user k) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (ck_user k) 8 ltac:(lia)).
        pose proof (Z.div_mod (nfix (ck_n k) + 7) 8 ltac:(lia)). unfold nfix in *. pose proof aceil_bounds.
        split; [clear - Ha KU H H0; lia| apply NRS; clear - Ha E3 E4 E6 N0 H H0 H1 H2; lia].
      + intros ST. apply kzx. intros a Ha. split; [do 7 right; left; exists k; auto| split; [clear - Ha KU; lia|]].
        apply (KNR k a Hk). clear - Ha E1 E2 E3 E4 U16 E16 DU16 DE16. lia. }
    assert (G5' : hm_regions (emb_h (null_h h c 0 true) dd sz) m').
    { intros c' Hc'. cbn [emb_h null_h h_L h_reg h_acct acct_set_emb acct_set_exh a_exh]. unfold null_reg.
      dpose LF0 as (_ & _ & B1 & _ & B2 & B3 & B4 & _). unfold space_end, kSpaceSize in B4. pose proof aceil_bounds as ACB.
      assert (KFA : forall c0, 1 <= c0 <= 31 -> kept m m' (fa_beg (h_L h) c0) (r_mapped_fa (h_reg h c0))).
      { intros c0 Hc0. apply kzx. intros a Ha. split; [do 9 right; left; exists c0; auto|].
        ddestruct (fa_in_HB STKLO h HOK c0 a Hc0 Ha) as (_ & SE & _).
        split; [unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset in Ha; clear - Ha Hc0 B1 B2; nia| apply ri_byte; unfold ri_base; clear - SE; lia]. }
      assert (KTS : forall c0, 1 <= c0 <= 31 -> kept m m' (shad (region_beg (h_L h) c0 + r_alloc_user (h_reg h c0))) ((r_mapped_user (h_reg h c0) - r_alloc_user (h_reg h c0)) / 8)).
      { intros c0 Hc0. apply kzx. intros a Ha. split; [do 10 right; left; exists c0; split; [exact Hc0|]; cbn zeta; exact Ha|]. unfold shad in Ha.
        pose proof (WR c0 ltac:(unfold kNumClasses; clear - Hc0; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _ & _ & MULIM & _). unfold kUserLimit in MULIM.
        set (q := region_beg (h_L h) c0 + r_alloc_user (h_reg h c0)) in *. pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
        pose proof (Z.div_mod (r_mapped_user (h_reg h c0) - r_alloc_user (h_reg h c0)) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c0) - r_alloc_user (h_reg h c0)) 8 ltac:(lia)) as M2.
        unfold region_beg, kRegionSize in q.
        split; [clear - Ha Hc0 B1 B2 AUMU H H0; lia| apply NRS; subst q; clear - Ha Hc0 B1 B2 B3 B4 ACB AUMU MULIM H H0 D2 M2; lia]. }
      assert (KSF : forall c0 k, 1 <= c0 <= 31 -> 0 <= k < r_alloc_user (h_reg h c0) / class_size c0 -> kept m m' (shad (chunk_at (h_L h) c0 k)) 1).
      { intros c0 k Hc0 Hk. apply kzx. intros a Ha. split; [do 11 right; left; dexists c0, k; split; [exact Hc0|]; split; [exact Hk|]; clear - Ha; lia|]. unfold shad in Ha.
        pose proof (WR c0 ltac:(unfold kNumClasses; clear - Hc0; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & AUCS & _ & MULIM & _). unfold kUserLimit in MULIM.
        pose proof (class_size_range c0 Hc0) as CSR.
        assert (KC : k * class_size c0 + class_size c0 <= r_alloc_user (h_reg h c0)).
        { rewrite AUCS in Hk |- *. rewrite Z.mul_comm, Z.div_mul in Hk by lia. clear - Hk CSR. nia. }
        set (q := chunk_at (h_L h) c0 k) in *. pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
        unfold chunk_at, region_beg, kRegionSize in q.
        split; [clear - Ha Hc0 Hk B1 B2 H H0 CSR; nia| apply NRS; subst q; clear - Ha Hc0 Hk KC AUMU MULIM B1 B2 B3 B4 ACB H H0 CSR; nia]. }
      destruct (Z.eqb_spec c' c) as [->|NE].
      - (* [comment removed for export] *)
        pose proof (GR c Hc) as GRc. unfold hm_region in GRc |- *. cbn zeta in GRc |- *. rewrite EX0 in GRc.
        unfold rN. cbn [r_mapped_user r_alloc_user r_mapped_fa r_fa]. unfold r_nfreed in *. cbn [r_fa]. rewrite !Z.add_0_r.
        ddestruct GRc as (RMX & RNF & RMFA & RAU & R40 & RMU & R56 & R68 & (stw & R72) & (s80 & s88 & R80) & RFA & (js & RJS & JSL) & WRU & SHT & SHF).
        pose proof (WR c ltac:(unfold kNumClasses; clear - Hc; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _ & _ & _ & _ & _ & _ & NF4 & _). unfold r_nfreed in NF4.
        assert (K1a : kept m m' Rc 68).
        { apply kzx. intros a Ha. split; [do 8 right; left; exists c; split; [exact Hc| clear - Ha; lia]|].
          split; [unfold ri_addr, ri_base, space_end, kSpaceSize in Ha; clear - Ha Hc B1 B2; lia| clear - Ha; lia]. }
        assert (K1b : kept m m' (Rc + 69) 27).
        { apply kzx. intros a Ha. split; [do 8 right; left; exists c; split; [exact Hc| clear - Ha; lia]|].
          split; [unfold ri_addr, ri_base, space_end, kSpaceSize in Ha; clear - Ha Hc B1 B2; lia| clear - Ha; lia]. }
        pose proof (Z.div_mod (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (r_mapped_user (h_reg h c) - r_alloc_user (h_reg h c)) 8 ltac:(lia)) as MB.
        Ltac rka K1 := eapply keep_rw; [eassumption| eapply kept_sub; [exact K1| lia| cbn; lia]| assumption].
        split; [rka K1a|]. split; [rka K1a|]. split; [rka K1a|]. split; [rka K1a|]. split; [rka K1a|]. split; [rka K1a|]. split; [rka K1a|].
        split; [exact EX'|].
        split; [exists stw; rka K1b|]. split; [dexists s80, s88; rka K1b|].
        split. { eapply keep_u32arr; [exact RFA| eapply kept_sub; [exact (KFA c Hc)| lia| rewrite length_map; lia]| exact WM]. }
        split. { exists js. split; [| exact JSL]. eapply keep_u32arr; [exact RJS| eapply kept_sub; [exact (KFA c Hc)| lia| lia]| exact WM]. }
        split; [eapply wr_at_transport; [exact WRU| exact WM]|].
        split. { eapply keep_rw; [exact SHT| eapply kept_sub; [exact (KTS c Hc)| lia|]| exact WM]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
        intros k Hk. eapply keep_rw; [exact (SHF k Hk)| exact (KSF c k Hc Hk)| exact WM].
      - (* [comment removed for export] *)
        pose proof (WR c' ltac:(unfold kNumClasses; clear - Hc'; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _ & _ & _ & _ & _ & _ & NF4 & _).
        eapply (hm_region_frame m m' WM); [exact (GR c' Hc')| exact AUMU| exact NF4|]. split; [| split; [| split]].
        + apply kzx. intros a Ha. split; [do 8 right; left; exists c'; auto|].
          split; [unfold ri_addr, ri_base, space_end, kSpaceSize in Ha; clear - Ha Hc' B1 B2; lia| unfold ri_addr in *; clear - Ha NE Hc Hc'; lia].
        + exact (KFA c' Hc').
        + exact (KTS c' Hc').
        + intros k Hk. exact (KSF c' k Hc' Hk). }
    assert (G6' : hm_quar h m').
    { eapply hm_quar_frame; [exact WM| exact GQ| | |].
      + apply zimg_sub_x; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto.
      + apply kzx. intros a Ha. split; [right; left; clear - Ha; lia| split; [clear - Ha TI; lia| apply TLIT; clear - Ha; lia]].
      + intros b Hb. ddestruct (B63 b Hb) as (Hb63 & U1 & U2). apply kzx. intros a Ha. split; [do 12 right; left; exists b; auto| split; [clear - Ha Hb63; lia|]].
        apply (NRU 24); [clear; lia| clear - Ha U1 U2; lia]. }
    assert (G7' : hm_sec h m').
    { eapply hm_sec_frame; [exact WM| exact GS| exact WS| | |].
      + apply zimg_sub_x; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto.
      + dpose WS as (S1 & _ & S3 & S4 & S5 & _).
        apply kzx. intros a Ha. split; [do 13 right; left; exact Ha| split; [clear - Ha LF0; lia| apply NRP; clear - Ha S3 S4 S5; lia]].
      + intros sh Hsh. destruct (In_nth_error _ _ Hsh) as [i Ni]. dpose WK as (_ & _ & WK3). ddestruct (WK3 i sh Ni) as (k & Hk & PK & MB & MS).
        ddestruct (K63 k Hk) as (_ & _ & KA). specialize (KA PK). unfold ck_map_beg in MB.
        dpose WS as (_ & _ & _ & _ & _ & _ & _ & SHW). pose proof (proj1 (Forall_forall _ _) SHW sh Hsh) as (_ & SM & _).
        apply kzx. intros a Ha. split; [do 14 right; left; exists sh; auto| split; [clear - Ha KA MB; lia|]].
        apply (NRL _ a (tr_of_sec h sh Hsh) eq_refl). unfold sec_tr, t_hi. cbn [t_lo t_len]. clear - Ha SM. lia. }
    assert (G9' : hm_ia h m').
    { eapply hm_ia_frame; [exact WM| exact GI|]. apply zimg_sub_x; [vm_compute; reflexivity|]. intros a Ha. rewrite !in_rangesZ_app. tauto. }
    (* [comment removed for export] *)
    split; [split; [exact AWF'| destruct HP as [_ HLB]; rewrite HLB; reflexivity]|].
    split; [exact (hm_maps_frame _ _ _ GM WM)|]. split; [exact G1'|]. split; [exact G2'|]. split; [exact G3'|]. split; [exact G4'|].
    split; [exact G5'|]. split; [exact G6'|]. split; [exact G7'|]. split; [exact GF'|]. split; [exact G9'|].
    exact EMB'.
  Qed.
End ZFrameExh.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Repack.
  Variable STKLO : Z.
  Let R := R0 STKLO.
  Local Notation hok := (hok STKLO).

  #[using="Type"] Theorem exh_repack : ltac2:(CDefT.buildp (gd_tbl_AHeapExh ()) "Ph,$37.PLB,(3.$38.)PLF,(3.$38.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Pmo,$39.Pmo',$39.Pc,$2.Plo,$2.PSP,$2.Pxa,(1.$2.)PP',$2.Pd',$2.Pcap',$2.Psz',$2.P,(3:.VhAR,VSTKLO,R?.)P,(24.VhAR,R10.R?.R>.R=.)P,(3;.VhAR,$3<.R11.R<.)P,(<.(8.+1.R;.)(8.R;.+1>.))P,(8.(3=.R13.)$3>.)P,(8.(9.(3?.(40.R14.R=.))$41.)$42.)P,(8.VSTKLO,R=.)P,(8.R>.R=.)P,(8.R>.(43.(22.R17.)))P,(44.(28.(10.$2.$2.)(45.$2.$2.R10.R?.)(28.(10.$2.$2.)(45.$2.$2.(9.(46.(22.R18.))+<60.)(9.(46.(22.R18.))+<61.))(28.(10.$2.$2.)(45.$2.$2.(21.(22.R18.)R11.)(9.(21.(22.R18.)R11.)+8.))(28.(10.$2.$2.)(45.$2.$2.(9.(21.(22.R18.)R11.)+44.)(9.(21.(22.R18.)R11.)+45.))(28.(10.$2.$2.)(45.$2.$2.$47.(9.$47.+1.))(28.(10.$2.$2.)(45.$2.$2.$2=.(9.$2=.+4.))(16.(10.$2.$2.)(2;.(10.$2.$2.))(48.R<.))))))))R15.R14.)P,(49.$6.R16.R15.)P,(4:.(4;.VhAR,R1:.R13.R15.(4<.$11.)(4<.$11.)(4=.(4>.R1:.))(4?.(4>.R1:.)))(50.VhAR,R1:.R15.)R10.R14.)P,(5.$6.R17.(21.(22.R1;.)R14.)(28.$4.(51.(2:.&40.=))(2;.$4.)))P,(5.$6.R18.(9.(21.(22.R1<.)R15.)+44.)(28.$4.(29.(2:.&8.+1.))(2;.$4.)))P,(5.$6.R19.(9.(46.(22.R1=.))+<60.)(28.$4.(29.(2:.&8.=))(2;.$4.)))P,(5.$6.R1:.$47.(28.$4.(29.(2:.&8.+1.))(2;.$4.)))P,(5.$6.R1;.$2=.(28.$4.(2>.(2:.&40.+<.))(2;.$4.)))P,(30.R15.R14.R13.R12.R1<.)P,(52.(31.(53.(26.R21.)))(53.(26.R21.))(32.(53.(26.R21.)))(54.(26.R21.))R16.R15.R14.R13.R17.)P,(55.VhAR,(56.VhAR,$3<.R22.R1;.(4<.$11.)(4<.$11.)(4=.(4>.R22.))(4?.(4>.R22.)))R18.)P,(>.$11.(25.(26.R23.)R1<.)$27.)P,(=.+>0000000.(9.(57.(40.R24.R1=.))(58.+2.+12.)))Zh',$37.(34.(35.R25.R1>.=$14.)R19.R17.)(<.(3;.VhAR,$3<.R1.R20.)(<.(59.R21.R20.)(<.(3:.VhAR,VSTKLO,R1.)(<.Px,$2.P,(5:.$3<.(5;.R27.)R1.)(5:.$3<.(5;.R3.)R2.)(<.(5<.$6.VR,R25.R24.R1=.VSTKLO,(5=.(22.R26.))(2;.$5>.)R23.R22.)(<.(5?.R23.R22.)(24.VhAR,R1.R25.R24.R22.)))))))")
(* [comment removed for export] *).
  Proof.
    intros h LB LF m m' mo mo' c lo SP xa P' d' cap' sz' HOK HM0 HK0 GC HVM ROOMF LO SPL SPT MUX WM KFX MXc EXc UNWc OOMc ERRc EMBc STEP FRESH EX0 FRZ h'.
    dpose HOK as (EL & AW & VW). pose proof (Lfacts STKLO h HOK) as LF0. dpose (Lbands STKLO h HOK) as (TB & CB & FB & PB & DB). pose proof (Limg STKLO h HOK) as [TI DI].
    dpose AW as ([WL WLS] & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    dpose HM0 as (HP & GM & (GRO & GRW) & GT & GD & GC0 & GR & GQ & GS & GF & GI & GE).
    pose proof (awf'_bwf h AW) as BWF. assert (GC31 : 1 <= c <= 31) by (clear - GC; lia).
    pose proof (WR c ltac:(unfold kNumClasses; clear - GC; lia)) as WRc. cbn zeta in WRc. ddestruct WRc as (_ & AUMU & _ & MUAL & MULIM & MUAU & _).
    set (L := h_L h) in *. set (T := l_T L) in *. set (Rc := ri_addr L c) in *.
    (* [comment removed for export] *)
    assert (NZ : d' <> 0 /\ a_emb (h_acct h') = match xa with Some a => a | None => a_emb (h_acct h) end).
    { ddestruct STEP as (_ & _ & _ & [(E0 & a & -> & -> & ANZ) | (ENZ & -> & ->)]); split; try assumption; reflexivity. }
    destruct NZ as [NZ EEM].
    ddestruct (MX_exit h c mo HK0 BWF HVM GC31 ROOMF xa mo' h' KFX) as (HK' & FRM & CSE).
    { reflexivity. }
    { intros j. cbn [h' emb_h null_h h_reg]. unfold null_reg. destruct (Z.eqb_spec j c) as [->|]; [cbn [r_mapped_user]; unfold rN; lia| reflexivity]. }
    { intros j. cbn [h' emb_h null_h h_reg]. unfold null_reg. destruct (Z.eqb_spec j c) as [->|]; reflexivity. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. } { exact EEM. }
    (* [comment removed for export] *)
    assert (EA' : a_emb (h_acct h') = d') by reflexivity.
    pose proof (emb_geom AL0 h' mo' HK' ltac:(rewrite EA'; exact NZ)) as GEO. cbn zeta in GEO. rewrite EA' in GEO. change (h_L h') with L in GEO.
    ddestruct GEO as (D0 & DCE & DAL & DIMG & DBAND & DH1 & DH2). cbn [al_img_lo al_img_hi AL0] in DIMG. unfold kEmbBytes in *.
    assert (D63 : 0x65f000 <= d') by (clear - D0 DIMG; lia).
    assert (DT : forall t, In t (tr_base h) -> t_hi t <= d' \/ d' + 65536 <= t_lo t).
    { intros t Ht. rewrite <- EA'. apply (emb_apart AL0 h' mo' t HK' ltac:(rewrite EA'; exact NZ)).
      rewrite (tr_base_ext h h'); [exact Ht| reflexivity| | | reflexivity| reflexivity| reflexivity| reflexivity].
      - intros j. cbn [h' emb_h null_h h_reg]. unfold null_reg. destruct (Z.eqb_spec j c) as [->|]; [cbn [r_mapped_user]; unfold rN; lia| reflexivity].
      - intros j. cbn [h' emb_h null_h h_reg]. unfold null_reg. destruct (Z.eqb_spec j c) as [->|]; reflexivity. }
    (* [comment removed for export] *)
    assert (AWF' : awf' h').
    { assert (AWN : awf' (null_h h c 0 true)).
      { apply (awf'_null h c 0 true AW GC); [left; reflexivity| unfold rN; clear - MULIM; lia| unfold rN; clear - MUAU GC; lia| right; reflexivity]. }
      dpose WX as (_ & _ & _ & _ & _ & X6 & X7 & _).
      assert (FZ : frozen h c = true) by (unfold frozen, kUserLimit, kUserMapSize; apply Z.ltb_lt; clear - FRZ; lia).
      pose proof (csum_epi_exh h c GC31 FZ EX0) as EPI.
      ddestruct STEP as (_ & _ & [SZ1 SZ2] & _).
      assert (ESZ0 : 0 <= a_esz (h_acct h)) by (destruct X6 as [[_ ->]|(_ & _ & _ & _ & _ & _ & X)]; [clear; lia| exact X]).
      apply (awf'_emb (null_h h c 0 true) d' sz' AWN); unfold kEmbBytes.
      - unfold lowhigh, kHighMemBeg. clear - D0 DIMG DBAND. lia.
      - clear - D0; lia. - exact DCE. - exact DAL.
      - change (h_L (null_h h c 0 true)) with L. unfold kPrimHullLen in DH1. exact DH1.
      - change (h_L (null_h h c 0 true)) with L. unfold kPaHullLen in DH2. exact DH2.
      - rewrite EPI. unfold EM in *. clear - SZ1 SZ2 ESZ0 X7. lia. }
    assert (HOK' : hok h') by (split; [exact EL| split; [exact AWF'| exact (HK_vwf AL0 h' mo' HK')]]).
    (* [comment removed for export] *)
    assert (OUTW : forall a, ~ (lo <= a < SP) -> a <> T + 3168 -> ~ (Rc <= a < Rc + 8) -> a <> Rc + 68 -> ~ in_rangesZ xzone a -> ~ (d' <= a < d' + 65536) ->
              outside ((lo, SP) :: (T + 3168, T + 3169) :: (Rc, Rc + 8) :: (Rc + 68, Rc + 69) :: (A_OOM_CELL, A_OOM_CELL + 1) :: (A_ERRNO, A_ERRNO + 4) :: [] ++ emb_fp d') a).
    { intros a N1 N2 N3 N4 N5 N6. unfold emb_fp, A_EMB, kEmbBytes, A_OOM_CELL, A_ERRNO. unfold xzone in N5. cbn in N5. cbn [outside app]. clear - N1 N2 N3 N4 N5 N6. repeat split; lia. }
    pose proof GT as (UNW & _). fold L T in UNW.
    pose proof (GR c GC31) as GRc. unfold hm_region in GRc. cbn zeta in GRc. destruct GRc as (MX & _). fold L Rc in MX.
    assert (RC63 : 0x65f000 <= Rc /\ Rc + 128 <= ACEIL).
    { unfold Rc, ri_addr, ri_base, space_end, kSpaceSize. unfold kHighMemBeg, kPrimHullLen in LF0. fold L in LF0. unfold space_end, kSpaceSize in LF0. clear - LF0 GC. lia. }
    assert (AG : zagree (fun a => rzone h a /\ ~ in_rangesZ xzone a /\ a <> Rc + 68) m m').
    { (intros x dd_H; ddestruct dd_H as (Zx & NX & NB)). pose proof (rzone_lt_stklo STKLO h HOK _ Zx) as LT.
      pose proof (rzone_not_emb STKLO h HOK d' DT DH1 DH2 D63 DBAND _ Zx) as NE.
      destruct (Z.eq_dec (bv_unsigned x) (T + 3168)) as [E|NT].
      - rewrite <- (wa_unsigned_id x). apply (rw_cells_agree m m' (T + 3168) [C1 (Z_to_bv 8 0)] UNW UNWc); [cbn; clear - TI; lia| cbn; clear - E; lia].
      - destruct (Z_le_gt_dec Rc (bv_unsigned x)) as [G1|G1]; [destruct (Z_lt_ge_dec (bv_unsigned x) (Rc + 8)) as [G2|G2]|].
        + rewrite <- (wa_unsigned_id x). apply (rw_cells_agree m m' Rc [C8 (Z_to_bv 64 0)] MX MXc); [cbn; clear - RC63; lia| cbn; clear - G1 G2; lia].
        + apply MUX. apply OUTW; [clear - LT LO; lia| exact NT| clear - G2; lia| exact NB| exact NX| exact NE].
        + apply MUX. apply OUTW; [clear - LT LO; lia| exact NT| clear - G1; lia| exact NB| exact NX| exact NE]. }
    (* [comment removed for export] *)
    dpose VW as (TWF & APT & _).
    assert (STK0 : ACEIL <= STKLO) by (pose proof (Z.mod_pos_bound STKLO 64 ltac:(clear; lia)) as MB; clear - LF0 MB; lia).
    unfold kHighMemBeg, kPrimHullLen, kPaHullLen, kFakeBytes in LF0.
    assert (FST : T + 4096 <= l_fs L \/ l_fs L + 0xb09000 <= T).
    { destruct (APT _ _ (tr_of_T h) (fs_tr_in h)) as [E|X]; [exfalso; injection E; unfold kFakeBytes; clear; lia|].
      unfold t_hi, kFakeBytes in X. cbn [t_lo t_len] in X. subst T L. clear - X. lia. }
    assert (FSR : forall a, l_fs L <= a < l_fs L + 0xb09000 -> ~ (ri_base L <= a < ri_base L + 4096)).
    { intros a Fa Ra. destruct (ri_in_HB STKLO h HOK a Ra) as [HB _].
      exact (proj1 (lit_apart_hulls STKLO h HOK _ a (fs_tr_in h) eq_refl ltac:(unfold t_hi, kFakeBytes; cbn [t_lo t_len]; exact Fa)) HB). }
    assert (FSD : l_fs L + 0xb09000 <= d' \/ d' + 65536 <= l_fs L).
    { pose proof (DT _ (trb_fs h)) as X. unfold t_hi, kFakeBytes in X. cbn [t_lo t_len] in X. exact X. }
    assert (RCP : ri_base L <= Rc /\ Rc + 128 <= ri_base L + 4096) by (unfold Rc, ri_addr; clear - GC; lia).
    assert (XZ : forall a, in_rangesZ xzone a -> 0x10000 <= a < 0x65f000) by (intros a Ha; unfold xzone in Ha; cbn in Ha; clear - Ha; lia).
    assert (FSOUT : forall a, l_fs L <= a < l_fs L + 0xb09000 ->
              outside ((lo, SP) :: (T + 3168, T + 3169) :: (Rc, Rc + 8) :: (Rc + 68, Rc + 69) :: (A_OOM_CELL, A_OOM_CELL + 1) :: (A_ERRNO, A_ERRNO + 4) :: [] ++ emb_fp d') a).
    { intros a FR. apply OUTW.
      - clear - FR LF0 LO STK0. lia.
      - clear - FR FST. lia.
      - intros X. apply (FSR a FR). clear - X RCP. lia.
      - intros X. apply (FSR a FR). clear - X RCP. lia.
      - intros X. pose proof (XZ a X). clear - H FR LF0. lia.
      - clear - FR FSD. lia. }
    assert (AGF : zagree (fzone h LF) m m').
    { intros x Fx. apply MUX. apply FSOUT.
      destruct Fx as [F1|(fb & Hfb & F2)]; [subst L; clear - F1; lia|].
      dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3). unfold kFakeBytes in G2. subst L. clear - F2 G1 G2 G3. lia. }
    pose proof (hm_fake_zframe STKLO h m m' HOK WM LF GF AGF) as GF'.
    (* [comment removed for export] *)
    assert (EP' : P' = emb_P d' /\ cap' = emb_cap d').
    { ddestruct STEP as (-> & -> & _). unfold emb_P, emb_cap. destruct (Z.eqb_spec d' 0) as [E|_]; [exfalso; exact (NZ E)| split; reflexivity]. }
    destruct EP' as [-> ->].
    pose proof (HMc_zframe_exh STKLO h m m' c HOK WM GC31 AG LB LF d' sz' HM0 EX0 EXc
                  (ex_intro (fun e => rw_cells asegs m' A_ERRNO [C4 e]) (Z_to_bv 64 12) ERRc)
                  (ex_intro (fun o => rw_cells asegs m' A_OOM [C1 o]) (Z_to_bv 8 1) OOMc) EMBc AWF' GF') as HM'.
    (* [comment removed for export] *)
    assert (BT : forall A n a, In (A, n) LB -> A <= a < A + n ->
              0x65f000 <= a < ACEIL /\ a <> T + 3168 /\ ~ (ri_base L <= a < ri_base L + 4096) /\ ~ (d' <= a < d' + 65536)).
    { intros A n a HB Ra. dpose (block_bounds STKLO h LB LF m HOK HM0 A n HB) as (BB1 & BB2 & BB3 & _). split; [clear - Ra BB1 BB3; lia|].
      pose proof HP as [_ HLB]. rewrite HLB in HB. ddestruct (live_block h A n HB) as (k & Hk & _ & -> & ->).
      ddestruct (chunk_ext h k AW Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & [(PK & C30 & R1 & R2 & _)|(PK & sh & Hsh & SQ1 & SQ2)]).
      - pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; clear - C30; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU' & _).
        assert (UR : region_beg (h_L h) (ck_cls k) <= a < region_beg (h_L h) (ck_cls k) + r_mapped_user (h_reg h (ck_cls k))) by (clear - Ra E1 E2 E3 R1 R2 AUMU'; lia).
        destruct (user_in_HB STKLO h HOK (ck_cls k) a ltac:(clear - C30; lia) UR) as [HB' _].
        split; [| split].
        + ddestruct (user_point_unit h (ck_cls k) a AW ltac:(clear - C30; lia) UR) as (j & INj & Rj).
          destruct (APT _ _ (tr_of_T h) INj) as [E|X]; [exfalso; unfold uunit_tr in E; discriminate E|].
          unfold t_hi, uunit_tr in X, Rj. cbn [t_lo t_len] in X, Rj. subst T L. clear - X Rj. lia.
        + intros RIx. destruct (ri_in_HB STKLO h HOK a RIx) as [_ NU]. exact (NU (ck_cls k) ltac:(clear - C30; lia) UR).
        + unfold kPrimHullLen in *. clear - HB' DH1. subst L. lia.
      - dpose WS as (_ & _ & _ & _ & _ & _ & _ & SHW). pose proof (proj1 (Forall_forall _ _) SHW sh Hsh) as (_ & SM & _).
        assert (INS : t_lo (sec_tr sh) <= a < t_hi (sec_tr sh)) by (unfold sec_tr, t_hi; cbn [t_lo t_len]; clear - Ra E1 E2 E3 SQ1 SQ2; lia).
        split; [| split].
        + destruct (APT _ _ (tr_of_T h) (tr_of_sec h sh Hsh)) as [E|X].
          * exfalso. unfold sec_tr in E. injection E as E1' E2'. clear - E2' SM. lia.
          * unfold t_hi, sec_tr in X, INS. cbn [t_lo t_len] in X, INS. subst T L. clear - X INS. lia.
        + intros RIx. destruct (ri_in_HB STKLO h HOK a RIx) as [HB' _].
          exact (proj1 (lit_apart_hulls STKLO h HOK _ a (tr_of_sec h sh Hsh) eq_refl INS) HB').
        + pose proof (DT _ (trb_sec h sh Hsh)) as X. clear - X INS. lia. }
    (* [comment removed for export] *)
    split; [exact HK'|]. split; [exact FRM|]. split; [exact HOK'|].
    split. { intros x Hx. apply (proj1 (CSE x)). apply CSfx_inc; [intros a y Hy; left; exact Hy|]. apply (proj2 (CSh_entry AL0 h c x)). exact Hx. }
    split.
    { apply (presA_intro STKLO h LB LF m m' SP WM).
      - intros a Ha CA. apply MUX. rewrite wa_unsigned by exact Ha.
        destruct CA as [S|[C|(b & Hb & Rb)]].
        + apply OUTW.
          * clear - S; lia.
          * clear - S LF0 LO STK0 SPL. lia.
          * clear - S RC63 LF0 LO STK0 SPL. lia.
          * clear - S RC63 LF0 LO STK0 SPL. lia.
          * intros X. pose proof (XZ a X). pose proof aceil_bounds. clear - H H0 S LF0 LO STK0 SPL. lia.
          * clear - S DCE LF0 LO STK0 SPL. lia.
        + cbn [hl_data_lo hl_data_hi hl_static HL0 arl_L R R0] in C. destruct C as [C1 C2]. unfold RT in C2. cbn [in_rangesZ] in C2.
          apply OUTW.
          * pose proof aceil_bounds. clear - C1 H LF0 LO STK0. lia.
          * clear - C1 TI. lia.
          * clear - C1 RC63. lia.
          * clear - C1 RC63. lia.
          * unfold xzone. cbn [in_rangesZ]. clear - C1 C2. lia.
          * clear - C1 D63. lia.
        + apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
          * destruct b as [B j]. cbn [fst snd] in Rb. ddestruct (BT B j a Hb Rb) as (R1 & R2 & R3 & R4).
            apply OUTW; [clear - R1 LF0 LO STK0; lia| exact R2| clear - R3 RCP; lia| clear - R3 RCP; lia| intros X; pose proof (XZ a X); clear - H R1; lia| exact R4].
          * ddestruct (fdata_sub LF (fst b) (snd b) ltac:(destruct b; exact Hb)) as (fb & [(Hfb & F1 & F2)|(Hfb & F40)]);
              dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & G3); [| clear - F40 G3; lia].
            unfold kFakeBytes in G2. apply FSOUT. subst L. clear - Rb F1 F2 G1 G2. lia.
      - intros c0 Hc0 Hr. apply MUX. rewrite wa_unsigned by exact Hr.
        assert (SHC : shadow_of AL0 c0 = HM.shad c0) by reflexivity. rewrite SHC in *.
        assert (C47 : 0 <= c0 < 2^47).
        { dpose (hok_L STKLO h HOK) as (_ & _ & _ & SHI & _).
          destruct (cshd_cases STKLO h LB LF c0 Hc0) as [S|[(A & n & HIn & RA)|[(fb & Hfb & Rfb)|C]]].
          - subst L. clear - S LF0 SHI; pose proof aceil_bounds; lia.
          - destruct (BT A n c0 HIn RA) as [R1 _]. clear - R1; pose proof aceil_bounds; lia.
          - dpose (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb) as (G1 & G2 & _). subst L. unfold kFakeBytes in *. clear - G1 G2 Rfb LF0; pose proof aceil_bounds; lia.
          - clear - C; lia. }
        assert (SB : 0x7fff8000 <= HM.shad c0 < 0x10007fff8000) by (unfold HM.shad; pose proof (Z.div_mod c0 8 ltac:(lia)); pose proof (Z.mod_pos_bound c0 8 ltac:(lia)); clear - C47 H H0; lia).
        apply OUTW.
        * pose proof aceil_bounds. clear - SB H LF0 LO STK0. lia.
        * clear - SB TB. lia.
        * clear - SB RCP LF0. unfold ri_base, space_end, kSpaceSize in *. lia.
        * clear - SB RCP LF0. unfold ri_base, space_end, kSpaceSize in *. lia.
        * intros X. pose proof (XZ _ X). clear - H SB. lia.
        * clear - SB DBAND. lia. }
    split.
    { (* [comment removed for export] *)
      split.
      - intros x Hx Hz. apply MUX. apply OUTW.
        + pose proof aceil_bounds. clear - Hx H LF0 LO STK0. lia.
        + clear - Hx TI. lia.
        + clear - Hx RC63. lia.
        + clear - Hx RC63. lia.
        + intros X. apply Hz. unfold awz, xzone, A_INSTANCE, A_IA, A_OOM, A_IA_INIT, A_SS, A_DEP_END, A_OOM_CELL, A_ERRNO, A_EMB in *. cbn [in_rangesZ] in X |- *. clear - X. lia.
        + clear - Hx D63. lia.
      - intros x Hx. apply MUX. apply OUTW.
        + pose proof aceil_bounds. clear - Hx H LF0 LO STK0. lia.
        + clear - Hx TB. lia.
        + clear - Hx RCP LF0. unfold ri_base, space_end, kSpaceSize in *. lia.
        + clear - Hx RCP LF0. unfold ri_base, space_end, kSpaceSize in *. lia.
        + intros X. pose proof (XZ _ X). clear - H Hx. lia.
        + clear - Hx DBAND. lia. }
    exact HM'.
  Qed.
End Repack.
End ARUN_1.
