(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes MState HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK AW_FreeG AW_FreeR AW_FreeRB AW_FreeFam AW_FreeRM AW_FreeFF.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKinvS AKFrame. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AInstFree AW_Unwind AW_Unwind2 AW_MmapFixed AW_DepotB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_FreeA AW_QPut AW_Enqueue AW_Drain AW_Blist AW_RecTop AW_FreePhD.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_FakeDefs AW_FakeRep HMLib HM HMFrame AW_FreeHM AW_FreeHMS AW_FreeHMX AW_FreeHMQ AW_MunmapCfg AW_RecStep AW_RecLoop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_DepotTop AW_MallocB AHeapR AMallocPost AHeapL AFreePost.
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
Ltac2 gd_tbl_AW_FreePres () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_chunks'"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AHeapR.hok"; "RocqVerifyHarness.AgentSubmission.BHeap.HM.HMc"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_depot'"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.hgeom"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeHMX.fkeepR"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.qs_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.rp_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_RecLoop.wmono_ex"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AMallocPost.img_keep"].

Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma shadE : forall a, AW_FreeG.shad a = 0x7fff8000 + a / 8. Proof. reflexivity. Qed.

#[using="Type"] Lemma shad_add8 : forall a n, a mod 8 = 0 -> AW_FreeG.shad (a + n) = AW_FreeG.shad a + n / 8.
Proof.
  intros a n A8. rewrite !shadE.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite A8, Z.add_0_r in Da.
  pose proof (Z.div_mod (a + n) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (a + n) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod n 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as M2. lia.
Qed.
#[using="Type"] Lemma shad_lt8 : forall a c, a mod 8 = 0 -> c < a -> AW_FreeG.shad c < AW_FreeG.shad a.
Proof.
  intros a c A8 LT. rewrite !shadE.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite A8, Z.add_0_r in Da.
  pose proof (Z.div_mod c 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as M1. lia.
Qed.
#[using="Type"] Lemma shad_le : forall a c, a <= c -> AW_FreeG.shad a <= AW_FreeG.shad c.
Proof. intros a c H. apply shad_mono. exact H. Qed.
#[using="Type"] Lemma shad_range47 : forall c, 0 <= c < 2^47 -> 0x7fff8000 <= AW_FreeG.shad c < kHighMemBeg.
Proof. intros c Hc. rewrite shadE. unfold kHighMemBeg. pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). lia. Qed.
#[using="Type"] Lemma mod4096_8 : forall a, a mod 4096 = 0 -> a mod 8 = 0.
Proof. intros a H. pose proof (Z.div_mod a 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D. replace (4096 * (a / 4096)) with ((512 * (a / 4096)) * 8) by lia. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MoreZones.
  Variable h : ahst.
  Hypothesis G : hgeom h.
  #[using="G"] Lemma z_fs_pa : zapart (l_fs (h_L h), kFakeBytes) (l_pa (h_L h), 0x800000).
  Proof. exact (G 2%nat 3%nat _ _ eq_refl eq_refl ltac:(discriminate)). Qed.
  #[using="G"] Lemma z_node_fs : forall j b, nth_error (d_nb (h_dep h)) j = Some b -> zapart (l_fs (h_L h), kFakeBytes) (b, 2^20).
  Proof. intros j b Hj. eapply (z_fixed_dyn h G 2); [lia| reflexivity| exact (hzones_node h j b Hj)]. Qed.
  #[using="G"] Lemma z_store_fs : forall j b, nth_error (d_bl (h_dep h)) j = Some b -> zapart (l_fs (h_L h), kFakeBytes) (b, 2^23).
  Proof. intros j b Hj. eapply (z_fixed_dyn h G 2 _ (length (d_nb (h_dep h)) + j)%nat); [lia| reflexivity| rewrite <- (hzones_store h j b Hj); f_equal; lia]. Qed.
End MoreZones.

(* [comment removed for export] *)
#[using="Type"] Lemma ab_unique : ltac2:(CDefT.buildp (gd_tbl_AW_FreePres ()) "Ph,$0.Pk1,$1.Pk2,$1.P,(2.VhAR,R3.)P,(3.$1.R3.(4.R4.))P,(3.$1.R3.(4.R5.))P,(5.$6.(7.R5.)(7.R4.))(5.$1.R6.R5.)")
(* [comment removed for export] *).
Proof.
  (intros h k1 k2 dd_H; ddestruct dd_H as (_ & ND & _); intros Hk1 Hk2 EA). revert Hk1 Hk2. induction (h_chunks h) as [|x l IH]; [intros []|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  intros [->|Hk1] [->|Hk2]; [reflexivity| | | exact (IH ND' Hk1 Hk2)].
  - exfalso. apply NI. rewrite EA. apply in_map. exact Hk2.
  - exfalso. apply NI. rewrite <- EA. apply in_map. exact Hk1.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tr_of_extra : forall h r, In r (l_extra (h_L h)) -> In (TR (fst r) (snd r) (xkind (snd r)) true false) (tr_of h).  (* [comment removed for export] *)
Proof.
  intros h r Hr. unfold tr_of. rewrite !in_app_iff. do 6 right. left. unfold fixed_of. rewrite !in_app_iff. right; left.
  apply (in_map (fun r0 => TR (fst r0) (snd r0) (xkind (snd r0)) true false)). exact Hr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FP.
  Variable STKLO : Z.
  Let R := R0 STKLO.

  #[using="Type"] Theorem free_pres : ltac2:(CDefT.buildp (gd_tbl_AW_FreePres ()) "Ph,$0.Ph2,$0.PLB,(8.(9.$6.$6.))PLF,(8.(9.$6.$6.))Pm,P,(:.&40.)(;.(:.&8.))Pm',P,(:.&40.)(;.(:.&8.))Plo,$6.PSP,$6.P,(<.VhAR,VSTKLO,R8.)P,(=.VhAR,R9.R7.R6.R5.)P,(>.R9.)P,(2.VhAR,R:.)P,(?.R;.)P,(10.VhAR,R<.)P,(11.R=.)P,(5.$12.(13.R>.)(13.R?.))P,(14.(13.R10.)(15.R?.)(16.R?.)(17.R?.)(18.(19.R?.))(1:.(19.R?.))R:.R9.R<.R;.)P,(1;.(16.R10.)R=.R<.)P,(1<.VSTKLO,R<.)P,(1<.R=.R<.)P,(1<.R=.(1=.(13.R14.)))(1>.(1?.$20.VR,(15.R14.)R12.R>.VSTKLO,(1=.(13.R15.))(21.$22.)R11.R10.)(23.R11.R10.))")
(* [comment removed for export] *).
  Proof.
    intros h h2 LB LF m m' lo SP HOK HM0 WR2 WK2 WS2 WD2 GEO2 EL2 FK WMX LOL LOSP SPH.
    dpose HOK as (ESL & AWF & VWF). pose proof AWF as (WL' & _). dpose WL' as (WL & _ & _).
    dpose WL as (_ & B6a & B6b & B64K & B6c & B6d & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STK0 & STKH & _ & FSA & FSLH & FSC & TA & TLH & TC & _ & _ & _ & _ & PAA & PALH & PAC & _).
    pose proof aceil_bounds as ACB. unfold kHighMemBeg in B6c. unfold lowhigh, kHighMemBeg in FSLH, TLH, PALH.
    assert (WLh2 : wf_L (h_L h2)) by (rewrite EL2; exact WL).
    set (L := h_L h) in *.
    (* [comment removed for export] *)
    assert (KP : forall a, 0 <= a < 2^64 ->
              ~ (lo <= a < SP) -> ~ (l_T L <= a < l_T L + 4096) -> ~ (in_hull L a /\ ~ in_blk (blocks h2) a) ->
              ~ (AW_FreeG.shad (l_b6 L) <= a < AW_FreeG.shad (l_b6 L + 0x2000011000) /\ ~ (exists c, in_blk (blocks h2) c /\ a = AW_FreeG.shad c)) ->
              ~ (exists q, In q (qs_of h2) /\ (fst q <= a < fst q + snd q \/ AW_FreeG.shad (fst q) <= a < AW_FreeG.shad (fst q) + snd q / 8)) ->
              ~ in_rangesZ free_img_ranges a ->
              ~ (exists b, In b (d_nb (h_dep h2)) /\ b <= a < b + 2^20) -> ~ (exists b, In b (d_bl (h_dep h2)) /\ b <= a < b + 2^23) ->
              ~ (l_pa L <= a < l_pa L + 0x800000) -> ~ in_rp (rp_of h2) a ->
              m' (wa a) = m (wa a)).
    { intros a Ha. pose proof (FK (wa a)) as X. cbv zeta in X. rewrite (wa_unsigned a Ha) in X. exact X. }
    (* [comment removed for export] *)
    assert (QSI : forall q, In q (qs_of h2) -> exists kq, In kq (h_chunks h2) /\ ck_prim kq = false /\ ck_st kq = CHUNK_QUARANTINE /\ fst q = ck_map_beg kq /\ snd q = ck_map_size kq
              /\ fst q mod 8 = 0 /\ snd q mod 4096 = 0 /\ 4096 < snd q /\ 0x65f000 <= fst q /\ fst q + snd q <= ACEIL /\ (fst q + snd q <= 0x7fff7000 \/ kHighMemBeg <= fst q)
              /\ AW_FreeG.ext_lo kq = fst q /\ AW_FreeG.ext_hi kq = fst q + snd q
              /\ exists i, nth_error (s_chunks (h_sec h2)) i = Some (SH (fst q) (snd q) (needed2 (ck_n kq)))).
    { intros q Hq. unfold qs_of in Hq. apply in_map_iff in Hq as (kq & <- & Hkq). apply filter_In in Hkq as [Hkq Pq]. apply andb_prop in Pq as [P1 P2].
      apply Bool.negb_true_iff in P1. apply Z.eqb_eq in P2. cbn [fst snd].
      ddestruct (chunk_ext' h2 kq WLh2 WR2 WK2 Hkq) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & [(PK & _)|(PK & i & Ni & XL & XH)]); [congruence|].
      dpose WK2 as (WKF & _ & _). pose proof (proj1 (Forall_forall _ _) WKF kq Hkq) as (_ & _ & _ & WX). rewrite P1 in WX. ddestruct WX as (_ & _ & MB4 & _).
      dpose WS2 as (_ & _ & _ & _ & _ & _ & _ & WS8). pose proof (proj1 (Forall_forall _ _) WS8 _ (nth_error_In _ _ Ni)) as (SM & SB & _). cbn [s_map_size s_map_beg] in SM, SB.
      exists kq. rewrite XL, XH in *. repeat (split; [first [exact Hkq| exact P1| exact P2| reflexivity| exact (mod4096_8 _ MB4)| exact SM| exact SB| clear - E5; lia| exact E6| exact (proj2 E5)]|]).
      exists i. exact Ni. }
    assert (RPI : forall r, In r (rp_of h2) -> snd r = 32 /\ exists k i, In k (h_chunks h2) /\ ck_prim k = false /\ nth_error (s_chunks (h_sec h2)) i = Some (SH (fst r) (ck_map_size k) (needed2 (ck_n k)))
              /\ fst r = ck_map_beg k /\ 4096 < ck_map_size k /\ 0x65f000 <= fst r /\ fst r + ck_map_size k <= ACEIL /\ (fst r + ck_map_size k <= 0x7fff7000 \/ kHighMemBeg <= fst r)
              /\ AW_FreeG.ext_lo k = fst r /\ AW_FreeG.ext_hi k = fst r + ck_map_size k /\ ck_map_beg k + 4096 + 16 <= ck_user k).
    { intros r Hr. unfold rp_of in Hr. apply in_map_iff in Hr as (sh & <- & Hsh). cbn [fst snd]. split; [reflexivity|].
      destruct (In_nth_error _ _ Hsh) as [i0 Ni0]. dpose WK2 as (WKF & _ & WK3). ddestruct (WK3 i0 sh Ni0) as (k & Hk & PK & MB & MS).
      ddestruct (chunk_ext' h2 k WLh2 WR2 WK2 Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & [(PK' & _)|(_ & i & Ni & XL & XH)]); [congruence|].
      dpose WS2 as (_ & _ & _ & _ & _ & _ & _ & WS8). pose proof (proj1 (Forall_forall _ _) WS8 _ (nth_error_In _ _ Ni)) as (SM & SB & _). cbn [s_map_size s_map_beg] in SM, SB.
      dpose (chunk_geom' h2 k WLh2 WR2 WK2 Hk) as (RZ16 & _ & _).
      dexists k, i. rewrite <- MB in *. rewrite XL, XH in *. repeat (split; [first [exact Hk| exact PK| exact Ni| reflexivity| exact SB| clear - E5; lia| exact E6| exact (proj2 E5)]|]).
      unfold ck_user, ck_map_beg. clear - RZ16. lia. }
    assert (NBI : forall b, In b (d_nb (h_dep h2)) -> 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ exists j, nth_error (d_nb (h_dep h2)) j = Some b).
    { intros b Hb. dpose WD2 as (_ & _ & F & _). pose proof (proj1 (Forall_forall _ _) F b Hb) as (X1 & X2 & _). split; [exact X1|]. split; [exact X2| exact (In_nth_error _ _ Hb)]. }
    assert (BLI : forall b, In b (d_bl (h_dep h2)) -> 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ exists j, nth_error (d_bl (h_dep h2)) j = Some b).
    { intros b Hb. dpose WD2 as (_ & _ & _ & _ & _ & F & _). pose proof (proj1 (Forall_forall _ _) F b Hb) as (X1 & X2 & _). split; [exact X1|]. split; [exact X2| exact (In_nth_error _ _ Hb)]. }
    assert (BKI : forall b, In b (blocks h2) -> exists k, In k (h_chunks h2) /\ ck_st k = CHUNK_ALLOCATED /\ fst b = ck_user k /\ snd b = ck_n k
              /\ AW_FreeG.ext_lo k + 16 <= ck_user k /\ ck_user k + ck_n k <= AW_FreeG.ext_hi k /\ 0x65f000 <= AW_FreeG.ext_lo k /\ AW_FreeG.ext_hi k <= ACEIL
              /\ (AW_FreeG.ext_hi k <= 0x7fff7000 \/ kHighMemBeg <= AW_FreeG.ext_lo k)
              /\ ((ck_prim k = true /\ forall x, AW_FreeG.ext_lo k <= x < AW_FreeG.ext_hi k -> in_hull L x)
                  \/ (ck_prim k = false /\ ck_map_beg k + 4096 + 16 <= ck_user k /\ AW_FreeG.ext_lo k = ck_map_beg k /\ AW_FreeG.ext_hi k = ck_map_beg k + ck_map_size k /\ ck_map_beg k mod 8 = 0
                      /\ exists i, nth_error (s_chunks (h_sec h2)) i = Some (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k)))))).
    { intros b Hb. unfold blocks, live in Hb. apply in_map_iff in Hb as (k & <- & Hk). apply filter_In in Hk as [Hk ST]. apply Z.eqb_eq in ST. cbn [fst snd].
      ddestruct (chunk_ext' h2 k WLh2 WR2 WK2 Hk) as (N0 & E1 & E2 & E3 & E4 & E5 & E6 & ARM).
      dpose (chunk_geom' h2 k WLh2 WR2 WK2 Hk) as (RZ16 & _ & _).
      exists k. split; [exact Hk|]. split; [exact ST|]. split; [reflexivity|]. split; [reflexivity|].
      split; [clear - E1 E2; lia|]. split; [clear - E3; lia|]. split; [exact (proj1 E5)|]. split; [exact E6|]. split; [exact (proj2 E5)|].
      destruct ARM as [(PK & C30 & R1 & R2 & _)|(PK & i & Ni & XL & XH)].
      - left. split; [exact PK|]. intros x Hx. pose proof (WR2 (ck_cls k) ltac:(unfold kNumClasses; clear - C30; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _).
        destruct (user_in_hull h2 (ck_cls k) x WLh2 WR2 ltac:(clear - C30; lia) ltac:(clear - Hx R1 R2 AUMU; lia)) as (HX & _). unfold in_hull. subst L. rewrite <- EL2. exact HX.
      - right. dpose WK2 as (WKF & _ & _). pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (_ & _ & _ & WX). rewrite PK in WX. ddestruct WX as (_ & _ & MB4 & _).
        split; [exact PK|]. split; [unfold ck_user, ck_map_beg; clear - RZ16; lia|]. split; [exact XL|]. split; [exact XH|]. split; [exact (mod4096_8 _ MB4)|]. exists i. exact Ni. }
    (* [comment removed for export] *)
    pose proof (z_T_hull h2 GEO2) as ZTH. pose proof (z_pa_hull h2 GEO2) as ZPH. pose proof (z_fs_hull h2 GEO2) as ZFH. pose proof (z_T_fs h2 GEO2) as ZTF. pose proof (z_fs_pa h2 GEO2) as ZFP.
    unfold zapart in ZTH, ZPH, ZFH, ZTF, ZFP. cbn [fst snd] in ZTH, ZPH, ZFH, ZTF, ZFP. rewrite EL2 in ZTH, ZPH, ZFH, ZTF, ZFP. fold L in ZTH, ZPH, ZFH, ZTF, ZFP.
    assert (SHhi : AW_FreeG.shad (l_b6 L + 0x2000011000) < kHighMemBeg).
    { rewrite shadE. unfold kHighMemBeg. pose proof (Z.div_mod (l_b6 L + 0x2000011000) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (l_b6 L + 0x2000011000) 8 ltac:(lia)). clear - H H0 B6d ACB. lia. }
    assert (SHlo : 0x7fff8000 + 0x10007fff8000 / 8 <= AW_FreeG.shad (l_b6 L)).
    { rewrite shadE. apply Z.add_le_mono_l. apply Z.div_le_mono; [clear; lia| exact B6c]. }
    assert (IMGZ : forall a, 0x65f000 <= a -> ~ in_rangesZ free_img_ranges a).
    { intros a Ha. unfold free_img_ranges, A_INSTANCE, A_IA, A_IA_INIT. cbn [in_rangesZ]. clear - Ha. lia. }
    (* [comment removed for export] *)
    assert (KB : forall s, 0x7fff8000 <= s < kHighMemBeg ->
              ~ (AW_FreeG.shad (l_b6 L) <= s < AW_FreeG.shad (l_b6 L + 0x2000011000) /\ ~ (exists c, in_blk (blocks h2) c /\ s = AW_FreeG.shad c)) ->
              (forall q, In q (qs_of h2) -> ~ (AW_FreeG.shad (fst q) <= s < AW_FreeG.shad (fst q) + snd q / 8)) ->
              m' (wa s) = m (wa s)).
    { intros s Hs Z4 Z5. unfold kHighMemBeg in Hs. apply KP.
      - clear - Hs; lia. - clear - Hs LOL STK0 ESL ACB; subst L; lia. - clear - Hs TLH; lia. - intros [[H1 _] _]. clear - Hs H1 B6c; lia. - exact Z4.
      - (intros dd_H; ddestruct dd_H as (q & Hq & [Rq|Rq])); [| exact (Z5 q Hq Rq)]. ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & Q63 & QCE & QLH & _). unfold kHighMemBeg in QLH. clear - Hs Rq Q63 QCE QLH ACB. lia.
      - apply IMGZ. clear - Hs; lia.
      - (intros dd_H; ddestruct dd_H as (b & Hb & Rb)). ddestruct (NBI b Hb) as (_ & _ & j & Hj). pose proof (z_node_band h2 GEO2 j b Hj) as Y. unfold zapart in Y. cbn [fst snd] in Y. clear - Hs Rb Y. lia.
      - (intros dd_H; ddestruct dd_H as (b & Hb & Rb)). ddestruct (BLI b Hb) as (_ & _ & j & Hj). pose proof (z_store_band h2 GEO2 j b Hj) as Y. unfold zapart in Y. cbn [fst snd] in Y. clear - Hs Rb Y. lia.
      - clear - Hs PALH. lia.
      - (intros dd_H; ddestruct dd_H as (r & Hr & Rr)). ddestruct (RPI r Hr) as (E32 & k & i & _ & _ & _ & _ & BIG & R63 & RCE & RLH & _). unfold kHighMemBeg in RLH. rewrite E32 in Rr. clear - Hs Rr BIG R63 RCE RLH. lia. }
    (* [comment removed for export] *)
    assert (KI : forall a, 0x10000 <= a < 0x65f000 -> ~ in_rangesZ awz a -> m' (wa a) = m (wa a)).
    { intros a Ha NZ. apply KP.
      - clear - Ha; lia. - clear - Ha LOL STK0 ESL ACB; subst L; lia. - clear - Ha TLH; lia. - intros [[H1 _] _]. clear - Ha H1 B6c; lia.
      - intros [[H1 _] _]. clear - Ha H1 SHlo. lia.
      - (intros dd_H; ddestruct dd_H as (q & Hq & Rq)). ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & Q63 & _). pose proof (shad_le 0x65f000 (fst q) Q63) as SQ. rewrite (shadE 0x65f000) in SQ. clear - Ha Rq Q63 SQ. lia.
      - intros X. apply NZ. unfold awz, free_img_ranges, A_INSTANCE, A_IA, A_IA_INIT, A_OOM, A_SS, A_DEP_END, A_ERRNO, AW_Populate.A_EMB in *. cbn [in_rangesZ] in X |- *. clear - X. lia.   (* [comment removed for export] *)
      - (intros dd_H; ddestruct dd_H as (b & Hb & Rb)). destruct (NBI b Hb) as (B1 & _). clear - Ha Rb B1. lia.
      - (intros dd_H; ddestruct dd_H as (b & Hb & Rb)). destruct (BLI b Hb) as (B1 & _). clear - Ha Rb B1. lia.
      - clear - Ha PALH. lia.
      - (intros dd_H; ddestruct dd_H as (r & Hr & Rr)). ddestruct (RPI r Hr) as (E32 & k & i & _ & _ & _ & _ & _ & R63 & _). clear - Ha Rr R63. lia. }
    (* [comment removed for export] *)
    assert (KIS : forall s, 0x7fffa000 <= s < 0x800c3e00 -> m' (wa s) = m (wa s)).
    { intros s Hs. apply KB.
      - unfold kHighMemBeg. clear - Hs; lia.
      - intros [[H1 _] _]. clear - Hs H1 SHlo. lia.
      - intros q Hq Rq. ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & Q63 & _). pose proof (shad_le 0x65f000 (fst q) Q63) as SQ. rewrite (shadE 0x65f000) in SQ. clear - Hs Rq SQ. lia. }
    (* [comment removed for export] *)
    assert (KS : forall a, SP <= a -> a < 2^64 -> m' (wa a) = m (wa a)).
    { intros a H1 H2. assert (AC : ACEIL <= a) by (clear - H1 LOL LOSP STK0 ESL; subst L; lia). apply KP.
      - clear - H1 H2 AC ACB; lia. - clear - H1; lia. - clear - AC TC; subst L; lia. - intros [[_ X] _]. clear - AC X B6d; subst L; lia.
      - intros [[_ X] _]. clear - AC X SHhi ACB. unfold kHighMemBeg in SHhi. lia.
      - (intros dd_H; ddestruct dd_H as (q & Hq & Rq)). ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & Q8 & _ & _ & Q63 & QCE & _).
        pose proof (shad_le (fst q + snd q) ACEIL QCE) as SQ. rewrite (shad_add8 (fst q) (snd q) Q8) in SQ. pose proof (shad_range47 ACEIL ltac:(clear - ACB; lia)) as SA. unfold kHighMemBeg in SA.
        clear - AC Rq QCE SQ SA ACB. lia.
      - apply IMGZ. clear - AC ACB; lia.
      - (intros dd_H; ddestruct dd_H as (b & Hb & Rb)). ddestruct (NBI b Hb) as (_ & B2 & _). clear - AC Rb B2. lia.
      - (intros dd_H; ddestruct dd_H as (b & Hb & Rb)). ddestruct (BLI b Hb) as (_ & B2 & _). clear - AC Rb B2. lia.
      - clear - AC PAC; subst L; lia.
      - (intros dd_H; ddestruct dd_H as (r & Hr & Rr)). ddestruct (RPI r Hr) as (E32 & k & i & _ & _ & _ & _ & BIG & _ & RCE & _). rewrite E32 in Rr. clear - AC Rr BIG RCE. lia. }
    (* [comment removed for export] *)
    assert (KBLK : forall b a, In b (blocks h2) -> fst b <= a < fst b + snd b -> m' (wa a) = m (wa a) /\ ~ in_qs (qs_of h2) a
              /\ forall q, In q (qs_of h2) -> a + 1 <= fst q \/ fst q + snd q <= a).
    { intros b a Hb Ra. ddestruct (BKI b Hb) as (k & Hk & ST & EB & EN & X1 & X2 & X63 & XCE & XLH & ARM). rewrite EB, EN in Ra.
      assert (QA : forall q, In q (qs_of h2) -> a + 1 <= fst q \/ fst q + snd q <= a).
      { intros q Hq. ddestruct (QSI q Hq) as (kq & Hkq & _ & STq & _ & _ & _ & _ & _ & _ & _ & _ & QL & QH & _).
        assert (NE : ck_ab k <> ck_ab kq) by (intros E; pose proof (ab_unique h2 k kq WK2 Hk Hkq E) as <-; rewrite ST in STq; discriminate STq).
        pose proof (ext_disj' h2 k kq WLh2 WR2 WK2 GEO2 Hk Hkq NE) as D. rewrite QL, QH in D. clear - D Ra X1 X2. lia. }
      split; [| split; [(intros dd_H; ddestruct dd_H as (q & Hq & Rq)); destruct (QA q Hq); clear - Rq H; lia| exact QA]].
      unfold kHighMemBeg in XLH. apply KP.
      - clear - Ra X1 X2 X63 XCE ACB; lia. - clear - Ra X2 XCE LOL STK0 ESL; subst L; lia.
      - destruct ARM as [(PK & HU)|(PK & U16 & XL & XH & M8 & i & Ni)].
        + pose proof (HU a ltac:(clear - Ra X1 X2; lia)) as HX. unfold in_hull in HX. clear - HX ZTH. lia.
        + pose proof (z_sec_T h2 GEO2 i _ Ni) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. rewrite EL2 in Y. fold L in Y. clear - Y Ra X1 X2 XL XH. lia.
      - intros [_ NB]. apply NB. exists b. split; [exact Hb| rewrite EB, EN; exact Ra].
      - intros [R1 _]. clear - R1 Ra X1 X2 X63 XLH SHlo SHhi. unfold kHighMemBeg in SHhi. lia.
      - (intros dd_H; ddestruct dd_H as (q & Hq & [Rq|Rq])); [destruct (QA q Hq); clear - Rq H; lia|].
        ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & Q8 & _ & QB & Q63 & QCE & _).
        pose proof (shad_le (fst q + snd q) ACEIL QCE) as SQ. rewrite (shad_add8 (fst q) (snd q) Q8) in SQ. pose proof (shad_range47 ACEIL ltac:(clear - ACB; lia)) as SA.
        pose proof (shad_range47 (fst q) ltac:(clear - Q63 QCE QB ACB; lia)) as SB. unfold kHighMemBeg in SA, SB. clear - Rq Ra X1 X2 X63 XLH SQ SA SB. lia.
      - apply IMGZ. clear - Ra X1 X63; lia.
      - (intros dd_H; ddestruct dd_H as (nb & Hnb & Rnb)). ddestruct (NBI nb Hnb) as (_ & _ & j & Hj). destruct ARM as [(PK & HU)|(PK & U16 & XL & XH & M8 & i & Ni)].
        + pose proof (HU a ltac:(clear - Ra X1 X2; lia)) as HX. unfold in_hull in HX. pose proof (z_node_hull h2 GEO2 j nb Hj) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL2 in Y. fold L in Y. clear - HX Y Rnb. lia.
        + pose proof (z_sec_node h2 GEO2 i _ j nb Ni Hj) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. clear - Y Ra X1 X2 XL XH Rnb. lia.
      - (intros dd_H; ddestruct dd_H as (nb & Hnb & Rnb)). ddestruct (BLI nb Hnb) as (_ & _ & j & Hj). destruct ARM as [(PK & HU)|(PK & U16 & XL & XH & M8 & i & Ni)].
        + pose proof (HU a ltac:(clear - Ra X1 X2; lia)) as HX. unfold in_hull in HX. pose proof (z_store_hull h2 GEO2 j nb Hj) as Y. unfold zapart in Y. cbn [fst snd] in Y. rewrite EL2 in Y. fold L in Y. clear - HX Y Rnb. lia.
        + pose proof (z_sec_store h2 GEO2 i _ j nb Ni Hj) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. clear - Y Ra X1 X2 XL XH Rnb. lia.
      - destruct ARM as [(PK & HU)|(PK & U16 & XL & XH & M8 & i & Ni)].
        + pose proof (HU a ltac:(clear - Ra X1 X2; lia)) as HX. unfold in_hull in HX. clear - HX ZPH. lia.
        + pose proof (z_sec_pa h2 GEO2 i _ Ni) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. rewrite EL2 in Y. fold L in Y. clear - Y Ra X1 X2 XL XH. lia.
      - (intros dd_H; ddestruct dd_H as (r & Hr & Rr)). ddestruct (RPI r Hr) as (E32 & kr & ir & Hkr & PKr & Nir & Er & BIGr & _ & _ & _ & RL & RH & U16r). rewrite E32 in Rr.
        destruct ARM as [(PK & HU)|(PK & U16 & XL & XH & M8 & i & Ni)].
        + pose proof (HU a ltac:(clear - Ra X1 X2; lia)) as HX. unfold in_hull in HX. pose proof (z_sec_hull h2 GEO2 ir _ Nir) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. rewrite EL2 in Y. fold L in Y.
          clear - HX Y Rr BIGr. lia.
        + destruct (Nat.eq_dec i ir) as [E|NI].
          * subst ir. rewrite Ni in Nir. injection Nir as EMB _ _. clear - Ra Rr EMB U16 Er. lia.
          * pose proof (z_sec_sec h2 GEO2 i ir _ _ Ni Nir NI) as Y. unfold zapart in Y. cbn [fst snd s_map_beg s_map_size] in Y. clear - Y Ra Rr X1 X2 XL XH BIGr. lia. }
    (* [comment removed for export] *)
    assert (KFS : forall a, l_fs L <= a < l_fs L + kFakeBytes -> m' (wa a) = m (wa a) /\ ~ in_qs (qs_of h2) a /\ forall q, In q (qs_of h2) -> a + 1 <= fst q \/ fst q + snd q <= a).
    { intros a Ha. unfold kFakeBytes in *.
      assert (QA : forall q, In q (qs_of h2) -> a + 1 <= fst q \/ fst q + snd q <= a).
      { intros q Hq. ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & i & Ni).
        pose proof (z_sec_fs h2 GEO2 i _ Ni) as Y. unfold zapart, kFakeBytes in Y. cbn [fst snd s_map_beg s_map_size] in Y. rewrite EL2 in Y. fold L in Y. clear - Y Ha. lia. }
      split; [| split; [(intros dd_H; ddestruct dd_H as (q & Hq & Rq)); destruct (QA q Hq); clear - Rq H; lia| exact QA]].
      apply KP.
      - clear - Ha FSC FSLH ACB; subst L; lia. - clear - Ha FSC LOL STK0 ESL; subst L; lia. - clear - Ha ZTF; lia.
      - intros [[H1 H2] _]. clear - Ha H1 H2 ZFH. lia.
      - intros [[H1 H2] _]. clear - Ha H1 H2 FSLH FSC SHlo SHhi ACB. unfold kHighMemBeg in SHhi. lia.
      - (intros dd_H; ddestruct dd_H as (q & Hq & [Rq|Rq])); [destruct (QA q Hq); clear - Rq H; lia|].
        ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & Q8 & _ & QB & Q63 & QCE & _).
        pose proof (shad_le (fst q + snd q) ACEIL QCE) as SQ. rewrite (shad_add8 (fst q) (snd q) Q8) in SQ. pose proof (shad_range47 ACEIL ltac:(clear - ACB; lia)) as SA.
        pose proof (shad_range47 (fst q) ltac:(clear - Q63 QCE QB ACB; lia)) as SB. unfold kHighMemBeg in SA, SB. clear - Rq Ha FSLH FSC SQ SA SB ACB. lia.
      - unfold free_img_ranges, A_INSTANCE, A_IA, A_IA_INIT. cbn [in_rangesZ]. clear - Ha FSLH. lia.
      - (intros dd_H; ddestruct dd_H as (nb & Hnb & Rnb)). ddestruct (NBI nb Hnb) as (_ & _ & j & Hj). pose proof (z_node_fs h2 GEO2 j nb Hj) as Y. unfold zapart, kFakeBytes in Y. cbn [fst snd] in Y. rewrite EL2 in Y. fold L in Y. clear - Y Ha Rnb. lia.
      - (intros dd_H; ddestruct dd_H as (nb & Hnb & Rnb)). ddestruct (BLI nb Hnb) as (_ & _ & j & Hj). pose proof (z_store_fs h2 GEO2 j nb Hj) as Y. unfold zapart, kFakeBytes in Y. cbn [fst snd] in Y. rewrite EL2 in Y. fold L in Y. clear - Y Ha Rnb. lia.
      - clear - Ha ZFP. lia.
      - (intros dd_H; ddestruct dd_H as (r & Hr & Rr)). ddestruct (RPI r Hr) as (E32 & kr & ir & _ & _ & Nir & _ & BIGr & _). rewrite E32 in Rr.
        pose proof (z_sec_fs h2 GEO2 ir _ Nir) as Y. unfold zapart, kFakeBytes in Y. cbn [fst snd s_map_beg s_map_size] in Y. rewrite EL2 in Y. fold L in Y. clear - Y Ha Rr BIGr. lia. }
    (* [comment removed for export] *)
    assert (FRM : forall fb, In fb LF -> l_fs L + 36864 <= fst fb /\ fst fb + snd fb <= l_fs L + kFakeBytes /\ 64 <= snd fb).
    { intros fb Hfb. exact (frame_bounds STKLO h LB LF m HOK HM0 fb Hfb). }
    assert (SHC : forall c, shadow_of AL0 c = AW_FreeG.shad c) by (intros; reflexivity).
    (* [comment removed for export] *)
    assert (KSH_STK : forall c, STKLO <= c < l_stk_hi L -> m' (wa (AW_FreeG.shad c)) = m (wa (AW_FreeG.shad c)) /\ ~ in_qs (qs_of h2) (AW_FreeG.shad c)).
    { intros c Hc. assert (CC : ACEIL <= c) by (clear - Hc STK0 ESL; subst L; lia).
      pose proof (shad_range47 c ltac:(clear - Hc CC STKH ACB; subst L; lia)) as SB.
      split.
      - apply KB; [exact SB| |].
        + intros [[_ X] _]. pose proof (shad_le (l_b6 L + 0x2000011000) c ltac:(clear - CC B6d; lia)) as Y. clear - X Y. lia.
        + intros q Hq Rq. ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & Q8 & _ & _ & _ & QCE & _).
          pose proof (shad_le (fst q + snd q) c ltac:(clear - CC QCE; lia)) as Y. rewrite (shad_add8 (fst q) (snd q) Q8) in Y. clear - Rq Y. lia.
      - (intros dd_H; ddestruct dd_H as (q & Hq & Rq)). ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QLH & _). unfold kHighMemBeg in QLH, SB. clear - Rq QLH SB. lia. }
    (* [comment removed for export] *)
    assert (KSH_BLK : forall b c, In b (blocks h2) -> fst b <= c < fst b + snd b ->
              m' (wa (AW_FreeG.shad c)) = m (wa (AW_FreeG.shad c)) /\ ~ in_qs (qs_of h2) (AW_FreeG.shad c)).
    { intros b c Hb Rc. ddestruct (KBLK b c Hb Rc) as (_ & _ & QA). ddestruct (BKI b Hb) as (k & Hk & ST & EB & EN & X1 & X2 & X63 & XCE & _). rewrite EB, EN in Rc.
      pose proof (shad_range47 c ltac:(clear - Rc X1 X2 X63 XCE ACB; lia)) as SB.
      split.
      - apply KB; [exact SB| |].
        + intros [_ NE]. apply NE. exists c. split; [| reflexivity]. exists b. split; [exact Hb| rewrite EB, EN; exact Rc].
        + intros q Hq Rq. ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & Q8 & _). destruct (QA q Hq) as [LT|GE].
          * pose proof (shad_lt8 (fst q) c Q8 ltac:(clear - LT; lia)) as Y. clear - Rq Y. lia.
          * pose proof (shad_le (fst q + snd q) c GE) as Y. rewrite (shad_add8 (fst q) (snd q) Q8) in Y. clear - Rq Y. lia.
      - (intros dd_H; ddestruct dd_H as (q & Hq & Rq)). ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QLH & _). unfold kHighMemBeg in QLH, SB. clear - Rq QLH SB. lia. }
    (* [comment removed for export] *)
    assert (KSH_FS : forall c, l_fs L <= c < l_fs L + kFakeBytes -> m' (wa (AW_FreeG.shad c)) = m (wa (AW_FreeG.shad c)) /\ ~ in_qs (qs_of h2) (AW_FreeG.shad c)).
    { intros c Hc. ddestruct (KFS c Hc) as (_ & _ & QA). unfold kFakeBytes in Hc, FSC, FSLH.
      pose proof (shad_range47 c ltac:(clear - Hc FSC FSLH ACB; subst L; lia)) as SB.
      split.
      - apply KB; [exact SB| |].
        + intros [[R1 R2] _]. unfold kFakeBytes in ZFH. destruct ZFH as [Z1|Z2].
          * pose proof (shad_lt8 (l_b6 L) c (mod4096_8 _ B64K) ltac:(clear - Hc Z1; lia)) as Y. clear - R1 Y. lia.
          * pose proof (shad_le (l_b6 L + 0x2000011000) c ltac:(clear - Hc Z2; lia)) as Y. clear - R2 Y. lia.
        + intros q Hq Rq. ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & Q8 & _). destruct (QA q Hq) as [LT|GE].
          * pose proof (shad_lt8 (fst q) c Q8 ltac:(clear - LT; lia)) as Y. clear - Rq Y. lia.
          * pose proof (shad_le (fst q + snd q) c GE) as Y. rewrite (shad_add8 (fst q) (snd q) Q8) in Y. clear - Rq Y. lia.
      - (intros dd_H; ddestruct dd_H as (q & Hq & Rq)). ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QLH & _). unfold kHighMemBeg in QLH, SB. clear - Rq QLH SB. lia. }
    (* [comment removed for export] *)
    assert (KSH_IMG : forall c, 0x0fa360 <= c < 0x65dab0 -> m' (wa (AW_FreeG.shad c)) = m (wa (AW_FreeG.shad c)) /\ ~ in_qs (qs_of h2) (AW_FreeG.shad c)).
    { intros c Hc. assert (SW : 0x7fffa000 <= AW_FreeG.shad c < 0x800c3e00).
      { rewrite shadE. pose proof (Z.div_mod c 8 ltac:(lia)). pose proof (Z.mod_pos_bound c 8 ltac:(lia)). clear - Hc H H0. lia. }
      split; [apply KIS; exact SW|].
      (intros dd_H; ddestruct dd_H as (q & Hq & Rq)). ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QLH & _). unfold kHighMemBeg in QLH. clear - Rq QLH SW. lia. }
    (* [comment removed for export] *)
    split.
    - split.
      + intros a Ha CA _. destruct CA as [S|[C|(b & Hb & Rb)]].
        * split; [apply KS; [exact S| clear - Ha; lia]|]. intros W. apply (WMX (wa a)); [| exact W]. rewrite (wa_unsigned a Ha).
          (intros dd_H; ddestruct dd_H as (q & Hq & Rq)). ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & _ & QCE & _). clear - S Rq QCE LOL LOSP STK0 ESL. subst L. lia.
        * cbn [hl_data_lo hl_data_hi hl_static HL0 arl_L R R0] in C. destruct C as [C1 C2]. unfold RT in C2. cbn [in_rangesZ] in C2.
          split. { apply KI; [clear - C1; lia|]. unfold awz, A_INSTANCE, A_IA, A_OOM, A_IA_INIT, A_SS, A_DEP_END, A_ERRNO, AW_Populate.A_EMB. cbn [in_rangesZ]. clear - C1 C2. lia. }
          intros W. apply (WMX (wa a)); [| exact W]. rewrite (wa_unsigned a Ha).
          (intros dd_H; ddestruct dd_H as (q & Hq & Rq)). ddestruct (QSI q Hq) as (kq & _ & _ & _ & _ & _ & _ & _ & _ & Q63 & _). clear - C1 Rq Q63. lia.
        * apply in_app_iff in Hb as [Hb|Hb].
          -- ddestruct (KBLK b a Hb Rb) as (E & NQ & _). split; [exact E|]. intros W. apply (WMX (wa a)); [rewrite (wa_unsigned a Ha); exact NQ| exact W].
          -- ddestruct (fdata_sub LF (fst b) (snd b) ltac:(destruct b; exact Hb)) as (fb & [(Hfb & F1 & F2)|(Hfb & F40)]); dpose (FRM fb Hfb) as (G1 & G2 & G3); [| exfalso; clear - F40 G3; lia].
             ddestruct (KFS a ltac:(clear - Rb F1 F2 G1 G2; lia)) as (E & NQ & _). split; [exact E|]. intros W. apply (WMX (wa a)); [rewrite (wa_unsigned a Ha); exact NQ| exact W].
      + intros c Hc Hr. change (shadow_of (arl_AL R) c) with (AW_FreeG.shad c) in Hr |- *.
        assert (GOAL : forall E_NQ : m' (wa (AW_FreeG.shad c)) = m (wa (AW_FreeG.shad c)) /\ ~ in_qs (qs_of h2) (AW_FreeG.shad c),
                  m' (wa (AW_FreeG.shad c)) = m (wa (AW_FreeG.shad c)) /\ (wview asegs m (wa (AW_FreeG.shad c)) <> None -> wview asegs m' (wa (AW_FreeG.shad c)) <> None)).
        { intros [E NQ]. split; [exact E|]. intros W. apply (WMX (wa _)); [rewrite (wa_unsigned _ Hr); exact NQ| exact W]. }
        apply GOAL. destruct (cshd_cases STKLO h (blocks h2) LF c Hc) as [S|[(A & n0 & HIn & RA)|[(fb & Hfb & Rfb)|C]]].
        * exact (KSH_STK c S).
        * exact (KSH_BLK (A, n0) c HIn RA).
        * dpose (FRM fb Hfb) as (G1 & G2 & G3). exact (KSH_FS c ltac:(clear - Rfb G1 G2; lia)).
        * exact (KSH_IMG c C).
    - split.
      + intros x Hx NZ. rewrite <- (wa_unsigned_id x). apply KI; [exact Hx| exact NZ].
      + intros x Hx. rewrite <- (wa_unsigned_id x). apply KIS. exact Hx.
  Qed.
End FP.
End ARUN_1.
