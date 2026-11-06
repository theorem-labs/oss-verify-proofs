(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_store__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_fast__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRefillP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQrecP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_storeC__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_recP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_storeC__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_storeRC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_mid.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHolesD.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ADfnS_allC.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_store__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRefillP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQrecP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_storeC__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_recP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_storeC__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_storeRC. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_mid. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_mid OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_storeR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ASF_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ASF_C_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_storeC__A3W.ASF_storeC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_storeC__A3W.ASF_storeRC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ASF_fastC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ASF_refillC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnS_C_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfn_back OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_storeC__A3W.ADfnS_storeC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_storeRC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_refill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_mid OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ADfnS_fastC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ADfnS_refillC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ADfnS_all.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition dfn_sec_recfastP :=
  dfn_sec_recfast DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (dfn_store_freeSC DI AFK HL CI CI_OK) (dfn_back DI AFK CI).
Definition dfn_sec_recrefillP :=
  dfn_sec_recrefill DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (dfn_mid_kitS DI AFK HL CI CI_OK) (dfn_store_freeSRC DI AFK HL CI CI_OK)
                      (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all.REFILLS DI AFK HL) (dfn_back DI AFK CI).

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem dfn_sec_recycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 QC1 REC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply dfn_sec_recfastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply dfn_sec_recfastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      (pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      subst st2 st1. unfold st_enq in QC1, REC. rewrite EAPP in QC1, REC. rewrite L2 in QC1. rewrite G2, L2 in REC. cbn [chunk_size] in QC1, REC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in QC1, REC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in REC.
      eapply dfn_sec_recrefillP; try eassumption.
      * unfold Q_BATCH_BYTES in QC1. generalize QC1; clear; intros; lia.
      * unfold Q_BATCH_BYTES in QC1, REC. generalize REC; clear; intros; lia.
Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem dfn_sec_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  4096 <= bv_unsigned ra ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - set (st2 := st_enq (set_live (delete p (a_live st)) st) (CSec mb ms n)).
    destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|NQC].
    + destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NREC].
      * eapply dfn_sec_recycle; try eassumption.
      * eapply (dfn_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NREC.
    + eapply (dfn_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros QC'. exfalso. subst st2. generalize QC' NQC; clear; intros; lia.
  - eapply (dfn_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_mid.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_storeR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ASF_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ASF_C_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_storeC__A3W.ASF_storeC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_storeC__A3W.ASF_storeRC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ASF_fastC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ASF_refillC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnS_C_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfn_back.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_storeC__A3W.ADfnS_storeC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_storeRC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_refill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_mid.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ADfnS_fastC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ADfnS_refillC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ADfnS_all.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition dfn_sec_recfastP :=
  dfn_sec_recfast DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (dfn_store_freeSC DI AFK HL CI CI_OK) (dfn_back DI AFK CI).
Definition dfn_sec_recrefillP :=
  dfn_sec_recrefill DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (dfn_mid_kitS DI AFK HL CI CI_OK) (dfn_store_freeSRC DI AFK HL CI CI_OK)
                      (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all.TwB.REFILLS DI AFK HL) (dfn_back DI AFK CI).

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem dfn_sec_recycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 QC1 REC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply dfn_sec_recfastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply dfn_sec_recfastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      (pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      subst st2 st1. unfold st_enq in QC1, REC. rewrite EAPP in QC1, REC. rewrite L2 in QC1. rewrite G2, L2 in REC. cbn [chunk_size] in QC1, REC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in QC1, REC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in REC.
      eapply dfn_sec_recrefillP; try eassumption.
      * unfold Q_BATCH_BYTES in QC1. generalize QC1; clear; intros; lia.
      * unfold Q_BATCH_BYTES in QC1, REC. generalize REC; clear; intros; lia.
Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem dfn_sec_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  4096 <= bv_unsigned ra ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - set (st2 := st_enq (set_live (delete p (a_live st)) st) (CSec mb ms n)).
    destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|NQC].
    + destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NREC].
      * eapply dfn_sec_recycle; try eassumption.
      * eapply (dfn_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NREC.
    + eapply (dfn_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros QC'. exfalso. subst st2. generalize QC' NQC; clear; intros; lia.
  - eapply (dfn_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.
End S.
End CANSEC1.
End TwB.
End ADfnS_allC.

(* [comment removed for export] *)
Module ASF_allC.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_store__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRefillP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQrecP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_storeC__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_recP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_mid OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_storeR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ASF_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ASF_C_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_storeC__A3W.ASF_storeC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_storeC__A3W.ASF_storeRC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ASF_fastC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ASF_refillC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition afree_sec_recfastP :=
  afree_sec_recfast DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeSC DI AFK HL CI CI_OK) (afree_back DI AFK CI).
Definition afree_sec_recrefillP :=
  afree_sec_recrefill DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (mid_kitS DI AFK HL CI CI_OK) (store_freeSRC DI AFK HL CI CI_OK)
                      (REFILLS DI AFK HL) (afree_back DI AFK CI).

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_sec_recycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 QC1 REC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply afree_sec_recfastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply afree_sec_recfastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      (pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      subst st2 st1. unfold st_enq in QC1, REC. rewrite EAPP in QC1, REC. rewrite L2 in QC1. rewrite G2, L2 in REC. cbn [chunk_size] in QC1, REC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in QC1, REC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in REC.
      eapply afree_sec_recrefillP; try eassumption.
      * unfold Q_BATCH_BYTES in QC1. generalize QC1; clear; intros; lia.
      * unfold Q_BATCH_BYTES in QC1, REC. generalize REC; clear; intros; lia.
Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_sec_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - set (st2 := st_enq (set_live (delete p (a_live st)) st) (CSec mb ms n)).
    destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|NQC].
    + destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NREC].
      * eapply afree_sec_recycle; try eassumption.
      * eapply (afree_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NREC.
    + eapply (afree_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros QC'. exfalso. subst st2. generalize QC' NQC; clear; intros; lia.
  - eapply (afree_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_mid.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_storeR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ASF_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ASF_C_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_storeC__A3W.ASF_storeC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_storeC__A3W.ASF_storeRC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ASF_fastC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ASF_refillC.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition afree_sec_recfastP :=
  afree_sec_recfast DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeSC DI AFK HL CI CI_OK) (afree_back DI AFK CI).
Definition afree_sec_recrefillP :=
  afree_sec_recrefill DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (mid_kitS DI AFK HL CI CI_OK) (store_freeSRC DI AFK HL CI CI_OK)
                      (REFILLS DI AFK HL) (afree_back DI AFK CI).

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_sec_recycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 QC1 REC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply afree_sec_recfastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply afree_sec_recfastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      (pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      subst st2 st1. unfold st_enq in QC1, REC. rewrite EAPP in QC1, REC. rewrite L2 in QC1. rewrite G2, L2 in REC. cbn [chunk_size] in QC1, REC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in QC1, REC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in REC.
      eapply afree_sec_recrefillP; try eassumption.
      * unfold Q_BATCH_BYTES in QC1. generalize QC1; clear; intros; lia.
      * unfold Q_BATCH_BYTES in QC1, REC. generalize REC; clear; intros; lia.
Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_sec_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - set (st2 := st_enq (set_live (delete p (a_live st)) st) (CSec mb ms n)).
    destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|NQC].
    + destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NREC].
      * eapply afree_sec_recycle; try eassumption.
      * eapply (afree_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NREC.
    + eapply (afree_sec_norecycle DI AFK HL CI CI_OK CI_OK2); try eassumption. intros QC'. exfalso. subst st2. generalize QC' NQC; clear; intros; lia.
  - eapply (afree_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.
End S.
End CANSEC1.
End TwB.
End ASF_allC.

(* [comment removed for export] *)
Module ADeallocFn.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRefillP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQrecP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHolesD. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_recP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_storeC__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.AFreeRefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeRC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreRC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.AFreeRecP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.AFreeRecRP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.ASF_allC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnRC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfn_back OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_storeC__A3W.ADfn_storeC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_storeC__A3W.ADfn_storeRC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ADfn_refillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ADfn_recP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ADfn_recRP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.ADfnS_allC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition dfn_recPP :=
  dfn_recP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (dfn_store_freeC DI AFK HL CI CI_OK) (dfn_back DI AFK CI).
Definition dfn_recRPP :=
  dfn_recRP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (dfn_store_freeRC DI AFK HL CI CI_OK) (dfn_back DI AFK CI).

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem dfn_prim_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (c : Z),
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  rw_cells asegs m 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1. intros.
  set (st1 := set_live (delete p (a_live st)) st).
  set (st2 := st_enq st1 (CPrim c n)).
  destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|QC0];
    [destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NR]|].
  - (* [comment removed for export] *)
    destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
    + eapply dfn_recPP; try eassumption. intros _. exact POS.
    + destruct (enq_is_app st) eqn:EA.
      * eapply dfn_recPP; try eassumption. intros E. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
        change (enq_app st1 (CPrim c n) = None) in E. congruence.
      * assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
        { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
          (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
        eapply dfn_recRPP; try eassumption.
  - (* [comment removed for export] *)
    eapply (dfn_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
  - (* [comment removed for export] *)
    eapply (dfn_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros LT. exfalso. subst st2 st1. lia.
Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem deallocfn_total : deallocfn_stmt CI (AHEAP_P (AHQ DI ASEC_of AFK)).
Proof.
  unfold deallocfn_stmt. intros until tb. intros AH HIN. intros.
  pose proof AH as AH0. (nd_pre AH0 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  destruct (proj1 BL p A n HIN) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & _)].
  - pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. (nd_pre WF0 9%nat; intros _ _ _ _ _ _ _ BUSY _; nd_post).
    destruct (BUSY b Hb) as [CLb M]. rewrite Sb in M. (nd_pre M 6%nat; intros Nb1 _ _ _ _ LIVE; nd_post). rewrite Nb in Nb1, LIVE.
    eapply dfn_prim_total with (c := xb_class b); try eassumption. lia.
  - eapply (dfn_sec_total DI AFK HL CI CI_OK CI_OK2 DEPD AFKD); eassumption.
Qed.
End S.

End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.AFreeRefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeRC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreRC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.AFreeRecP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.AFreeRecRP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.ASF_allC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfnRC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.ADfn_back.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_storeC__A3W.ADfn_storeC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_storeC__A3W.ADfn_storeRC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ADfn_refillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ADfn_recP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.ADfn_recRP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.ADfnS_allC.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition dfn_recPP :=
  dfn_recP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (dfn_store_freeC DI AFK HL CI CI_OK) (dfn_back DI AFK CI).
Definition dfn_recRPP :=
  dfn_recRP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (dfn_store_freeRC DI AFK HL CI CI_OK) (dfn_back DI AFK CI).

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem dfn_prim_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (c : Z),
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->
  rw_cells asegs m 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb) = pc :: trt ->
  In (pc :: trt) (al_U L) -> (length trt <= 29)%nat ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG SO 2056 ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1. intros.
  set (st1 := set_live (delete p (a_live st)) st).
  set (st2 := st_enq st1 (CPrim c n)).
  destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|QC0];
    [destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NR]|].
  - (* [comment removed for export] *)
    destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
    + eapply dfn_recPP; try eassumption. intros _. exact POS.
    + destruct (enq_is_app st) eqn:EA.
      * eapply dfn_recPP; try eassumption. intros E. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
        change (enq_app st1 (CPrim c n) = None) in E. congruence.
      * assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
        { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
          (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
        eapply dfn_recRPP; try eassumption.
  - (* [comment removed for export] *)
    eapply (dfn_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
  - (* [comment removed for export] *)
    eapply (dfn_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros LT. exfalso. subst st2 st1. lia.
Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem deallocfn_total : deallocfn_stmt CI (AHEAP_P (AHQ DI ASEC_of AFK)).
Proof.
  unfold deallocfn_stmt. intros until tb. intros AH HIN. intros.
  pose proof AH as AH0. (nd_pre AH0 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  destruct (proj1 BL p A n HIN) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & _)].
  - pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. (nd_pre WF0 9%nat; intros _ _ _ _ _ _ _ BUSY _; nd_post).
    destruct (BUSY b Hb) as [CLb M]. rewrite Sb in M. (nd_pre M 6%nat; intros Nb1 _ _ _ _ LIVE; nd_post). rewrite Nb in Nb1, LIVE.
    eapply dfn_prim_total with (c := xb_class b); try eassumption. lia.
  - eapply (dfn_sec_total DI AFK HL CI CI_OK CI_OK2 DEPD AFKD); eassumption.
Qed.
End S.

End CANSEC1.
End TwB.
End ADeallocFn.

(* [comment removed for export] *)
Module AFreeAll.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRefillP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQrecP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHolesD. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_recP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.AFreeRefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeRC_kit_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreRC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.AFreeRecP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.AFreeRecRP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.ASF_allC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition afree_recPP :=
  afree_recP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeC DI AFK HL CI CI_OK) (afree_back DI AFK CI).
Definition afree_recRPP :=
  afree_recRP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeRC DI AFK HL CI CI_OK) (afree_back DI AFK CI).

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_prim_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1. intros.
  set (st1 := set_live (delete p (a_live st)) st).
  set (st2 := st_enq st1 (CPrim c n)).
  destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|QC0];
    [destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NR]|].
  - (* [comment removed for export] *)
    destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
    + eapply afree_recPP; try eassumption. intros _. exact POS.
    + destruct (enq_is_app st) eqn:EA.
      * eapply afree_recPP; try eassumption. intros E. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
        change (enq_app st1 (CPrim c n) = None) in E. congruence.
      * assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
        { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
          (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
        eapply afree_recRPP; try eassumption.
  - (* [comment removed for export] *)
    eapply (afree_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
  - (* [comment removed for export] *)
    eapply (afree_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros LT. exfalso. subst st2 st1. lia.
Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_total : afree_stmt CI (AHEAP_P (AHQ DI ASEC_of AFK)).
Proof.
  unfold afree_stmt. intros until tr. intros AH HIN. intros.
  pose proof AH as AH0. (nd_pre AH0 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  destruct (proj1 BL p A n HIN) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & _)].
  - pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. (nd_pre WF0 9%nat; intros _ _ _ _ _ _ _ BUSY _; nd_post).
    destruct (BUSY b Hb) as [CLb M]. rewrite Sb in M. (nd_pre M 6%nat; intros Nb1 _ _ _ _ LIVE; nd_post). rewrite Nb in Nb1, LIVE.
    eapply afree_prim_total with (c := xb_class b); try eassumption. lia.
  - eapply (afree_sec_total DI AFK HL CI CI_OK CI_OK2 DEPD AFKD); eassumption.
Qed.
End S.

(* [comment removed for export] *)
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.AFreeRefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeRC_kit_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeStoreRC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQrecP__A3W.AFreeBack.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.AFreeRecP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_recP__A3W.AFreeRecRP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.ASF_allC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition afree_recPP :=
  afree_recP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeC DI AFK HL CI CI_OK) (afree_back DI AFK CI).
Definition afree_recRPP :=
  afree_recRP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeRC DI AFK HL CI CI_OK) (afree_back DI AFK CI).

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_prim_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1. intros.
  set (st1 := set_live (delete p (a_live st)) st).
  set (st2 := st_enq st1 (CPrim c n)).
  destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|QC0];
    [destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NR]|].
  - (* [comment removed for export] *)
    destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
    + eapply afree_recPP; try eassumption. intros _. exact POS.
    + destruct (enq_is_app st) eqn:EA.
      * eapply afree_recPP; try eassumption. intros E. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
        change (enq_app st1 (CPrim c n) = None) in E. congruence.
      * assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
        { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
          (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
        eapply afree_recRPP; try eassumption.
  - (* [comment removed for export] *)
    eapply (afree_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
  - (* [comment removed for export] *)
    eapply (afree_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros LT. exfalso. subst st2 st1. lia.
Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_total : afree_stmt CI (AHEAP_P (AHQ DI ASEC_of AFK)).
Proof.
  unfold afree_stmt. intros until tr. intros AH HIN. intros.
  pose proof AH as AH0. (nd_pre AH0 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  destruct (proj1 BL p A n HIN) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & _)].
  - pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. (nd_pre WF0 9%nat; intros _ _ _ _ _ _ _ BUSY _; nd_post).
    destruct (BUSY b Hb) as [CLb M]. rewrite Sb in M. (nd_pre M 6%nat; intros Nb1 _ _ _ _ LIVE; nd_post). rewrite Nb in Nb1, LIVE.
    eapply afree_prim_total with (c := xb_class b); try eassumption. lia.
  - eapply (afree_sec_total DI AFK HL CI CI_OK CI_OK2 DEPD AFKD); eassumption.
Qed.
End S.

(* [comment removed for export] *)
End CANSEC1.
End TwB.
End AFreeAll.
