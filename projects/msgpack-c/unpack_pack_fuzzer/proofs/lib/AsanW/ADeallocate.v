(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP AFreeModel AFreeModelR AFreeRep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeRead. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.AFreeRead. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ASec F_afree_arep F_afree_arepR AFreeRefillP AFreeC_kit_iface AFreeRC_kit_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocStoreC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.AFreeStoreC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeStoreRC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeStoreRC.AFreeStoreRC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AFreeBack. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASF_kit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.ASF_kit. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AHolesD. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocFast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.AFreeRecP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocFast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.AFreeRecRP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ASF_allC F_adepot AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AInstance AInstanceM AInstanceF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ARefill_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASF_fast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_fast.ASF_fast. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocStoreC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.ASF_store. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ASF_refill. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocSF_mid. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocSF_mid.ASF_mid. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeStoreRC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeStoreRC.ASF_storeR. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASecRecycle. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecRecycle.ASF_big. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ASF_C_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASF_fastC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_fastC.ASF_fastC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocStoreC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.ASF_storeC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocFast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.ASF_refillC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeStoreRC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeStoreRC.ASF_storeRC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ASF_all AFreeAll.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ADeallocLib. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocFast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.ADeallocFast. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocSF_mid. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocSF_mid.ADeallocMid. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocFast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.ADeallocRefill. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ADeallocRefillP ADeallocC_kit_iface ADeallocC2_iface ADeallocBack. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocStoreC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.ADeallocStoreC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocStoreC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.ADeallocStoreRC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocStoreC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.ADeallocSF_storeC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeStoreRC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeStoreRC.ADeallocSF_storeRC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocFast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.ADeallocRecP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocFast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.ADeallocRecRP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASF_fast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_fast.ADeallocSF_fast. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASF_fastC. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_fastC.ADeallocSF_fastC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocSF_mid. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocSF_mid.ADeallocSF_mid. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocFast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.ADeallocSF_refill. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ADeallocFast. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.ADeallocSF_refillC. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASecRecycle. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecRecycle.ADeallocSF_big.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC2. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Definition adeallocate_stmt (CI : list (Z * Z)) (AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z),
  AHEAP L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xd6730 \/ 0xd67f0 <= fst iv)
                                  /\ (snd iv <= 0xdacc0 \/ 0x15bcf0 <= fst iv)
                                  /\ (snd iv <= 0x169548 \/ 0x16954c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition adealloc_sec_fastP := adealloc_sec_fast DI AFK CI (store_freeS DI AFK HL CI CI_OK).
Definition adealloc_sec_refillP :=
  adealloc_sec_refill DI AFK HL CI CI_OK CI_OK2 (mid_kitS_D DI AFK HL CI CI_OK) (store_freeRS DI AFK HL CI CI_OK) (REFILLS DI AFK HL).

Theorem adealloc_sec_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->

  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply adealloc_sec_fastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply adealloc_sec_fastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
        destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
      eapply adealloc_sec_refillP; try eassumption.

      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as (_ & G1 & G2 & _ & _ & L2 & _).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.

Definition adealloc_sec_recfastP :=
  adealloc_sec_recfast DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeSC_D DI AFK HL CI CI_OK) (afree_back_D DI AFK CI).
Definition adealloc_sec_recrefillP :=
  adealloc_sec_recrefill DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (mid_kitS_D DI AFK HL CI CI_OK) (store_freeSRC_D DI AFK HL CI CI_OK)
                         (REFILLS DI AFK HL) (afree_back_D DI AFK CI).

Theorem adealloc_sec_recycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 QC1 REC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply adealloc_sec_recfastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply adealloc_sec_recfastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
        destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as (_ & G1 & G2 & _ & _ & L2 & _).
      subst st2 st1. unfold st_enq in QC1, REC. rewrite EAPP in QC1, REC. rewrite L2 in QC1. rewrite G2, L2 in REC. cbn [chunk_size] in QC1, REC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in QC1, REC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in REC.
      eapply adealloc_sec_recrefillP; try eassumption.
      * unfold Q_BATCH_BYTES in QC1. generalize QC1; clear; intros; lia.
      * unfold Q_BATCH_BYTES in QC1, REC. generalize REC; clear; intros; lia.
Qed.

Theorem adealloc_sec_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).
Proof.
  intros until ms. intros LIVE. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - set (st2 := st_enq (set_live (delete p (a_live st)) st) (CSec mb ms n)).
    destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|NQC].
    + destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NREC].
      * eapply adealloc_sec_recycle; try eassumption.
      * eapply adealloc_sec_norecycle; try eassumption. intros _. exact NREC.
    + eapply adealloc_sec_norecycle; try eassumption. intros QC'. exfalso. subst st2. generalize QC' NQC; clear; intros; lia.
  - eapply (adealloc_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.

Definition adealloc_recPP :=
  adealloc_recP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeC_D DI AFK HL CI CI_OK) (afree_back_D DI AFK CI).
Definition adealloc_recRPP :=
  adealloc_recRP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeRC_D DI AFK HL CI CI_OK) (afree_back_D DI AFK CI).

Theorem adealloc_prim_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (c : Z),
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd6458 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3c9b4) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1. intros.
  set (st1 := set_live (delete p (a_live st)) st).
  set (st2 := st_enq st1 (CPrim c n)).
  destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|QC0];
    [destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NR]|].
  -
    destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
    + eapply adealloc_recPP; try eassumption. intros _. exact POS.
    + destruct (enq_is_app st) eqn:EA.
      * eapply adealloc_recPP; try eassumption. intros E. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
        change (enq_app st1 (CPrim c n) = None) in E. congruence.
      * assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
        { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
          destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
        eapply adealloc_recRPP; try eassumption.
  -
    eapply (adealloc_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
  -
    eapply (adealloc_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros LT. exfalso. subst st2 st1. lia.
Qed.

Theorem adeallocate_total : adeallocate_stmt CI (AHEAP_P (AHQ DI ASEC_of AFK)).
Proof.
  unfold adeallocate_stmt. intros until trt. intros AH HIN. intros.
  pose proof AH as AH0. destruct AH0 as (ALO & ARNG & [X [AR BL]] & HFK).
  destruct (proj1 BL p A n HIN) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & _)].
  - pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
    destruct (BUSY b Hb) as [CLb M]. rewrite Sb in M. destruct M as (Nb1 & _ & _ & _ & _ & LIVE). rewrite Nb in Nb1, LIVE.
    eapply adealloc_prim_total with (c := xb_class b); try eassumption. lia.
  - eapply adealloc_sec_total; eassumption.
Qed.
End S.

Theorem AHI_dealloc : adeallocate_stmt aci_I (AHEAP_P AHI).
Proof.
  exact (adeallocate_total adepot_iface AFAKE AH_laws aci_I aci_okQ aci_ok2
           ltac:(cbn [ADEPOT adepot_iface]; exact adepot_frameD) afake_frameD).
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ABytes.TwinB AQConst.TwinB AKitQ.TwinB AMalloc_iface.TwinB ADepot_iface.TwinB ARep.TwinB ARepQ.TwinB ARepQP.TwinB ALayout.TwinB AHeapP.TwinB AFreeModel.TwinB AFreeModelR.TwinB AFreeRep.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.TwinB.AFreeRead. Import ASec.TwinB F_afree_arep.TwinB F_afree_arepR.TwinB AFreeRefillP.TwinB AFreeC_kit_iface.TwinB AFreeRC_kit_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.TwinB.AFreeStoreC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeStoreRC.TwinB.AFreeStoreRC. Import AFreeBack.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.TwinB.ASF_kit. Import AHolesD.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.TwinB.AFreeRecP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.TwinB.AFreeRecRP. Import ASF_allC.TwinB F_adepot.TwinB AFake_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep. Import AInstance.TwinB AInstanceM.TwinB AInstanceF.TwinB.
Import ARefill_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_fast.TwinB.ASF_fast.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.TwinB.ASF_store. Import ASF_refill.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocSF_mid.TwinB.ASF_mid.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeStoreRC.TwinB.ASF_storeR.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecRecycle.TwinB.ASF_big. Import ASF_C_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_fastC.TwinB.ASF_fastC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.TwinB.ASF_storeC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.TwinB.ASF_refillC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeStoreRC.TwinB.ASF_storeRC. Import ASF_all.TwinB AFreeAll.TwinB.
Import ADeallocLib.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.TwinB.ADeallocFast.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocSF_mid.TwinB.ADeallocMid.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.TwinB.ADeallocRefill. Import ADeallocRefillP.TwinB ADeallocC_kit_iface.TwinB ADeallocC2_iface.TwinB ADeallocBack.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.TwinB.ADeallocStoreC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.TwinB.ADeallocStoreRC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocStoreC.TwinB.ADeallocSF_storeC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeStoreRC.TwinB.ADeallocSF_storeRC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.TwinB.ADeallocRecP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.TwinB.ADeallocRecRP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_fast.TwinB.ADeallocSF_fast.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_fastC.TwinB.ADeallocSF_fastC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocSF_mid.TwinB.ADeallocSF_mid.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.TwinB.ADeallocSF_refill.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADeallocFast.TwinB.ADeallocSF_refillC.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecRecycle.TwinB.ADeallocSF_big.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC2. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.
Definition adeallocate_stmt (CI : list (Z * Z)) (AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z),
  AHEAP L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells bsegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xd88f0 \/ 0xd89b0 <= fst iv)
                                  /\ (snd iv <= 0xdce80 \/ 0x15deb0 <= fst iv)
                                  /\ (snd iv <= 0x16b708 \/ 0x16b70c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Definition adealloc_sec_fastP := adealloc_sec_fast DI AFK CI (store_freeS DI AFK HL CI CI_OK).
Definition adealloc_sec_refillP :=
  adealloc_sec_refill DI AFK HL CI CI_OK CI_OK2 (mid_kitS_D DI AFK HL CI CI_OK) (store_freeRS DI AFK HL CI CI_OK) (REFILLS DI AFK HL).

Theorem adealloc_sec_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->

  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells bsegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply adealloc_sec_fastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply adealloc_sec_fastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
        destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
      eapply adealloc_sec_refillP; try eassumption.

      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as (_ & G1 & G2 & _ & _ & L2 & _).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.

Definition adealloc_sec_recfastP :=
  adealloc_sec_recfast DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeSC_D DI AFK HL CI CI_OK) (afree_back_D DI AFK CI).
Definition adealloc_sec_recrefillP :=
  adealloc_sec_recrefill DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (mid_kitS_D DI AFK HL CI CI_OK) (store_freeSRC_D DI AFK HL CI CI_OK)
                         (REFILLS DI AFK HL) (afree_back_D DI AFK CI).

Theorem adealloc_sec_recycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells bsegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 QC1 REC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply adealloc_sec_recfastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply adealloc_sec_recfastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
        destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as (_ & G1 & G2 & _ & _ & L2 & _).
      subst st2 st1. unfold st_enq in QC1, REC. rewrite EAPP in QC1, REC. rewrite L2 in QC1. rewrite G2, L2 in REC. cbn [chunk_size] in QC1, REC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in QC1, REC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in REC.
      eapply adealloc_sec_recrefillP; try eassumption.
      * unfold Q_BATCH_BYTES in QC1. generalize QC1; clear; intros; lia.
      * unfold Q_BATCH_BYTES in QC1, REC. generalize REC; clear; intros; lia.
Qed.

Theorem adealloc_sec_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells bsegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  4096 <= bv_unsigned ra ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - set (st2 := st_enq (set_live (delete p (a_live st)) st) (CSec mb ms n)).
    destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|NQC].
    + destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NREC].
      * eapply adealloc_sec_recycle; try eassumption.
      * eapply adealloc_sec_norecycle; try eassumption. intros _. exact NREC.
    + eapply adealloc_sec_norecycle; try eassumption. intros QC'. exfalso. subst st2. generalize QC' NQC; clear; intros; lia.
  - eapply (adealloc_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.

Definition adealloc_recPP :=
  adealloc_recP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeC_D DI AFK HL CI CI_OK) (afree_back_D DI AFK CI).
Definition adealloc_recRPP :=
  adealloc_recRP DI AFK HL CI CI_OK CI_OK2 DEPD AFKD (store_freeRC_D DI AFK HL CI CI_OK) (afree_back_D DI AFK CI).

Theorem adealloc_prim_total : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (tb2 : list word) (trt : list Z) (c : Z),
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 0xd8618 -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 0 -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 SO -> a5 = Z_to_bv 64 1 ->

  rw_cells bsegs m SO [C8 (Z_to_bv 64 (SO + 16)); C4 (Z_to_bv 64 (1 + Z.of_nat (length trt))); C4 (Z_to_bv 64 0)] ->
  u64arr bsegs m (SO + 16) tb2 -> length tb2 = 255%nat -> (length trt <= 29)%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trt)) tb2) = pc :: trt -> In (pc :: trt) (al_U L) ->
  bv_unsigned sp <= SO -> SO + 2056 <= 2^47 -> rng RNG SO 2056 ->

  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3d344) fc None m (seg_rom bsegs)).
Proof.
  intros until c. intros LIVE N1. intros.
  set (st1 := set_live (delete p (a_live st)) st).
  set (st2 := st_enq st1 (CPrim c n)).
  destruct (Z.lt_ge_cases Q_CACHE (a_qloc_bytes st2)) as [QC1|QC0];
    [destruct (Z.lt_ge_cases Q_MAX (a_qglob_bytes st2 + a_qloc_bytes st2)) as [REC|NR]|].
  -
    destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
    + eapply adealloc_recPP; try eassumption. intros _. exact POS.
    + destruct (enq_is_app st) eqn:EA.
      * eapply adealloc_recPP; try eassumption. intros E. exfalso.
        assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
        change (enq_app st1 (CPrim c n) = None) in E. congruence.
      * assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
        { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
          destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
        eapply adealloc_recRPP; try eassumption.
  -
    eapply (adealloc_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros _. exact NR.
  -
    eapply (adealloc_norecycle DI ASEC_of AFK HL CI CI_OK CI_OK2); try eassumption. intros LT. exfalso. subst st2 st1. lia.
Qed.

Theorem adeallocate_total : adeallocate_stmt CI (AHEAP_P (AHQ DI ASEC_of AFK)).
Proof.
  unfold adeallocate_stmt. intros until trt. intros AH HIN. intros.
  pose proof AH as AH0. destruct AH0 as (ALO & ARNG & [X [AR BL]] & HFK).
  destruct (proj1 BL p A n HIN) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & _)].
  - pose proof AR as AR0. destruct AR0 as (WF & _). pose proof WF as WF0. destruct WF0 as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
    destruct (BUSY b Hb) as [CLb M]. rewrite Sb in M. destruct M as (Nb1 & _ & _ & _ & _ & LIVE). rewrite Nb in Nb1, LIVE.
    eapply adealloc_prim_total with (c := xb_class b); try eassumption. lia.
  - eapply adealloc_sec_total; eassumption.
Qed.
End S.

Theorem AHI_dealloc : adeallocate_stmt aci_I (AHEAP_P AHI).
Proof.
  exact (adeallocate_total adepot_iface AFAKE AH_laws aci_I aci_okQ aci_ok2
           ltac:(cbn [ADEPOT adepot_iface]; exact adepot_frameD) afake_frameD).
Qed.
End CANSEC2.
End TwinB.
