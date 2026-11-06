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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_fast__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_store__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_mid.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AFreeRefillP.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeMid OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeStoreR.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
#[using="HL"] Lemma REFILL : forall Q1, refill_stmt (AHQm DI ASEC AFK Q1).
Proof. intros Q1. exact (arefillP (AHQm DI ASEC AFK Q1) (AHQm_laws DI ASEC AFK HL Q1)). Qed.

Definition afree_refillP :=
  afree_refill DI ASEC AFK HL CI CI_OK CI_OK2 (mid_kit DI ASEC AFK HL CI CI_OK) (store_freeR DI ASEC AFK HL CI CI_OK) REFILL.

#[using="HL CI_OK CI_OK2"] Theorem afree_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CPrim c n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1 st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply (afree_fastP DI ASEC AFK HL CI CI_OK); try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply (afree_fastP DI ASEC AFK HL CI CI_OK); try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
      change (enq_app st1 (CPrim c n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      eapply afree_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CPrim c n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CPrim c n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      (pose proof (enq_new_core (CPrim c n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeMid.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeStoreR.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
#[using="HL"] Lemma REFILL : forall Q1, refill_stmt (AHQm DI ASEC AFK Q1).
Proof. intros Q1. exact (arefillP (AHQm DI ASEC AFK Q1) (AHQm_laws DI ASEC AFK HL Q1)). Qed.

Definition afree_refillP :=
  afree_refill DI ASEC AFK HL CI CI_OK CI_OK2 (mid_kit DI ASEC AFK HL CI CI_OK) (store_freeR DI ASEC AFK HL CI CI_OK) REFILL.

#[using="HL CI_OK CI_OK2"] Theorem afree_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CPrim c n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1 st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply (afree_fastP DI ASEC AFK HL CI CI_OK); try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply (afree_fastP DI ASEC AFK HL CI CI_OK); try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
      change (enq_app st1 (CPrim c n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      eapply afree_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CPrim c n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CPrim c n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      (pose proof (enq_new_core (CPrim c n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.
End S.
End CANSEC1.
End TwB.
End AFreeRefillP.

(* [comment removed for export] *)
Module ADfn_refillP.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_fast__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeMid OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeStoreR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.AFreeRefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.ADfn_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfn_arepR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfn_mid.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Let REFILL := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.AFreeRefillP.REFILL DI ASEC AFK HL.

Definition dfn_fastP := dfn_fast DI ASEC AFK CI (store_free DI ASEC AFK HL CI CI_OK).
Definition dfn_refillP :=
  dfn_refill DI ASEC AFK HL CI CI_OK CI_OK2 (dfn_mid_kit DI ASEC AFK HL CI CI_OK) (store_freeR DI ASEC AFK HL CI CI_OK) REFILL.

#[using="HL CI_OK CI_OK2 REFILL"] Theorem dfn_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CPrim c n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC AFK) L RNG st LB m -> In (HB p A n) LB ->
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
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1 st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply dfn_fastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply dfn_fastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
      change (enq_app st1 (CPrim c n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      eapply dfn_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CPrim c n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CPrim c n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      (pose proof (enq_new_core (CPrim c n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeMid.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeStoreR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.AFreeRefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.ADfn_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfn_arepR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfn_mid.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Let REFILL := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.AFreeRefillP.TwB.REFILL DI ASEC AFK HL.

Definition dfn_fastP := dfn_fast DI ASEC AFK CI (store_free DI ASEC AFK HL CI CI_OK).
Definition dfn_refillP :=
  dfn_refill DI ASEC AFK HL CI CI_OK CI_OK2 (dfn_mid_kit DI ASEC AFK HL CI CI_OK) (store_freeR DI ASEC AFK HL CI CI_OK) REFILL.

#[using="HL CI_OK CI_OK2 REFILL"] Theorem dfn_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CPrim c n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC AFK) L RNG st LB m -> In (HB p A n) LB ->
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
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Proof.
  intros until c. intros LIVE N1 st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply dfn_fastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply dfn_fastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CPrim c n)) EA1) as [s Hs].
      change (enq_app st1 (CPrim c n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      eapply dfn_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CPrim c n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CPrim c n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      (pose proof (enq_new_core (CPrim c n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.
End S.
End CANSEC1.
End TwB.
End ADfn_refillP.

(* [comment removed for export] *)
Module ASF_all.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_store__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_fast__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_mid OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_storeR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ASF_big.
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

#[using="HL"] Lemma REFILLS : forall cs Q1, refill_stmt (AHSm DI AFK cs Q1).
Proof. intros cs Q1. exact (arefillP (AHSm DI AFK cs Q1) (AHSm_laws DI AFK HL cs Q1)). Qed.

Definition afree_sec_refillP :=
  afree_sec_refill DI AFK HL CI CI_OK CI_OK2 (mid_kitS DI AFK HL CI CI_OK) (store_freeRS DI AFK HL CI CI_OK) REFILLS.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2"] Theorem afree_sec_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
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
  intros until ms. intros LIVE NQM st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply (afree_sec_fastP DI AFK HL CI CI_OK); try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply (afree_sec_fastP DI AFK HL CI CI_OK); try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      eapply afree_sec_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      (pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.

(* [comment removed for export] *)
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_sec : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (n <= Q_MAX -> Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
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
  intros until ms. intros LIVE st1 st2 NOREC. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - eapply afree_sec_norecycle; try eassumption. exact (NOREC LE).
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_mid.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_storeR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ASF_big.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
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

#[using="HL"] Lemma REFILLS : forall cs Q1, refill_stmt (AHSm DI AFK cs Q1).
Proof. intros cs Q1. exact (arefillP (AHSm DI AFK cs Q1) (AHSm_laws DI AFK HL cs Q1)). Qed.

Definition afree_sec_refillP :=
  afree_sec_refill DI AFK HL CI CI_OK CI_OK2 (mid_kitS DI AFK HL CI CI_OK) (store_freeRS DI AFK HL CI CI_OK) REFILLS.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2"] Theorem afree_sec_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
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
  intros until ms. intros LIVE NQM st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply (afree_sec_fastP DI AFK HL CI CI_OK); try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply (afree_sec_fastP DI AFK HL CI CI_OK); try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      eapply afree_sec_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      (pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.

(* [comment removed for export] *)
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

#[using="HL CI_OK CI_OK2 DEPD AFKD"] Theorem afree_sec : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (n <= Q_MAX -> Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
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
  intros until ms. intros LIVE st1 st2 NOREC. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - eapply afree_sec_norecycle; try eassumption. exact (NOREC LE).
  - eapply (afree_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.
End S.
End CANSEC1.
End TwB.
End ASF_all.

(* [comment removed for export] *)
Module ADfnS_all.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_store__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_fast__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_mid. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_mid OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_storeR OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ASF_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_refill OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_mid OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_big.
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

Let REFILLS := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all.REFILLS DI AFK HL.

Definition dfn_sec_fastP := dfn_sec_fast DI AFK CI (store_freeS DI AFK HL CI CI_OK).
Definition dfn_sec_refillP :=
  dfn_sec_refill DI AFK HL CI CI_OK CI_OK2 (dfn_mid_kitS DI AFK HL CI CI_OK) (store_freeRS DI AFK HL CI CI_OK) REFILLS.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 REFILLS"] Theorem dfn_sec_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
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
  intros until ms. intros LIVE NQM st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply dfn_sec_fastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply dfn_sec_fastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      eapply dfn_sec_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      (pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.

(* [comment removed for export] *)
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

#[using="HL CI_OK CI_OK2 REFILLS DEPD AFKD"] Theorem dfn_sec : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (n <= Q_MAX -> Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
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
  intros until ms. intros LIVE st1 st2 NOREC. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - eapply dfn_sec_norecycle; try eassumption. exact (NOREC LE).
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_store.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_mid.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_store__A3W.ASF_storeR.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ASF_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_fast.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_refill.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_mid.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfnS_big.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
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

Let REFILLS := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRefillP__A3W.ASF_all.TwB.REFILLS DI AFK HL.

Definition dfn_sec_fastP := dfn_sec_fast DI AFK CI (store_freeS DI AFK HL CI CI_OK).
Definition dfn_sec_refillP :=
  dfn_sec_refill DI AFK HL CI CI_OK CI_OK2 (dfn_mid_kitS DI AFK HL CI CI_OK) (store_freeRS DI AFK HL CI CI_OK) REFILLS.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2 REFILLS"] Theorem dfn_sec_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
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
  intros until ms. intros LIVE NQM st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply dfn_sec_fastP; try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply dfn_sec_fastP; try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. (nd_pre AH 4%nat; intros _ _ [X [AR _]] _; nd_post). destruct AR as (WF & _).
        (nd_pre WF 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC K_BATCH_CLASS (K24)) 11%nat; intros _ _ _ _ _ _ _ _ _ CNTB _; nd_post). lia. }
      eapply dfn_sec_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      (pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as ndP__; nd_pre ndP__ 7%nat; intros _ G1 G2 _ _ L2 _; nd_post).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.

(* [comment removed for export] *)
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

#[using="HL CI_OK CI_OK2 REFILLS DEPD AFKD"] Theorem dfn_sec : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (n <= Q_MAX -> Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
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
  intros until ms. intros LIVE st1 st2 NOREC. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - eapply dfn_sec_norecycle; try eassumption. exact (NOREC LE).
  - eapply (dfn_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.
End S.
End CANSEC1.
End TwB.
End ADfnS_all.
