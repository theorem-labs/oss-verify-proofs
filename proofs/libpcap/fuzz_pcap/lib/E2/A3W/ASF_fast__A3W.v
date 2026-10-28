(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_read.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ASF_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_read. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_freeS_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m ->
  dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms',
    free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                   (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms' ->
    afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m (st_after st2) RNG ms'.
Hypothesis STORE : store_freeS_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_sec_fast__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (enq_app st1 (CSec mb ms n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) ->
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 42).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 43).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 44).
Let hm := mb + 6128.
#[using="STORE hm"] Lemma afree_sec_fast__body : ltac:(let T := type of (fun (h : afree_sec_fast__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (tr, (mb, ms))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NQM st1 st2 CNT NOREC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EA _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_s SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahmx; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 B1 B3 CX HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  chg (mb + 6128) hm.
  (* [comment removed for export] *)
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_space L ALO) as RSP.
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  (pose proof (rup8_facts n ltac:(lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad (hm + 16) = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8)).
  { subst hm. rewrite !shad_div, RUPS. (pose proof (sec_facts n ltac:(lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post). clear -MAL RUP RUP8 RS1 NSE NMS N6 NB. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 3%nat; intros SHE SHL SHP; nd_post).
  (* [comment removed for export] *)
  assert (HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> hm + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= hm).
  { intros kk KK. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ _ _ _ PERC _; nd_post).
    (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post).
    (pose proof (slot_in_region L st K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1) KK) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 _; nd_post).
    rewrite size_of_class_24 in P4. subst hm. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1 Q2 RSP SC_s MSB. lia. }
  assert (HM0' : ablk hm (hm + 24)) by (subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB; lia]).   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CHc & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m _ CS8) as [stj STS].
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  assert (EKX : exists k24 chunks, let ek := ek_of L st X Q n k24 stj chunks in
       ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m
    /\ ek_seps ek L hm (qlast L (q_loc Q))
    /\ 0 <= ek_delta ek n /\ a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st
    /\ (ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
        \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q)))
    /\ (enq_is_app st = false ->
          nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
       /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
       /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
       /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
       /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS))).
  { pose proof (st_enq_bytes st p (CSec mb ms n) L X Q) as SB.
    destruct (enq_is_app st) eqn:EAPP.
    - (nd_pre (read_ek_appS (AHQ DI ASEC_of AFK) L st X Q m RNG hm n ALO ARNG AR AQ NQM HMSEP stj [] 0 EAPP
                (Z_to_bv 64 0) (Z_to_bv 64 0) 0 CR STS) 5%nat; intros EK ES ED EB _; nd_post).
      specialize (SB 0 stj [] ltac:(intros E; exfalso; change (enq_app st1 (CSec mb ms n) = None) in E; assert (EA1 : enq_is_app st1 = true) by exact EAPP;
                    destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs]; congruence)).
      cbn [chunk_size] in SB. (nd_pre SB 3%nat; intros SB1 SB2 _; nd_post).
      exists 0, []. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [left; exact EB|]. intros; discriminate.
    - assert (POS : 0 < c_count (get_cls st K_BATCH_CLASS)).
      { apply CNT. destruct (enq_app st1 (CSec mb ms n)) eqn:E; [| reflexivity]. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CSec mb ms n))); eexists; exact E).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      (nd_pre (read_ek_newS (AHQ DI ASEC_of AFK) L st X Q m RNG hm n ALO ARNG AR AQ HM0' HMSEP stj EAPP POS STS) 14%nat; intros k24 chunks EK ES ED EB NK NBk KK NIB JKb FSH CIN _; nd_post).
      specialize (SB k24 stj chunks ltac:(intros _; exact POS)). cbn [chunk_size] in SB. (nd_pre SB 3%nat; intros SB1 SB2 _; nd_post).
      exists k24, chunks. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [right; exists k24; split; [exact EB|]; split; [exact KK| exact NIB]|].
      intros _. repeat (split; [assumption|]). exact POS. }
  (nd_pre EKX 3%nat; intros k24 chunks EKX; nd_post). cbv zeta in EKX. (nd_pre EKX 7%nat; intros EK ES ED0 SB1 SB2 EBB NEWF; nd_post).
  set (ek := ek_of L st X Q n k24 stj chunks) in *.
  (* [comment removed for export] *)
  (nd_pre (read_dkS (AHQ DI ASEC_of AFK) L st X Q m RNG hm ALO ARNG AR AQ HMSEP (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek ED0 EBB
              ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros DK DS GL GLST; nd_post).
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  rewrite (afree_fast_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT NOREC).
  apply implS_ret.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. (pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 3%nat; intros B0 B1' _; nd_post). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (LL64 : 0 <= qlast L (q_loc Q) < 2^64).
  { destruct (qlast_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (DELTA : ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  assert (IN : In (CSec mb ms n) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
  pose proof (proj1 (Forall_forall _ _) RSECS _ IN) as [RMB RSH]. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  eapply evtF_mono.
  { eapply (free_fast_spec DI L (q_ia Q) ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) uw sj (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EA; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | subst hm; clear -SC_t MSB; lia | subst hm; clear -SC_c MSB; lia | subst hm; clear -SC_n MSB; lia | subst hm; clear -SC_st MSB; lia]
         | |- rng _ (shad _) _ => rewrite SHE; eapply rng_sub; [exact RSH| clear; lia| clear -SHL; lia]
         | |- rng _ _ 24 => subst hm; eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => subst hm; unfold tclr; clear -SC_tls MSB; lia
         end.
    all: try assumption.
    all: subst hm; unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize NB N6 NMS NQM MLO ML1 ML3 MCE MAL MSAL RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B1 CX LLB NC NM LF64 LL64 ED0 DELTA RA4 RUP; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms' PM.
  (* [comment removed for export] *)
  eapply (STORE L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 cx A lo k24 stj chunks).
  all: try lazymatch goal with
       | |- free_fast_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact PM
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => exact ARNG
       | |- AREP _ _ _ _ _ => exact AR
       | |- AQUAR_at _ _ _ _ _ => exact AQ
       | |- ablocks _ _ _ _ => exact BL
       | |- In _ _ => exact HIN
       | |- _ !! _ = _ => exact LIVE
       | |- _ = false -> _ => exact NEWF
       | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
       | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
       | |- rw_cells _ _ _ _ => exact H5
       end.
  all: try assumption.
  all: try (generalize NQM LO BOT STK3; clear; intros; unfold AFREE_STACK, Q_MAX in *; lia).
  all: match goal with |- ?G => idtac "REMS" G end.
Qed.
End Zd1.
#[using="STORE"] Theorem afree_sec_fast : ltac:(let t := eval cbv delta [afree_sec_fast__stmt] in afree_sec_fast__stmt in exact t).
Proof. exact afree_sec_fast__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB. Local Ltac Zify.zify_pre_hook ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition store_freeS_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m ->
  dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms',
    free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                   (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms' ->
    afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m (st_after st2) RNG ms'.
Hypothesis STORE : store_freeS_stmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_sec_fast__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (enq_app st1 (CSec mb ms n) = None -> 0 < c_count (get_cls st K_BATCH_CLASS)) ->
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 42).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 43).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'afree_sec_fast__stmt 44).
Let hm := mb + 6128.
#[using="STORE hm"] Lemma afree_sec_fast__body : ltac:(let T := type of (fun (h : afree_sec_fast__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (tr, (mb, ms))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NQM st1 st2 CNT NOREC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EA _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_s SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahmx; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 B1 B3 CX HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  chg (mb + 6128) hm.
  (* [comment removed for export] *)
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_space L ALO) as RSP.
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  (pose proof (rup8_facts n ltac:(lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad (hm + 16) = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8)).
  { subst hm. rewrite !shad_div, RUPS. (pose proof (sec_facts n ltac:(lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post). clear -MAL RUP RUP8 RS1 NSE NMS N6 NB. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 3%nat; intros SHE SHL SHP; nd_post).
  (* [comment removed for export] *)
  assert (HMSEP : forall kk, 0 <= kk < ndist st K_BATCH_CLASS -> hm + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= hm).
  { intros kk KK. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ _ _ _ PERC _; nd_post).
    (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros Q1 Q2 _; nd_post).
    (pose proof (slot_in_region L st K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1) KK) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 _; nd_post).
    rewrite size_of_class_24 in P4. subst hm. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1 Q2 RSP SC_s MSB. lia. }
  assert (HM0' : ablk hm (hm + 24)) by (subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB; lia]).   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CHc & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m _ CS8) as [stj STS].
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  assert (EKX : exists k24 chunks, let ek := ek_of L st X Q n k24 stj chunks in
       ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m
    /\ ek_seps ek L hm (qlast L (q_loc Q))
    /\ 0 <= ek_delta ek n /\ a_qloc_bytes st2 = a_qloc_bytes st + ek_delta ek n /\ a_qglob_bytes st2 = a_qglob_bytes st
    /\ (ek_b ek (qlast L (q_loc Q)) = qlast L (q_loc Q)
        \/ exists kk, ek_b ek (qlast L (q_loc Q)) = abatch_addr L kk /\ 0 <= kk < ndist st K_BATCH_CLASS /\ ~ In kk (map qb_slot (q_loc Q ++ q_glob Q)))
    /\ (enq_is_app st = false ->
          nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
       /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
       /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
       /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
       /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS))).
  { pose proof (st_enq_bytes st p (CSec mb ms n) L X Q) as SB.
    destruct (enq_is_app st) eqn:EAPP.
    - (nd_pre (read_ek_appS (AHQ DI ASEC_of AFK) L st X Q m RNG hm n ALO ARNG AR AQ NQM HMSEP stj [] 0 EAPP
                (Z_to_bv 64 0) (Z_to_bv 64 0) 0 CR STS) 5%nat; intros EK ES ED EB _; nd_post).
      specialize (SB 0 stj [] ltac:(intros E; exfalso; change (enq_app st1 (CSec mb ms n) = None) in E; assert (EA1 : enq_is_app st1 = true) by exact EAPP;
                    destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs]; congruence)).
      cbn [chunk_size] in SB. (nd_pre SB 3%nat; intros SB1 SB2 _; nd_post).
      exists 0, []. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [left; exact EB|]. intros; discriminate.
    - assert (POS : 0 < c_count (get_cls st K_BATCH_CLASS)).
      { apply CNT. destruct (enq_app st1 (CSec mb ms n)) eqn:E; [| reflexivity]. exfalso.
        assert (EA1 : enq_is_app st1 = true) by (apply (proj2 (enq_is_app_spec st1 (CSec mb ms n))); eexists; exact E).
        change (enq_is_app st1) with (enq_is_app st) in EA1. congruence. }
      (nd_pre (read_ek_newS (AHQ DI ASEC_of AFK) L st X Q m RNG hm n ALO ARNG AR AQ HM0' HMSEP stj EAPP POS STS) 14%nat; intros k24 chunks EK ES ED EB NK NBk KK NIB JKb FSH CIN _; nd_post).
      specialize (SB k24 stj chunks ltac:(intros _; exact POS)). cbn [chunk_size] in SB. (nd_pre SB 3%nat; intros SB1 SB2 _; nd_post).
      exists k24, chunks. cbv zeta. split; [exact EK|]. split; [exact ES|]. split; [rewrite ED; lia|]. split; [exact SB1|]. split; [exact SB2|].
      split; [right; exists k24; split; [exact EB|]; split; [exact KK| exact NIB]|].
      intros _. repeat (split; [assumption|]). exact POS. }
  (nd_pre EKX 3%nat; intros k24 chunks EKX; nd_post). cbv zeta in EKX. (nd_pre EKX 7%nat; intros EK ES ED0 SB1 SB2 EBB NEWF; nd_post).
  set (ek := ek_of L st X Q n k24 stj chunks) in *.
  (* [comment removed for export] *)
  (nd_pre (read_dkS (AHQ DI ASEC_of AFK) L st X Q m RNG hm ALO ARNG AR AQ HMSEP (ek_b ek (qlast L (q_loc Q))) (ek_delta ek n) ek ED0 EBB
              ltac:(rewrite <- SB1, <- SB2; exact NOREC) eq_refl) 4%nat; intros DK DS GL GLST; nd_post).
  set (g := g_of L st Q (ek_delta ek n)) in *.
  (* [comment removed for export] *)
  rewrite (afree_fast_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; exact NQM) CNT NOREC).
  apply implS_ret.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. (pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 3%nat; intros B0 B1' _; nd_post). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (LL64 : 0 <= qlast L (q_loc Q) < 2^64).
  { destruct (qlast_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (DELTA : ek_delta ek n <= n + 8192) by (subst ek; unfold ek_of; destruct (enq_is_app st); cbn [ek_delta]; lia).
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  assert (IN : In (CSec mb ms n) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
  pose proof (proj1 (Forall_forall _ _) RSECS _ IN) as [RMB RSH]. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  eapply evtF_mono.
  { eapply (free_fast_spec DI L (q_ia Q) ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) uw sj (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EA; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | subst hm; clear -SC_t MSB; lia | subst hm; clear -SC_c MSB; lia | subst hm; clear -SC_n MSB; lia | subst hm; clear -SC_st MSB; lia]
         | |- rng _ (shad _) _ => rewrite SHE; eapply rng_sub; [exact RSH| clear; lia| clear -SHL; lia]
         | |- rng _ _ 24 => subst hm; eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => subst hm; unfold tclr; clear -SC_tls MSB; lia
         end.
    all: try assumption.
    all: subst hm; unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize NB N6 NMS NQM MLO ML1 ML3 MCE MAL MSAL RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B1 CX LLB NC NM LF64 LL64 ED0 DELTA RA4 RUP; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms' PM.
  (* [comment removed for export] *)
  eapply (STORE L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 cx A lo k24 stj chunks).
  all: try lazymatch goal with
       | |- free_fast_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact PM
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => exact ARNG
       | |- AREP _ _ _ _ _ => exact AR
       | |- AQUAR_at _ _ _ _ _ => exact AQ
       | |- ablocks _ _ _ _ => exact BL
       | |- In _ _ => exact HIN
       | |- _ !! _ = _ => exact LIVE
       | |- _ = false -> _ => exact NEWF
       | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
       | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
       | |- rw_cells _ _ _ _ => exact H5
       end.
  all: try assumption.
  all: try (generalize NQM LO BOT STK3; clear; intros; unfold AFREE_STACK, Q_MAX in *; lia).
  all: match goal with |- ?G => idtac "REMS" G end.
Qed.
End Zd1.
#[using="STORE"] Theorem afree_sec_fast : ltac:(let t := eval cbv delta [afree_sec_fast__stmt] in afree_sec_fast__stmt in exact t).
Proof. exact afree_sec_fast__body. Qed.
End S.
End CANSEC1.
End TwB.
End ASF_fast.

(* [comment removed for export] *)
Module F_afree_arepR.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AImg AProto ABase. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Local Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Local Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Local Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma ablocks_xbusy : forall L st st' X X' LB, x_busy X' = x_busy X -> a_live st' = a_live st -> ablocks L st X LB -> ablocks L st' X' LB.
Proof. intros L st st' X X' LB E EL AB. eapply ablocks_same; [exact AB| exact E| exact EL]. Qed.

Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Notation AHQ := (AHQ DI ASEC AFK).
Hypothesis HL : ahole_laws AHQ.
Variable CI : list (Z * Z).
(* [comment removed for export] *)
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

(* [comment removed for export] *)
Definition AHQm (Q1 : qconc) : aholes := mkAHoles (fun L s X m => AQUAR_at L s X Q1 m) ASEC (ADEPOT DI) AFK.

#[using="HL"] Lemma AHQm_laws : forall Q1, ahole_laws (AHQm Q1).
Proof.
  intros Q1. destruct HL as [HQF HSF HDF HFF HFB].
  constructor; cbn [ah_quar ah_sec ah_depot ah_fake AHQm OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.AHQ] in *; try assumption.
  intros L st st' X X' m m' W AQ MU WM UT QS. exact (AQUAR_frame_at L st st' X X' Q1 m m' W AQ MU WM UT QS).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mid_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo lst nx bsz : Z)
         (hs : list word) (tr : list Z) (l1 l2 : list xbusy),
  let st1 := set_live (delete p (a_live st)) st in
  let X1 := xquar X c k n b1 ctx l1 l2 in
  let Q1 := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q) in
  alayout_ok L -> arng L RNG st -> AREP AHQ L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms1,
    free_to_refill_post DI L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n b1 ctx lo lst nx bsz hs tr m ms1 ->
       AREP (AHQm Q1) L st1 X1 (ms_mem ms1)
    /\ ablocks L st1 X1 (lb_remove p LB) /\ AFK L (lb_remove p LB) (ms_mem ms1)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m (ms_mem ms1).

(* [comment removed for export] *)
Definition store_freeR_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (c k n b1 ctx lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHQm Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  x_busy X = l1 ++ bquar c k n b1 ctx :: l2 -> 1 <= n ->
  (exists pend, q_pend Q = (c, k) :: pend) ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  (Q_CACHE < a_qloc_bytes sq -> a_qglob_bytes sq + a_qloc_bytes sq <= Q_MAX) ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms',
    free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                   (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms' ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
      /\ AHEAP_P AHQ L RNG (st_after sq) LB m'.

Hypothesis MID : mid_stmt.
Hypothesis STORE_R : store_freeR_stmt.
(* [comment removed for export] *)
Hypothesis REFILL : forall Q1, refill_stmt (AHQm Q1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma busy_slot_range' : forall L st X b, awf L st X -> In b (x_busy X) ->
  1 <= xb_class b < K_NUM_CLASSES /\ 0 <= xb_slot b < ndist st (xb_class b).
Proof.
  intros L st X b WF Hb. pose proof WF as WF0. (nd_pre WF0 9%nat; intros _ _ _ _ _ PERC _ BUSY _; nd_post).
  destruct (BUSY b Hb) as [HC _]. split; [exact HC|].
  (nd_pre (PERC (xb_class b) HC) 12%nat; intros _ _ _ _ _ _ _ _ _ _ _ RANGE; nd_post).
  apply RANGE. apply in_or_app. right. apply in_or_app. right. unfold busy_slots. apply in_map. apply List.filter_In.
  split; [exact Hb| apply Z.eqb_refl].
Qed.

Definition aheap_pres_refill__stmt : Prop := forall L st X LB (sp : word) (sE lo : Z) m m',
  alayout_ok L -> awf L st X -> ablocks L st X LB ->
  munch (arefill_W L st K_BATCH_CLASS sE) m m' -> wmono asegs m m' ->
  ATOP <= lo -> lo <= sE - 1536 -> sE <= bv_unsigned sp ->
  aheap_pres CI LB (bv_unsigned sp) m m'.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 2).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 4).
Variable sE : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 5).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 7).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 8).
#[using="CI_OK CI_OK2"] Lemma aheap_pres_refill__body : ltac:(let T := type of (fun (h : aheap_pres_refill__stmt) => h L st X LB sp sE lo m m') in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (LB, (sp, (sE, (lo, (m, m'))))))))) as _.
  intros ALO WF BL MU WM CEIL LO SLE a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  (* [comment removed for export] *)
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post). (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 3%nat; intros SP1 SP2 _; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_fake L ALO) as FKO. unfold aobj in RES, FKO. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1, TL4, RES, FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_res L ALO) as D_t_res. unfold adisj in D_t_f, D_f_res, D_t_res.
  pose proof WF as WF0. (nd_pre WF0 7%nat; intros SBE PAE SAL SLO SHI PERC _; nd_post).
  (nd_pre (PERC K_BATCH_CLASS (K24)) 12%nat; intros A24a A24b _ _ _ _ _ _ _ _ _ _; nd_post).
  pose proof (slot_geo L st X K_BATCH_CLASS 0 ALO WF (K24)) as SG0.
  assert (ERI : aregion_info L K_BATCH_CLASS = al_space_beg L + 137438953472 + 3072) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_BATCH_CLASS; lia).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; lia).
  pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM.
  assert (MM8 : c_mapped_user (get_cls st K_BATCH_CLASS) mod 8 = 0).
  { (nd_pre (PERC K_BATCH_CLASS (K24)) 5%nat; intros _ _ _ MU8 _; nd_post). generalize MU8; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia. }
  assert (W6B : 0x2008fff7000 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
             /\ shad (aregion L K_BATCH_CLASS) + shlen K_REGION = shad (aregion L K_BATCH_CLASS + K_REGION)
             /\ shad (aregion L K_BATCH_CLASS + K_REGION) <= 0x10007fff8000).
  { split; [| split; [symmetry; apply shad_add_shlen; generalize RM; clear; intros; Z.div_mod_to_equations; lia|]];
    rewrite !shad_div; unfold ASHOFF, K_REGION; rewrite ER24; generalize SP1 SP2 A24a A24b; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF;
    change (2^37) with 137438953472; change (2^32) with 4294967296; intros; Z.div_mod_to_equations; lia. }
  (nd_pre W6B 3%nat; intros W6LO W6E W6HI; nd_post). rewrite W6E.
  unfold AIMG_HI, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  eapply (disjoint_outside _ a 1); [| clear; lia].
  cbn [disjoint_from fst snd]. unfold AINSTANCE.
  destruct CL as [CL|TL].
  2:{ (* [comment removed for export] *)
      pose proof (ad_tls_t L ALO) as DLT. pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLT, DLR.
      pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
      destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
      4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_res L ALO) as DA2. unfold adisj in DA1, DA2.
          generalize IM OAH OAHI DA1 DA2 SLE LO CEIL TL1 TL2 SP1 SP2 RSP RHI ERI ER24 A24a A24b W6LO W6HI ATR0; clear; intros; repeat split; lia. }
      3:{ unfold AIMSH_LO, AIMSH_LEN in IM. generalize IM SLE LO CEIL TL1 TL2 SP1 SP2 RSP RHI ERI ER24 A24a A24b W6LO W6HI ATR0; clear; intros; repeat split; lia. }
      - generalize T DLT DLR TLN ATR0 TBA SLE LO CEIL TL1 TL2 SP1 SP2 RSP RHI ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
      - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
        assert (SA : shad ATOP <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -ATR0; Z.div_mod_to_equations; lia).
        assert (TSA : shad ta + 1 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                      \/ shad (aregion L K_BATCH_CLASS + 4294967296) <= shad ta).
        { destruct (tls_shadow_apart ta (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                      (4294967296 - c_mapped_user (get_cls st K_BATCH_CLASS)) Hta ltac:(clear -A24a A24b; lia)) as [D|D].
          { destruct DLR as [D|D]; [left; generalize D RSP ER24 A24a A24b; clear; intros; lia
                                   | right; split; [generalize D RSP ER24 A24a A24b SP1 SP2; clear; intros; lia
                                                   | generalize RM MM8; clear; intros; Z.div_mod_to_equations; lia]]. }
          - left; exact D.
          - right. rewrite <- (shad_add_shlen _ (4294967296 - c_mapped_user (get_cls st K_BATCH_CLASS))) in D
              by (generalize RM MM8; clear; intros; Z.div_mod_to_equations; lia).
            replace (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS) + (4294967296 - c_mapped_user (get_cls st K_BATCH_CLASS)))
              with (aregion L K_BATCH_CLASS + 4294967296) in D by (clear; lia). exact D. }
        generalize TS1 TS2 SA TSA SLE LO CEIL TL1 TL2 SP1 SP2 RSP RHI ERI ER24 A24a A24b W6LO W6HI ATR0; clear; intros; repeat split; lia. }
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - (* [comment removed for export] *) generalize ST SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
  - (* [comment removed for export] *)
    (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post).
    pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE, AIMG_HI in *.
    generalize R Q1 Q3 Q7 SLE LO CEIL TL1 TL2 TL4 SP1 SP2 RHI ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    (nd_pre BLK 3%nat; intros [[q|cls] A' n'] Hin R; nd_post); cbn [ab_addr ab_size] in R.
    + destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      * destruct (busy_slot_range' L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        (pose proof (slot_geo L st X (xb_class b) (xb_slot b) ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros _ _ _ P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slot_sep_objects L st X (xb_class b) (xb_slot b) ALO WF HCb HKb) as (BT & _).
        assert (SL5 : aslot_addr L (xb_class b) (xb_slot b) + size_of_class (xb_class b) <= aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS)
                      \/ aregion L K_BATCH_CLASS + 4294967296 <= aslot_addr L (xb_class b) (xb_slot b)).
        { (nd_pre (PERC (xb_class b) HCb) 3%nat; intros Ac1 Ac2 _; nd_post).
          destruct (Z.lt_trichotomy (xb_class b) K_BATCH_CLASS) as [LT|[E24|GT]].
          - left. pose proof (regions_sep L (xb_class b) K_BATCH_CLASS LT) as RS. generalize RS P2 P3 Ac1 Ac2 A24a A24b. clear. unfold K_REGION. change (2^32) with 4294967296. intros. lia.
          - left. generalize P2 P3 A24a A24b. rewrite E24. clear. intros. lia.
          - right. pose proof (regions_sep L K_BATCH_CLASS (xb_class b) GT) as RS. generalize RS P1. clear. unfold K_REGION. change (2^32) with 4294967296. intros. lia. }
        unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
        generalize R FIT P5 P6 P7 P8 BT SL5 SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
      * (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        generalize R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RES RHI RSP SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
    + (nd_pre (proj1 (proj2 BL) cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post).
      generalize R K1 K2 K3 FKO D_t_f D_f_res RES RHI RSP SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
  - (* [comment removed for export] *)
    (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
    assert (SHI' : forall x, 0 <= x < 2^47 -> 0x7fff8000 <= shad x /\ shad x + 1 <= 0x10007fff8000) by (intros x Hx; clear - Hx; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    destruct Ha' as [ST | [CIa | FK]].
    + (* [comment removed for export] *)
      atop_facts.
      assert (B1 : shad (aregion L K_BATCH_CLASS + 4294967296) <= shad a') by (apply shad_mono; generalize ST SLE LO CEIL SP2 ER24; clear; intros; lia).
      destruct (SHI' a' ltac:(generalize ST SLE LO CEIL; clear; intros; lia)) as [B2 B3].
      generalize B1 B2 B3 TL1 SP1 ERI ER24 A24a SLE LO CEIL W6LO; clear; intros; repeat split; lia.
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *. unfold AIMG_HI in *.
      assert (B1 : shad a' + 1 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))).
      { rewrite !shad_div. generalize R Q3 SP1 ER24 A24a; clear; intros; Z.div_mod_to_equations; lia. }
      destruct (SHI' a' ltac:(generalize R Q1 Q3; clear; intros; lia)) as [B2 B3].
      generalize B1 B2 B3 TL1 SP1 ERI ER24 A24a SLE LO CEIL W6LO; clear; intros; repeat split; lia.
    + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post).
      assert (B1 : shad a' + 1 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                   \/ shad (aregion L K_BATCH_CLASS + 4294967296) <= shad a').
      { destruct D_f_res as [D|D].
        - left. rewrite !shad_div. generalize D R K1 K3 RSP ER24 A24a RM MM8; clear; intros; Z.div_mod_to_equations; lia.
        - right. apply shad_mono. generalize D R K1 K3 RSP RES SP2 ER24; clear; intros; lia. }
      destruct (SHI' a' ltac:(generalize R K1 K3 FKO; clear; intros; lia)) as [B2 B3].
      generalize B1 B2 B3 TL1 SP1 ERI ER24 A24a SLE LO CEIL W6LO; clear; intros; repeat split; lia.
Qed.
End Zd1.
#[using="CI_OK CI_OK2"] Lemma aheap_pres_refill : ltac:(let t := eval cbv delta [aheap_pres_refill__stmt] in aheap_pres_refill__stmt in exact t).
Proof. exact aheap_pres_refill__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_refill__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  (Q_CACHE < a_qloc_bytes st + (n + 8192) -> a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P AHQ L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P AHQ) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 42).
Variable c : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 43).
Let full := match a_qloc st with [] => false | _ :: _ => true end.
Let bsz := b_size (List.last (a_qloc st) dummy_batch).
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL full bsz"] Lemma afree_refill__body : ltac:(let T := type of (fun (h : afree_refill__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr c) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (tr, c)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE N1 EA CNT0 NOREC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  set (st1 := set_live (delete p (a_live st)) st).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  pose proof BL as BL0. destruct BL0 as (BH & _).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  destruct (BH p A n HIN) as [(y & Hy & Sy & Uy & Ny)|(mb & msz & Lp & _)]; [| exfalso; rewrite LIVE in Lp; discriminate].
  destruct (BUSY y Hy) as [CLy My]. rewrite Sy in My. (nd_pre My 6%nat; intros _ _ _ _ _ M5; nd_post). rewrite LIVE in M5.
  injection M5 as Cy Ny'. clear Ny'.
  (nd_pre (in_split _ _ Hy) 3%nat; intros l1 l2 XB; nd_post).
  destruct y as [yc yk yn yst yb1 yctx]. cbn in Sy, Uy, Ny, Cy, CLy. subst yst yn yc.
  rename yk into k. rename yb1 into b1. rename yctx into ctx.
  change ({| xb_class := c; xb_slot := k; xb_n := n; xb_st := BLive p; xb_b1 := b1; xb_ctx := ctx |}) with (bfreed p c k n b1 ctx) in XB.
  unfold xb_user, xb_alloc in Uy. cbn [xb_class xb_slot xb_n] in Uy.
  (* [comment removed for export] *)
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros _ N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  destruct (slot_rng L st X c k ALO WF HC KR RNG ARNG) as [RSL RSS].
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 8%nat; intros SE G2 GE G0 GFS SHLO SHHI _; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  set (AB := aslot_addr L c k) in *. set (UB := AB + rz_size n) in *.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; lia).
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CH & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  rewrite CNT0 in CR.
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros HDR [uw HUW] UJR LH SHA SHU SHR; nd_post).
  fold AB in HDR, HUW, UJR, LH, SHA, SHU, SHR. fold UB in HDR, HUW, UJR, LH, SHU, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  (pose proof (read_last AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) EA) as ndP__; nd_pre ndP__ 6%nat; intros FULL DTL DHL DNL DSL LST64; nd_post).
  cbv zeta in FULL.
  chg (match a_qloc st with [] => false | _ :: _ => true end) full.
  set (lst := qlast L (q_loc Q)) in *.
  chg (b_size (List.last (a_qloc st) dummy_batch)) bsz.
  set (hs := map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb)))) in *.
  assert (FULL' : if full then 0 < Z.of_nat (length (a_qloc st)) /\ rw_cells asegs m lst [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else Z.of_nat (length (a_qloc st)) = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. (nd_pre FULL 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post). repeat (split; [assumption|]). exact F7. }
  (* [comment removed for export] *)
  rewrite (afree_refill_eq st p (CPrim c n) LIVE ltac:(cbn [chunk_size]; exact NQM) EA CNT0). fold st1.
  idtac "CHECKPOINT-A".
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. (pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 3%nat; intros B0 B1 _; nd_post). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (CEIL : ATOP <= lo) by (generalize BOT STK3; clear; intros; lia).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE in *.
  box DT. box DC. box DN. box DSO. box DF. box CL5. box DL7. box DL8. box DL9. box DL10. box DTL. box DHL. box DNL. box DSL.
  eapply implF_evtF.
  { eapply (free_to_refill_spec DI L (q_ia Q) full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) (fhm L c k n) n b1 ctx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz uw _ _ sj hs (block_shadow_bytes n) trt).
    all: rewrite ?EHM.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- if _ then _ else _ => exact FULL'
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ (shad _) _ => eapply rw_cells_addr_eq; [exact SHU| f_equal; lia]
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ - 16 + 16) [C8 _] => eapply rw_cells_addr_eq; [exact HUW| lia]
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, <- Uy; subst AB UB; apply Z_to_bv_eqm; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia] | reflexivity]   (* [comment removed for export] *)
         | |- _ \/ _ => first [unboxed DT | unboxed DC | unboxed DN | unboxed DSO | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10
                             | unboxed DTL | unboxed DHL | unboxed DNL | unboxed DSL
                             | ub DT; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DC; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DN; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DSO; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DTL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DHL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DNL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DSL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia)
                             | ub DT; lia | ub DC; lia | ub DN; lia | ub DSO; lia | ub DTL; lia | ub DHL; lia | ub DNL; lia | ub DSL; lia]
         | |- rng _ (shad _) _ => replace (UB - 16 + 16) with UB by (clear; lia); eapply rng_sub; [exact RSS| rewrite SE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| rewrite SE, GE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSL| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)] | eapply rng_sub; [exact RCTX| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)] | eapply rng_sub; [exact RSL| lia| lia] | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
         end.
    all: try assumption.
    all: unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia).
    all: try (tclr_solve ALO ltac:((pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ SG5 SG6 _; nd_post);
                                    unfold K_SPACE_SIZE in SG6; change (2^37) with 137438953472 in SG6;
                                    generalize SG5 SG6 ABHM UBS RUP N0 N1; subst UB AB; clear; intros; lia)).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PTR.
  pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst 0 bsz hs trt l1 l2
              ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1) as MIDI.
  rewrite EHM in MIDI. specialize (MIDI PTR). (nd_pre MIDI 4%nat; intros ARm BLm FKm HPm; nd_post).
  unfold free_to_refill_post in PTR.
  (nd_pre PTR 18%nat; intros id t0a t1a t2a a4a a5a a6a a7a t3a t4a t5a t6a m1 sj1 tb1 junk2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 22%nat; intros MUf WMf MIf STf IDR HD1 FC1 SH1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 SS1 TB1 LTB1 FRS1 FRP1 FRE1 LBS1 DEP1; nd_post).
  cbn [ms_mem MS] in ARm, FKm, HPm.
  idtac "CHECKPOINT-B".
  (* [comment removed for export] *)
  set (Q1 := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)) in *.
  set (X1 := xquar X c k n b1 ctx l1 l2) in *.
  eapply (REFILL Q1 _ (KB (CPrim c n)) _ L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st1 X1 K_BATCH_CLASS lo).
  all: try lazymatch goal with
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => (* [comment removed for export] *)
           apply (arng_st L RNG st st1); [intros; reflexivity| reflexivity| apply (sec_chunks_free st p c n); [exact LIVE| reflexivity| apply Permutation_refl]| exact ARNG]
       | |- AREP _ _ _ _ _ => exact ARm
       | |- mem_inv _ _ => exact MIf
       | |- stk _ _ _ _ => rewrite unsigned_lit by (first [clear -SP47 LO BOT STK3; lia | lia]); exact STf     (* [comment removed for export] *)
       | |- @eq word _ _ => first [exact TP | reflexivity | unfold acache_addr, K_BATCH_CLASS; apply Z_to_bv_eqm; first [clear; lia | lia] | unfold AINSTANCE; reflexivity]
       | |- _ <= K_BATCH_CLASS < _ => exact (K24)
       | |- c_count _ = 0 => exact CNT0
       | |- _ <= _ => first [exact CEIL | rewrite ?unsigned_lit by (first [clear -SP47 LO BOT STK3; lia | lia]); first [clear -SP47 LO BOT STK3; lia | lia]]
       | |- rng _ _ _ => rewrite unsigned_lit by (first [clear -SP47 LO BOT STK3; lia | lia]); eapply rng_sub; [exact RSTK| first [clear -SP47 LO BOT STK3; lia | lia]| first [clear -SP47 LO BOT STK3; lia | lia]]
       end.
  all: match goal with |- forall _ _ _ _, refill_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => idtac | |- ?G => idtac "REMR" G end.
  intros st_r X' RNG' ms' RR. unfold refill_ret in RR.
  (nd_pre RR 17%nat; intros FPLE t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 20%nat; intros MUr WMr MIr STr ARr ARNGr CINr CNTr MAXr XBr XCr LIVEr NEXTr QLr QBr QGr QGBr NSECr NRESr GCr; nd_post).
  rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
  idtac "CHECKPOINT-C".
  (* [comment removed for export] *)
  assert (EAr : enq_is_app st_r = false) by (unfold enq_is_app; rewrite QLr; exact EA).
  (pose proof (enq_new_core (CPrim c n) st_r) as ndP__; nd_pre ndP__ 7%nat; intros _ NG1 NG2 _ NL1 NL2 _; nd_post). cbn [chunk_size] in NL1, NL2.
  assert (ENr : st_enq st_r (CPrim c n) = enq_new st_r (CPrim c n)).
  { unfold st_enq. destruct (enq_app st_r (CPrim c n)) as [s'|] eqn:E; [| reflexivity]. exfalso.
    assert (EA1 : enq_is_app st_r = true) by (apply (proj2 (enq_is_app_spec st_r (CPrim c n))); eexists; exact E). congruence. }
  assert (NORECr : Q_CACHE < a_qloc_bytes (st_enq st_r (CPrim c n)) -> a_qglob_bytes (st_enq st_r (CPrim c n)) + a_qloc_bytes (st_enq st_r (CPrim c n)) <= Q_MAX).
  { rewrite ENr, NG2, NL2, QBr, QGBr. change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES. generalize NOREC; clear; intros; lia. }
  rewrite (KB_apop_eq st_r (CPrim c n) EAr NORECr).
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x382f8)) with (Z_to_bv 64 0x382f8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2' G3 G4 G5 G6 G7 G8 R8 M8; nd_post). fold AB in AL16, G1, G2', G5, G6, G7, G8.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ad_t_res L ALO) as D_t_res. unfold adisj in D_t_res.
  pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in RES. pose proof (ao_space L ALO) as RSP.   (* [comment removed for export] *)
  (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros A24a A24b _; nd_post).
  assert (ERI : aregion_info L K_BATCH_CLASS = al_space_beg L + 137438953472 + 3072) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_BATCH_CLASS; lia).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; lia).
  assert (SLW5 : AB + size_of_class c <= aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS) \/ aregion L K_BATCH_CLASS + K_REGION <= AB).
  { (nd_pre (PERC c HC) 3%nat; intros Ac1 Ac2 _; nd_post).
    destruct (Z.lt_trichotomy c K_BATCH_CLASS) as [LT|[E24|GT]].
    - left. pose proof (regions_sep L c K_BATCH_CLASS LT) as RS. generalize RS G2' G3 Ac1 Ac2 A24a A24b. clear. unfold K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. intros. lia.
    - left. generalize G2' G3 A24a A24b. rewrite E24. clear. intros. lia.
    - right. pose proof (regions_sep L K_BATCH_CLASS c GT) as RS. generalize RS G1. clear. intros. lia. }
  assert (UB8 : UB mod 8 = 0) by (generalize UB16; clear; intros; Z.div_mod_to_equations; lia).
  assert (SLW6 : shad UB + shlen (rup n 8) <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
              \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad AB).
  { pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM. destruct SLW5 as [D|D].
    - left. apply shad_sep; [| exact UB8]. generalize D UBS; clear; intros; lia.
    - right. apply shad_sep; [exact D| generalize RM; clear; intros; Z.div_mod_to_equations; lia]. }
  assert (W6B : 2199023255552 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
             /\ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= 17594333495296).
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_REGION. rewrite ER24. generalize SP1 SP2 A24a A24b. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. change (2^37) with 137438953472. change (2^32) with 4294967296. change (2^41) with 2199023255552. intros. Z.div_mod_to_equations. lia. }
  destruct W6B as [W6LO W6HI].
  word_range sp SPR.
  change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS) in MUr.
  (* [comment removed for export] *)
  lazymatch type of MUr with munch ?W _ _ =>
    assert (KHI : forall Ad sz, bv_unsigned sp + -2272 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz H1 H2; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize H1 H2 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KIM : forall Ad sz, 0xaf800 <= Ad -> Ad + sz <= 0x13e090 -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz H1 H2 H3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize H1 H2 H3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KCH : forall Ad sz, AB <= Ad -> Ad + sz <= UB + rup n 8 -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz H1 H2 H3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      pose proof DT as DT'; unbox DT'; pose proof SLW5 as SL5;
      generalize H1 H2 H3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR DT' SL5 G6 G7 UBS ABUB; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KSH : disjoint_from W (shad UB) (shlen (rup n 8)));
    [ cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION; pose proof SLW6 as SL6;
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR SL6 SHLO SHHI SE GE GFS G0 G2; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |]
  end.
  (* [comment removed for export] *)
  rewrite EHM in HD1, FC1, SH1.
  eapply (cells_frame _ m1 m') in HD1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; generalize ABUB RUP N1; clear; intros; lia].
  eapply (cells_frame _ m1 m') in FC1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; generalize ABUB RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia].
  eapply (cells_frame _ m1 m') in SH1; [| exact MUr | exact WMr | replace (UB - 16 + 16) with UB by (clear; lia); match goal with |- disjoint_from _ _ ?z => replace z with (shlen (rup n 8)) by (cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id; [reflexivity| generalize G0; clear; intros; lia]) end; exact KSH].
  (* [comment removed for export] *)
  clear STATS1 LSJ1 UW1.
  eapply (cells_frame _ m1 m') in FL1; [| exact MUr | exact WMr | apply KIM; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (stk_transport_disjoint _ _ m1 m') in IAS1; [| exact MUr | exact WMr | apply KIM; clear; lia].
  eapply (cells_frame _ m1 m') in SS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (u64arr_frame _ m1 m') in TB1; [| exact MUr | exact WMr | apply KHI; rewrite ?LTB1; clear; cbn; lia].
  eapply (cells_frame _ m1 m') in FRS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRP1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRE1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MUr. rewrite length_le8 in Hi. rewrite wa_unsigned by lia.
    eapply disjoint_outside; [apply (KIM (0xaf808 + 8 * j) 8); generalize Hj; clear; intros; lia| generalize Hi; clear; intros; lia]. }
  clear IAM1.
  idtac "CHECKPOINT-C2".
  (* [comment removed for export] *)
  pose proof ARr as AR0. (nd_pre AR0 11%nat; intros WFr RTr INSTr THRr CLSr HQr HSr HDr HROr HRT2r AVLr; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQm] in HQr, HSr, HDr.
  assert (XB' : x_busy X' = l1 ++ bany BQuar c k n b1 ctx :: l2) by (rewrite XBr; reflexivity).
  (nd_pre THRr 6%nat; intros T0r T40r CACHESr CSTATSr [sjr [STATSr LSJr]] UNWr; nd_post).
  destruct (junk_split m' (al_t L + 2768) 16 16 CSTATSr ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m' (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m' _ CS8) as [stj' STSr].
  assert (POSr : 0 < c_count (get_cls st_r K_BATCH_CLASS)) by (rewrite CNTr; exact MAXr).
  (nd_pre (read_ek_new (AHQm Q1) L st_r X' Q1 m' RNG' BQuar c k n b1 ctx l1 l2 ALO ARNGr ARr HQr XB' ltac:(discriminate) stj' EAr POSr STSr) 15%nat; intros k24 chunks EK ES ED EB NK NB KK NIB JK FSH CIN _ EKE; nd_post).
  pose proof HQr as AQr. (nd_pre AQr 6%nat; intros [QKr MXr] [QCr ABLr] [GCQr ABGr] (FLr & IASr & IAMr) CPr NUMr; nd_post).
  (nd_pre (read_dk (AHQm Q1) L st_r X' Q1 m' RNG' BQuar c k n b1 ctx l1 l2 ALO ARNGr ARr HQr XB' ltac:(discriminate)
              (abatch_addr L k24) (n + 8192) (ek_of L st_r X' Q1 n k24 stj' chunks) ltac:(lia)
              ltac:(right; exists k24; split; [reflexivity|]; split; [exact KK| exact NIB])
              ltac:(rewrite ENr, NG2, NL2 in NORECr; generalize NORECr; clear; unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES; intros; lia) EB) 4%nat; intros DK DS GL GLST; nd_post).
  set (ek := ek_of L st_r X' Q1 n k24 stj' chunks) in *.
  set (g := g_of L st_r Q1 (n + 8192)) in *.
  idtac "CHECKPOINT-D".
  (* [comment removed for export] *)
  destruct (any_range L st_r X' BQuar c k n b1 ctx l1 l2 XB' WFr) as [HCr KRr].
  destruct (slot_rng L st_r X' c k ALO WFr HCr KRr RNG' ARNGr) as [RSLr RSSr]. fold AB in RSLr, RSSr.
  pose proof ARNGr as AG0. (nd_pre AG0 6%nat; intros RIMGr RT4r RCTXr RNOr RSTOr _; nd_post).
  pose proof ARNGr as AG1. (nd_pre AG1 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ RTLSr; nd_post).      (* [comment removed for export] *)
  pose proof (rng_fp_le _ _ _ _ FPLE RSTK) as RSTKr.
  assert (BLr : ablocks L st_r X' (lb_remove p LB)) by (apply (ablocks_xbusy L (set_live (delete p (a_live st)) st) st_r X1); [exact XBr | exact LIVEr | exact BLm]).
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_dtls L ALO) as DTO. unfold aobj in DTO.
  unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in FKO, DTO.   (* [comment removed for export] *)
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKr : AFK L (lb_remove p LB) m').
  { eapply (hf_frame _ HL L (lb_remove p LB) m1 m'); [exact FKm | exact MUr | exact WMr |].
    unfold fake_untouched. unfold AINSTANCE, K_REGION.
    assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                   \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad (al_fake L))).
    { destruct D_f_res as [D|D].
      - left. apply shad_sep; [| generalize FKO; clear; intros; Z.div_mod_to_equations; lia]. rewrite ER24. generalize D RSP A24a; clear; intros; lia.
      - right. apply shad_sep; [| pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM; generalize RM; clear; intros; Z.div_mod_to_equations; lia].
        rewrite ER24. unfold K_REGION. generalize D RSP RES; clear; atop_facts; intros; lia. }
    unfold K_REGION in SHF.
    repeat (apply Forall_cons; [cbn [fst snd];
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR FKO DTO D_f_res D_t_f D_d_res D_t_d RES RHI RSP SHF; clear;
      unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296;
      rewrite ?shad_div, ?shlen_div; unfold ASHOFF; intros; repeat split; fu_focus; Z.div_mod_to_equations; lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  clear D_f_res D_t_f D_d_res D_t_d D_t_res.
  idtac "CHECKPOINT-D2".
  rewrite <- EHM in HD1, FC1, SH1.
  pose proof EK as EK0. pose proof ES as ES0. pose proof DK as DK0.
  rewrite EKE in EK, ES, DK. cbn [ek_pre] in EK.
  (nd_pre EK 20%nat; intros FULLr SBr CRr CHr LCHr CNTr' NTHr IXSr STSr' HBr BJr SBPr B0r BL1r DTBr DTLr DBLr DHBr DHLr RBr; nd_post).
  box DTBr. box DTLr. box DBLr. box DHBr. box DHLr.
  pose proof ES as ES1. cbn [ek_seps] in ES1. (nd_pre ES1 4%nat; intros SB1r SB2r SB3r SLr; nd_post).
  assert (DHL24 : fhm L c k n + 24 <= qlast L (q_loc Q1) \/ qlast L (q_loc Q1) + 8192 <= fhm L c k n).
  { destruct (a_qloc st_r); [destruct FULLr as [_ E0]; rewrite E0; right; generalize HLO EHM; clear; intros; lia | exact (proj1 (SLr eq_refl))]. }
  box SB1r. box DHL24.
  assert (NBr : 0 <= Z.of_nat (length (a_qloc st_r)) < 2^62) by (rewrite QLr; change (a_qloc st1) with (a_qloc st); generalize LLB NC; clear; unfold Q_BATCH_BYTES; intros; lia).
  assert (QB0r : 0 <= a_qloc_bytes st_r) by (rewrite QBr; change (a_qloc_bytes st1) with (a_qloc_bytes st); generalize LLB; clear; unfold Q_BATCH_BYTES; intros; lia).
  (* [comment removed for export] *)
  eapply evtF_mono.
  { lazymatch type of EKE with _ = EkNew ?fu ?nx ?bs ?cn ?mx ?cz ?sj0 ?ix ?chs ?sb ?bb ?hs0 =>
      eapply (free_from_refill_spec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
                (al_t L) (fhm L c k n) n b1 ctx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
                nx bs cn sb id bb mx cz sj0 ix sjr tb1 chs hs0 junk2 j0 trt)
    end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact STr | exact IAS1]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MIr
         | |- ADEPOT _ _ _ => exact HDr
         | |- u64arr _ _ (_ + 2800) _ => exact STATSr
         | |- u64arr _ _ _ _ => first [exact TB1 | exact CHr]
         | |- if _ then _ else _ => exact FULLr
         | |- forall j, _ -> bytes_at _ _ _ _ => exact IAM2
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH1
         | |- rw_cells _ _ (aq_tcache _) _ => exact QCr
         | |- rw_cells _ _ (_ + 80) _ => exact QCr
         | |- rw_cells _ _ (_ + 2128) _ => exact CRr
         | |- rw_cells _ _ (_ + 2784) _ => exact STSr'
         | |- rw_cells _ _ (_ + 3168) _ => exact UNWr
         | |- rw_cells _ _ (_ + -72) _ => exact FRS1
         | |- rw_cells _ _ (_ + -2128) _ => exact SS1
         | |- rw_cells _ _ (_ + -2208) _ => exact FRP1
         | |- rw_cells _ _ (_ + -2272) _ => exact FRE1
         | |- rw_cells _ _ (fhm _ _ _ _ + 16) _ => exact FC1
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact QKr
         | |- nth_error _ _ = _ => exact NTHr
         | |- @eq Z _ _ => exact HBr
         | |- ex _ => exact BJr
         | |- _ + 24 <= al_t _ \/ _ => pose proof DT as DT2; unbox DT2; generalize DT2 EHM S8 ABUB RUP N1; clear; intros; lia
         | |- _ \/ _ => first [unboxed DTBr | unboxed DTLr | unboxed DBLr | unboxed SB1r | unboxed DHL24 | unboxed DT | unboxed DL7 | unboxed DL8]
         | |- rng _ (shad _) _ => replace (fhm L c k n + 16) with UB by (generalize EHM; clear; intros; lia); eapply rng_sub; [exact RSSr| rewrite SE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| rewrite SE, GE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]
         | |- rng _ (fhm _ _ _ _) _ => eapply rng_sub; [exact RSLr| first [generalize EHM; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| first [generalize EHM; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSTKr| first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]]
         end.
    all: try assumption.
    all: try (unfold Q_MAX, Q_BATCH_BYTES; rewrite ?QLr, ?QBr; change (a_qloc st1) with (a_qloc st); change (a_qloc_bytes st1) with (a_qloc_bytes st);
              generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM UBS S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B10 LLB NC NM LF64 LST64 RA4 IDR EHM; clear; intros; lia).
    all: try (rewrite ?EHM; tclr_solve ALO ltac:((pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ SG5 SG6 _; nd_post);
                                    unfold K_SPACE_SIZE in SG6; change (2^37) with 137438953472 in SG6;
                                    generalize SG5 SG6 ABHM UBS RUP N0 N1; subst UB AB; clear; intros; lia)).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMT" G end. }
  cbv beta. intros msf PF.
  idtac "CHECKPOINT-E".
  rewrite <- EKE in PF.
  pose proof ARm as ARm0. destruct ARm0 as [WFm _].
  assert (DK1 : dk_pre ek (g_of L st_r Q1 (ek_delta ek n)) RNG' (al_t L) (qlast L (q_loc Q1)) (fhm L c k n) (a_qloc_bytes st_r + ek_delta ek n) m') by (rewrite ED; exact DK0).
  assert (PF1 : free_fast_post DI L ek (g_of L st_r Q1 (ek_delta ek n)) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                  (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r) b1 ctx lo m' msf) by (rewrite ED; exact PF).
  (pose proof (STORE_R L RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' st_r (lb_remove p LB) X' Q1 c k n b1 ctx lo k24 l1 l2 stj' chunks
                ALO ARNGr ARr BLr FKr XB' N1 (ex_intro _ (q_pend Q) eq_refl) EAr NK NB KK NIB JK FSH CIN POSr NORECr EK0 DK1 CEIL LO msf PF1) as ndP__; nd_pre ndP__ 17%nat; intros t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f mf ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MIf2 STf2 HPf AHf; nd_post).
  unfold afree_post. split; [exact FPLE|].
  exists t0f, t1f, t2f, a0f, a1f, a2f, a3f, a4f, a5f, a6f, a7f, t3f, t4f, t5f, t6f, mf.
  split; [reflexivity|]. split; [exact MIf2|]. split; [exact STf2|]. split; [| exact AHf].
  eapply aheap_pres_trans; [exact HPm|]. eapply aheap_pres_trans; [| exact HPf].
  eapply (aheap_pres_refill L st1 X1 (lb_remove p LB) sp (bv_unsigned sp + -2272) lo m1 m');
    [exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia].
Qed.
End Zd2.
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL"] Theorem afree_refill : ltac:(let t := eval cbv delta [afree_refill__stmt] in afree_refill__stmt in exact t).
Proof. exact afree_refill__body. Qed.
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
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB. Local Ltac Zify.zify_pre_hook ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Local Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Local Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Local Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma ablocks_xbusy : forall L st st' X X' LB, x_busy X' = x_busy X -> a_live st' = a_live st -> ablocks L st X LB -> ablocks L st' X' LB.
Proof. intros L st st' X X' LB E EL AB. eapply ablocks_same; [exact AB| exact E| exact EL]. Qed.

Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Notation AHQ := (AHQ DI ASEC AFK).
Hypothesis HL : ahole_laws AHQ.
Variable CI : list (Z * Z).
(* [comment removed for export] *)
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

(* [comment removed for export] *)
Definition AHQm (Q1 : qconc) : aholes := mkAHoles (fun L s X m => AQUAR_at L s X Q1 m) ASEC (ADEPOT DI) AFK.

#[using="HL"] Lemma AHQm_laws : forall Q1, ahole_laws (AHQm Q1).
Proof.
  intros Q1. destruct HL as [HQF HSF HDF HFF HFB].
  constructor; cbn [ah_quar ah_sec ah_depot ah_fake AHQm OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB.AHQ] in *; try assumption.
  intros L st st' X X' m m' W AQ MU WM UT QS. exact (AQUAR_frame_at L st st' X X' Q1 m m' W AQ MU WM UT QS).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mid_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo lst nx bsz : Z)
         (hs : list word) (tr : list Z) (l1 l2 : list xbusy),
  let st1 := set_live (delete p (a_live st)) st in
  let X1 := xquar X c k n b1 ctx l1 l2 in
  let Q1 := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q) in
  alayout_ok L -> arng L RNG st -> AREP AHQ L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms1,
    free_to_refill_post DI L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n b1 ctx lo lst nx bsz hs tr m ms1 ->
       AREP (AHQm Q1) L st1 X1 (ms_mem ms1)
    /\ ablocks L st1 X1 (lb_remove p LB) /\ AFK L (lb_remove p LB) (ms_mem ms1)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m (ms_mem ms1).

(* [comment removed for export] *)
Definition store_freeR_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (c k n b1 ctx lo k24 : Z)
         (l1 l2 : list xbusy) (stj : word) (chunks : list word),
  let ch := CPrim c n in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHQm Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  x_busy X = l1 ++ bquar c k n b1 ctx :: l2 -> 1 <= n ->
  (exists pend, q_pend Q = (c, k) :: pend) ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  (Q_CACHE < a_qloc_bytes sq -> a_qglob_bytes sq + a_qloc_bytes sq <= Q_MAX) ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n (fhm L c k n) m ->
  dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) (fhm L c k n) (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms',
    free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                   (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms' ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
      /\ AHEAP_P AHQ L RNG (st_after sq) LB m'.

Hypothesis MID : mid_stmt.
Hypothesis STORE_R : store_freeR_stmt.
(* [comment removed for export] *)
Hypothesis REFILL : forall Q1, refill_stmt (AHQm Q1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma busy_slot_range' : forall L st X b, awf L st X -> In b (x_busy X) ->
  1 <= xb_class b < K_NUM_CLASSES /\ 0 <= xb_slot b < ndist st (xb_class b).
Proof.
  intros L st X b WF Hb. pose proof WF as WF0. (nd_pre WF0 9%nat; intros _ _ _ _ _ PERC _ BUSY _; nd_post).
  destruct (BUSY b Hb) as [HC _]. split; [exact HC|].
  (nd_pre (PERC (xb_class b) HC) 12%nat; intros _ _ _ _ _ _ _ _ _ _ _ RANGE; nd_post).
  apply RANGE. apply in_or_app. right. apply in_or_app. right. unfold busy_slots. apply in_map. apply List.filter_In.
  split; [exact Hb| apply Z.eqb_refl].
Qed.

Definition aheap_pres_refill__stmt : Prop := forall L st X LB (sp : word) (sE lo : Z) m m',
  alayout_ok L -> awf L st X -> ablocks L st X LB ->
  munch (arefill_W L st K_BATCH_CLASS sE) m m' -> wmono asegs m m' ->
  ATOP <= lo -> lo <= sE - 1536 -> sE <= bv_unsigned sp ->
  aheap_pres CI LB (bv_unsigned sp) m m'.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 2).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 4).
Variable sE : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 5).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 6).
Variable m : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 7).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'aheap_pres_refill__stmt 8).
#[using="CI_OK CI_OK2"] Lemma aheap_pres_refill__body : ltac:(let T := type of (fun (h : aheap_pres_refill__stmt) => h L st X LB sp sE lo m m') in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (LB, (sp, (sE, (lo, (m, m'))))))))) as _.
  intros ALO WF BL MU WM CEIL LO SLE a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  (* [comment removed for export] *)
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post). (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 3%nat; intros SP1 SP2 _; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_fake L ALO) as FKO. unfold aobj in RES, FKO. pose proof (ao_space L ALO) as RSP.
  pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1, TL4, RES, FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_res L ALO) as D_t_res. unfold adisj in D_t_f, D_f_res, D_t_res.
  pose proof WF as WF0. (nd_pre WF0 7%nat; intros SBE PAE SAL SLO SHI PERC _; nd_post).
  (nd_pre (PERC K_BATCH_CLASS (K24)) 12%nat; intros A24a A24b _ _ _ _ _ _ _ _ _ _; nd_post).
  pose proof (slot_geo L st X K_BATCH_CLASS 0 ALO WF (K24)) as SG0.
  assert (ERI : aregion_info L K_BATCH_CLASS = al_space_beg L + 137438953472 + 3072) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_BATCH_CLASS; lia).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; lia).
  pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM.
  assert (MM8 : c_mapped_user (get_cls st K_BATCH_CLASS) mod 8 = 0).
  { (nd_pre (PERC K_BATCH_CLASS (K24)) 5%nat; intros _ _ _ MU8 _; nd_post). generalize MU8; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia. }
  assert (W6B : 0x2008fff7000 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
             /\ shad (aregion L K_BATCH_CLASS) + shlen K_REGION = shad (aregion L K_BATCH_CLASS + K_REGION)
             /\ shad (aregion L K_BATCH_CLASS + K_REGION) <= 0x10007fff8000).
  { split; [| split; [symmetry; apply shad_add_shlen; generalize RM; clear; intros; Z.div_mod_to_equations; lia|]];
    rewrite !shad_div; unfold ASHOFF, K_REGION; rewrite ER24; generalize SP1 SP2 A24a A24b; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF;
    change (2^37) with 137438953472; change (2^32) with 4294967296; intros; Z.div_mod_to_equations; lia. }
  (nd_pre W6B 3%nat; intros W6LO W6E W6HI; nd_post). rewrite W6E.
  unfold AIMG_HI, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  eapply (disjoint_outside _ a 1); [| clear; lia].
  cbn [disjoint_from fst snd]. unfold AINSTANCE.
  destruct CL as [CL|TL].
  2:{ (* [comment removed for export] *)
      pose proof (ad_tls_t L ALO) as DLT. pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLT, DLR.
      pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
      destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
      4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_res L ALO) as DA2. unfold adisj in DA1, DA2.
          generalize IM OAH OAHI DA1 DA2 SLE LO CEIL TL1 TL2 SP1 SP2 RSP RHI ERI ER24 A24a A24b W6LO W6HI ATR0; clear; intros; repeat split; lia. }
      3:{ unfold AIMSH_LO, AIMSH_LEN in IM. generalize IM SLE LO CEIL TL1 TL2 SP1 SP2 RSP RHI ERI ER24 A24a A24b W6LO W6HI ATR0; clear; intros; repeat split; lia. }
      - generalize T DLT DLR TLN ATR0 TBA SLE LO CEIL TL1 TL2 SP1 SP2 RSP RHI ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
      - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
        assert (SA : shad ATOP <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -ATR0; Z.div_mod_to_equations; lia).
        assert (TSA : shad ta + 1 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                      \/ shad (aregion L K_BATCH_CLASS + 4294967296) <= shad ta).
        { destruct (tls_shadow_apart ta (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                      (4294967296 - c_mapped_user (get_cls st K_BATCH_CLASS)) Hta ltac:(clear -A24a A24b; lia)) as [D|D].
          { destruct DLR as [D|D]; [left; generalize D RSP ER24 A24a A24b; clear; intros; lia
                                   | right; split; [generalize D RSP ER24 A24a A24b SP1 SP2; clear; intros; lia
                                                   | generalize RM MM8; clear; intros; Z.div_mod_to_equations; lia]]. }
          - left; exact D.
          - right. rewrite <- (shad_add_shlen _ (4294967296 - c_mapped_user (get_cls st K_BATCH_CLASS))) in D
              by (generalize RM MM8; clear; intros; Z.div_mod_to_equations; lia).
            replace (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS) + (4294967296 - c_mapped_user (get_cls st K_BATCH_CLASS)))
              with (aregion L K_BATCH_CLASS + 4294967296) in D by (clear; lia). exact D. }
        generalize TS1 TS2 SA TSA SLE LO CEIL TL1 TL2 SP1 SP2 RSP RHI ERI ER24 A24a A24b W6LO W6HI ATR0; clear; intros; repeat split; lia. }
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - (* [comment removed for export] *) generalize ST SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
  - (* [comment removed for export] *)
    (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post).
    pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE, AIMG_HI in *.
    generalize R Q1 Q3 Q7 SLE LO CEIL TL1 TL2 TL4 SP1 SP2 RHI ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    (nd_pre BLK 3%nat; intros [[q|cls] A' n'] Hin R; nd_post); cbn [ab_addr ab_size] in R.
    + destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      * destruct (busy_slot_range' L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        (pose proof (slot_geo L st X (xb_class b) (xb_slot b) ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros _ _ _ P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slot_sep_objects L st X (xb_class b) (xb_slot b) ALO WF HCb HKb) as (BT & _).
        assert (SL5 : aslot_addr L (xb_class b) (xb_slot b) + size_of_class (xb_class b) <= aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS)
                      \/ aregion L K_BATCH_CLASS + 4294967296 <= aslot_addr L (xb_class b) (xb_slot b)).
        { (nd_pre (PERC (xb_class b) HCb) 3%nat; intros Ac1 Ac2 _; nd_post).
          destruct (Z.lt_trichotomy (xb_class b) K_BATCH_CLASS) as [LT|[E24|GT]].
          - left. pose proof (regions_sep L (xb_class b) K_BATCH_CLASS LT) as RS. generalize RS P2 P3 Ac1 Ac2 A24a A24b. clear. unfold K_REGION. change (2^32) with 4294967296. intros. lia.
          - left. generalize P2 P3 A24a A24b. rewrite E24. clear. intros. lia.
          - right. pose proof (regions_sep L K_BATCH_CLASS (xb_class b) GT) as RS. generalize RS P1. clear. unfold K_REGION. change (2^32) with 4294967296. intros. lia. }
        unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
        generalize R FIT P5 P6 P7 P8 BT SL5 SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
      * (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        generalize R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RES RHI RSP SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
    + (nd_pre (proj1 (proj2 BL) cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post).
      generalize R K1 K2 K3 FKO D_t_f D_f_res RES RHI RSP SLE LO CEIL TL1 TL2 SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; intros; repeat split; lia.
  - (* [comment removed for export] *)
    (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
    assert (SHI' : forall x, 0 <= x < 2^47 -> 0x7fff8000 <= shad x /\ shad x + 1 <= 0x10007fff8000) by (intros x Hx; clear - Hx; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    destruct Ha' as [ST | [CIa | FK]].
    + (* [comment removed for export] *)
      atop_facts.
      assert (B1 : shad (aregion L K_BATCH_CLASS + 4294967296) <= shad a') by (apply shad_mono; generalize ST SLE LO CEIL SP2 ER24; clear; intros; lia).
      destruct (SHI' a' ltac:(generalize ST SLE LO CEIL; clear; intros; lia)) as [B2 B3].
      generalize B1 B2 B3 TL1 SP1 ERI ER24 A24a SLE LO CEIL W6LO; clear; intros; repeat split; lia.
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *. unfold AIMG_HI in *.
      assert (B1 : shad a' + 1 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))).
      { rewrite !shad_div. generalize R Q3 SP1 ER24 A24a; clear; intros; Z.div_mod_to_equations; lia. }
      destruct (SHI' a' ltac:(generalize R Q1 Q3; clear; intros; lia)) as [B2 B3].
      generalize B1 B2 B3 TL1 SP1 ERI ER24 A24a SLE LO CEIL W6LO; clear; intros; repeat split; lia.
    + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post).
      assert (B1 : shad a' + 1 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                   \/ shad (aregion L K_BATCH_CLASS + 4294967296) <= shad a').
      { destruct D_f_res as [D|D].
        - left. rewrite !shad_div. generalize D R K1 K3 RSP ER24 A24a RM MM8; clear; intros; Z.div_mod_to_equations; lia.
        - right. apply shad_mono. generalize D R K1 K3 RSP RES SP2 ER24; clear; intros; lia. }
      destruct (SHI' a' ltac:(generalize R K1 K3 FKO; clear; intros; lia)) as [B2 B3].
      generalize B1 B2 B3 TL1 SP1 ERI ER24 A24a SLE LO CEIL W6LO; clear; intros; repeat split; lia.
Qed.
End Zd1.
#[using="CI_OK CI_OK2"] Lemma aheap_pres_refill : ltac:(let t := eval cbv delta [aheap_pres_refill__stmt] in aheap_pres_refill__stmt in exact t).
Proof. exact aheap_pres_refill__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_refill__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  (Q_CACHE < a_qloc_bytes st + (n + 8192) -> a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P AHQ L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P AHQ) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 42).
Variable c : ltac2:(SecDietF.SzSecF.ty 'afree_refill__stmt 43).
Let full := match a_qloc st with [] => false | _ :: _ => true end.
Let bsz := b_size (List.last (a_qloc st) dummy_batch).
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL full bsz"] Lemma afree_refill__body : ltac:(let T := type of (fun (h : afree_refill__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr c) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (tr, c)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE N1 EA CNT0 NOREC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  set (st1 := set_live (delete p (a_live st)) st).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB.AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  pose proof BL as BL0. destruct BL0 as (BH & _).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  destruct (BH p A n HIN) as [(y & Hy & Sy & Uy & Ny)|(mb & msz & Lp & _)]; [| exfalso; rewrite LIVE in Lp; discriminate].
  destruct (BUSY y Hy) as [CLy My]. rewrite Sy in My. (nd_pre My 6%nat; intros _ _ _ _ _ M5; nd_post). rewrite LIVE in M5.
  injection M5 as Cy Ny'. clear Ny'.
  (nd_pre (in_split _ _ Hy) 3%nat; intros l1 l2 XB; nd_post).
  destruct y as [yc yk yn yst yb1 yctx]. cbn in Sy, Uy, Ny, Cy, CLy. subst yst yn yc.
  rename yk into k. rename yb1 into b1. rename yctx into ctx.
  change ({| xb_class := c; xb_slot := k; xb_n := n; xb_st := BLive p; xb_b1 := b1; xb_ctx := ctx |}) with (bfreed p c k n b1 ctx) in XB.
  unfold xb_user, xb_alloc in Uy. cbn [xb_class xb_slot xb_n] in Uy.
  (* [comment removed for export] *)
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros _ N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  destruct (slot_rng L st X c k ALO WF HC KR RNG ARNG) as [RSL RSS].
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 8%nat; intros SE G2 GE G0 GFS SHLO SHHI _; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  set (AB := aslot_addr L c k) in *. set (UB := AB + rz_size n) in *.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; lia).
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CH & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  rewrite CNT0 in CR.
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros HDR [uw HUW] UJR LH SHA SHU SHR; nd_post).
  fold AB in HDR, HUW, UJR, LH, SHA, SHU, SHR. fold UB in HDR, HUW, UJR, LH, SHU, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  (pose proof (read_last AHQ L st X Q m RNG (BLive p) c k n b1 ctx l1 l2 ALO ARNG AR AQ XB ltac:(discriminate) EA) as ndP__; nd_pre ndP__ 6%nat; intros FULL DTL DHL DNL DSL LST64; nd_post).
  cbv zeta in FULL.
  chg (match a_qloc st with [] => false | _ :: _ => true end) full.
  set (lst := qlast L (q_loc Q)) in *.
  chg (b_size (List.last (a_qloc st) dummy_batch)) bsz.
  set (hs := map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb)))) in *.
  assert (FULL' : if full then 0 < Z.of_nat (length (a_qloc st)) /\ rw_cells asegs m lst [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else Z.of_nat (length (a_qloc st)) = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. (nd_pre FULL 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post). repeat (split; [assumption|]). exact F7. }
  (* [comment removed for export] *)
  rewrite (afree_refill_eq st p (CPrim c n) LIVE ltac:(cbn [chunk_size]; exact NQM) EA CNT0). fold st1.
  idtac "CHECKPOINT-A".
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. (pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 3%nat; intros B0 B1 _; nd_post). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (CEIL : ATOP <= lo) by (generalize BOT STK3; clear; intros; lia).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE in *.
  box DT. box DC. box DN. box DSO. box DF. box CL5. box DL7. box DL8. box DL9. box DL10. box DTL. box DHL. box DNL. box DSL.
  eapply implF_evtF.
  { eapply (free_to_refill_spec DI L (q_ia Q) full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) (fhm L c k n) n b1 ctx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz uw _ _ sj hs (block_shadow_bytes n) trt).
    all: rewrite ?EHM.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- if _ then _ else _ => exact FULL'
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ (shad _) _ => eapply rw_cells_addr_eq; [exact SHU| f_equal; lia]
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ - 16 + 16) [C8 _] => eapply rw_cells_addr_eq; [exact HUW| lia]
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, <- Uy; subst AB UB; apply Z_to_bv_eqm; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia] | reflexivity]   (* [comment removed for export] *)
         | |- _ \/ _ => first [unboxed DT | unboxed DC | unboxed DN | unboxed DSO | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10
                             | unboxed DTL | unboxed DHL | unboxed DNL | unboxed DSL
                             | ub DT; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DC; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DN; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DSO; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DTL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DHL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DNL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia) | ub DSL; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear -Y; intros; lia)
                             | ub DT; lia | ub DC; lia | ub DN; lia | ub DSO; lia | ub DTL; lia | ub DHL; lia | ub DNL; lia | ub DSL; lia]
         | |- rng _ (shad _) _ => replace (UB - 16 + 16) with UB by (clear; lia); eapply rng_sub; [exact RSS| rewrite SE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| rewrite SE, GE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSL| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)] | eapply rng_sub; [exact RCTX| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)| (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia)] | eapply rng_sub; [exact RSL| lia| lia] | eapply rng_sub; [exact RCTX| lia| lia] | solve_rng]
         end.
    all: try assumption.
    all: unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia).
    all: try (tclr_solve ALO ltac:((pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ SG5 SG6 _; nd_post);
                                    unfold K_SPACE_SIZE in SG6; change (2^37) with 137438953472 in SG6;
                                    generalize SG5 SG6 ABHM UBS RUP N0 N1; subst UB AB; clear; intros; lia)).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PTR.
  pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst 0 bsz hs trt l1 l2
              ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1) as MIDI.
  rewrite EHM in MIDI. specialize (MIDI PTR). (nd_pre MIDI 4%nat; intros ARm BLm FKm HPm; nd_post).
  unfold free_to_refill_post in PTR.
  (nd_pre PTR 18%nat; intros id t0a t1a t2a a4a a5a a6a a7a t3a t4a t5a t6a m1 sj1 tb1 junk2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 22%nat; intros MUf WMf MIf STf IDR HD1 FC1 SH1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 SS1 TB1 LTB1 FRS1 FRP1 FRE1 LBS1 DEP1; nd_post).
  cbn [ms_mem MS] in ARm, FKm, HPm.
  idtac "CHECKPOINT-B".
  (* [comment removed for export] *)
  set (Q1 := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)) in *.
  set (X1 := xquar X c k n b1 ctx l1 l2) in *.
  eapply (REFILL Q1 _ (KB (CPrim c n)) _ L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st1 X1 K_BATCH_CLASS lo).
  all: try lazymatch goal with
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => (* [comment removed for export] *)
           apply (arng_st L RNG st st1); [intros; reflexivity| reflexivity| apply (sec_chunks_free st p c n); [exact LIVE| reflexivity| apply Permutation_refl]| exact ARNG]
       | |- AREP _ _ _ _ _ => exact ARm
       | |- mem_inv _ _ => exact MIf
       | |- stk _ _ _ _ => rewrite unsigned_lit by (first [clear -SP47 LO BOT STK3; lia | lia]); exact STf     (* [comment removed for export] *)
       | |- @eq word _ _ => first [exact TP | reflexivity | unfold acache_addr, K_BATCH_CLASS; apply Z_to_bv_eqm; first [clear; lia | lia] | unfold AINSTANCE; reflexivity]
       | |- _ <= K_BATCH_CLASS < _ => exact (K24)
       | |- c_count _ = 0 => exact CNT0
       | |- _ <= _ => first [exact CEIL | rewrite ?unsigned_lit by (first [clear -SP47 LO BOT STK3; lia | lia]); first [clear -SP47 LO BOT STK3; lia | lia]]
       | |- rng _ _ _ => rewrite unsigned_lit by (first [clear -SP47 LO BOT STK3; lia | lia]); eapply rng_sub; [exact RSTK| first [clear -SP47 LO BOT STK3; lia | lia]| first [clear -SP47 LO BOT STK3; lia | lia]]
       end.
  all: match goal with |- forall _ _ _ _, refill_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => idtac | |- ?G => idtac "REMR" G end.
  intros st_r X' RNG' ms' RR. unfold refill_ret in RR.
  (nd_pre RR 17%nat; intros FPLE t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 20%nat; intros MUr WMr MIr STr ARr ARNGr CINr CNTr MAXr XBr XCr LIVEr NEXTr QLr QBr QGr QGBr NSECr NRESr GCr; nd_post).
  rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
  idtac "CHECKPOINT-C".
  (* [comment removed for export] *)
  assert (EAr : enq_is_app st_r = false) by (unfold enq_is_app; rewrite QLr; exact EA).
  (pose proof (enq_new_core (CPrim c n) st_r) as ndP__; nd_pre ndP__ 7%nat; intros _ NG1 NG2 _ NL1 NL2 _; nd_post). cbn [chunk_size] in NL1, NL2.
  assert (ENr : st_enq st_r (CPrim c n) = enq_new st_r (CPrim c n)).
  { unfold st_enq. destruct (enq_app st_r (CPrim c n)) as [s'|] eqn:E; [| reflexivity]. exfalso.
    assert (EA1 : enq_is_app st_r = true) by (apply (proj2 (enq_is_app_spec st_r (CPrim c n))); eexists; exact E). congruence. }
  assert (NORECr : Q_CACHE < a_qloc_bytes (st_enq st_r (CPrim c n)) -> a_qglob_bytes (st_enq st_r (CPrim c n)) + a_qloc_bytes (st_enq st_r (CPrim c n)) <= Q_MAX).
  { rewrite ENr, NG2, NL2, QBr, QGBr. change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES. generalize NOREC; clear; intros; lia. }
  rewrite (KB_apop_eq st_r (CPrim c n) EAr NORECr).
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x38360)) with (Z_to_bv 64 0x38360) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2' G3 G4 G5 G6 G7 G8 R8 M8; nd_post). fold AB in AL16, G1, G2', G5, G6, G7, G8.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ad_t_res L ALO) as D_t_res. unfold adisj in D_t_res.
  pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in RES. pose proof (ao_space L ALO) as RSP.   (* [comment removed for export] *)
  (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros A24a A24b _; nd_post).
  assert (ERI : aregion_info L K_BATCH_CLASS = al_space_beg L + 137438953472 + 3072) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_BATCH_CLASS; lia).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; lia).
  assert (SLW5 : AB + size_of_class c <= aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS) \/ aregion L K_BATCH_CLASS + K_REGION <= AB).
  { (nd_pre (PERC c HC) 3%nat; intros Ac1 Ac2 _; nd_post).
    destruct (Z.lt_trichotomy c K_BATCH_CLASS) as [LT|[E24|GT]].
    - left. pose proof (regions_sep L c K_BATCH_CLASS LT) as RS. generalize RS G2' G3 Ac1 Ac2 A24a A24b. clear. unfold K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. intros. lia.
    - left. generalize G2' G3 A24a A24b. rewrite E24. clear. intros. lia.
    - right. pose proof (regions_sep L K_BATCH_CLASS c GT) as RS. generalize RS G1. clear. intros. lia. }
  assert (UB8 : UB mod 8 = 0) by (generalize UB16; clear; intros; Z.div_mod_to_equations; lia).
  assert (SLW6 : shad UB + shlen (rup n 8) <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
              \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad AB).
  { pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM. destruct SLW5 as [D|D].
    - left. apply shad_sep; [| exact UB8]. generalize D UBS; clear; intros; lia.
    - right. apply shad_sep; [exact D| generalize RM; clear; intros; Z.div_mod_to_equations; lia]. }
  assert (W6B : 2199023255552 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
             /\ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= 17594333495296).
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_REGION. rewrite ER24. generalize SP1 SP2 A24a A24b. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. change (2^37) with 137438953472. change (2^32) with 4294967296. change (2^41) with 2199023255552. intros. Z.div_mod_to_equations. lia. }
  destruct W6B as [W6LO W6HI].
  word_range sp SPR.
  change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS) in MUr.
  (* [comment removed for export] *)
  lazymatch type of MUr with munch ?W _ _ =>
    assert (KHI : forall Ad sz, bv_unsigned sp + -2272 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz H1 H2; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize H1 H2 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KIM : forall Ad sz, 0xafc00 <= Ad -> Ad + sz <= 0x13e490 -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz H1 H2 H3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize H1 H2 H3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KCH : forall Ad sz, AB <= Ad -> Ad + sz <= UB + rup n 8 -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz H1 H2 H3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      pose proof DT as DT'; unbox DT'; pose proof SLW5 as SL5;
      generalize H1 H2 H3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR DT' SL5 G6 G7 UBS ABUB; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KSH : disjoint_from W (shad UB) (shlen (rup n 8)));
    [ cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION; pose proof SLW6 as SL6;
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR SL6 SHLO SHHI SE GE GFS G0 G2; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |]
  end.
  (* [comment removed for export] *)
  rewrite EHM in HD1, FC1, SH1.
  eapply (cells_frame _ m1 m') in HD1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; generalize ABUB RUP N1; clear; intros; lia].
  eapply (cells_frame _ m1 m') in FC1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; generalize ABUB RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia].
  eapply (cells_frame _ m1 m') in SH1; [| exact MUr | exact WMr | replace (UB - 16 + 16) with UB by (clear; lia); match goal with |- disjoint_from _ _ ?z => replace z with (shlen (rup n 8)) by (cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id; [reflexivity| generalize G0; clear; intros; lia]) end; exact KSH].
  (* [comment removed for export] *)
  clear STATS1 LSJ1 UW1.
  eapply (cells_frame _ m1 m') in FL1; [| exact MUr | exact WMr | apply KIM; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (stk_transport_disjoint _ _ m1 m') in IAS1; [| exact MUr | exact WMr | apply KIM; clear; lia].
  eapply (cells_frame _ m1 m') in SS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (u64arr_frame _ m1 m') in TB1; [| exact MUr | exact WMr | apply KHI; rewrite ?LTB1; clear; cbn; lia].
  eapply (cells_frame _ m1 m') in FRS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRP1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRE1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros i Hi. apply MUr. rewrite length_le8 in Hi. rewrite wa_unsigned by lia.
    eapply disjoint_outside; [apply (KIM (0xafc08 + 8 * j) 8); generalize Hj; clear; intros; lia| generalize Hi; clear; intros; lia]. }
  clear IAM1.
  idtac "CHECKPOINT-C2".
  (* [comment removed for export] *)
  pose proof ARr as AR0. (nd_pre AR0 11%nat; intros WFr RTr INSTr THRr CLSr HQr HSr HDr HROr HRT2r AVLr; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQm] in HQr, HSr, HDr.
  assert (XB' : x_busy X' = l1 ++ bany BQuar c k n b1 ctx :: l2) by (rewrite XBr; reflexivity).
  (nd_pre THRr 6%nat; intros T0r T40r CACHESr CSTATSr [sjr [STATSr LSJr]] UNWr; nd_post).
  destruct (junk_split m' (al_t L + 2768) 16 16 CSTATSr ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m' (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m' _ CS8) as [stj' STSr].
  assert (POSr : 0 < c_count (get_cls st_r K_BATCH_CLASS)) by (rewrite CNTr; exact MAXr).
  (nd_pre (read_ek_new (AHQm Q1) L st_r X' Q1 m' RNG' BQuar c k n b1 ctx l1 l2 ALO ARNGr ARr HQr XB' ltac:(discriminate) stj' EAr POSr STSr) 15%nat; intros k24 chunks EK ES ED EB NK NB KK NIB JK FSH CIN _ EKE; nd_post).
  pose proof HQr as AQr. (nd_pre AQr 6%nat; intros [QKr MXr] [QCr ABLr] [GCQr ABGr] (FLr & IASr & IAMr) CPr NUMr; nd_post).
  (nd_pre (read_dk (AHQm Q1) L st_r X' Q1 m' RNG' BQuar c k n b1 ctx l1 l2 ALO ARNGr ARr HQr XB' ltac:(discriminate)
              (abatch_addr L k24) (n + 8192) (ek_of L st_r X' Q1 n k24 stj' chunks) ltac:(lia)
              ltac:(right; exists k24; split; [reflexivity|]; split; [exact KK| exact NIB])
              ltac:(rewrite ENr, NG2, NL2 in NORECr; generalize NORECr; clear; unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES; intros; lia) EB) 4%nat; intros DK DS GL GLST; nd_post).
  set (ek := ek_of L st_r X' Q1 n k24 stj' chunks) in *.
  set (g := g_of L st_r Q1 (n + 8192)) in *.
  idtac "CHECKPOINT-D".
  (* [comment removed for export] *)
  destruct (any_range L st_r X' BQuar c k n b1 ctx l1 l2 XB' WFr) as [HCr KRr].
  destruct (slot_rng L st_r X' c k ALO WFr HCr KRr RNG' ARNGr) as [RSLr RSSr]. fold AB in RSLr, RSSr.
  pose proof ARNGr as AG0. (nd_pre AG0 6%nat; intros RIMGr RT4r RCTXr RNOr RSTOr _; nd_post).
  pose proof ARNGr as AG1. (nd_pre AG1 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ RTLSr; nd_post).      (* [comment removed for export] *)
  pose proof (rng_fp_le _ _ _ _ FPLE RSTK) as RSTKr.
  assert (BLr : ablocks L st_r X' (lb_remove p LB)) by (apply (ablocks_xbusy L (set_live (delete p (a_live st)) st) st_r X1); [exact XBr | exact LIVEr | exact BLm]).
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_dtls L ALO) as DTO. unfold aobj in DTO.
  unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in FKO, DTO.   (* [comment removed for export] *)
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKr : AFK L (lb_remove p LB) m').
  { eapply (hf_frame _ HL L (lb_remove p LB) m1 m'); [exact FKm | exact MUr | exact WMr |].
    unfold fake_untouched. unfold AINSTANCE, K_REGION.
    assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                   \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad (al_fake L))).
    { destruct D_f_res as [D|D].
      - left. apply shad_sep; [| generalize FKO; clear; intros; Z.div_mod_to_equations; lia]. rewrite ER24. generalize D RSP A24a; clear; intros; lia.
      - right. apply shad_sep; [| pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM; generalize RM; clear; intros; Z.div_mod_to_equations; lia].
        rewrite ER24. unfold K_REGION. generalize D RSP RES; clear; atop_facts; intros; lia. }
    unfold K_REGION in SHF.
    repeat (apply Forall_cons; [cbn [fst snd];
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR FKO DTO D_f_res D_t_f D_d_res D_t_d RES RHI RSP SHF; clear;
      unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296;
      rewrite ?shad_div, ?shlen_div; unfold ASHOFF; intros; repeat split; fu_focus; Z.div_mod_to_equations; lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  clear D_f_res D_t_f D_d_res D_t_d D_t_res.
  idtac "CHECKPOINT-D2".
  rewrite <- EHM in HD1, FC1, SH1.
  pose proof EK as EK0. pose proof ES as ES0. pose proof DK as DK0.
  rewrite EKE in EK, ES, DK. cbn [ek_pre] in EK.
  (nd_pre EK 20%nat; intros FULLr SBr CRr CHr LCHr CNTr' NTHr IXSr STSr' HBr BJr SBPr B0r BL1r DTBr DTLr DBLr DHBr DHLr RBr; nd_post).
  box DTBr. box DTLr. box DBLr. box DHBr. box DHLr.
  pose proof ES as ES1. cbn [ek_seps] in ES1. (nd_pre ES1 4%nat; intros SB1r SB2r SB3r SLr; nd_post).
  assert (DHL24 : fhm L c k n + 24 <= qlast L (q_loc Q1) \/ qlast L (q_loc Q1) + 8192 <= fhm L c k n).
  { destruct (a_qloc st_r); [destruct FULLr as [_ E0]; rewrite E0; right; generalize HLO EHM; clear; intros; lia | exact (proj1 (SLr eq_refl))]. }
  box SB1r. box DHL24.
  assert (NBr : 0 <= Z.of_nat (length (a_qloc st_r)) < 2^62) by (rewrite QLr; change (a_qloc st1) with (a_qloc st); generalize LLB NC; clear; unfold Q_BATCH_BYTES; intros; lia).
  assert (QB0r : 0 <= a_qloc_bytes st_r) by (rewrite QBr; change (a_qloc_bytes st1) with (a_qloc_bytes st); generalize LLB; clear; unfold Q_BATCH_BYTES; intros; lia).
  (* [comment removed for export] *)
  eapply evtF_mono.
  { lazymatch type of EKE with _ = EkNew ?fu ?nx ?bs ?cn ?mx ?cz ?sj0 ?ix ?chs ?sb ?bb ?hs0 =>
      eapply (free_from_refill_spec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
                (al_t L) (fhm L c k n) n b1 ctx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
                nx bs cn sb id bb mx cz sj0 ix sjr tb1 chs hs0 junk2 j0 trt)
    end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact STr | exact IAS1]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MIr
         | |- ADEPOT _ _ _ => exact HDr
         | |- u64arr _ _ (_ + 2800) _ => exact STATSr
         | |- u64arr _ _ _ _ => first [exact TB1 | exact CHr]
         | |- if _ then _ else _ => exact FULLr
         | |- forall j, _ -> bytes_at _ _ _ _ => exact IAM2
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH1
         | |- rw_cells _ _ (aq_tcache _) _ => exact QCr
         | |- rw_cells _ _ (_ + 80) _ => exact QCr
         | |- rw_cells _ _ (_ + 2128) _ => exact CRr
         | |- rw_cells _ _ (_ + 2784) _ => exact STSr'
         | |- rw_cells _ _ (_ + 3168) _ => exact UNWr
         | |- rw_cells _ _ (_ + -72) _ => exact FRS1
         | |- rw_cells _ _ (_ + -2128) _ => exact SS1
         | |- rw_cells _ _ (_ + -2208) _ => exact FRP1
         | |- rw_cells _ _ (_ + -2272) _ => exact FRE1
         | |- rw_cells _ _ (fhm _ _ _ _ + 16) _ => exact FC1
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact QKr
         | |- nth_error _ _ = _ => exact NTHr
         | |- @eq Z _ _ => exact HBr
         | |- ex _ => exact BJr
         | |- _ + 24 <= al_t _ \/ _ => pose proof DT as DT2; unbox DT2; generalize DT2 EHM S8 ABUB RUP N1; clear; intros; lia
         | |- _ \/ _ => first [unboxed DTBr | unboxed DTLr | unboxed DBLr | unboxed SB1r | unboxed DHL24 | unboxed DT | unboxed DL7 | unboxed DL8]
         | |- rng _ (shad _) _ => replace (fhm L c k n + 16) with UB by (generalize EHM; clear; intros; lia); eapply rng_sub; [exact RSSr| rewrite SE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| rewrite SE, GE; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]
         | |- rng _ (fhm _ _ _ _) _ => eapply rng_sub; [exact RSLr| first [generalize EHM; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| first [generalize EHM; (generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSTKr| first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]| first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia]]]
         end.
    all: try assumption.
    all: try (unfold Q_MAX, Q_BATCH_BYTES; rewrite ?QLr, ?QBr; change (a_qloc st1) with (a_qloc st); change (a_qloc_bytes st1) with (a_qloc_bytes st);
              generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM UBS S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B10 LLB NC NM LF64 LST64 RA4 IDR EHM; clear; intros; lia).
    all: try (rewrite ?EHM; tclr_solve ALO ltac:((pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ SG5 SG6 _; nd_post);
                                    unfold K_SPACE_SIZE in SG6; change (2^37) with 137438953472 in SG6;
                                    generalize SG5 SG6 ABHM UBS RUP N0 N1; subst UB AB; clear; intros; lia)).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMT" G end. }
  cbv beta. intros msf PF.
  idtac "CHECKPOINT-E".
  rewrite <- EKE in PF.
  pose proof ARm as ARm0. destruct ARm0 as [WFm _].
  assert (DK1 : dk_pre ek (g_of L st_r Q1 (ek_delta ek n)) RNG' (al_t L) (qlast L (q_loc Q1)) (fhm L c k n) (a_qloc_bytes st_r + ek_delta ek n) m') by (rewrite ED; exact DK0).
  assert (PF1 : free_fast_post DI L ek (g_of L st_r Q1 (ek_delta ek n)) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n
                  (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r) b1 ctx lo m' msf) by (rewrite ED; exact PF).
  (pose proof (STORE_R L RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' st_r (lb_remove p LB) X' Q1 c k n b1 ctx lo k24 l1 l2 stj' chunks
                ALO ARNGr ARr BLr FKr XB' N1 (ex_intro _ (q_pend Q) eq_refl) EAr NK NB KK NIB JK FSH CIN POSr NORECr EK0 DK1 CEIL LO msf PF1) as ndP__; nd_pre ndP__ 17%nat; intros t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f mf ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MIf2 STf2 HPf AHf; nd_post).
  unfold afree_post. split; [exact FPLE|].
  exists t0f, t1f, t2f, a0f, a1f, a2f, a3f, a4f, a5f, a6f, a7f, t3f, t4f, t5f, t6f, mf.
  split; [reflexivity|]. split; [exact MIf2|]. split; [exact STf2|]. split; [| exact AHf].
  eapply aheap_pres_trans; [exact HPm|]. eapply aheap_pres_trans; [| exact HPf].
  eapply (aheap_pres_refill L st1 X1 (lb_remove p LB) sp (bv_unsigned sp + -2272) lo m1 m');
    [exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia].
Qed.
End Zd2.
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL"] Theorem afree_refill : ltac:(let t := eval cbv delta [afree_refill__stmt] in afree_refill__stmt in exact t).
Proof. exact afree_refill__body. Qed.
End S.
End CANSEC1.
End TwB.
End F_afree_arepR.

(* [comment removed for export] *)
Module ASF_refill.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_read. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Local Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Local Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Local Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
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

#[using="Type"] Lemma sec_same0_of : forall st st', sec_same st st' -> sec_same0 st st'.
Proof.
  intros st st' (EN & ER & EP & EL & _). split; [exact EN|]. split; [exact ER|]. split; [exact EP|].
  intros [c n0|mb ms n0] Hs; [discriminate|]. unfold sec_live. split; intros [q Hq]; exists q; [apply (proj1 (EL q mb ms n0)); exact Hq| apply (proj2 (EL q mb ms n0)); exact Hq].
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

(* [comment removed for export] *)
Definition AHSm (cs : list achunk) (Q1 : qconc) : aholes :=
  mkAHoles (fun L s X m => AQUAR_at L s X Q1 m) (ASECc cs) (ADEPOT DI) AFK.

#[using="HL"] Lemma AHSm_laws : forall cs Q1, ahole_laws (AHSm cs Q1).
Proof.
  intros cs Q1. destruct HL as [HQF HSF HDF HFF HFB].
  constructor; cbn [ah_quar ah_sec ah_depot ah_fake AHSm OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.AHQ] in *; try assumption.
  - intros L st st' X X' m m' W AQ MU WM UT QS. exact (AQUAR_frame_at L st st' X X' Q1 m m' W AQ MU WM UT QS).
  - intros L st st' X X' m m' W AS MU WM SU SS. eapply asecc_frame; [exact AS| exact MU| exact WM| exact SU| apply sec_same0_of; exact SS].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mid_stmtS : Prop :=
  forall (L : alayout) (RNG : footprint) (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo lst nx bsz : Z)
         (hs : list word) (tr : list Z),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let Q1 := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms1,
    free_to_refill_post DI L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n b1 ctx lo lst nx bsz hs tr m ms1 ->
       AREP (AHSm (sec_chunks_of st) Q1) L st1 X (ms_mem ms1)
    /\ ablocks L st1 X (lb_remove p LB) /\ AFK L (lb_remove p LB) (ms_mem ms1)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m (ms_mem ms1).

(* [comment removed for export] *)
Definition store_freeRS_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (cs : list achunk) (mb ms n b1 ctx lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHSm cs Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  Permutation cs (ch :: sec_chunks_of s) -> RSEC cs RNG -> ~ sec_live s ch -> n <= Q_MAX ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  (Q_CACHE < a_qloc_bytes sq -> a_qglob_bytes sq + a_qloc_bytes sq <= Q_MAX) ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n hm m ->
  dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms',
    free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                   (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms' ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
      /\ AHEAP_P (AHQ DI ASEC_of AFK) L RNG (st_after sq) LB m'.

Hypothesis MID : mid_stmtS.
Hypothesis STORE_R : store_freeRS_stmt.
(* [comment removed for export] *)
Hypothesis REFILL : forall cs Q1, refill_stmt (AHSm cs Q1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_sec_refill__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  (Q_CACHE < a_qloc_bytes st + (n + 8192) -> a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) <= Q_MAX) ->
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 42).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 43).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 44).
Let hm := mb + 6128.
Let full := match a_qloc st with [] => false | _ :: _ => true end.
Let bsz := b_size (List.last (a_qloc st) dummy_batch).
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL hm full bsz"] Lemma afree_sec_refill__body : ltac:(let T := type of (fun (h : afree_sec_refill__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (tr, (mb, ms))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NQM EA CNT0 NOREC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  set (st1 := set_live (delete p (a_live st)) st).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EAu _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_r SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahmx; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 B1 B3 CX HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  chg (mb + 6128) hm.
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in RES.   (* [comment removed for export] *)
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  (pose proof (rup8_facts n ltac:(clear -NB; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad (hm + 16) = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ hm + 16 + rup n 8 <= mb + ms
                  /\ 2148238848 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst hm. rewrite !shad_div, RUPS. unfold ASHOFF. (pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 6%nat; intros SHE SHL SHP UBS SHLO SHHI; nd_post).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (HM0' : ablk hm (hm + 24)) by (subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB; lia]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (HMSEPg : forall s Xs, awf L s Xs -> forall kk, 0 <= kk < ndist s K_BATCH_CLASS -> hm + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= hm).
  { intros s Xs WFs kk KK. (nd_pre WFs 7%nat; intros _ _ _ _ _ PERCs _; nd_post).
    (nd_pre (PERCs K_BATCH_CLASS (K24)) 3%nat; intros Q1' Q2' _; nd_post).
    (pose proof (slot_in_region L s K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1') KK) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 _; nd_post).
    rewrite size_of_class_24 in P4. subst hm. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1' Q2' RSP SC_r MSB. lia. }
  pose proof (HMSEPg st X WF) as HMSEP.
  (* [comment removed for export] *)
  assert (IN : In (CSec mb ms n) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
  pose proof (proj1 (Forall_forall _ _) RSECS _ IN) as [RMB RSH]. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CHc & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  rewrite CNT0 in CR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  (pose proof (read_lastS (AHQ DI ASEC_of AFK) L st X Q m RNG hm ALO ARNG AR AQ HM0' HMSEP EA) as ndP__; nd_pre ndP__ 6%nat; intros FULL DTL DHL DNL DSL LST64; nd_post).
  cbv zeta in FULL.
  chg (match a_qloc st with [] => false | _ :: _ => true end) full.
  set (lst := qlast L (q_loc Q)) in *.
  chg (b_size (List.last (a_qloc st) dummy_batch)) bsz.
  set (hs := map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb)))) in *.
  assert (FULL' : if full then 0 < Z.of_nat (length (a_qloc st)) /\ rw_cells asegs m lst [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else Z.of_nat (length (a_qloc st)) = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. (nd_pre FULL 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post). repeat (split; [assumption|]). exact F7. }
  (* [comment removed for export] *)
  rewrite (afree_refill_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; exact NQM) EA CNT0). fold st1.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. (pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 3%nat; intros B0 B1' _; nd_post). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (CEIL : ATOP <= lo) by (generalize BOT STK3; clear; intros; lia).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  (* [comment removed for export] *)
  box SC_t. box SC_c. box SC_r. box SC_p. box SC_n. box SC_st. box SC_f. box SC_d. box CL5. box DL7. box DL8. box DL9. box DL10. box DTL. box DHL. box DNL. box DSL.
  eapply implF_evtF.
  { eapply (free_to_refill_spec DI L (q_ia Q) full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz uw _ _ sj hs (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- if _ then _ else _ => exact FULL'
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EAu; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10 | unboxed DTL | unboxed DHL | unboxed DNL | unboxed DSL
                             | ub SC_t; clear -Y MSB; subst hm; lia | ub SC_c; clear -Y MSB; subst hm; lia | ub SC_n; clear -Y MSB; subst hm; lia | ub SC_st; clear -Y MSB; subst hm; lia]
         | |- rng _ (shad _) _ => rewrite SHE; eapply rng_sub; [exact RSH| clear; lia| clear -SHL; lia]
         | |- rng _ _ 24 => subst hm; eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => subst hm; unfold tclr; clear -SC_tls MSB; lia
         end.
    all: try assumption.
    all: subst hm; unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize NB N6 NMS NQM MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MAL MSAL RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B1 CX LLB NC NM LF64 LST64 RA4 RUP; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PTR.
  (pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 cx A lo lst 0 bsz hs trt
              ALO ARNG AR AQ BL HFK LIVE HIN NQM H5 B1 B3 CX CEIL LO ms1 PTR) as ndP__; nd_pre ndP__ 4%nat; intros ARm BLm FKm HPm; nd_post).
  unfold free_to_refill_post in PTR.
  (nd_pre PTR 18%nat; intros id t0a t1a t2a a4a a5a a6a a7a t3a t4a t5a t6a m1 sj1 tb1 junk2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 22%nat; intros MUf WMf MIf STf IDR HD1 FC1 SH1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 SS1 TB1 LTB1 FRS1 FRP1 FRE1 LBS1 DEP1; nd_post).
  cbn [ms_mem MS] in ARm, FKm, HPm.
  (* [comment removed for export] *)
  set (Q1 := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)) in *.
  assert (PD1 : Permutation (CSec mb ms n :: sec_chunks_of st1) (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st1 p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  eapply (REFILL (sec_chunks_of st) Q1 _ (KB (CSec mb ms n)) _ L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st1 X K_BATCH_CLASS lo).
  all: try lazymatch goal with
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => apply (arng_sub L RNG st st1); [intros; reflexivity| reflexivity| intros cc Hcc; eapply Permutation_in; [exact PD1| right; exact Hcc]| exact ARNG]
       | |- AREP _ _ _ _ _ => exact ARm
       | |- mem_inv _ _ => exact MIf
       | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact STf
       | |- @eq word _ _ => first [exact TP | reflexivity | unfold acache_addr, K_BATCH_CLASS; f_equal; clear; lia | unfold AINSTANCE; reflexivity]
       | |- _ <= K_BATCH_CLASS < _ => exact (K24)
       | |- c_count _ = 0 => exact CNT0
       | |- _ <= _ => first [exact CEIL | rewrite ?unsigned_lit by lia; lia]
       | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub; [exact RSTK| lia| lia]
       end.
  all: match goal with |- forall _ _ _ _, refill_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => idtac | |- ?G => idtac "REMR" G end.
  intros st_r X' RNG' ms' RR. unfold refill_ret in RR.
  (nd_pre RR 17%nat; intros FPLE t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 20%nat; intros MUr WMr MIr STr ARr ARNGr CINr CNTr MAXr XBr XCr LIVEr NEXTr QLr QBr QGr QGBr NSECr NRESr GCr; nd_post).
  rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
  (* [comment removed for export] *)
  assert (EAr : enq_is_app st_r = false) by (unfold enq_is_app; rewrite QLr; exact EA).
  (pose proof (enq_new_core (CSec mb ms n) st_r) as ndP__; nd_pre ndP__ 7%nat; intros _ NG1 NG2 _ NL1 NL2 _; nd_post). cbn [chunk_size] in NL1, NL2.
  assert (ENr : st_enq st_r (CSec mb ms n) = enq_new st_r (CSec mb ms n)).
  { unfold st_enq. destruct (enq_app st_r (CSec mb ms n)) as [s'|] eqn:E; [| reflexivity]. exfalso.
    assert (EA1 : enq_is_app st_r = true) by (apply (proj2 (enq_is_app_spec st_r (CSec mb ms n))); eexists; exact E). congruence. }
  assert (NORECr : Q_CACHE < a_qloc_bytes (st_enq st_r (CSec mb ms n)) -> a_qglob_bytes (st_enq st_r (CSec mb ms n)) + a_qloc_bytes (st_enq st_r (CSec mb ms n)) <= Q_MAX).
  { rewrite ENr, NG2, NL2, QBr, QGBr. change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES. generalize NOREC; clear; intros; lia. }
  rewrite (KB_apop_eq st_r (CSec mb ms n) EAr NORECr).
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x382f8)) with (Z_to_bv 64 0x382f8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. unfold adisj in D_t_res.
  (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros A24a A24b _; nd_post).
  assert (ERI : aregion_info L K_BATCH_CLASS = al_space_beg L + 137438953472 + 3072) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_BATCH_CLASS; lia).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; lia).
  assert (W6B : 2199023255552 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
             /\ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= 17594333495296).
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_REGION. rewrite ER24. generalize SP1 SP2 A24a A24b. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. change (2^37) with 137438953472. change (2^32) with 4294967296. change (2^41) with 2199023255552. intros. Z.div_mod_to_equations. lia. }
  destruct W6B as [W6LO W6HI].
  (* [comment removed for export] *)
  assert (SLW5 : mb + ms <= aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS) \/ aregion L K_BATCH_CLASS + K_REGION <= mb).
  { rewrite ER24. unfold K_REGION. ub SC_r. destruct Y as [D|D]; [left| right]; generalize D RSP RES RHI A24a A24b; clear; unfold K_FREEARR_OFF; intros; lia. }
  assert (SLW6 : shad (hm + 16) + shlen (rup n 8) <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
              \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad (hm + 16)).
  { pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM. destruct SLW5 as [D|D].
    - left. rewrite SHE. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. generalize HH SHL; clear; intros; lia.
    - right. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| generalize RM; clear; intros; Z.div_mod_to_equations; lia]| rewrite SHE; clear; lia]. }
  word_range sp SPR.
  change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS) in MUr.
  (* [comment removed for export] *)
  lazymatch type of MUr with munch ?W _ _ =>
    assert (KHI : forall Ad sz, bv_unsigned sp + -2272 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz Y1 Y2; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize Y1 Y2 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KIM : forall Ad sz, 0xaf800 <= Ad -> Ad + sz <= 0x13e090 -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz Y1 Y2 Y3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize Y1 Y2 Y3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KCH : forall Ad sz, mb <= Ad -> Ad + sz <= mb + ms -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz Y1 Y2 Y3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION; pose proof SLW5 as SL5; pose proof SC_t as SCT; unbox SCT; pose proof SC_r as SCR; unbox SCR;
      generalize Y1 Y2 Y3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR SCT SCR RSP RES RHI SL5 MLO ML1 ML3 KAM KBM KEM KCM KDM MCE; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KSH : disjoint_from W (shad (hm + 16)) (shlen (rup n 8)));
    [ cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION; pose proof SLW6 as SL6;
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR SL6 SHLO SHHI SHE SHL SHP; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |]
  end.
  (* [comment removed for export] *)
  eapply (cells_frame _ m1 m') in HD1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; subst hm; generalize NMS N6 NB; clear; intros; lia].
  eapply (cells_frame _ m1 m') in FC1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; subst hm; generalize NMS N6 NB; clear; intros; lia].
  eapply (cells_frame _ m1 m') in SH1; [| exact MUr | exact WMr | match goal with |- disjoint_from _ _ ?z => replace z with (shlen (rup n 8)) by (cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id; [reflexivity| generalize SHP; clear; intros; lia]) end; exact KSH].
  clear STATS1 LSJ1 UW1.
  eapply (cells_frame _ m1 m') in FL1; [| exact MUr | exact WMr | apply KIM; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (stk_transport_disjoint _ _ m1 m') in IAS1; [| exact MUr | exact WMr | apply KIM; clear; lia].
  eapply (cells_frame _ m1 m') in SS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (u64arr_frame _ m1 m') in TB1; [| exact MUr | exact WMr | apply KHI; rewrite ?LTB1; clear; cbn; lia].
  eapply (cells_frame _ m1 m') in FRS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRP1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRE1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MUr. rewrite length_le8 in Hi. rewrite wa_unsigned by lia.
    eapply disjoint_outside; [apply (KIM (0xaf808 + 8 * j) 8); generalize Hj; clear; intros; lia| generalize Hi; clear; intros; lia]. }
  clear IAM1.
  (* [comment removed for export] *)
  pose proof ARr as AR0. (nd_pre AR0 11%nat; intros WFr RTr INSTr THRr CLSr HQr HSr HDr HROr HRT2r AVLr; nd_post).
  cbn [ah_quar ah_sec ah_depot AHSm] in HQr, HSr, HDr.
  (nd_pre THRr 6%nat; intros T0r T40r CACHESr CSTATSr [sjr [STATSr LSJr]] UNWr; nd_post).
  destruct (junk_split m' (al_t L + 2768) 16 16 CSTATSr ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m' (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m' _ CS8) as [stj' STSr].
  assert (POSr : 0 < c_count (get_cls st_r K_BATCH_CLASS)) by (rewrite CNTr; exact MAXr).
  pose proof (HMSEPg st_r X' WFr) as HMSEPr.
  (nd_pre (read_ek_newS (AHSm (sec_chunks_of st) Q1) L st_r X' Q1 m' RNG' hm n ALO ARNGr ARr HQr HM0' HMSEPr stj' EAr POSr STSr) 15%nat; intros k24 chunks EK ES ED EB NK NBk KK NIB JKb FSH CIN _ EKE; nd_post).
  pose proof HQr as AQr. (nd_pre AQr 6%nat; intros [QKr MXr] [QCr ABLr] [GCQr ABGr] (FLr & IASr & IAMr) CPr NUMr; nd_post).
  (nd_pre (read_dkS (AHSm (sec_chunks_of st) Q1) L st_r X' Q1 m' RNG' hm ALO ARNGr ARr HQr HMSEPr
              (abatch_addr L k24) (n + 8192) (ek_of L st_r X' Q1 n k24 stj' chunks) ltac:(lia)
              ltac:(right; exists k24; split; [reflexivity|]; split; [exact KK| exact NIB])
              ltac:(rewrite ENr, NG2, NL2 in NORECr; generalize NORECr; clear; unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES; intros; lia) EB) 4%nat; intros DK DS GL GLST; nd_post).
  set (ek := ek_of L st_r X' Q1 n k24 stj' chunks) in *.
  set (g := g_of L st_r Q1 (n + 8192)) in *.
  (* [comment removed for export] *)
  pose proof ARNGr as AG0. (nd_pre AG0 14%nat; intros RIMGr RT4r RCTXr RNOr RSTOr _ _ _ _ _ _ RSECSr _ RTLSr; nd_post).      (* [comment removed for export] *)
  pose proof (rng_fp_le _ _ _ _ FPLE RSTK) as RSTKr. pose proof (rng_fp_le _ _ _ _ FPLE RMB) as RMBr. pose proof (rng_fp_le _ _ _ _ FPLE RSH) as RSHr.
  assert (BLr : ablocks L st_r X' (lb_remove p LB)) by (apply (ablocks_xbusy L st1 st_r X); [exact XBr | exact LIVEr | exact BLm]).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *) pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKr : AFK L (lb_remove p LB) m').
  { eapply (hf_frame _ HL L (lb_remove p LB) m1 m'); [exact FKm | exact MUr | exact WMr |].
    unfold fake_untouched. unfold AINSTANCE, K_REGION.
    assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                   \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad (al_fake L))).
    { destruct D_f_res as [D|D].
      - left. apply shad_sep; [| generalize FKO FKi FBND; clear; intros; Z.div_mod_to_equations; lia]. rewrite ER24. generalize D RSP A24a; clear; intros; lia.
      - right. apply shad_sep; [| pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM; generalize RM; clear; intros; Z.div_mod_to_equations; lia].
        rewrite ER24. unfold K_REGION. generalize D RSP RES RHI; clear; atop_facts; intros; lia. }
    unfold K_REGION in SHF.
    repeat (apply Forall_cons; [cbn [fst snd];
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR FKO FKi FBND DTO DBND DIMG D_f_res D_t_f D_d_res D_t_d RES RHI RSP SHF; clear;
      unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296;
      rewrite ?shad_div, ?shlen_div; unfold ASHOFF; intros; repeat split; fu_focus; Z.div_mod_to_equations; lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  clear D_f_res D_t_f D_d_res D_t_d D_t_res.
  pose proof EK as EK0. pose proof ES as ES0. pose proof DK as DK0.
  rewrite EKE in EK, ES, DK. cbn [ek_pre] in EK.
  (nd_pre EK 20%nat; intros FULLr SBr CRr CHr LCHr CNTr' NTHr IXSr STSr' HBr BJr SBPr B0r BL1r DTBr DTLr DBLr DHBr DHLr RBr; nd_post).
  box DTBr. box DTLr. box DBLr. box DHBr. box DHLr.
  pose proof ES as ES1. cbn [ek_seps] in ES1. (nd_pre ES1 4%nat; intros SB1r SB2r SB3r SLr; nd_post).
  assert (DHL24 : hm + 24 <= qlast L (q_loc Q1) \/ qlast L (q_loc Q1) + 8192 <= hm).
  { destruct (a_qloc st_r); [destruct FULLr as [_ E0]; rewrite E0; right; generalize HM0'; clear; intros HB; (pose proof (ablk_lin _ _ HB) as ndP__; nd_pre ndP__ 4%nat; intros HB1 HB2 HB3 HB4; nd_post); unfold AIMG_HI in HB1; lia | exact (proj1 (SLr eq_refl))]. }   (* [comment removed for export] *)
  box SB1r. box DHL24.
  assert (NBr : 0 <= Z.of_nat (length (a_qloc st_r)) < 2^62) by (rewrite QLr; change (a_qloc st1) with (a_qloc st); generalize LLB NC; clear; unfold Q_BATCH_BYTES; intros; lia).
  assert (QB0r : 0 <= a_qloc_bytes st_r) by (rewrite QBr; change (a_qloc_bytes st1) with (a_qloc_bytes st); generalize LLB; clear; unfold Q_BATCH_BYTES; intros; lia).
  (* [comment removed for export] *)
  eapply evtF_mono.
  { lazymatch type of EKE with _ = EkNew ?fu ?nx ?bs ?cn ?mx ?cz ?sj0 ?ix ?chs ?sb ?bb ?hs0 =>
      eapply (free_from_refill_spec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
                (al_t L) hm n b1 cx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
                nx bs cn sb id bb mx cz sj0 ix sjr tb1 chs hs0 junk2 j0 trt)
    end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact STr | exact IAS1]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0x | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MIr
         | |- ADEPOT _ _ _ => exact HDr
         | |- u64arr _ _ (_ + 2800) _ => exact STATSr
         | |- u64arr _ _ _ _ => first [exact TB1 | exact CHr]
         | |- if _ then _ else _ => exact FULLr
         | |- forall j, _ -> bytes_at _ _ _ _ => exact IAM2
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH1
         | |- rw_cells _ _ (aq_tcache _) _ => exact QCr
         | |- rw_cells _ _ (_ + 80) _ => exact QCr
         | |- rw_cells _ _ (_ + 2128) _ => exact CRr
         | |- rw_cells _ _ (_ + 2784) _ => exact STSr'
         | |- rw_cells _ _ (_ + 3168) _ => exact UNWr
         | |- rw_cells _ _ (_ + -72) _ => exact FRS1
         | |- rw_cells _ _ (_ + -2128) _ => exact SS1
         | |- rw_cells _ _ (_ + -2208) _ => exact FRP1
         | |- rw_cells _ _ (_ + -2272) _ => exact FRE1
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact FC1
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact QKr
         | |- nth_error _ _ = _ => exact NTHr
         | |- @eq Z _ _ => exact HBr
         | |- ex _ => exact BJr
         | |- _ + 24 <= al_t _ \/ _ => ub SC_t; clear -Y MSB; subst hm; lia
         | |- _ \/ _ => first [unboxed DTBr | unboxed DTLr | unboxed DBLr | unboxed SB1r | unboxed DHL24 | unboxed DL7 | unboxed DL8]
         | |- rng _ (shad _) _ => rewrite SHE; eapply rng_sub; [exact RSHr| clear; lia| clear -SHL; lia]
         | |- rng _ _ 24 => subst hm; eapply rng_sub; [exact RMBr| clear; lia| clear -MSB; lia]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSTKr| clear; lia| clear -LO; lia]]
         | |- rng_aimg _ => exact RIMGr
         | |- rng_atls _ => exact RTLSr
         | |- tclr _ 24 => subst hm; unfold tclr; clear -SC_tls MSB; lia      (* [comment removed for export] *)
         end.
    all: try assumption.
    all: try (subst hm; unfold Q_MAX, Q_BATCH_BYTES; rewrite ?QLr, ?QBr; change (a_qloc st1) with (a_qloc st); change (a_qloc_bytes st1) with (a_qloc_bytes st);
              generalize NB N6 NMS NQM MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MAL MSAL RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B1 CX LLB NC NM LF64 LST64 RA4 IDR RUP; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMT" G end. }
  cbv beta. intros msf PF.
  rewrite <- EKE in PF.
  pose proof ARm as ARm0. destruct ARm0 as [WFm _].
  assert (DK1 : dk_pre ek (g_of L st_r Q1 (ek_delta ek n)) RNG' (al_t L) (qlast L (q_loc Q1)) hm (a_qloc_bytes st_r + ek_delta ek n) m') by (rewrite ED; exact DK0).
  assert (PF1 : free_fast_post DI L ek (g_of L st_r Q1 (ek_delta ek n)) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                  (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r) b1 cx lo m' msf) by (rewrite ED; exact PF).
  (* [comment removed for export] *)
  assert (PDr : Permutation (sec_chunks_of st) (CSec mb ms n :: sec_chunks_of st_r)).
  { rewrite (sec_chunks_of_eq st1 st_r LIVEr QLr QGr). apply Permutation_sym. exact PD1. }
  assert (NOTLr : ~ sec_live st_r (CSec mb ms n)).
  { intros [q Hq]. destruct HS as (WFS & _). apply (sec_not_live_after L st _ p mb ms n st1 WFS (Permutation_refl _) LIVE eq_refl). exists q. rewrite <- LIVEr. exact Hq. }
  assert (RSCSr : RSEC (sec_chunks_of st) RNG') by (eapply RSEC_mono; [exact FPLE| exact RSECS]).
  (pose proof (STORE_R L RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' st_r (lb_remove p LB) X' Q1 (sec_chunks_of st) mb ms n b1 cx lo k24 stj' chunks
                ALO ARNGr ARr BLr FKr PDr RSCSr NOTLr NQM B1 B3 CX EAr NK NBk KK NIB JKb FSH CIN POSr NORECr EK0 DK1 CEIL LO msf PF1) as ndP__; nd_pre ndP__ 17%nat; intros t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f mf ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MIf2 STf2 HPf AHf; nd_post).
  unfold afree_post. split; [exact FPLE|].
  exists t0f, t1f, t2f, a0f, a1f, a2f, a3f, a4f, a5f, a6f, a7f, t3f, t4f, t5f, t6f, mf.
  split; [reflexivity|]. split; [exact MIf2|]. split; [exact STf2|]. split; [| exact AHf].
  eapply aheap_pres_trans; [exact HPm|]. eapply aheap_pres_trans; [| exact HPf].
  eapply (aheap_pres_refill CI CI_OK CI_OK2 L st1 X (lb_remove p LB) sp (bv_unsigned sp + -2272) lo m1 m');
    [exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia].
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL"] Theorem afree_sec_refill : ltac:(let t := eval cbv delta [afree_sec_refill__stmt] in afree_sec_refill__stmt in exact t).
Proof. exact afree_sec_refill__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Local Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Local Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Local Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
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

#[using="Type"] Lemma sec_same0_of : forall st st', sec_same st st' -> sec_same0 st st'.
Proof.
  intros st st' (EN & ER & EP & EL & _). split; [exact EN|]. split; [exact ER|]. split; [exact EP|].
  intros [c n0|mb ms n0] Hs; [discriminate|]. unfold sec_live. split; intros [q Hq]; exists q; [apply (proj1 (EL q mb ms n0)); exact Hq| apply (proj2 (EL q mb ms n0)); exact Hq].
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

(* [comment removed for export] *)
Definition AHSm (cs : list achunk) (Q1 : qconc) : aholes :=
  mkAHoles (fun L s X m => AQUAR_at L s X Q1 m) (ASECc cs) (ADEPOT DI) AFK.

#[using="HL"] Lemma AHSm_laws : forall cs Q1, ahole_laws (AHSm cs Q1).
Proof.
  intros cs Q1. destruct HL as [HQF HSF HDF HFF HFB].
  constructor; cbn [ah_quar ah_sec ah_depot ah_fake AHSm OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB.AHQ] in *; try assumption.
  - intros L st st' X X' m m' W AQ MU WM UT QS. exact (AQUAR_frame_at L st st' X X' Q1 m m' W AQ MU WM UT QS).
  - intros L st st' X X' m m' W AS MU WM SU SS. eapply asecc_frame; [exact AS| exact MU| exact WM| exact SU| apply sec_same0_of; exact SS].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mid_stmtS : Prop :=
  forall (L : alayout) (RNG : footprint) (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo lst nx bsz : Z)
         (hs : list word) (tr : list Z),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let Q1 := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms1,
    free_to_refill_post DI L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n b1 ctx lo lst nx bsz hs tr m ms1 ->
       AREP (AHSm (sec_chunks_of st) Q1) L st1 X (ms_mem ms1)
    /\ ablocks L st1 X (lb_remove p LB) /\ AFK L (lb_remove p LB) (ms_mem ms1)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m (ms_mem ms1).

(* [comment removed for export] *)
Definition store_freeRS_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (cs : list achunk) (mb ms n b1 ctx lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHSm cs Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  Permutation cs (ch :: sec_chunks_of s) -> RSEC cs RNG -> ~ sec_live s ch -> n <= Q_MAX ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  (Q_CACHE < a_qloc_bytes sq -> a_qglob_bytes sq + a_qloc_bytes sq <= Q_MAX) ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n hm m ->
  dk_pre ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms',
    free_fast_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                   (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms' ->
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
      /\ AHEAP_P (AHQ DI ASEC_of AFK) L RNG (st_after sq) LB m'.

Hypothesis MID : mid_stmtS.
Hypothesis STORE_R : store_freeRS_stmt.
(* [comment removed for export] *)
Hypothesis REFILL : forall cs Q1, refill_stmt (AHSm cs Q1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afree_sec_refill__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  (Q_CACHE < a_qloc_bytes st + (n + 8192) -> a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) <= Q_MAX) ->
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 42).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 43).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'afree_sec_refill__stmt 44).
Let hm := mb + 6128.
Let full := match a_qloc st with [] => false | _ :: _ => true end.
Let bsz := b_size (List.last (a_qloc st) dummy_batch).
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL hm full bsz"] Lemma afree_sec_refill__body : ltac:(let T := type of (fun (h : afree_sec_refill__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (tr, (mb, ms))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NQM EA CNT0 NOREC AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  set (st1 := set_live (delete p (a_live st)) st).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB.AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  (* [comment removed for export] *)
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EAu _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_r SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahmx; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 B1 B3 CX HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  chg (mb + 6128) hm.
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_res_hi L ALO) as RHI. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in RES.   (* [comment removed for export] *)
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  (pose proof (rup8_facts n ltac:(clear -NB; lia)) as ndP__; nd_pre ndP__ 3%nat; intros RUP RUP8 RUPS; nd_post).
  assert (SHGEO : shad (hm + 16) = shad mb + 768 /\ shlen (rup n 8) <= ms / 8 - 768 /\ 0 < shlen (rup n 8) /\ hm + 16 + rup n 8 <= mb + ms
                  /\ 2148239360 <= shad mb /\ shad mb + ms / 8 <= 17594332446720).   (* [comment removed for export] *)
  { subst hm. rewrite !shad_div, RUPS. unfold ASHOFF. (pose proof (sec_facts n ltac:(clear -NB; lia) NPR) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ RS1 _ NSE _; nd_post).
    unfold K_HIGH_MEM in *. pose proof atop_range as AR8. clear -MAL RUP RUP8 RS1 NSE NMS N6 NB ML1 ML3 MCE MSAL AR8. Z.div_mod_to_equations. lia. }
  (nd_pre SHGEO 6%nat; intros SHE SHL SHP UBS SHLO SHHI; nd_post).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (HM0' : ablk hm (hm + 24)) by (subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB; lia]).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (HMSEPg : forall s Xs, awf L s Xs -> forall kk, 0 <= kk < ndist s K_BATCH_CLASS -> hm + 24 <= abatch_addr L kk \/ abatch_addr L kk + 8192 <= hm).
  { intros s Xs WFs kk KK. (nd_pre WFs 7%nat; intros _ _ _ _ _ PERCs _; nd_post).
    (nd_pre (PERCs K_BATCH_CLASS (K24)) 3%nat; intros Q1' Q2' _; nd_post).
    (pose proof (slot_in_region L s K_BATCH_CLASS kk ltac:(rewrite size_of_class_24; lia) (proj1 Q1') KK) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 _; nd_post).
    rewrite size_of_class_24 in P4. subst hm. unfold abatch_addr, aregion, K_REGION, K_FREEARR_OFF, K_BATCH_CLASS in *.
    clear -P5 P4 Q1' Q2' RSP SC_r MSB. lia. }
  pose proof (HMSEPg st X WF) as HMSEP.
  (* [comment removed for export] *)
  assert (IN : In (CSec mb ms n) (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact NTH]).
  pose proof (proj1 (Forall_forall _ _) RSECS _ IN) as [RMB RSH]. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  destruct (CACHES K_BATCH_CLASS (K24)) as [tail (CR & CHc & LCH)].
  replace (acache_addr L K_BATCH_CLASS) with (al_t L + 2128) in CR by (unfold acache_addr, K_BATCH_CLASS; lia).
  rewrite CNT0 in CR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  (pose proof (read_lastS (AHQ DI ASEC_of AFK) L st X Q m RNG hm ALO ARNG AR AQ HM0' HMSEP EA) as ndP__; nd_pre ndP__ 6%nat; intros FULL DTL DHL DNL DSL LST64; nd_post).
  cbv zeta in FULL.
  chg (match a_qloc st with [] => false | _ :: _ => true end) full.
  set (lst := qlast L (q_loc Q)) in *.
  chg (b_size (List.last (a_qloc st) dummy_batch)) bsz.
  set (hs := map (Z_to_bv 64) (qhdrs L (b_chunks (List.last (a_qloc st) dummy_batch)) (qb_ks (List.last (q_loc Q) dummy_qb)))) in *.
  assert (FULL' : if full then 0 < Z.of_nat (length (a_qloc st)) /\ rw_cells asegs m lst [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)]
             /\ 0x10007fff8000 <= lst /\ lst + 8192 <= ATOP /\ u64arr asegs m (lst + 24) hs /\ length hs = 1021%nat /\ rng RNG lst 8192
           else Z.of_nat (length (a_qloc st)) = 0 /\ lst = 0).
  { destruct full; [| exact FULL]. (nd_pre FULL 8%nat; intros F1 F2 F3 F4 F5 F6 F7 _; nd_post). repeat (split; [assumption|]). exact F7. }
  (* [comment removed for export] *)
  rewrite (afree_refill_eq st p (CSec mb ms n) LIVE ltac:(cbn [chunk_size]; exact NQM) EA CNT0). fold st1.
  (* [comment removed for export] *)
  assert (AB64 : forall q, In q (q_loc Q ++ q_glob Q) -> 0 <= abatch_addr L (qb_slot q) < 2^64).
  { intros q Hq. (pose proof (bslot_geo L st X ALO WF (qb_slot q) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 3%nat; intros B0 B1' _; nd_post). atop_facts. lia. }
  assert (LF64 : 0 <= qfirst L (q_loc Q) < 2^64).
  { destruct (qfirst_cases L (q_loc Q)) as [-> |(q & Hq & ->)]; [lia| apply AB64; apply in_or_app; left; exact Hq]. }
  assert (CEIL : ATOP <= lo) by (generalize BOT STK3; clear; intros; lia).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  (* [comment removed for export] *)
  box SC_t. box SC_c. box SC_r. box SC_p. box SC_n. box SC_st. box SC_f. box SC_d. box CL5. box DL7. box DL8. box DL9. box DL10. box DTL. box DHL. box DNL. box DSL.
  eapply implF_evtF.
  { eapply (free_to_refill_spec DI L (q_ia Q) full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo (al_top L) (al_bot L)
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz uw _ _ sj hs (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- if _ then _ else _ => exact FULL'
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EAu; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10 | unboxed DTL | unboxed DHL | unboxed DNL | unboxed DSL
                             | ub SC_t; clear -Y MSB; subst hm; lia | ub SC_c; clear -Y MSB; subst hm; lia | ub SC_n; clear -Y MSB; subst hm; lia | ub SC_st; clear -Y MSB; subst hm; lia]
         | |- rng _ (shad _) _ => rewrite SHE; eapply rng_sub; [exact RSH| clear; lia| clear -SHL; lia]
         | |- rng _ _ 24 => subst hm; eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => subst hm; unfold tclr; clear -SC_tls MSB; lia
         end.
    all: try assumption.
    all: subst hm; unfold AIMG_HI, Q_MAX, Q_CACHE, Q_BATCH_BYTES, UDEPTH in *.
    all: try (generalize NB N6 NMS NQM MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MAL MSAL RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B1 CX LLB NC NM LF64 LST64 RA4 RUP; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PTR.
  (pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 cx A lo lst 0 bsz hs trt
              ALO ARNG AR AQ BL HFK LIVE HIN NQM H5 B1 B3 CX CEIL LO ms1 PTR) as ndP__; nd_pre ndP__ 4%nat; intros ARm BLm FKm HPm; nd_post).
  unfold free_to_refill_post in PTR.
  (nd_pre PTR 18%nat; intros id t0a t1a t2a a4a a5a a6a a7a t3a t4a t5a t6a m1 sj1 tb1 junk2 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 22%nat; intros MUf WMf MIf STf IDR HD1 FC1 SH1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 SS1 TB1 LTB1 FRS1 FRP1 FRE1 LBS1 DEP1; nd_post).
  cbn [ms_mem MS] in ARm, FKm, HPm.
  (* [comment removed for export] *)
  set (Q1 := mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)) in *.
  assert (PD1 : Permutation (CSec mb ms n :: sec_chunks_of st1) (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st1 p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  eapply (REFILL (sec_chunks_of st) Q1 _ (KB (CSec mb ms n)) _ L RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 st1 X K_BATCH_CLASS lo).
  all: try lazymatch goal with
       | |- alayout_ok _ => exact ALO
       | |- arng _ _ _ => apply (arng_sub L RNG st st1); [intros; reflexivity| reflexivity| intros cc Hcc; eapply Permutation_in; [exact PD1| right; exact Hcc]| exact ARNG]
       | |- AREP _ _ _ _ _ => exact ARm
       | |- mem_inv _ _ => exact MIf
       | |- stk _ _ _ _ => rewrite unsigned_lit by lia; exact STf
       | |- @eq word _ _ => first [exact TP | reflexivity | unfold acache_addr, K_BATCH_CLASS; f_equal; clear; lia | unfold AINSTANCE; reflexivity]
       | |- _ <= K_BATCH_CLASS < _ => exact (K24)
       | |- c_count _ = 0 => exact CNT0
       | |- _ <= _ => first [exact CEIL | rewrite ?unsigned_lit by lia; lia]
       | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub; [exact RSTK| lia| lia]
       end.
  all: match goal with |- forall _ _ _ _, refill_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ -> _ => idtac | |- ?G => idtac "REMR" G end.
  intros st_r X' RNG' ms' RR. unfold refill_ret in RR.
  (nd_pre RR 17%nat; intros FPLE t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 20%nat; intros MUr WMr MIr STr ARr ARNGr CINr CNTr MAXr XBr XCr LIVEr NEXTr QLr QBr QGr QGBr NSECr NRESr GCr; nd_post).
  rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
  (* [comment removed for export] *)
  assert (EAr : enq_is_app st_r = false) by (unfold enq_is_app; rewrite QLr; exact EA).
  (pose proof (enq_new_core (CSec mb ms n) st_r) as ndP__; nd_pre ndP__ 7%nat; intros _ NG1 NG2 _ NL1 NL2 _; nd_post). cbn [chunk_size] in NL1, NL2.
  assert (ENr : st_enq st_r (CSec mb ms n) = enq_new st_r (CSec mb ms n)).
  { unfold st_enq. destruct (enq_app st_r (CSec mb ms n)) as [s'|] eqn:E; [| reflexivity]. exfalso.
    assert (EA1 : enq_is_app st_r = true) by (apply (proj2 (enq_is_app_spec st_r (CSec mb ms n))); eexists; exact E). congruence. }
  assert (NORECr : Q_CACHE < a_qloc_bytes (st_enq st_r (CSec mb ms n)) -> a_qglob_bytes (st_enq st_r (CSec mb ms n)) + a_qloc_bytes (st_enq st_r (CSec mb ms n)) <= Q_MAX).
  { rewrite ENr, NG2, NL2, QBr, QGBr. change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES. generalize NOREC; clear; intros; lia. }
  rewrite (KB_apop_eq st_r (CSec mb ms n) EAr NORECr).
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x38360)) with (Z_to_bv 64 0x38360) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. unfold adisj in D_t_res.
  (nd_pre (PERC K_BATCH_CLASS (K24)) 3%nat; intros A24a A24b _; nd_post).
  assert (ERI : aregion_info L K_BATCH_CLASS = al_space_beg L + 137438953472 + 3072) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, K_BATCH_CLASS; lia).
  assert (ER24 : aregion L K_BATCH_CLASS = al_space_beg L + 24 * 4294967296) by (unfold aregion, K_REGION, K_BATCH_CLASS; lia).
  assert (W6B : 2199023255552 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
             /\ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= 17594333495296).
  { rewrite !shad_div, shlen_div. unfold ASHOFF, K_REGION. rewrite ER24. generalize SP1 SP2 A24a A24b. clear. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF. change (2^37) with 137438953472. change (2^32) with 4294967296. change (2^41) with 2199023255552. intros. Z.div_mod_to_equations. lia. }
  destruct W6B as [W6LO W6HI].
  (* [comment removed for export] *)
  assert (SLW5 : mb + ms <= aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS) \/ aregion L K_BATCH_CLASS + K_REGION <= mb).
  { rewrite ER24. unfold K_REGION. ub SC_r. destruct Y as [D|D]; [left| right]; generalize D RSP RES RHI A24a A24b; clear; unfold K_FREEARR_OFF; intros; lia. }
  assert (SLW6 : shad (hm + 16) + shlen (rup n 8) <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
              \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad (hm + 16)).
  { pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM. destruct SLW5 as [D|D].
    - left. rewrite SHE. pose proof (shad_sep _ _ _ D MAL8) as HH. rewrite shlen_div in HH. generalize HH SHL; clear; intros; lia.
    - right. apply (Z.le_trans _ (shad mb)); [apply shad_sep; [exact D| generalize RM; clear; intros; Z.div_mod_to_equations; lia]| rewrite SHE; clear; lia]. }
  word_range sp SPR.
  change (get_cls st1 K_BATCH_CLASS) with (get_cls st K_BATCH_CLASS) in MUr.
  (* [comment removed for export] *)
  lazymatch type of MUr with munch ?W _ _ =>
    assert (KHI : forall Ad sz, bv_unsigned sp + -2272 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz Y1 Y2; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize Y1 Y2 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KIM : forall Ad sz, 0xafc00 <= Ad -> Ad + sz <= 0x13e490 -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz Y1 Y2 Y3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION;
      generalize Y1 Y2 Y3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KCH : forall Ad sz, mb <= Ad -> Ad + sz <= mb + ms -> 0 <= sz -> disjoint_from W Ad sz);
    [ intros Ad sz Y1 Y2 Y3; cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION; pose proof SLW5 as SL5; pose proof SC_t as SCT; unbox SCT; pose proof SC_r as SCR; unbox SCR;
      generalize Y1 Y2 Y3 LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR SCT SCR RSP RES RHI SL5 MLO ML1 ML3 KAM KBM KEM KCM KDM MCE; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |];
    assert (KSH : disjoint_from W (shad (hm + 16)) (shlen (rup n 8)));
    [ cbn [disjoint_from fst snd]; unfold AINSTANCE, K_REGION; pose proof SLW6 as SL6;
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR SL6 SHLO SHHI SHE SHL SHP; clear; unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296; intros; repeat split; lia |]
  end.
  (* [comment removed for export] *)
  eapply (cells_frame _ m1 m') in HD1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; subst hm; generalize NMS N6 NB; clear; intros; lia].
  eapply (cells_frame _ m1 m') in FC1; [| exact MUr | exact WMr | apply KCH; cbn [cells_size csize Nat.add]; subst hm; generalize NMS N6 NB; clear; intros; lia].
  eapply (cells_frame _ m1 m') in SH1; [| exact MUr | exact WMr | match goal with |- disjoint_from _ _ ?z => replace z with (shlen (rup n 8)) by (cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id; [reflexivity| generalize SHP; clear; intros; lia]) end; exact KSH].
  clear STATS1 LSJ1 UW1.
  eapply (cells_frame _ m1 m') in FL1; [| exact MUr | exact WMr | apply KIM; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (stk_transport_disjoint _ _ m1 m') in IAS1; [| exact MUr | exact WMr | apply KIM; clear; lia].
  eapply (cells_frame _ m1 m') in SS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (u64arr_frame _ m1 m') in TB1; [| exact MUr | exact WMr | apply KHI; rewrite ?LTB1; clear; cbn; lia].
  eapply (cells_frame _ m1 m') in FRS1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRP1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  eapply (cells_frame _ m1 m') in FRE1; [| exact MUr | exact WMr | apply KHI; cbn [cells_size csize Nat.add]; clear; lia].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MUr. rewrite length_le8 in Hi. rewrite wa_unsigned by lia.
    eapply disjoint_outside; [apply (KIM (0xafc08 + 8 * j) 8); generalize Hj; clear; intros; lia| generalize Hi; clear; intros; lia]. }
  clear IAM1.
  (* [comment removed for export] *)
  pose proof ARr as AR0. (nd_pre AR0 11%nat; intros WFr RTr INSTr THRr CLSr HQr HSr HDr HROr HRT2r AVLr; nd_post).
  cbn [ah_quar ah_sec ah_depot AHSm] in HQr, HSr, HDr.
  (nd_pre THRr 6%nat; intros T0r T40r CACHESr CSTATSr [sjr [STATSr LSJr]] UNWr; nd_post).
  destruct (junk_split m' (al_t L + 2768) 16 16 CSTATSr ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m' (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  destruct (c8_of_junk m' _ CS8) as [stj' STSr].
  assert (POSr : 0 < c_count (get_cls st_r K_BATCH_CLASS)) by (rewrite CNTr; exact MAXr).
  pose proof (HMSEPg st_r X' WFr) as HMSEPr.
  (nd_pre (read_ek_newS (AHSm (sec_chunks_of st) Q1) L st_r X' Q1 m' RNG' hm n ALO ARNGr ARr HQr HM0' HMSEPr stj' EAr POSr STSr) 15%nat; intros k24 chunks EK ES ED EB NK NBk KK NIB JKb FSH CIN _ EKE; nd_post).
  pose proof HQr as AQr. (nd_pre AQr 6%nat; intros [QKr MXr] [QCr ABLr] [GCQr ABGr] (FLr & IASr & IAMr) CPr NUMr; nd_post).
  (nd_pre (read_dkS (AHSm (sec_chunks_of st) Q1) L st_r X' Q1 m' RNG' hm ALO ARNGr ARr HQr HMSEPr
              (abatch_addr L k24) (n + 8192) (ek_of L st_r X' Q1 n k24 stj' chunks) ltac:(lia)
              ltac:(right; exists k24; split; [reflexivity|]; split; [exact KK| exact NIB])
              ltac:(rewrite ENr, NG2, NL2 in NORECr; generalize NORECr; clear; unfold Q_CACHE, Q_MAX, Q_BATCH_BYTES; intros; lia) EB) 4%nat; intros DK DS GL GLST; nd_post).
  set (ek := ek_of L st_r X' Q1 n k24 stj' chunks) in *.
  set (g := g_of L st_r Q1 (n + 8192)) in *.
  (* [comment removed for export] *)
  pose proof ARNGr as AG0. (nd_pre AG0 14%nat; intros RIMGr RT4r RCTXr RNOr RSTOr _ _ _ _ _ _ RSECSr _ RTLSr; nd_post).      (* [comment removed for export] *)
  pose proof (rng_fp_le _ _ _ _ FPLE RSTK) as RSTKr. pose proof (rng_fp_le _ _ _ _ FPLE RMB) as RMBr. pose proof (rng_fp_le _ _ _ _ FPLE RSH) as RSHr.
  assert (BLr : ablocks L st_r X' (lb_remove p LB)) by (apply (ablocks_xbusy L st1 st_r X); [exact XBr | exact LIVEr | exact BLm]).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *) pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKr : AFK L (lb_remove p LB) m').
  { eapply (hf_frame _ HL L (lb_remove p LB) m1 m'); [exact FKm | exact MUr | exact WMr |].
    unfold fake_untouched. unfold AINSTANCE, K_REGION.
    assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad (aregion L K_BATCH_CLASS + c_mapped_user (get_cls st K_BATCH_CLASS))
                   \/ shad (aregion L K_BATCH_CLASS) + shlen K_REGION <= shad (al_fake L))).
    { destruct D_f_res as [D|D].
      - left. apply shad_sep; [| generalize FKO FKi FBND; clear; intros; Z.div_mod_to_equations; lia]. rewrite ER24. generalize D RSP A24a; clear; intros; lia.
      - right. apply shad_sep; [| pose proof (aregion_mod L K_BATCH_CLASS SAL) as RM; generalize RM; clear; intros; Z.div_mod_to_equations; lia].
        rewrite ER24. unfold K_REGION. generalize D RSP RES RHI; clear; atop_facts; intros; lia. }
    unfold K_REGION in SHF.
    repeat (apply Forall_cons; [cbn [fst snd];
      generalize LO CEIL TL1 TL2 TL1u TL4u SP1 SP2 ERI ER24 A24a A24b W6LO W6HI SPR FKO FKi FBND DTO DBND DIMG D_f_res D_t_f D_d_res D_t_d RES RHI RSP SHF; clear;
      unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_FREEARR_OFF, K_REGION; change (2^37) with 137438953472; change (2^32) with 4294967296;
      rewrite ?shad_div, ?shlen_div; unfold ASHOFF; intros; repeat split; fu_focus; Z.div_mod_to_equations; lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  clear D_f_res D_t_f D_d_res D_t_d D_t_res.
  pose proof EK as EK0. pose proof ES as ES0. pose proof DK as DK0.
  rewrite EKE in EK, ES, DK. cbn [ek_pre] in EK.
  (nd_pre EK 20%nat; intros FULLr SBr CRr CHr LCHr CNTr' NTHr IXSr STSr' HBr BJr SBPr B0r BL1r DTBr DTLr DBLr DHBr DHLr RBr; nd_post).
  box DTBr. box DTLr. box DBLr. box DHBr. box DHLr.
  pose proof ES as ES1. cbn [ek_seps] in ES1. (nd_pre ES1 4%nat; intros SB1r SB2r SB3r SLr; nd_post).
  assert (DHL24 : hm + 24 <= qlast L (q_loc Q1) \/ qlast L (q_loc Q1) + 8192 <= hm).
  { destruct (a_qloc st_r); [destruct FULLr as [_ E0]; rewrite E0; right; generalize HM0'; clear; intros HB; (pose proof (ablk_lin _ _ HB) as ndP__; nd_pre ndP__ 4%nat; intros HB1 HB2 HB3 HB4; nd_post); unfold AIMG_HI in HB1; lia | exact (proj1 (SLr eq_refl))]. }   (* [comment removed for export] *)
  box SB1r. box DHL24.
  assert (NBr : 0 <= Z.of_nat (length (a_qloc st_r)) < 2^62) by (rewrite QLr; change (a_qloc st1) with (a_qloc st); generalize LLB NC; clear; unfold Q_BATCH_BYTES; intros; lia).
  assert (QB0r : 0 <= a_qloc_bytes st_r) by (rewrite QBr; change (a_qloc_bytes st1) with (a_qloc_bytes st); generalize LLB; clear; unfold Q_BATCH_BYTES; intros; lia).
  (* [comment removed for export] *)
  eapply evtF_mono.
  { lazymatch type of EKE with _ = EkNew ?fu ?nx ?bs ?cn ?mx ?cz ?sj0 ?ix ?chs ?sb ?bb ?hs0 =>
      eapply (free_from_refill_spec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
                (al_t L) hm n b1 cx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
                nx bs cn sb id bb mx cz sj0 ix sjr tb1 chs hs0 junk2 j0 trt)
    end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact STr | exact IAS1]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0x | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MIr
         | |- ADEPOT _ _ _ => exact HDr
         | |- u64arr _ _ (_ + 2800) _ => exact STATSr
         | |- u64arr _ _ _ _ => first [exact TB1 | exact CHr]
         | |- if _ then _ else _ => exact FULLr
         | |- forall j, _ -> bytes_at _ _ _ _ => exact IAM2
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
         | |- rw_cells _ _ (shad _) _ => exact SH1
         | |- rw_cells _ _ (aq_tcache _) _ => exact QCr
         | |- rw_cells _ _ (_ + 80) _ => exact QCr
         | |- rw_cells _ _ (_ + 2128) _ => exact CRr
         | |- rw_cells _ _ (_ + 2784) _ => exact STSr'
         | |- rw_cells _ _ (_ + 3168) _ => exact UNWr
         | |- rw_cells _ _ (_ + -72) _ => exact FRS1
         | |- rw_cells _ _ (_ + -2128) _ => exact SS1
         | |- rw_cells _ _ (_ + -2208) _ => exact FRP1
         | |- rw_cells _ _ (_ + -2272) _ => exact FRE1
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact FC1
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => exact QKr
         | |- nth_error _ _ = _ => exact NTHr
         | |- @eq Z _ _ => exact HBr
         | |- ex _ => exact BJr
         | |- _ + 24 <= al_t _ \/ _ => ub SC_t; clear -Y MSB; subst hm; lia
         | |- _ \/ _ => first [unboxed DTBr | unboxed DTLr | unboxed DBLr | unboxed SB1r | unboxed DHL24 | unboxed DL7 | unboxed DL8]
         | |- rng _ (shad _) _ => rewrite SHE; eapply rng_sub; [exact RSHr| clear; lia| clear -SHL; lia]
         | |- rng _ _ 24 => subst hm; eapply rng_sub; [exact RMBr| clear; lia| clear -MSB; lia]
         | |- rng _ _ _ => first [assumption | eapply rng_sub; [exact RSTKr| clear; lia| clear -LO; lia]]
         | |- rng_aimg _ => exact RIMGr
         | |- rng_atls _ => exact RTLSr
         | |- tclr _ 24 => subst hm; unfold tclr; clear -SC_tls MSB; lia      (* [comment removed for export] *)
         end.
    all: try assumption.
    all: try (subst hm; unfold Q_MAX, Q_BATCH_BYTES; rewrite ?QLr, ?QBr; change (a_qloc st1) with (a_qloc st); change (a_qloc_bytes st1) with (a_qloc_bytes st);
              generalize NB N6 NMS NQM MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MAL MSAL RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 DL1 DL2 DL3 DL4 DL5 DL6
                         B1 CX LLB NC NM LF64 LST64 RA4 IDR RUP; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMT" G end. }
  cbv beta. intros msf PF.
  rewrite <- EKE in PF.
  pose proof ARm as ARm0. destruct ARm0 as [WFm _].
  assert (DK1 : dk_pre ek (g_of L st_r Q1 (ek_delta ek n)) RNG' (al_t L) (qlast L (q_loc Q1)) hm (a_qloc_bytes st_r + ek_delta ek n) m') by (rewrite ED; exact DK0).
  assert (PF1 : free_fast_post DI L ek (g_of L st_r Q1 (ek_delta ek n)) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                  (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r) b1 cx lo m' msf) by (rewrite ED; exact PF).
  (* [comment removed for export] *)
  assert (PDr : Permutation (sec_chunks_of st) (CSec mb ms n :: sec_chunks_of st_r)).
  { rewrite (sec_chunks_of_eq st1 st_r LIVEr QLr QGr). apply Permutation_sym. exact PD1. }
  assert (NOTLr : ~ sec_live st_r (CSec mb ms n)).
  { intros [q Hq]. destruct HS as (WFS & _). apply (sec_not_live_after L st _ p mb ms n st1 WFS (Permutation_refl _) LIVE eq_refl). exists q. rewrite <- LIVEr. exact Hq. }
  assert (RSCSr : RSEC (sec_chunks_of st) RNG') by (eapply RSEC_mono; [exact FPLE| exact RSECS]).
  (pose proof (STORE_R L RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m' st_r (lb_remove p LB) X' Q1 (sec_chunks_of st) mb ms n b1 cx lo k24 stj' chunks
                ALO ARNGr ARr BLr FKr PDr RSCSr NOTLr NQM B1 B3 CX EAr NK NBk KK NIB JKb FSH CIN POSr NORECr EK0 DK1 CEIL LO msf PF1) as ndP__; nd_pre ndP__ 17%nat; intros t0f t1f t2f a0f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f mf ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MIf2 STf2 HPf AHf; nd_post).
  unfold afree_post. split; [exact FPLE|].
  exists t0f, t1f, t2f, a0f, a1f, a2f, a3f, a4f, a5f, a6f, a7f, t3f, t4f, t5f, t6f, mf.
  split; [reflexivity|]. split; [exact MIf2|]. split; [exact STf2|]. split; [| exact AHf].
  eapply aheap_pres_trans; [exact HPm|]. eapply aheap_pres_trans; [| exact HPf].
  eapply (aheap_pres_refill CI CI_OK CI_OK2 L st1 X (lb_remove p LB) sp (bv_unsigned sp + -2272) lo m1 m');
    [exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia].
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL"] Theorem afree_sec_refill : ltac:(let t := eval cbv delta [afree_sec_refill__stmt] in afree_sec_refill__stmt in exact t).
Proof. exact afree_sec_refill__body. Qed.
End S.
End CANSEC1.
End TwB.
End ASF_refill.
