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
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHolesD ASecRecycle.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adeallocfn_icptR__A3W.
From Stdlib Require Sorting.Permutation.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ADfnS_fast.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_read. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.
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
Hypothesis STORE : OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.store_freeS_stmt DI AFK CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_sec_fast__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 41).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 42).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 43).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 44).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 45).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 46).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 47).
Let hm := mb + 6128.
#[using="STORE hm"] Lemma dfn_sec_fast__body : ltac:(let T := type of (fun (h : dfn_sec_fast__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo SO pc trt tb mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (SO, (pc, (trt, (tb, (mb, ms)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NQM st1 st2 CNT NOREC AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RSO.
  assert (RA4 : True) by exact I.
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
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
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
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
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
  { eapply (dfn_fast_spec DI L ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) SO (1 + Z.of_nat (length trt)) pc
              uw _ _ sj tb (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, EA; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
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
    all: try (clear -LTRT; lia).
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
#[using="STORE"] Theorem dfn_sec_fast : ltac:(let t := eval cbv delta [dfn_sec_fast__stmt] in dfn_sec_fast__stmt in exact t).
Proof. exact dfn_sec_fast__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
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
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.TwB.
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
Hypothesis STORE : OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB.store_freeS_stmt DI AFK CI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_sec_fast__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 41).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 42).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 43).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 44).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 45).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 46).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_fast__stmt 47).
Let hm := mb + 6128.
#[using="STORE hm"] Lemma dfn_sec_fast__body : ltac:(let T := type of (fun (h : dfn_sec_fast__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo SO pc trt tb mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (SO, (pc, (trt, (tb, (mb, ms)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NQM st1 st2 CNT NOREC AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RSO.
  assert (RA4 : True) by exact I.
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
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
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
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
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
  { eapply (dfn_fast_spec DI L ek g RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) SO (1 + Z.of_nat (length trt)) pc
              uw _ _ sj tb (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- ek_pre _ _ _ _ _ _ _ _ => exact EK
         | |- ek_seps _ _ _ _ => exact ES
         | |- dk_pre _ _ _ _ _ _ _ _ => exact DK
         | |- dk_seps _ _ _ => exact DS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, EA; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
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
    all: try (clear -LTRT; lia).
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
#[using="STORE"] Theorem dfn_sec_fast : ltac:(let t := eval cbv delta [dfn_sec_fast__stmt] in dfn_sec_fast__stmt in exact t).
Proof. exact dfn_sec_fast__body. Qed.
End S.
End CANSEC1.
End TwB.
End ADfnS_fast.

(* [comment removed for export] *)
Module ADfnS_big.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHolesD ASecRecycle. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_asecdealloc OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_arecsec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_aputrec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrameD OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecRecycle OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.
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

#[using="Type"] Lemma afree_big_eq : forall st (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n -> a_qloc_bytes st <= Q_CACHE ->
  afree st (Some p) = large_dealloc (set_live (delete p (a_live st)) st) mb ms (fun st2 => aret st2).
Proof.
  intros st p mb ms n LIVE NB QB. unfold afree. rewrite LIVE. cbn [chunk_size].
  replace (n <=? Q_MAX) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
  unfold recycle_chunk, large_dealloc.
  replace (a_qloc_bytes (set_nsec (a_nsec (set_live (delete p (a_live st)) st) - 1) (set_live (delete p (a_live st)) st))) with (a_qloc_bytes st) by reflexivity.
  replace (Q_CACHE <? a_qloc_bytes st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition bigW (sp t mb ms PA idx last nodes store : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e08c); (t + 2800, t + 3169);
   (0x1804c8, 0x5d0510); (nodes, nodes + 1048576); (store, store + 8388608);
   (0xab010, 0xab019); (0xab028, 0xab038); (0xab240, 0xab244); (0xab258, 0xab268);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)].

End CANSEC1.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rec rl_skel (cs : constant FSet.t) (t : constr) : bool :=
  if zt_plain_arith_s cs t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(or) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(and) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(not) then rl_skel cs (Array.get args 0)
      else if lt_is_ref h reference:(iff) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else false
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then (if rl_skel cs (Constr.Binder.type b) then rl_skel cs c else false) else false
  | _ => false
  end.
Local Ltac2 rl_prune () : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if rl_skel cs ty then None else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac rl_prune := ltac2:(Control.enter rl_prune).
Set Default Proof Mode "Classic".
Local Ltac rl_lia := rl_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; rl_lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rl_lia ] end ].
Ltac kf := cbn [fst snd]; unfold AQ_MAX, AQ_MIN, AQ_MAXC, AQ_MUTEX, AQ_GCACHE, aq_tcache, AINSTANCE, ATP88, ATSD, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIMG_HI, K_HIGH_MEM in *; repeat split; first [ lia_rel | lia ].

Ltac find_ivb s H :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear -s H; lia]
        | apply Exists_cons_tl; find_ivb s H ].
Ltac solve_sub_fpb s H :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_ivb s H|]); apply Forall_nil.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition dfn_sec_big__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n ->
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 41).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 42).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 43).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 44).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 45).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 46).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 47).
#[using="HL DEPD AFKD CI_OK CI_OK2"] Lemma dfn_sec_big__body : ltac:(let T := type of (fun (h : dfn_sec_big__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo SO pc trt tb mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (SO, (pc, (trt, (tb, (mb, ms)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NBIG AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RSO RA4.
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EA _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_s SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahmx; nd_post).
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SB1 SB2 SB3 SB4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni Na [kN NBND]; nd_post). (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si Sa [kS SBND]; nd_post).   (* [comment removed for export] *)
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci Ca [kC CBND]; nd_post). (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros Ti4 Ta4 [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
  (* [comment removed for export] *)
  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT HRT2 RT3) as PRM.
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  pose proof INST as INST0. (nd_pre INST0 9%nat; intros I32 I48 I64 I72 I112 I680 I984 I40 I56; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS _ SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (pose proof SINST as ndP__; nd_pre ndP__ 6%nat; intros I80 [srt ISRT] JST JBS PAD JGL; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 B1 B3 CX HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (ch := CSec mb ms n) in *.
  assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
  assert (IN : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INo]).
  (* [comment removed for export] *)
  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. clear -NTHL IL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  (nd_pre (sec_wf1_facts' L lmb lms ln WFl) 12%nat; intros LAL LLO LCE LMSE LNB LRZ LMSB LMSAL _ _ LSCL _; nd_post).
  (pose proof (ablk_int _ _ LLO) as ndP__; nd_pre ndP__ 6%nat; intros kLl KALl KBLl KELl KCLl KDLl; nd_post).   (* [comment removed for export] *)
  (pose proof LSCL as ndP__; nd_pre ndP__ 10%nat; intros LC_t LC_c LC_s LC_p LC_n LC_st LC_f LC_d LC_l LC_ahmx; nd_post).      (* [comment removed for export] *)
  destruct (sec_shadow_cb m mb ms n true (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].
  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ (lmb + 32 <= al_nodes L \/ al_nodes L + 1048576 <= lmb) /\ (lmb + 32 <= al_store L \/ al_store L + 8388608 <= lmb)
   /\ tclr lmb 32).      (* [comment removed for export] *)
  { (nd_pre (PER _ _ NTHL) 3%nat; intros llv _ LCH; nd_post). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|].   (* [comment removed for export] *) all: split; [clear -LCE LMSB; lia|]. all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: split; [clear -LC_p LMSB WR WB; lia|].
    all: split; [clear -LC_n LMSB; lia|]. all: split; [clear -LC_st LMSB; lia|]. all: unfold tclr; clear -LC_l LMSB; lia. }
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  pose proof (proj1 (Forall_forall _ _) RSECS ch IN) as [RMB RSH]. unfold ch in RMB, RSH. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  rewrite (afree_big_eq st p mb ms n LIVE NBIG NC).
  set (st1 := set_live (delete p (a_live st)) st).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  iprefix. eapply evtF_cut.
  { eapply (dfn_front_spec DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (al_t L) (al_ctx L) (mb + 6128) n b1 cx lo SO (1 + Z.of_nat (length trt)) pc uw _ _ sj tb trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (_ + 6128 + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         end.
    all: try lazymatch goal with
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, EA; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | clear -SC_t MSB; lia | clear -SC_c MSB; lia | clear -SC_n MSB; lia | clear -SC_st MSB; lia | clear -D_t_c; lia]
         | |- rng _ (_ + 6128) _ => eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => unfold tclr; clear -SC_tls MSB; lia
         end.
    all: try assumption.
    all: try (unfold AIMG_HI; generalize NB N6 NMS MLO MCE MAL LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL1u TL4u TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B1 CX RA4; clear; intros; Z.div_mod_to_equations; lia).
    all: try (clear -LTRT; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold dfn_front_post in PFR.
  (nd_pre PFR 13%nat; intros id t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 sj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 14%nat; intros MUf WMf MIf STf IDR HD1 FC1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 DEP1; nd_post).
  apply evtF_done.
  (* [comment removed for export] *)
  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
  assert (SHR : 2148238848 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)   (* [comment removed for export] *)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof QK as QKx. xport QKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof QC as QCx. xport QCx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t DL7 DL8 NBND SBND; kf).
  pose proof I32 as I32x. xport I32x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I64 as I64x. xport I64x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I72 as I72x. xport I72x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I112 as I112x. xport I112x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof ISRT as ISRTx. xport ISRTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I680 as I680x. xport I680x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof PAD as PADx. xport PADx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TI as TIx. xport TIx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TK as TKx. xport TKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof T88 as T88x. xport T88x MUf WMf ltac:(pose proof (tclr_nodes L ALO) as XN; pose proof (tclr_store L ALO) as XS; unfold tclr in XN, XS;      (* [comment removed for export] *)
                                                  clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND SC_tls XN XS; kf).
  pose proof TSD as TSDx. xport TSDx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof CT as CTx. xport CTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3 CL5 SC_c DL9 DL10 NBND SBND; kf).
  pose proof U64 as U64x. xport U64x MUf WMf ltac:(rewrite length_map; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 OP OPi OPa OPs D_t_p SC_p D_n_p D_s_p LENO WB WR NBND SBND; kf).
  pose proof H1 as H1x. xport H1x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t SC_n SC_st NBND SBND; kf).
  pose proof SH as SHx. xport SHx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SHR NBND SBND; kf).
  pose proof JST as JSTx. eapply (junk_frame _ m m1) in JSTx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  pose proof JGL as JGLx. eapply (junk_frame _ m m1) in JGLx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (PRM1 : premap_cells m1).
  { eapply premap_cells_frameD; [exact PRM | exact MUf | ..]; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf. }
  assert (HRO1 : arelro0 m1).
  { eapply arelro0_munch; [exact HRO | exact MUf |]. unfold ARELRO_LO, ARELRO_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (LHDR1 : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m1 lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ tclr lmb 32).
  { intros NE. (nd_pre (LHDR NE) 10%nat; intros L1 L2 L3 L4 L5 L6 L7 L8 L9 L10; nd_post). atop_facts.
    (pose proof (ablk_int _ _ L2) as ndP__; nd_pre ndP__ 6%nat; intros kL KAL KBL KEL KCL KDL; nd_post).   (* [comment removed for export] *)
    xport L1 MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 L2 KAL KBL KEL KCL KDL L3 L4 L5 L8 L9 NBND SBND; kf).
    repeat (split; [assumption|]). first [exact L7 | exact L10]. }
  clear LHDR.
  (* [comment removed for export] *)
  eapply (put_passthru_spec RNG (fun st2 => aret st2) st1 _ ra sp gp tp) with
     (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj1) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 3) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj)
     (nb := Z.of_nat (length (a_qloc st))) (fst0 := qfirst L (q_loc Q)) (lst := qlast L (q_loc Q)) (qb := a_qloc_bytes st).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact STf
       | |- mem_inv _ _ => exact MIf
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact HRO1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- junk_at _ _ 32 => exact JSTx
       | |- junk_at _ _ 16 => exact JGLx
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680x| exact PADx]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
       | |- rw_cells _ _ _ [CB _ _] => exact SHx
       | |- rw_cells _ _ (_ + 152) _ => exact CTx
       | |- rw_cells _ _ (_ + 80) _ => exact QCx
       | |- rw_cells _ _ _ _ => first [eassumption | exact QKx | exact I32x | exact I64x | exact I72x | exact I112x | exact ISRTx | exact TIx | exact TKx | exact T88x | exact TSDx | exact H1x]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64x
       | |- u64arr _ _ _ _ => exact STATS1
       | |- length _ = _ => exact LSJ1
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map; exact LENO
       | |- _ -> _ /\ _ => exact LHDR1
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RSECS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- tclr (al_ptr_array _) _ => eapply tclr_sub; [exact (tclr_ptr L ALO) | clear; lia | clear -WR; lia]      (* [comment removed for export] *)
       | |- tclr _ _ => exact SC_tls
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (_ - _) => eapply rng_sub; [exact RSTK| clear; lia | clear -LO; lia]
       | |- rng _ (shad _) _ => rewrite shlen_div; exact RSH
       | |- rng _ (al_ptr_array _) _ => exact RPA
       | |- rng _ (al_t _) _ => exact RT4
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ _ _ => exact RMB
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia   (* [comment removed for export] *)
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: unfold K_HIGH_MEM, AREQMAX in *.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- _ => try first [ assumption | exact SC_t | exact CL5
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -SP47 LO BOT STK3; lia | clear -OC CBND Ci; lia | clear -OT TBND TIMG; lia | clear -OP OPi OPa OPs WR WB; lia | clear -IL LENO; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -LLB NC; unfold Q_CACHE, Q_BATCH_BYTES in *; lia | clear; rewrite unsigned_lit by lia; lia
                       | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia
                       | clear -LC_t LMSB; lia | clear -LCE LMSB; lia ]
       end.
  (* [comment removed for export] *)
  intros RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LE1 HF PP TC'.
  cbv beta. apply implS_ret.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  (nd_pre PP 12%nat; intros MU2 MI' ST' NSC' SRT' JST' MTX' JGL' ARR' LHDR' [sj' [STATS' LSJ']] SHZ'; nd_post).
  unfold putrec_W in MU2.
  (* [comment removed for export] *)
  eapply (cells_frameD _ m1 m') in FL1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in UW1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR LC_t SC_t D_t_p; kf].
  eapply (stk_transportD _ _ m1 m') in IAS1; [| exact MU2| cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MU2. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by (clear -Hj Hi; lia).
    clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hj Hi. kf. }
  clear IAM1.
  assert (DEP' : ADEPOT DI L m').
  { eapply DEPD; [exact DEP1| exact MU2|].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hq DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 D_n_p D_s_p SC_n SC_st LC_n LC_st LMSB NBND SBND; kf |]).
    apply Forall_nil. }
  clear DEP1.
  apply evtF_done.
  (* [comment removed for export] *)
  unfold afree_post. split; [exact LE|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
  (* [comment removed for export] *)
  assert (MU : munch (bigW (bv_unsigned sp) (al_t L) mb ms (al_ptr_array L) (Z.of_nat i) lmb (al_nodes L) (al_store L)) m m').
  { unfold bigW. eapply munch_trans; [| eapply munch_weaken; [| exact MU2]]. eapply munch_weaken; [| exact MUf]. all: solve_sub_fpb sp MSB. }
  clear MU2 MUf. unfold bigW in MU.
  (* [comment removed for export] *)
  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD. pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as ATR.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_res L ALO) as D_n_r. pose proof (ad_store_res L ALO) as D_s_r.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p. pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_r, D_p_r, D_n_r, D_s_r, D_t_f, D_f_p, D_n_f, D_s_f, D_t_d, D_d_p, D_n_d, D_s_d, D_c_n, D_c_s.
  (pose proof LSCL as ndP__; nd_pre ndP__ 4%nat; intros _ _ LC_r _; nd_post).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_s as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH3 : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI ATR. Z.div_mod_to_equations. lia. }
  (nd_pre RSH3 3%nat; intros SR1 SR2 SR3; nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFi OFa [kF FBND]; nd_post).   (* [comment removed for export] *)
  assert (FSH : 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFi OFa ATR. Z.div_mod_to_equations. lia. }
  assert (SHCE : shad mb + shlen ms <= shad ATOP /\ 17594064011264 <= shad ATOP <= 17594332446720) by (rewrite !shad_div, shlen_div; unfold ASHOFF in *; clear -MCE MAL8 MSAL ATR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, SHCE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- LENO; clear -IL; lia).
  (* [comment removed for export] *)
  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall Ad kk, 0x10000 <= Ad -> 0 <= kk ->      (* [comment removed for export] *)
            (Ad + kk <= 0xab010 \/ (0xab268 <= Ad /\ Ad + kk <= 0xaf800) \/ (0x130830 <= Ad /\ Ad + kk <= 0x13e088)
             \/ (0x13e08c <= Ad /\ Ad + kk <= 0x1804c8) \/ (0x5d0510 <= Ad /\ Ad + kk <= AIMG_HI)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (K_stack : forall Ad kk, bv_unsigned sp <= Ad -> 0 <= kk -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 LO BOT STK3 TL2 OP OPi OPa OPs LCE LMSB MCE SHR DL2 DL5 I64b WB WR ATR. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_t : forall Ad kk, al_t L <= Ad -> 0 <= kk -> (Ad + kk <= al_t L + 2800 \/ (al_t L + 3169 <= Ad /\ Ad + kk <= al_t L + 4096)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TL2 TL1u TL4u DL7 DL8 D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_ctx : forall Ad kk, al_ctx L <= Ad -> 0 <= kk -> Ad + kk <= al_ctx L + 65536 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OC CBND Ci D_t_c D_c_p D_c_n D_c_s LC_c SC_c SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_tls : forall Ad kk, ATPv + -200 <= Ad -> 0 <= kk -> Ad + kk <= ATPv + 312 -> disjoint_from Wd Ad kk).      (* [comment removed for export] *)
  { pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_ptr L ALO) as D_l_p. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
    unfold adisj in D_l_t, D_l_p, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
    intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 D_l_t D_l_p D_l_n D_l_s LC_l SC_tls SHR I64b WR WB MSB LMSB TL1 TLN ATR0. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_res : forall Ad kk, al_res L <= Ad -> 0 <= kk -> Ad + kk <= al_res L + 137439023104 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 ORS RHI D_t_r D_p_r D_n_r D_s_r LC_r SC_s SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_shres : forall Ad kk, shad (al_res L) <= Ad -> 0 <= kk -> Ad + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 SR1 SR2 SR3 SHSEP SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (K_hi : forall Ad kk, (Ad + kk <= 2147446784 \/ 17594333495296 <= Ad) -> 0 <= kk -> (6303744 <= Ad /\ Ad + kk <= ATOP) ->
            (Ad + kk <= mb \/ mb + ms <= Ad) -> (Ad + kk <= lmb + 24 \/ lmb + 32 <= Ad) ->
            (Ad + kk <= al_t L \/ al_t L + 4096 <= Ad) -> (Ad + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= Ad) ->
            (Ad + kk <= al_nodes L \/ al_nodes L + 1048576 <= Ad) -> (Ad + kk <= al_store L \/ al_store L + 8388608 <= Ad) ->
            disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 LO BOT STK3 SHR I64b WR WB ATR. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_sh : forall Ad kk, 2147446784 <= Ad -> 0 <= kk -> Ad + kk <= 17594333495296 ->      (* [comment removed for export] *)
            (Ad + kk <= shad mb \/ shad mb + shlen ms <= Ad) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  assert (K_pa : forall Ad kk, al_ptr_array L + 8 * a_nsec st <= Ad -> 0 <= kk -> Ad + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OP OPi OPa OPs D_t_p D_n_p D_s_p LC_p SC_p SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 OFK OFi FBND D_t_f D_f_p D_n_f D_s_f LC_f SC_f SHR I64b WR WB TL1 LMSB MSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros ODi ODa [kD DBND] [jD DIMG]; nd_post). clear -LO BOT STK3 OD ODi DBND DIMG D_t_d D_d_p D_n_d D_s_d LC_d SC_d SHR I64b WR WB TL1 LMSB MSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 FSH SHSEPF SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  pose proof (ao_space L ALO) as RSP'.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }
  (* [comment removed for export] *)
  set (st' := set_nsec (a_nsec st1 - 1) st1) in *.
  assert (PD : Permutation (ch :: sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st' p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  assert (NDcs : List.NoDup (ch :: sec_chunks_of st')) by (destruct WD as [ND _]; exact (Permutation_NoDup (Permutation_sym PD) ND)).
  assert (NOTIN : ~ In ch (sec_chunks_of st')) by (inversion NDcs; assumption).
  (* [comment removed for export] *)
  split.
  { intros a Ha CLa.
    assert (E : m' (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by exact Ha. eapply (disjoint_outside Wd a 1); [| clear; lia].
      destruct CLa as [CLa|TL].
      2:{ (* [comment removed for export] *)
          destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
          4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_ptr L ALO) as DA2. pose proof (ad_ahm_nodes L ALO) as DA3. pose proof (ad_ahm_store L ALO) as DA4.
              unfold adisj in DA1, DA2, DA3, DA4. (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post). (pose proof LSCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ LC_ahm; nd_post).
              apply K_hi; clear -IM OAH OAHI DA1 DA2 DA3 DA4 SC_ahm LC_ahm LMSB; lia. }
          3:{ unfold AIMSH_LO, AIMSH_LEN in IM. pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
              apply K_sh; clear -IM SDM MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia. }
          - apply K_tls; clear -T; lia.
          - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
            apply K_sh; [clear -TS1; lia | clear; lia | clear -TS2 SHCE; lia |].
            destruct (tls_shadow_apart ta mb ms Hta ltac:(clear -MSB; lia)) as [D|D]; [| left; clear -D; lia | right; exact D].
            destruct SC_tls as [D|D]; [right; split; [exact D| exact MAL8] | left; exact D]. }
      destruct CLa as [STa | [CIa | [BLK | SHD]]].
      - apply K_stack; clear -STa; lia.
      - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post).
        pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE in Q7.
        apply K_img; unfold AIMG_HI in *; clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7; lia.
      - (nd_pre BLK 3%nat; intros b Hb R; nd_post). apply In_lb_remove in Hb. destruct Hb as [Hb NK].
        destruct b as [[p'|cls] A' n']; cbn [ab_addr ab_size ab_kind] in R, NK.
        + destruct (proj1 BL p' A' n' Hb) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA' & G')].
          * destruct (BB y Hy) as [B1' B2']. pose proof (awf_fits L st X y WF Hy) as FT. unfold xb_fits in FT. rewrite Sy in FT.
            unfold xb_user in Uy. apply K_res; clear -R B1' B2' FT Uy Ny; lia.
          * assert (NEp : p' <> p) by (intros ->; apply NK; reflexivity).
            assert (INc : In (CSec mb' ms' n') (sec_chunks_of st')).
            { apply (live_sec_in st' p'). cbn [a_live st' set_nsec set_live st1]. rewrite lookup_delete_ne by (intros E; exact (NEp (eq_sym E))). exact Lp. }
            assert (NEc : CSec mb' ms' n' <> ch) by (intros E; apply NOTIN; rewrite <- E; exact INc).
            assert (INc0 : In (CSec mb' ms' n') (sec_chunks_of st)) by (eapply Permutation_in; [exact PD| right; exact INc]).
            destruct WD as [_ DJ]. destruct (DJ _ _ INc0 IN NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
            all: (nd_pre (sec_wf1_facts' L mb' ms' n' G') 13%nat; intros _ JLO JCE _ JNB _ JMSB _ JNMS _ (JC_t & _ & _ & JC_p & JC_n & JC_st & _) _ JN6; nd_post).
            all: (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
            all: assert (INo' : In (CSec mb' ms' n') order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INc0]).
            all: assert (DLj : CSec mb' ms' n' = CSec lmb lms ln \/ (mb' + ms' <= lmb \/ lmb + lms <= mb'))
                   by (destruct (achunk_eq_dec (CSec mb' ms' n') (CSec lmb lms ln)) as [E|NE']; [left; exact E| right; destruct WDo as [_ DJo]; destruct (DJo _ _ INo' INl NE') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1]]).
            all: unfold SEC_UOFF, K_HIGH_MEM in *.
            all: apply K_hi; try (clear -R EA' KAJ KBJ KEJ KCJ KDJ JCE JNMS JN6 Dc JC_t JC_p JC_n JC_st; lia).
            all: destruct DLj as [EE|DLj]; [injection EE as <- <- <-; clear -R EA'; lia| clear -R EA' JNMS JN6 DLj LMSB; lia].
        + (nd_pre (proj1 (proj2 BL) cls A' n' Hb) 3%nat; intros F1 F2 F3; nd_post). eapply disjoint_from_sub; [exact K_fake| clear -R F1; lia| clear -R F3; lia| clear; lia].
      - (nd_pre SHD 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). pose proof (shad_div a') as SD. unfold ASHOFF in SD.
        destruct Ha' as [STa | [CIa | FK]].
        + atop_facts. apply K_sh; [clear -STa SD LO BOT ATR; Z.div_mod_to_equations; lia| clear; lia| clear -STa SD; Z.div_mod_to_equations; lia| clear -STa SD SHCE LO BOT ATR; right; rewrite !shad_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia].   (* [comment removed for export] *)
        + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
          pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
          apply K_sh; clear -R SD SDM Q1 Q3 MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia.
        + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). apply In_lb_remove in Hin. destruct Hin as [Hin _].
          (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros F1 F2 F3; nd_post).
          pose proof (shad_div (al_fake L)) as SDF. pose proof (shlen_div 11571200) as SLF. unfold ASHOFF in SDF.
          eapply disjoint_from_sub; [exact K_shfake| clear -R F1 SD SDF; Z.div_mod_to_equations; lia| clear -R F3 SD SDF SLF FAL8; Z.div_mod_to_equations; lia| clear; lia]. }
    split; [exact E|]. intros Hw. rewrite (wview_agree asegs m m' (wa a) E). exact Hw. }
  (* [comment removed for export] *)
  split; [exact ALO|].
  split.
  { (* [comment removed for export] *) eapply arng_mono; [exact LE|]. eapply (arng_sub L RNG st st'); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros c Hc. eapply Permutation_in; [exact PD| right; exact Hc]. }
  split.
  2: { (* [comment removed for export] *)
       eapply (hf_blocks _ HL); cbn [ah_fake AHQ].
       - eapply AFKD; [exact HFK| exact MU| |].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) K_fake) as F1. pose proof (proj1 (disjoint_from_Forall _ _ _) K_shfake) as F2.
           pose proof (proj1 (disjoint_from_Forall _ _ _) K_dtls) as F3.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xa7288 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
           pose proof (tclr_cell_in (-8) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF5a GF5b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + -8) 16 GF5a ltac:(clear; lia) GF5b)) as F5.
           pose proof (tclr_cell_in (8) 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF6a GF6b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + 8) 8 GF6a ltac:(clear; lia) GF6b)) as F6.
           pose proof (tclr_cell_in (296) 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF7a GF7b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + 296) 8 GF7a ltac:(clear; lia) GF7b)) as F7.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x1401b1 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F8.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x13e098 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F9.
           unfold fake_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
           rewrite Forall_forall in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). specialize (F5 _ Hin).
           specialize (F6 _ Hin). specialize (F7 _ Hin). specialize (F8 _ Hin). specialize (F9 _ Hin). cbn [fst snd] in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           repeat (lazymatch goal with |- _ /\ _ => split end);
             lazymatch goal with      (* [comment removed for export] *)
             | |- context [ATPv + -8] => first [exact F5 | clear -F5; lia]
             | |- context [ATPv + 8] => first [exact F6 | clear -F6; lia]
             | |- context [ATPv + 296] => first [exact F7 | clear -F7; lia]
             | |- _ => first [clear -F1; lia| clear -F2; lia| clear -F3; lia| clear -F4; lia| clear -F8; lia| clear -F9; lia]
             end.
         + pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L + 48) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
           eapply Forall_impl; [| exact F1]. cbv beta. intros iv Hiv. clear -Hiv. lia.
       - intros c F0 n0. rewrite In_lb_remove. cbn [ab_kind]. split; [intros [H _]; exact H| intros H; split; [exact H| discriminate]]. }
  exists X. split.
  2: { eapply (ablocks_free_sec L st X LB p mb ms n st' X LIVE WF); [reflexivity| intros y Hy; exact Hy| exact BL]. }
  (* [comment removed for export] *)
  split. { eapply (awf_delete_sec L st X p mb ms n st' WF LIVE); reflexivity. }
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia | apply K_tls; clear; lia] |]). apply Forall_nil. }
  split. { (* [comment removed for export] *) unfold ainstance. cbn [a_nres a_nsec set_nsec set_live st' st1]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. { (* [comment removed for export] *) unfold athread.
           split; [eapply cells_frameD; [exact T0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           exact UW1. }
  split.
  { (* [comment removed for export] *)
    intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. (pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. (pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  (* [comment removed for export] *)
  split.
  { exists (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_nsec set_live st' st1].
    assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from Wd (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
    { intros q Hq. (nd_pre (qcoupled_bslot_busy L st X Q q CP Hq) 5%nat; intros b Hb Sb Cb Kb; nd_post).
      destruct (BB b Hb) as [B1' B2']. unfold xb_alloc in B1', B2'. rewrite Cb, Kb in B1'. rewrite Cb, Kb, size_of_class_24 in B2'.
      unfold abatch_addr, Q_BATCH_BYTES. apply K_res; [exact B1'| clear; lia| exact B2']. }
    split; [eapply aquar_glob_const_frameD; [exact MU| exact (conj QK MX)| |]; apply K_img; clear; unfold AQ_MAX, AQ_MUTEX, AIMG_HI; lia|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj QC ABL)| unfold aq_tcache; apply K_t; clear; lia| intros q Hq; apply DQ; apply in_app_iff; left; exact Hq]|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj GCQ ABG)| apply K_img; clear; unfold AQ_GCACHE, AIMG_HI; lia| intros q Hq; apply DQ; apply in_app_iff; right; exact Hq]|].
    split; [split; [exact FL1| split; [exact IAS1| intros _; exact IAM2]]|].
    split; [exact CP| exact (conj NB1 (conj NB2 (conj NF (conj NC NM))))]. }
  (* [comment removed for export] *)
  split.
  2: { (* [comment removed for export] *)
       split; [exact DEP'|].
       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact HRT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }
  (* [comment removed for export] *)
  cbn [ah_sec AHQ]. unfold ASEC_of. set (cs' := sec_chunks_of st') in *.
  (* [comment removed for export] *)
  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ CSec mb' ms' n' <> ch
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall Ad kk, mb' + 32 <= Ad -> 0 < kk -> Ad + kk <= mb' + ms' -> disjoint_from Wd Ad kk)
          /\ (forall Ad kk, shad mb' <= Ad -> 0 < kk -> Ad + kk <= shad mb' + ms' / 8 -> disjoint_from Wd Ad kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    (nd_pre (sec_wf1_facts' L mb' ms' n' Wj) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ JSCL _; nd_post).
    (nd_pre JSCL 7%nat; intros JC_t _ _ JC_p JC_n JC_st _; nd_post). unfold K_HIGH_MEM in JLO, JCE.
    (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 2148238848 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)      (* [comment removed for export] *)
           by (rewrite shad_div; unfold ASHOFF; clear -KBJ KDJ JMSB ATR; Z.div_mod_to_equations; lia).
    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [exact NEc|]. all: split; [clear -Dc; lia|].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_hi; [clear -Z1 Z3 KAJ KEJ KCJ; lia| clear -Z2; lia| clear -Z1 Z3 KBJ KDJ; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -KAJ KEJ KCJ JMSB; lia| clear; lia| clear -KBJ KDJ JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia]. }
  (* [comment removed for export] *)
  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (symmetry; exact LENO).
  assert (LCS : Z.of_nat (length cs') = a_nsec st - 1).
  { pose proof (Permutation_length PD) as PL. cbn [length] in PL. rewrite <- WL. clear -PL. lia. }
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE); [reflexivity|].
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  assert (WFA : asec_wf L st' cs').
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec set_live st' st1]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    split; [exact LCS|]. split; [clear -WB I64b; lia|].
    split. { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PD| right; exact Hc]. }
    split; [inversion NDcs; assumption|].
    destruct WD as [_ DJ]. intros ci cj Hi Hj NE. apply DJ; [| | exact NE]; (eapply Permutation_in; [exact PD| right; assumption]). }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]|].   (* [comment removed for export] *)
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L cs' m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM in Hx.
    unfold AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
    assert (SX : 2148238848 <= shad x /\ shad x + 1 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -Hx ATR; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: { (* [comment removed for export] *)
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, AIMG_HI, KLS; exact Hx) HFh).
    2,4: eapply Permutation_Forall; [exact PD|]; constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec set_live st' st1].
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| exact SHZn]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec set_live st' st1].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  - (* [comment removed for export] *)
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO.
             eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    (nd_pre (PER j c Hj') 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    (nd_pre (CHK j mb' ms' n' Hj' NEji) 6%nat; intros Wj _ Dj DCj DSj DHj; nd_post).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  - (* [comment removed for export] *)
    (nd_pre (List.nth_error_split order i NTH) 4%nat; intros o1 rest EO LO1; nd_post).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    + (* [comment removed for export] *)
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      assert (NEli : (length order - 1)%nat <> i) by (clear -NE; lia).
      (nd_pre (PER _ _ NTHL) 3%nat; intros lvl LVl CHl; nd_post). exists lvl. split; [rewrite (LVE _ _ NTHL NEli); exact LVl|].
      (nd_pre (CHK _ lmb lms ln NTHL NEli) 6%nat; intros Wj _ Dj DCj DSj _; nd_post).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      (nd_pre (PER j c Hj') 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      (nd_pre (CHK j mb' ms' n' Hj' NEji) 6%nat; intros Wj _ Dj DCj DSj DHj; nd_post).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End Zd1.
#[using="HL DEPD AFKD CI_OK CI_OK2"] Theorem dfn_sec_big : ltac:(let t := eval cbv delta [dfn_sec_big__stmt] in dfn_sec_big__stmt in exact t).
Proof. exact dfn_sec_big__body. Qed.
End S.
End CANSEC2.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_asecdealloc.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_arecsec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_aputrec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrameD.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecRecycle.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.TwB.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

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

#[using="Type"] Lemma afree_big_eq : forall st (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n -> a_qloc_bytes st <= Q_CACHE ->
  afree st (Some p) = large_dealloc (set_live (delete p (a_live st)) st) mb ms (fun st2 => aret st2).
Proof.
  intros st p mb ms n LIVE NB QB. unfold afree. rewrite LIVE. cbn [chunk_size].
  replace (n <=? Q_MAX) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
  unfold recycle_chunk, large_dealloc.
  replace (a_qloc_bytes (set_nsec (a_nsec (set_live (delete p (a_live st)) st) - 1) (set_live (delete p (a_live st)) st))) with (a_qloc_bytes st) by reflexivity.
  replace (Q_CACHE <? a_qloc_bytes st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition bigW (sp t mb ms PA idx last nodes store : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e48c); (t + 2800, t + 3169);
   (0x1808c8, 0x5d0910); (nodes, nodes + 1048576); (store, store + 8388608);
   (0xab410, 0xab419); (0xab428, 0xab438); (0xab640, 0xab644); (0xab658, 0xab668);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)].

End CANSEC1.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rec rl_skel (cs : constant FSet.t) (t : constr) : bool :=
  if zt_plain_arith_s cs t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(or) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(and) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(not) then rl_skel cs (Array.get args 0)
      else if lt_is_ref h reference:(iff) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else false
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then (if rl_skel cs (Constr.Binder.type b) then rl_skel cs c else false) else false
  | _ => false
  end.
Local Ltac2 rl_prune () : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if rl_skel cs ty then None else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac rl_prune := ltac2:(Control.enter rl_prune).
Set Default Proof Mode "Classic".
Local Ltac rl_lia := rl_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; rl_lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rl_lia ] end ].
Ltac kf := cbn [fst snd]; unfold AQ_MAX, AQ_MIN, AQ_MAXC, AQ_MUTEX, AQ_GCACHE, aq_tcache, AINSTANCE, ATP88, ATSD, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIMG_HI, K_HIGH_MEM in *; repeat split; first [ lia_rel | lia ].

Ltac find_ivb s H :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear -s H; lia]
        | apply Exists_cons_tl; find_ivb s H ].
Ltac solve_sub_fpb s H :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_ivb s H|]); apply Forall_nil.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition dfn_sec_big__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n ->
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 41).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 42).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 43).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 44).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 45).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 46).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_big__stmt 47).
#[using="HL DEPD AFKD CI_OK CI_OK2"] Lemma dfn_sec_big__body : ltac:(let T := type of (fun (h : dfn_sec_big__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo SO pc trt tb mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (SO, (pc, (trt, (tb, (mb, ms)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NBIG AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RSO RA4.
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EA _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_s SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahmx; nd_post).
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SB1 SB2 SB3 SB4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni Na [kN NBND]; nd_post). (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si Sa [kS SBND]; nd_post).   (* [comment removed for export] *)
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci Ca [kC CBND]; nd_post). (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros Ti4 Ta4 [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
  (* [comment removed for export] *)
  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT HRT2 RT3) as PRM.
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  pose proof INST as INST0. (nd_pre INST0 9%nat; intros I32 I48 I64 I72 I112 I680 I984 I40 I56; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS _ SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (pose proof SINST as ndP__; nd_pre ndP__ 6%nat; intros I80 [srt ISRT] JST JBS PAD JGL; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 B1 B3 CX HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (ch := CSec mb ms n) in *.
  assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
  assert (IN : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INo]).
  (* [comment removed for export] *)
  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. clear -NTHL IL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  (nd_pre (sec_wf1_facts' L lmb lms ln WFl) 12%nat; intros LAL LLO LCE LMSE LNB LRZ LMSB LMSAL _ _ LSCL _; nd_post).
  (pose proof (ablk_int _ _ LLO) as ndP__; nd_pre ndP__ 6%nat; intros kLl KALl KBLl KELl KCLl KDLl; nd_post).   (* [comment removed for export] *)
  (pose proof LSCL as ndP__; nd_pre ndP__ 10%nat; intros LC_t LC_c LC_s LC_p LC_n LC_st LC_f LC_d LC_l LC_ahmx; nd_post).      (* [comment removed for export] *)
  destruct (sec_shadow_cb m mb ms n true (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].
  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ (lmb + 32 <= al_nodes L \/ al_nodes L + 1048576 <= lmb) /\ (lmb + 32 <= al_store L \/ al_store L + 8388608 <= lmb)
   /\ tclr lmb 32).      (* [comment removed for export] *)
  { (nd_pre (PER _ _ NTHL) 3%nat; intros llv _ LCH; nd_post). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|].   (* [comment removed for export] *) all: split; [clear -LCE LMSB; lia|]. all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: split; [clear -LC_p LMSB WR WB; lia|].
    all: split; [clear -LC_n LMSB; lia|]. all: split; [clear -LC_st LMSB; lia|]. all: unfold tclr; clear -LC_l LMSB; lia. }
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  pose proof (proj1 (Forall_forall _ _) RSECS ch IN) as [RMB RSH]. unfold ch in RMB, RSH. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  rewrite (afree_big_eq st p mb ms n LIVE NBIG NC).
  set (st1 := set_live (delete p (a_live st)) st).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  iprefix. eapply evtF_cut.
  { eapply (dfn_front_spec DI L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (al_t L) (al_ctx L) (mb + 6128) n b1 cx lo SO (1 + Z.of_nat (length trt)) pc uw _ _ sj tb trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (_ + 6128 + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         end.
    all: try lazymatch goal with
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, EA; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | clear -SC_t MSB; lia | clear -SC_c MSB; lia | clear -SC_n MSB; lia | clear -SC_st MSB; lia | clear -D_t_c; lia]
         | |- rng _ (_ + 6128) _ => eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => unfold tclr; clear -SC_tls MSB; lia
         end.
    all: try assumption.
    all: try (unfold AIMG_HI; generalize NB N6 NMS MLO MCE MAL LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL1u TL4u TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B1 CX RA4; clear; intros; Z.div_mod_to_equations; lia).
    all: try (clear -LTRT; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold dfn_front_post in PFR.
  (nd_pre PFR 13%nat; intros id t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 sj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 14%nat; intros MUf WMf MIf STf IDR HD1 FC1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 DEP1; nd_post).
  apply evtF_done.
  (* [comment removed for export] *)
  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
  assert (SHR : 2148239360 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)   (* [comment removed for export] *)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof QK as QKx. xport QKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof QC as QCx. xport QCx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t DL7 DL8 NBND SBND; kf).
  pose proof I32 as I32x. xport I32x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I64 as I64x. xport I64x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I72 as I72x. xport I72x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I112 as I112x. xport I112x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof ISRT as ISRTx. xport ISRTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I680 as I680x. xport I680x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof PAD as PADx. xport PADx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TI as TIx. xport TIx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TK as TKx. xport TKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof T88 as T88x. xport T88x MUf WMf ltac:(pose proof (tclr_nodes L ALO) as XN; pose proof (tclr_store L ALO) as XS; unfold tclr in XN, XS;      (* [comment removed for export] *)
                                                  clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND SC_tls XN XS; kf).
  pose proof TSD as TSDx. xport TSDx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof CT as CTx. xport CTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3 CL5 SC_c DL9 DL10 NBND SBND; kf).
  pose proof U64 as U64x. xport U64x MUf WMf ltac:(rewrite length_map; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 OP OPi OPa OPs D_t_p SC_p D_n_p D_s_p LENO WB WR NBND SBND; kf).
  pose proof H1 as H1x. xport H1x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t SC_n SC_st NBND SBND; kf).
  pose proof SH as SHx. xport SHx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SHR NBND SBND; kf).
  pose proof JST as JSTx. eapply (junk_frame _ m m1) in JSTx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  pose proof JGL as JGLx. eapply (junk_frame _ m m1) in JGLx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (PRM1 : premap_cells m1).
  { eapply premap_cells_frameD; [exact PRM | exact MUf | ..]; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf. }
  assert (HRO1 : arelro0 m1).
  { eapply arelro0_munch; [exact HRO | exact MUf |]. unfold ARELRO_LO, ARELRO_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (LHDR1 : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m1 lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ tclr lmb 32).
  { intros NE. (nd_pre (LHDR NE) 10%nat; intros L1 L2 L3 L4 L5 L6 L7 L8 L9 L10; nd_post). atop_facts.
    (pose proof (ablk_int _ _ L2) as ndP__; nd_pre ndP__ 6%nat; intros kL KAL KBL KEL KCL KDL; nd_post).   (* [comment removed for export] *)
    xport L1 MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 L2 KAL KBL KEL KCL KDL L3 L4 L5 L8 L9 NBND SBND; kf).
    repeat (split; [assumption|]). first [exact L7 | exact L10]. }
  clear LHDR.
  (* [comment removed for export] *)
  eapply (put_passthru_spec RNG (fun st2 => aret st2) st1 _ ra sp gp tp) with
     (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj1) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 3) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj)
     (nb := Z.of_nat (length (a_qloc st))) (fst0 := qfirst L (q_loc Q)) (lst := qlast L (q_loc Q)) (qb := a_qloc_bytes st).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact STf
       | |- mem_inv _ _ => exact MIf
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact HRO1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- junk_at _ _ 32 => exact JSTx
       | |- junk_at _ _ 16 => exact JGLx
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680x| exact PADx]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
       | |- rw_cells _ _ _ [CB _ _] => exact SHx
       | |- rw_cells _ _ (_ + 152) _ => exact CTx
       | |- rw_cells _ _ (_ + 80) _ => exact QCx
       | |- rw_cells _ _ _ _ => first [eassumption | exact QKx | exact I32x | exact I64x | exact I72x | exact I112x | exact ISRTx | exact TIx | exact TKx | exact T88x | exact TSDx | exact H1x]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64x
       | |- u64arr _ _ _ _ => exact STATS1
       | |- length _ = _ => exact LSJ1
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map; exact LENO
       | |- _ -> _ /\ _ => exact LHDR1
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RSECS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- tclr (al_ptr_array _) _ => eapply tclr_sub; [exact (tclr_ptr L ALO) | clear; lia | clear -WR; lia]      (* [comment removed for export] *)
       | |- tclr _ _ => exact SC_tls
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (_ - _) => eapply rng_sub; [exact RSTK| clear; lia | clear -LO; lia]
       | |- rng _ (shad _) _ => rewrite shlen_div; exact RSH
       | |- rng _ (al_ptr_array _) _ => exact RPA
       | |- rng _ (al_t _) _ => exact RT4
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ _ _ => exact RMB
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia   (* [comment removed for export] *)
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: unfold K_HIGH_MEM, AREQMAX in *.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- _ => try first [ assumption | exact SC_t | exact CL5
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -SP47 LO BOT STK3; lia | clear -OC CBND Ci; lia | clear -OT TBND TIMG; lia | clear -OP OPi OPa OPs WR WB; lia | clear -IL LENO; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -LLB NC; unfold Q_CACHE, Q_BATCH_BYTES in *; lia | clear; rewrite unsigned_lit by lia; lia
                       | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia
                       | clear -LC_t LMSB; lia | clear -LCE LMSB; lia ]
       end.
  (* [comment removed for export] *)
  intros RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LE1 HF PP TC'.
  cbv beta. apply implS_ret.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  (nd_pre PP 12%nat; intros MU2 MI' ST' NSC' SRT' JST' MTX' JGL' ARR' LHDR' [sj' [STATS' LSJ']] SHZ'; nd_post).
  unfold putrec_W in MU2.
  (* [comment removed for export] *)
  eapply (cells_frameD _ m1 m') in FL1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in UW1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR LC_t SC_t D_t_p; kf].
  eapply (stk_transportD _ _ m1 m') in IAS1; [| exact MU2| cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MU2. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by (clear -Hj Hi; lia).
    clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hj Hi. kf. }
  clear IAM1.
  assert (DEP' : ADEPOT DI L m').
  { eapply DEPD; [exact DEP1| exact MU2|].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hq DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 D_n_p D_s_p SC_n SC_st LC_n LC_st LMSB NBND SBND; kf |]).
    apply Forall_nil. }
  clear DEP1.
  apply evtF_done.
  (* [comment removed for export] *)
  unfold afree_post. split; [exact LE|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
  (* [comment removed for export] *)
  assert (MU : munch (bigW (bv_unsigned sp) (al_t L) mb ms (al_ptr_array L) (Z.of_nat i) lmb (al_nodes L) (al_store L)) m m').
  { unfold bigW. eapply munch_trans; [| eapply munch_weaken; [| exact MU2]]. eapply munch_weaken; [| exact MUf]. all: solve_sub_fpb sp MSB. }
  clear MU2 MUf. unfold bigW in MU.
  (* [comment removed for export] *)
  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD. pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as ATR.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_res L ALO) as D_n_r. pose proof (ad_store_res L ALO) as D_s_r.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p. pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_r, D_p_r, D_n_r, D_s_r, D_t_f, D_f_p, D_n_f, D_s_f, D_t_d, D_d_p, D_n_d, D_s_d, D_c_n, D_c_s.
  (pose proof LSCL as ndP__; nd_pre ndP__ 4%nat; intros _ _ LC_r _; nd_post).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_s as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH3 : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI ATR. Z.div_mod_to_equations. lia. }
  (nd_pre RSH3 3%nat; intros SR1 SR2 SR3; nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFi OFa [kF FBND]; nd_post).   (* [comment removed for export] *)
  assert (FSH : 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFi OFa ATR. Z.div_mod_to_equations. lia. }
  assert (SHCE : shad mb + shlen ms <= shad ATOP /\ 17594064011264 <= shad ATOP <= 17594332446720) by (rewrite !shad_div, shlen_div; unfold ASHOFF in *; clear -MCE MAL8 MSAL ATR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, SHCE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- LENO; clear -IL; lia).
  (* [comment removed for export] *)
  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall Ad kk, 0x10000 <= Ad -> 0 <= kk ->      (* [comment removed for export] *)
            (Ad + kk <= 0xab410 \/ (0xab668 <= Ad /\ Ad + kk <= 0xafc00) \/ (0x130c30 <= Ad /\ Ad + kk <= 0x13e488)
             \/ (0x13e48c <= Ad /\ Ad + kk <= 0x1808c8) \/ (0x5d0910 <= Ad /\ Ad + kk <= AIMG_HI)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (K_stack : forall Ad kk, bv_unsigned sp <= Ad -> 0 <= kk -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 LO BOT STK3 TL2 OP OPi OPa OPs LCE LMSB MCE SHR DL2 DL5 I64b WB WR ATR. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_t : forall Ad kk, al_t L <= Ad -> 0 <= kk -> (Ad + kk <= al_t L + 2800 \/ (al_t L + 3169 <= Ad /\ Ad + kk <= al_t L + 4096)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TL2 TL1u TL4u DL7 DL8 D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_ctx : forall Ad kk, al_ctx L <= Ad -> 0 <= kk -> Ad + kk <= al_ctx L + 65536 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OC CBND Ci D_t_c D_c_p D_c_n D_c_s LC_c SC_c SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_tls : forall Ad kk, ATPv + -200 <= Ad -> 0 <= kk -> Ad + kk <= ATPv + 312 -> disjoint_from Wd Ad kk).      (* [comment removed for export] *)
  { pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_ptr L ALO) as D_l_p. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
    unfold adisj in D_l_t, D_l_p, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
    intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 D_l_t D_l_p D_l_n D_l_s LC_l SC_tls SHR I64b WR WB MSB LMSB TL1 TLN ATR0. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_res : forall Ad kk, al_res L <= Ad -> 0 <= kk -> Ad + kk <= al_res L + 137439023104 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 ORS RHI D_t_r D_p_r D_n_r D_s_r LC_r SC_s SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_shres : forall Ad kk, shad (al_res L) <= Ad -> 0 <= kk -> Ad + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 SR1 SR2 SR3 SHSEP SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (K_hi : forall Ad kk, (Ad + kk <= 2147446784 \/ 17594333495296 <= Ad) -> 0 <= kk -> (6307840 <= Ad /\ Ad + kk <= ATOP) ->
            (Ad + kk <= mb \/ mb + ms <= Ad) -> (Ad + kk <= lmb + 24 \/ lmb + 32 <= Ad) ->
            (Ad + kk <= al_t L \/ al_t L + 4096 <= Ad) -> (Ad + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= Ad) ->
            (Ad + kk <= al_nodes L \/ al_nodes L + 1048576 <= Ad) -> (Ad + kk <= al_store L \/ al_store L + 8388608 <= Ad) ->
            disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 LO BOT STK3 SHR I64b WR WB ATR. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_sh : forall Ad kk, 2147446784 <= Ad -> 0 <= kk -> Ad + kk <= 17594333495296 ->      (* [comment removed for export] *)
            (Ad + kk <= shad mb \/ shad mb + shlen ms <= Ad) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  assert (K_pa : forall Ad kk, al_ptr_array L + 8 * a_nsec st <= Ad -> 0 <= kk -> Ad + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OP OPi OPa OPs D_t_p D_n_p D_s_p LC_p SC_p SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 OFK OFi FBND D_t_f D_f_p D_n_f D_s_f LC_f SC_f SHR I64b WR WB TL1 LMSB MSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros ODi ODa [kD DBND] [jD DIMG]; nd_post). clear -LO BOT STK3 OD ODi DBND DIMG D_t_d D_d_p D_n_d D_s_d LC_d SC_d SHR I64b WR WB TL1 LMSB MSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 FSH SHSEPF SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  pose proof (ao_space L ALO) as RSP'.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }
  (* [comment removed for export] *)
  set (st' := set_nsec (a_nsec st1 - 1) st1) in *.
  assert (PD : Permutation (ch :: sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st' p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  assert (NDcs : List.NoDup (ch :: sec_chunks_of st')) by (destruct WD as [ND _]; exact (Permutation_NoDup (Permutation_sym PD) ND)).
  assert (NOTIN : ~ In ch (sec_chunks_of st')) by (inversion NDcs; assumption).
  (* [comment removed for export] *)
  split.
  { intros a Ha CLa.
    assert (E : m' (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by exact Ha. eapply (disjoint_outside Wd a 1); [| clear; lia].
      destruct CLa as [CLa|TL].
      2:{ (* [comment removed for export] *)
          destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
          4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_ptr L ALO) as DA2. pose proof (ad_ahm_nodes L ALO) as DA3. pose proof (ad_ahm_store L ALO) as DA4.
              unfold adisj in DA1, DA2, DA3, DA4. (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post). (pose proof LSCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ LC_ahm; nd_post).
              apply K_hi; clear -IM OAH OAHI DA1 DA2 DA3 DA4 SC_ahm LC_ahm LMSB; lia. }
          3:{ unfold AIMSH_LO, AIMSH_LEN in IM. pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
              apply K_sh; clear -IM SDM MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia. }
          - apply K_tls; clear -T; lia.
          - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
            apply K_sh; [clear -TS1; lia | clear; lia | clear -TS2 SHCE; lia |].
            destruct (tls_shadow_apart ta mb ms Hta ltac:(clear -MSB; lia)) as [D|D]; [| left; clear -D; lia | right; exact D].
            destruct SC_tls as [D|D]; [right; split; [exact D| exact MAL8] | left; exact D]. }
      destruct CLa as [STa | [CIa | [BLK | SHD]]].
      - apply K_stack; clear -STa; lia.
      - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post).
        pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE in Q7.
        apply K_img; unfold AIMG_HI in *; clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7; lia.
      - (nd_pre BLK 3%nat; intros b Hb R; nd_post). apply In_lb_remove in Hb. destruct Hb as [Hb NK].
        destruct b as [[p'|cls] A' n']; cbn [ab_addr ab_size ab_kind] in R, NK.
        + destruct (proj1 BL p' A' n' Hb) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA' & G')].
          * destruct (BB y Hy) as [B1' B2']. pose proof (awf_fits L st X y WF Hy) as FT. unfold xb_fits in FT. rewrite Sy in FT.
            unfold xb_user in Uy. apply K_res; clear -R B1' B2' FT Uy Ny; lia.
          * assert (NEp : p' <> p) by (intros ->; apply NK; reflexivity).
            assert (INc : In (CSec mb' ms' n') (sec_chunks_of st')).
            { apply (live_sec_in st' p'). cbn [a_live st' set_nsec set_live st1]. rewrite lookup_delete_ne by (intros E; exact (NEp (eq_sym E))). exact Lp. }
            assert (NEc : CSec mb' ms' n' <> ch) by (intros E; apply NOTIN; rewrite <- E; exact INc).
            assert (INc0 : In (CSec mb' ms' n') (sec_chunks_of st)) by (eapply Permutation_in; [exact PD| right; exact INc]).
            destruct WD as [_ DJ]. destruct (DJ _ _ INc0 IN NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
            all: (nd_pre (sec_wf1_facts' L mb' ms' n' G') 13%nat; intros _ JLO JCE _ JNB _ JMSB _ JNMS _ (JC_t & _ & _ & JC_p & JC_n & JC_st & _) _ JN6; nd_post).
            all: (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
            all: assert (INo' : In (CSec mb' ms' n') order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INc0]).
            all: assert (DLj : CSec mb' ms' n' = CSec lmb lms ln \/ (mb' + ms' <= lmb \/ lmb + lms <= mb'))
                   by (destruct (achunk_eq_dec (CSec mb' ms' n') (CSec lmb lms ln)) as [E|NE']; [left; exact E| right; destruct WDo as [_ DJo]; destruct (DJo _ _ INo' INl NE') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1]]).
            all: unfold SEC_UOFF, K_HIGH_MEM in *.
            all: apply K_hi; try (clear -R EA' KAJ KBJ KEJ KCJ KDJ JCE JNMS JN6 Dc JC_t JC_p JC_n JC_st; lia).
            all: destruct DLj as [EE|DLj]; [injection EE as <- <- <-; clear -R EA'; lia| clear -R EA' JNMS JN6 DLj LMSB; lia].
        + (nd_pre (proj1 (proj2 BL) cls A' n' Hb) 3%nat; intros F1 F2 F3; nd_post). eapply disjoint_from_sub; [exact K_fake| clear -R F1; lia| clear -R F3; lia| clear; lia].
      - (nd_pre SHD 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). pose proof (shad_div a') as SD. unfold ASHOFF in SD.
        destruct Ha' as [STa | [CIa | FK]].
        + atop_facts. apply K_sh; [clear -STa SD LO BOT ATR; Z.div_mod_to_equations; lia| clear; lia| clear -STa SD; Z.div_mod_to_equations; lia| clear -STa SD SHCE LO BOT ATR; right; rewrite !shad_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia].   (* [comment removed for export] *)
        + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
          pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
          apply K_sh; clear -R SD SDM Q1 Q3 MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia.
        + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). apply In_lb_remove in Hin. destruct Hin as [Hin _].
          (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros F1 F2 F3; nd_post).
          pose proof (shad_div (al_fake L)) as SDF. pose proof (shlen_div 11571200) as SLF. unfold ASHOFF in SDF.
          eapply disjoint_from_sub; [exact K_shfake| clear -R F1 SD SDF; Z.div_mod_to_equations; lia| clear -R F3 SD SDF SLF FAL8; Z.div_mod_to_equations; lia| clear; lia]. }
    split; [exact E|]. intros Hw. rewrite (wview_agree asegs m m' (wa a) E). exact Hw. }
  (* [comment removed for export] *)
  split; [exact ALO|].
  split.
  { (* [comment removed for export] *) eapply arng_mono; [exact LE|]. eapply (arng_sub L RNG st st'); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros c Hc. eapply Permutation_in; [exact PD| right; exact Hc]. }
  split.
  2: { (* [comment removed for export] *)
       eapply (hf_blocks _ HL); cbn [ah_fake AHQ].
       - eapply AFKD; [exact HFK| exact MU| |].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) K_fake) as F1. pose proof (proj1 (disjoint_from_Forall _ _ _) K_shfake) as F2.
           pose proof (proj1 (disjoint_from_Forall _ _ _) K_dtls) as F3.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xa7668 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
           pose proof (tclr_cell_in (-8) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF5a GF5b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + -8) 16 GF5a ltac:(clear; lia) GF5b)) as F5.
           pose proof (tclr_cell_in (8) 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF6a GF6b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + 8) 8 GF6a ltac:(clear; lia) GF6b)) as F6.
           pose proof (tclr_cell_in (296) 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF7a GF7b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + 296) 8 GF7a ltac:(clear; lia) GF7b)) as F7.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x1405b1 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F8.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x13e498 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F9.
           unfold fake_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
           rewrite Forall_forall in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). specialize (F5 _ Hin).
           specialize (F6 _ Hin). specialize (F7 _ Hin). specialize (F8 _ Hin). specialize (F9 _ Hin). cbn [fst snd] in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           repeat (lazymatch goal with |- _ /\ _ => split end);
             lazymatch goal with      (* [comment removed for export] *)
             | |- context [ATPv + -8] => first [exact F5 | clear -F5; lia]
             | |- context [ATPv + 8] => first [exact F6 | clear -F6; lia]
             | |- context [ATPv + 296] => first [exact F7 | clear -F7; lia]
             | |- _ => first [clear -F1; lia| clear -F2; lia| clear -F3; lia| clear -F4; lia| clear -F8; lia| clear -F9; lia]
             end.
         + pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L + 48) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
           eapply Forall_impl; [| exact F1]. cbv beta. intros iv Hiv. clear -Hiv. lia.
       - intros c F0 n0. rewrite In_lb_remove. cbn [ab_kind]. split; [intros [H _]; exact H| intros H; split; [exact H| discriminate]]. }
  exists X. split.
  2: { eapply (ablocks_free_sec L st X LB p mb ms n st' X LIVE WF); [reflexivity| intros y Hy; exact Hy| exact BL]. }
  (* [comment removed for export] *)
  split. { eapply (awf_delete_sec L st X p mb ms n st' WF LIVE); reflexivity. }
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia | apply K_tls; clear; lia] |]). apply Forall_nil. }
  split. { (* [comment removed for export] *) unfold ainstance. cbn [a_nres a_nsec set_nsec set_live st' st1]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. { (* [comment removed for export] *) unfold athread.
           split; [eapply cells_frameD; [exact T0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           exact UW1. }
  split.
  { (* [comment removed for export] *)
    intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. (pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. (pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  (* [comment removed for export] *)
  split.
  { exists (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_nsec set_live st' st1].
    assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from Wd (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
    { intros q Hq. (nd_pre (qcoupled_bslot_busy L st X Q q CP Hq) 5%nat; intros b Hb Sb Cb Kb; nd_post).
      destruct (BB b Hb) as [B1' B2']. unfold xb_alloc in B1', B2'. rewrite Cb, Kb in B1'. rewrite Cb, Kb, size_of_class_24 in B2'.
      unfold abatch_addr, Q_BATCH_BYTES. apply K_res; [exact B1'| clear; lia| exact B2']. }
    split; [eapply aquar_glob_const_frameD; [exact MU| exact (conj QK MX)| |]; apply K_img; clear; unfold AQ_MAX, AQ_MUTEX, AIMG_HI; lia|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj QC ABL)| unfold aq_tcache; apply K_t; clear; lia| intros q Hq; apply DQ; apply in_app_iff; left; exact Hq]|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj GCQ ABG)| apply K_img; clear; unfold AQ_GCACHE, AIMG_HI; lia| intros q Hq; apply DQ; apply in_app_iff; right; exact Hq]|].
    split; [split; [exact FL1| split; [exact IAS1| intros _; exact IAM2]]|].
    split; [exact CP| exact (conj NB1 (conj NB2 (conj NF (conj NC NM))))]. }
  (* [comment removed for export] *)
  split.
  2: { (* [comment removed for export] *)
       split; [exact DEP'|].
       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact HRT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }
  (* [comment removed for export] *)
  cbn [ah_sec AHQ]. unfold ASEC_of. set (cs' := sec_chunks_of st') in *.
  (* [comment removed for export] *)
  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ CSec mb' ms' n' <> ch
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall Ad kk, mb' + 32 <= Ad -> 0 < kk -> Ad + kk <= mb' + ms' -> disjoint_from Wd Ad kk)
          /\ (forall Ad kk, shad mb' <= Ad -> 0 < kk -> Ad + kk <= shad mb' + ms' / 8 -> disjoint_from Wd Ad kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    (nd_pre (sec_wf1_facts' L mb' ms' n' Wj) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ JSCL _; nd_post).
    (nd_pre JSCL 7%nat; intros JC_t _ _ JC_p JC_n JC_st _; nd_post). unfold K_HIGH_MEM in JLO, JCE.
    (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 2148239360 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)      (* [comment removed for export] *)
           by (rewrite shad_div; unfold ASHOFF; clear -KBJ KDJ JMSB ATR; Z.div_mod_to_equations; lia).
    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [exact NEc|]. all: split; [clear -Dc; lia|].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_hi; [clear -Z1 Z3 KAJ KEJ KCJ; lia| clear -Z2; lia| clear -Z1 Z3 KBJ KDJ; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -KAJ KEJ KCJ JMSB; lia| clear; lia| clear -KBJ KDJ JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia]. }
  (* [comment removed for export] *)
  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (symmetry; exact LENO).
  assert (LCS : Z.of_nat (length cs') = a_nsec st - 1).
  { pose proof (Permutation_length PD) as PL. cbn [length] in PL. rewrite <- WL. clear -PL. lia. }
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE); [reflexivity|].
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  assert (WFA : asec_wf L st' cs').
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec set_live st' st1]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    split; [exact LCS|]. split; [clear -WB I64b; lia|].
    split. { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PD| right; exact Hc]. }
    split; [inversion NDcs; assumption|].
    destruct WD as [_ DJ]. intros ci cj Hi Hj NE. apply DJ; [| | exact NE]; (eapply Permutation_in; [exact PD| right; assumption]). }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]|].   (* [comment removed for export] *)
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L cs' m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM in Hx.
    unfold AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
    assert (SX : 2148239360 <= shad x /\ shad x + 1 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -Hx ATR; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: { (* [comment removed for export] *)
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, AIMG_HI, KLS; exact Hx) HFh).
    2,4: eapply Permutation_Forall; [exact PD|]; constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec set_live st' st1].
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| exact SHZn]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec set_live st' st1].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  - (* [comment removed for export] *)
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO.
             eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    (nd_pre (PER j c Hj') 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    (nd_pre (CHK j mb' ms' n' Hj' NEji) 6%nat; intros Wj _ Dj DCj DSj DHj; nd_post).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  - (* [comment removed for export] *)
    (nd_pre (List.nth_error_split order i NTH) 4%nat; intros o1 rest EO LO1; nd_post).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    + (* [comment removed for export] *)
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      assert (NEli : (length order - 1)%nat <> i) by (clear -NE; lia).
      (nd_pre (PER _ _ NTHL) 3%nat; intros lvl LVl CHl; nd_post). exists lvl. split; [rewrite (LVE _ _ NTHL NEli); exact LVl|].
      (nd_pre (CHK _ lmb lms ln NTHL NEli) 6%nat; intros Wj _ Dj DCj DSj _; nd_post).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      (nd_pre (PER j c Hj') 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      (nd_pre (CHK j mb' ms' n' Hj' NEji) 6%nat; intros Wj _ Dj DCj DSj DHj; nd_post).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End Zd1.
#[using="HL DEPD AFKD CI_OK CI_OK2"] Theorem dfn_sec_big : ltac:(let t := eval cbv delta [dfn_sec_big__stmt] in dfn_sec_big__stmt in exact t).
Proof. exact dfn_sec_big__body. Qed.
End S.
End CANSEC2.
(* [comment removed for export] *)
End TwB.
End ADfnS_big.

(* [comment removed for export] *)
Module ASF_big.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHolesD ASecRecycle. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_asecdealloc OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_arecsec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_aputrec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrameD OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecRecycle OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.
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

#[using="Type"] Lemma afree_big_eq : forall st (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n -> a_qloc_bytes st <= Q_CACHE ->
  afree st (Some p) = large_dealloc (set_live (delete p (a_live st)) st) mb ms (fun st2 => aret st2).
Proof.
  intros st p mb ms n LIVE NB QB. unfold afree. rewrite LIVE. cbn [chunk_size].
  replace (n <=? Q_MAX) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
  unfold recycle_chunk, large_dealloc.
  replace (a_qloc_bytes (set_nsec (a_nsec (set_live (delete p (a_live st)) st) - 1) (set_live (delete p (a_live st)) st))) with (a_qloc_bytes st) by reflexivity.
  replace (Q_CACHE <? a_qloc_bytes st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition bigW (sp t mb ms PA idx last nodes store : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (0xaf800, 0xaf800 + 0x81030); (0x13e088, 0x13e08c); (t + 2800, t + 3169);
   (0x1804c8, 0x5d0510); (nodes, nodes + 1048576); (store, store + 8388608);
   (0xab010, 0xab019); (0xab028, 0xab038); (0xab240, 0xab244); (0xab258, 0xab268);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)].

End CANSEC1.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rec rl_skel (cs : constant FSet.t) (t : constr) : bool :=
  if zt_plain_arith_s cs t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(or) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(and) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(not) then rl_skel cs (Array.get args 0)
      else if lt_is_ref h reference:(iff) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else false
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then (if rl_skel cs (Constr.Binder.type b) then rl_skel cs c else false) else false
  | _ => false
  end.
Local Ltac2 rl_prune () : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if rl_skel cs ty then None else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac rl_prune := ltac2:(Control.enter rl_prune).
Set Default Proof Mode "Classic".
Local Ltac rl_lia := rl_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; rl_lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rl_lia ] end ].
Ltac kf := cbn [fst snd]; unfold AQ_MAX, AQ_MIN, AQ_MAXC, AQ_MUTEX, AQ_GCACHE, aq_tcache, AINSTANCE, ATP88, ATSD, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIMG_HI, K_HIGH_MEM in *; repeat split; first [ lia_rel | lia ].

Ltac find_ivb s H :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear -s H; lia]
        | apply Exists_cons_tl; find_ivb s H ].
Ltac solve_sub_fpb s H :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_ivb s H|]); apply Forall_nil.

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition afree_sec_big__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n ->
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
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 42).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 43).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 44).
#[using="HL DEPD AFKD CI_OK CI_OK2"] Lemma afree_sec_big__body : ltac:(let T := type of (fun (h : afree_sec_big__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (tr, (mb, ms))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NBIG AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EA _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_s SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahmx; nd_post).
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SB1 SB2 SB3 SB4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni Na [kN NBND]; nd_post). (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si Sa [kS SBND]; nd_post).   (* [comment removed for export] *)
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci Ca [kC CBND]; nd_post). (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros Ti4 Ta4 [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  (* [comment removed for export] *)
  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT HRT2 RT3) as PRM.
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  pose proof INST as INST0. (nd_pre INST0 9%nat; intros I32 I48 I64 I72 I112 I680 I984 I40 I56; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS _ SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (pose proof SINST as ndP__; nd_pre ndP__ 6%nat; intros I80 [srt ISRT] JST JBS PAD JGL; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 B1 B3 CX HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (ch := CSec mb ms n) in *.
  assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
  assert (IN : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INo]).
  (* [comment removed for export] *)
  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. clear -NTHL IL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  (nd_pre (sec_wf1_facts' L lmb lms ln WFl) 12%nat; intros LAL LLO LCE LMSE LNB LRZ LMSB LMSAL _ _ LSCL _; nd_post).
  (pose proof (ablk_int _ _ LLO) as ndP__; nd_pre ndP__ 6%nat; intros kLl KALl KBLl KELl KCLl KDLl; nd_post).   (* [comment removed for export] *)
  (pose proof LSCL as ndP__; nd_pre ndP__ 10%nat; intros LC_t LC_c LC_s LC_p LC_n LC_st LC_f LC_d LC_l LC_ahmx; nd_post).      (* [comment removed for export] *)
  destruct (sec_shadow_cb m mb ms n true (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].
  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ (lmb + 32 <= al_nodes L \/ al_nodes L + 1048576 <= lmb) /\ (lmb + 32 <= al_store L \/ al_store L + 8388608 <= lmb)
   /\ tclr lmb 32).      (* [comment removed for export] *)
  { (nd_pre (PER _ _ NTHL) 3%nat; intros llv _ LCH; nd_post). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|].   (* [comment removed for export] *) all: split; [clear -LCE LMSB; lia|]. all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: split; [clear -LC_p LMSB WR WB; lia|].
    all: split; [clear -LC_n LMSB; lia|]. all: split; [clear -LC_st LMSB; lia|]. all: unfold tclr; clear -LC_l LMSB; lia. }
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  pose proof (proj1 (Forall_forall _ _) RSECS ch IN) as [RMB RSH]. unfold ch in RMB, RSH. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  rewrite (afree_big_eq st p mb ms n LIVE NBIG NC).
  set (st1 := set_live (delete p (a_live st)) st).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  iprefix. eapply evtF_cut.
  { eapply (free_front_spec DI L (q_ia Q) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (al_t L) (al_ctx L) (mb + 6128) n b1 cx lo (al_top L) (al_bot L) uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (_ + 6128 + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         end.
    all: try lazymatch goal with
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EA; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | clear -SC_t MSB; lia | clear -SC_c MSB; lia | clear -SC_n MSB; lia | clear -SC_st MSB; lia | clear -D_t_c; lia]
         | |- rng _ (_ + 6128) _ => eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => unfold tclr; clear -SC_tls MSB; lia
         end.
    all: try assumption.
    all: try (unfold AIMG_HI; generalize NB N6 NMS MLO MCE MAL LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL1u TL4u TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B1 CX RA4; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  (nd_pre PFR 15%nat; intros id t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 sj1 tb1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MUf WMf MIf STf IDR HD1 FC1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 SS1 TB1 LTB1 FRS1 DEP1; nd_post).
  apply evtF_done.
  (* [comment removed for export] *)
  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
  assert (SHR : 2148238848 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)   (* [comment removed for export] *)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof QK as QKx. xport QKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof QC as QCx. xport QCx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t DL7 DL8 NBND SBND; kf).
  pose proof I32 as I32x. xport I32x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I64 as I64x. xport I64x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I72 as I72x. xport I72x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I112 as I112x. xport I112x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof ISRT as ISRTx. xport ISRTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I680 as I680x. xport I680x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof PAD as PADx. xport PADx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TI as TIx. xport TIx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TK as TKx. xport TKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof T88 as T88x. xport T88x MUf WMf ltac:(pose proof (tclr_nodes L ALO) as XN; pose proof (tclr_store L ALO) as XS; unfold tclr in XN, XS;      (* [comment removed for export] *)
                                                  clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND SC_tls XN XS; kf).
  pose proof TSD as TSDx. xport TSDx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof CT as CTx. xport CTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3 CL5 SC_c DL9 DL10 NBND SBND; kf).
  pose proof U64 as U64x. xport U64x MUf WMf ltac:(rewrite length_map; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 OP OPi OPa OPs D_t_p SC_p D_n_p D_s_p LENO WB WR NBND SBND; kf).
  pose proof H1 as H1x. xport H1x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t SC_n SC_st NBND SBND; kf).
  pose proof SH as SHx. xport SHx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SHR NBND SBND; kf).
  pose proof JST as JSTx. eapply (junk_frame _ m m1) in JSTx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  pose proof JGL as JGLx. eapply (junk_frame _ m m1) in JGLx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (PRM1 : premap_cells m1).
  { eapply premap_cells_frameD; [exact PRM | exact MUf | ..]; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf. }
  assert (HRO1 : arelro0 m1).
  { eapply arelro0_munch; [exact HRO | exact MUf |]. unfold ARELRO_LO, ARELRO_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (LHDR1 : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m1 lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ tclr lmb 32).
  { intros NE. (nd_pre (LHDR NE) 10%nat; intros L1 L2 L3 L4 L5 L6 L7 L8 L9 L10; nd_post). atop_facts.
    (pose proof (ablk_int _ _ L2) as ndP__; nd_pre ndP__ 6%nat; intros kL KAL KBL KEL KCL KDL; nd_post).   (* [comment removed for export] *)
    xport L1 MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 L2 KAL KBL KEL KCL KDL L3 L4 L5 L8 L9 NBND SBND; kf).
    repeat (split; [assumption|]). first [exact L7 | exact L10]. }
  clear LHDR.
  (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply (put_passthru_spec RNG (fun st2 => aret st2) st1 _ _ sp0 gp tp) with
     (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj1) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 3) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj)
     (nb := Z.of_nat (length (a_qloc st))) (fst0 := qfirst L (q_loc Q)) (lst := qlast L (q_loc Q)) (qb := a_qloc_bytes st).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite Hsp; exact STf
       | |- mem_inv _ _ => exact MIf
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact HRO1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- junk_at _ _ 32 => exact JSTx
       | |- junk_at _ _ 16 => exact JGLx
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680x| exact PADx]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
       | |- rw_cells _ _ _ [CB _ _] => exact SHx
       | |- rw_cells _ _ (_ + 152) _ => exact CTx
       | |- rw_cells _ _ (_ + 80) _ => exact QCx
       | |- rw_cells _ _ _ _ => first [eassumption | exact QKx | exact I32x | exact I64x | exact I72x | exact I112x | exact ISRTx | exact TIx | exact TKx | exact T88x | exact TSDx | exact H1x]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64x
       | |- u64arr _ _ _ _ => exact STATS1
       | |- length _ = _ => exact LSJ1
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map; exact LENO
       | |- _ -> _ /\ _ => exact LHDR1
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RSECS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- tclr (al_ptr_array _) _ => eapply tclr_sub; [exact (tclr_ptr L ALO) | clear; lia | clear -WR; lia]      (* [comment removed for export] *)
       | |- tclr _ _ => exact SC_tls
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (_ - _) => rewrite Hsp; eapply rng_sub; [exact RSTK| clear; lia | clear -LO; lia]
       | |- rng _ (shad _) _ => rewrite shlen_div; exact RSH
       | |- rng _ (al_ptr_array _) _ => exact RPA
       | |- rng _ (al_t _) _ => exact RT4
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ _ _ => exact RMB
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia   (* [comment removed for export] *)
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: try rewrite Hsp.
  all: unfold K_HIGH_MEM, AREQMAX in *.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- _ => try first [ assumption | exact SC_t | exact CL5
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -SP47 LO BOT STK3; lia | clear -OC CBND Ci; lia | clear -OT TBND TIMG; lia | clear -OP OPi OPa OPs WR WB; lia | clear -IL LENO; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -LLB NC; unfold Q_CACHE, Q_BATCH_BYTES in *; lia | clear; rewrite unsigned_lit by lia; lia
                       | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia
                       | clear -LC_t LMSB; lia | clear -LCE LMSB; lia ]
       end.
  (* [comment removed for export] *)
  intros RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LE1 HF PP TC'.
  cbv beta. apply implS_ret.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  (nd_pre PP 12%nat; intros MU2 MI' ST' NSC' SRT' JST' MTX' JGL' ARR' LHDR' [sj' [STATS' LSJ']] SHZ'; nd_post).
  unfold putrec_W in MU2.
  unname_sp.
  (* [comment removed for export] *)
  apply rw_cells_of_u64arr in TB1. rewrite LTB1 in TB1.
  eapply (cells_frameD _ m1 m') in SS1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in TB1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in FRS1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in FL1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in UW1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR LC_t SC_t D_t_p; kf].
  eapply (stk_transportD _ _ m1 m') in IAS1; [| exact MU2| cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xaf808 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MU2. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by (clear -Hj Hi; lia).
    clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hj Hi. kf. }
  clear IAM1.
  assert (DEP' : ADEPOT DI L m').
  { eapply DEPD; [exact DEP1| exact MU2|].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hq DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 D_n_p D_s_p SC_n SC_st LC_n LC_st LMSB NBND SBND; kf |]).
    apply Forall_nil. }
  clear DEP1.
  replace (ret_pc (Z_to_bv 64 353068)) with (Z_to_bv 64 353068) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  eapply evtF_mono.
  { eapply (ficptD_spec RNG' sp gp tp); [exact ST' | atop_facts; clear -BOT STK3; lia | clear -LO; lia | exact MI'
      | eexists; split; [exact SS1 | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by (clear; lia); exact TB1 | reflexivity]
      | exact FRS1 | eapply rng_fp_le; [exact LE| exact RIMG] | eapply rng_fp_le; [exact LE| exact RTLS] | eapply rng_fp_le; [exact LE| exact RSTK] ]. }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  unfold afree_post. split; [exact LE|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST3|].
  (* [comment removed for export] *)
  assert (MU : munch (bigW (bv_unsigned sp) (al_t L) mb ms (al_ptr_array L) (Z.of_nat i) lmb (al_nodes L) (al_store L)) m m').
  { unfold bigW. eapply munch_trans; [| eapply munch_weaken; [| exact MU2]]. eapply munch_weaken; [| exact MUf]. all: solve_sub_fpb sp MSB. }
  clear MU2 MUf. unfold bigW in MU.
  (* [comment removed for export] *)
  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD. pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as ATR.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_res L ALO) as D_n_r. pose proof (ad_store_res L ALO) as D_s_r.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p. pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_r, D_p_r, D_n_r, D_s_r, D_t_f, D_f_p, D_n_f, D_s_f, D_t_d, D_d_p, D_n_d, D_s_d, D_c_n, D_c_s.
  (pose proof LSCL as ndP__; nd_pre ndP__ 4%nat; intros _ _ LC_r _; nd_post).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_s as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH3 : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI ATR. Z.div_mod_to_equations. lia. }
  (nd_pre RSH3 3%nat; intros SR1 SR2 SR3; nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFi OFa [kF FBND]; nd_post).   (* [comment removed for export] *)
  assert (FSH : 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFi OFa ATR. Z.div_mod_to_equations. lia. }
  assert (SHCE : shad mb + shlen ms <= shad ATOP /\ 17594064011264 <= shad ATOP <= 17594332446720) by (rewrite !shad_div, shlen_div; unfold ASHOFF in *; clear -MCE MAL8 MSAL ATR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, SHCE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- LENO; clear -IL; lia).
  (* [comment removed for export] *)
  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall Ad kk, 0x10000 <= Ad -> 0 <= kk ->      (* [comment removed for export] *)
            (Ad + kk <= 0xab010 \/ (0xab268 <= Ad /\ Ad + kk <= 0xaf800) \/ (0x130830 <= Ad /\ Ad + kk <= 0x13e088)
             \/ (0x13e08c <= Ad /\ Ad + kk <= 0x1804c8) \/ (0x5d0510 <= Ad /\ Ad + kk <= AIMG_HI)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (K_stack : forall Ad kk, bv_unsigned sp <= Ad -> 0 <= kk -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 LO BOT STK3 TL2 OP OPi OPa OPs LCE LMSB MCE SHR DL2 DL5 I64b WB WR ATR. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_t : forall Ad kk, al_t L <= Ad -> 0 <= kk -> (Ad + kk <= al_t L + 2800 \/ (al_t L + 3169 <= Ad /\ Ad + kk <= al_t L + 4096)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TL2 TL1u TL4u DL7 DL8 D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_ctx : forall Ad kk, al_ctx L <= Ad -> 0 <= kk -> Ad + kk <= al_ctx L + 65536 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OC CBND Ci D_t_c D_c_p D_c_n D_c_s LC_c SC_c SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_tls : forall Ad kk, ATPv + -200 <= Ad -> 0 <= kk -> Ad + kk <= ATPv + 312 -> disjoint_from Wd Ad kk).      (* [comment removed for export] *)
  { pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_ptr L ALO) as D_l_p. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
    unfold adisj in D_l_t, D_l_p, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
    intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 D_l_t D_l_p D_l_n D_l_s LC_l SC_tls SHR I64b WR WB MSB LMSB TL1 TLN ATR0. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_res : forall Ad kk, al_res L <= Ad -> 0 <= kk -> Ad + kk <= al_res L + 137439023104 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 ORS RHI D_t_r D_p_r D_n_r D_s_r LC_r SC_s SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_shres : forall Ad kk, shad (al_res L) <= Ad -> 0 <= kk -> Ad + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 SR1 SR2 SR3 SHSEP SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (K_hi : forall Ad kk, (Ad + kk <= 2147446784 \/ 17594333495296 <= Ad) -> 0 <= kk -> (6303744 <= Ad /\ Ad + kk <= ATOP) ->
            (Ad + kk <= mb \/ mb + ms <= Ad) -> (Ad + kk <= lmb + 24 \/ lmb + 32 <= Ad) ->
            (Ad + kk <= al_t L \/ al_t L + 4096 <= Ad) -> (Ad + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= Ad) ->
            (Ad + kk <= al_nodes L \/ al_nodes L + 1048576 <= Ad) -> (Ad + kk <= al_store L \/ al_store L + 8388608 <= Ad) ->
            disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 LO BOT STK3 SHR I64b WR WB ATR. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_sh : forall Ad kk, 2147446784 <= Ad -> 0 <= kk -> Ad + kk <= 17594333495296 ->      (* [comment removed for export] *)
            (Ad + kk <= shad mb \/ shad mb + shlen ms <= Ad) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  assert (K_pa : forall Ad kk, al_ptr_array L + 8 * a_nsec st <= Ad -> 0 <= kk -> Ad + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OP OPi OPa OPs D_t_p D_n_p D_s_p LC_p SC_p SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 OFK OFi FBND D_t_f D_f_p D_n_f D_s_f LC_f SC_f SHR I64b WR WB TL1 LMSB MSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros ODi ODa [kD DBND] [jD DIMG]; nd_post). clear -LO BOT STK3 OD ODi DBND DIMG D_t_d D_d_p D_n_d D_s_d LC_d SC_d SHR I64b WR WB TL1 LMSB MSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 FSH SHSEPF SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  pose proof (ao_space L ALO) as RSP'.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }
  (* [comment removed for export] *)
  set (st' := set_nsec (a_nsec st1 - 1) st1) in *.
  assert (PD : Permutation (ch :: sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st' p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  assert (NDcs : List.NoDup (ch :: sec_chunks_of st')) by (destruct WD as [ND _]; exact (Permutation_NoDup (Permutation_sym PD) ND)).
  assert (NOTIN : ~ In ch (sec_chunks_of st')) by (inversion NDcs; assumption).
  (* [comment removed for export] *)
  split.
  { intros a Ha CLa.
    assert (E : m' (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by exact Ha. eapply (disjoint_outside Wd a 1); [| clear; lia].
      destruct CLa as [CLa|TL].
      2:{ (* [comment removed for export] *)
          destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
          4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_ptr L ALO) as DA2. pose proof (ad_ahm_nodes L ALO) as DA3. pose proof (ad_ahm_store L ALO) as DA4.
              unfold adisj in DA1, DA2, DA3, DA4. (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post). (pose proof LSCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ LC_ahm; nd_post).
              apply K_hi; clear -IM OAH OAHI DA1 DA2 DA3 DA4 SC_ahm LC_ahm LMSB; lia. }
          3:{ unfold AIMSH_LO, AIMSH_LEN in IM. pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
              apply K_sh; clear -IM SDM MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia. }
          - apply K_tls; clear -T; lia.
          - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
            apply K_sh; [clear -TS1; lia | clear; lia | clear -TS2 SHCE; lia |].
            destruct (tls_shadow_apart ta mb ms Hta ltac:(clear -MSB; lia)) as [D|D]; [| left; clear -D; lia | right; exact D].
            destruct SC_tls as [D|D]; [right; split; [exact D| exact MAL8] | left; exact D]. }
      destruct CLa as [STa | [CIa | [BLK | SHD]]].
      - apply K_stack; clear -STa; lia.
      - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post).
        pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE in Q7.
        apply K_img; unfold AIMG_HI in *; clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7; lia.
      - (nd_pre BLK 3%nat; intros b Hb R; nd_post). apply In_lb_remove in Hb. destruct Hb as [Hb NK].
        destruct b as [[p'|cls] A' n']; cbn [ab_addr ab_size ab_kind] in R, NK.
        + destruct (proj1 BL p' A' n' Hb) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA' & G')].
          * destruct (BB y Hy) as [B1' B2']. pose proof (awf_fits L st X y WF Hy) as FT. unfold xb_fits in FT. rewrite Sy in FT.
            unfold xb_user in Uy. apply K_res; clear -R B1' B2' FT Uy Ny; lia.
          * assert (NEp : p' <> p) by (intros ->; apply NK; reflexivity).
            assert (INc : In (CSec mb' ms' n') (sec_chunks_of st')).
            { apply (live_sec_in st' p'). cbn [a_live st' set_nsec set_live st1]. rewrite lookup_delete_ne by (intros E; exact (NEp (eq_sym E))). exact Lp. }
            assert (NEc : CSec mb' ms' n' <> ch) by (intros E; apply NOTIN; rewrite <- E; exact INc).
            assert (INc0 : In (CSec mb' ms' n') (sec_chunks_of st)) by (eapply Permutation_in; [exact PD| right; exact INc]).
            destruct WD as [_ DJ]. destruct (DJ _ _ INc0 IN NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
            all: (nd_pre (sec_wf1_facts' L mb' ms' n' G') 13%nat; intros _ JLO JCE _ JNB _ JMSB _ JNMS _ (JC_t & _ & _ & JC_p & JC_n & JC_st & _) _ JN6; nd_post).
            all: (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
            all: assert (INo' : In (CSec mb' ms' n') order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INc0]).
            all: assert (DLj : CSec mb' ms' n' = CSec lmb lms ln \/ (mb' + ms' <= lmb \/ lmb + lms <= mb'))
                   by (destruct (achunk_eq_dec (CSec mb' ms' n') (CSec lmb lms ln)) as [E|NE']; [left; exact E| right; destruct WDo as [_ DJo]; destruct (DJo _ _ INo' INl NE') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1]]).
            all: unfold SEC_UOFF, K_HIGH_MEM in *.
            all: apply K_hi; try (clear -R EA' KAJ KBJ KEJ KCJ KDJ JCE JNMS JN6 Dc JC_t JC_p JC_n JC_st; lia).
            all: destruct DLj as [EE|DLj]; [injection EE as <- <- <-; clear -R EA'; lia| clear -R EA' JNMS JN6 DLj LMSB; lia].
        + (nd_pre (proj1 (proj2 BL) cls A' n' Hb) 3%nat; intros F1 F2 F3; nd_post). eapply disjoint_from_sub; [exact K_fake| clear -R F1; lia| clear -R F3; lia| clear; lia].
      - (nd_pre SHD 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). pose proof (shad_div a') as SD. unfold ASHOFF in SD.
        destruct Ha' as [STa | [CIa | FK]].
        + atop_facts. apply K_sh; [clear -STa SD LO BOT ATR; Z.div_mod_to_equations; lia| clear; lia| clear -STa SD; Z.div_mod_to_equations; lia| clear -STa SD SHCE LO BOT ATR; right; rewrite !shad_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia].   (* [comment removed for export] *)
        + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
          pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
          apply K_sh; clear -R SD SDM Q1 Q3 MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia.
        + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). apply In_lb_remove in Hin. destruct Hin as [Hin _].
          (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros F1 F2 F3; nd_post).
          pose proof (shad_div (al_fake L)) as SDF. pose proof (shlen_div 11571200) as SLF. unfold ASHOFF in SDF.
          eapply disjoint_from_sub; [exact K_shfake| clear -R F1 SD SDF; Z.div_mod_to_equations; lia| clear -R F3 SD SDF SLF FAL8; Z.div_mod_to_equations; lia| clear; lia]. }
    split; [exact E|]. intros Hw. rewrite (wview_agree asegs m m' (wa a) E). exact Hw. }
  (* [comment removed for export] *)
  split; [exact ALO|].
  split.
  { (* [comment removed for export] *) eapply arng_mono; [exact LE|]. eapply (arng_sub L RNG st st'); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros c Hc. eapply Permutation_in; [exact PD| right; exact Hc]. }
  split.
  2: { (* [comment removed for export] *)
       eapply (hf_blocks _ HL); cbn [ah_fake AHQ].
       - eapply AFKD; [exact HFK| exact MU| |].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) K_fake) as F1. pose proof (proj1 (disjoint_from_Forall _ _ _) K_shfake) as F2.
           pose proof (proj1 (disjoint_from_Forall _ _ _) K_dtls) as F3.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xa7288 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
           pose proof (tclr_cell_in (-8) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF5a GF5b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + -8) 16 GF5a ltac:(clear; lia) GF5b)) as F5.
           pose proof (tclr_cell_in (8) 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF6a GF6b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + 8) 8 GF6a ltac:(clear; lia) GF6b)) as F6.
           pose proof (tclr_cell_in (296) 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF7a GF7b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + 296) 8 GF7a ltac:(clear; lia) GF7b)) as F7.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x1401b1 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F8.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x13e098 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F9.
           unfold fake_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
           rewrite Forall_forall in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). specialize (F5 _ Hin).
           specialize (F6 _ Hin). specialize (F7 _ Hin). specialize (F8 _ Hin). specialize (F9 _ Hin). cbn [fst snd] in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           repeat (lazymatch goal with |- _ /\ _ => split end);
             lazymatch goal with      (* [comment removed for export] *)
             | |- context [ATPv + -8] => first [exact F5 | clear -F5; lia]
             | |- context [ATPv + 8] => first [exact F6 | clear -F6; lia]
             | |- context [ATPv + 296] => first [exact F7 | clear -F7; lia]
             | |- _ => first [clear -F1; lia| clear -F2; lia| clear -F3; lia| clear -F4; lia| clear -F8; lia| clear -F9; lia]
             end.
         + pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L + 48) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
           eapply Forall_impl; [| exact F1]. cbv beta. intros iv Hiv. clear -Hiv. lia.
       - intros c F0 n0. rewrite In_lb_remove. cbn [ab_kind]. split; [intros [H _]; exact H| intros H; split; [exact H| discriminate]]. }
  exists X. split.
  2: { eapply (ablocks_free_sec L st X LB p mb ms n st' X LIVE WF); [reflexivity| intros y Hy; exact Hy| exact BL]. }
  (* [comment removed for export] *)
  split. { eapply (awf_delete_sec L st X p mb ms n st' WF LIVE); reflexivity. }
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia | apply K_tls; clear; lia] |]). apply Forall_nil. }
  split. { (* [comment removed for export] *) unfold ainstance. cbn [a_nres a_nsec set_nsec set_live st' st1]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. { (* [comment removed for export] *) unfold athread.
           split; [eapply cells_frameD; [exact T0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           exact UW1. }
  split.
  { (* [comment removed for export] *)
    intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. (pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. (pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  (* [comment removed for export] *)
  split.
  { exists (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_nsec set_live st' st1].
    assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from Wd (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
    { intros q Hq. (nd_pre (qcoupled_bslot_busy L st X Q q CP Hq) 5%nat; intros b Hb Sb Cb Kb; nd_post).
      destruct (BB b Hb) as [B1' B2']. unfold xb_alloc in B1', B2'. rewrite Cb, Kb in B1'. rewrite Cb, Kb, size_of_class_24 in B2'.
      unfold abatch_addr, Q_BATCH_BYTES. apply K_res; [exact B1'| clear; lia| exact B2']. }
    split; [eapply aquar_glob_const_frameD; [exact MU| exact (conj QK MX)| |]; apply K_img; clear; unfold AQ_MAX, AQ_MUTEX, AIMG_HI; lia|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj QC ABL)| unfold aq_tcache; apply K_t; clear; lia| intros q Hq; apply DQ; apply in_app_iff; left; exact Hq]|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj GCQ ABG)| apply K_img; clear; unfold AQ_GCACHE, AIMG_HI; lia| intros q Hq; apply DQ; apply in_app_iff; right; exact Hq]|].
    split; [split; [exact FL1| split; [exact IAS1| intros _; exact IAM2]]|].
    split; [exact CP| exact (conj NB1 (conj NB2 (conj NF (conj NC NM))))]. }
  (* [comment removed for export] *)
  split.
  2: { (* [comment removed for export] *)
       split; [exact DEP'|].
       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact HRT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }
  (* [comment removed for export] *)
  cbn [ah_sec AHQ]. unfold ASEC_of. set (cs' := sec_chunks_of st') in *.
  (* [comment removed for export] *)
  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ CSec mb' ms' n' <> ch
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall Ad kk, mb' + 32 <= Ad -> 0 < kk -> Ad + kk <= mb' + ms' -> disjoint_from Wd Ad kk)
          /\ (forall Ad kk, shad mb' <= Ad -> 0 < kk -> Ad + kk <= shad mb' + ms' / 8 -> disjoint_from Wd Ad kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    (nd_pre (sec_wf1_facts' L mb' ms' n' Wj) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ JSCL _; nd_post).
    (nd_pre JSCL 7%nat; intros JC_t _ _ JC_p JC_n JC_st _; nd_post). unfold K_HIGH_MEM in JLO, JCE.
    (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 2148238848 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)      (* [comment removed for export] *)
           by (rewrite shad_div; unfold ASHOFF; clear -KBJ KDJ JMSB ATR; Z.div_mod_to_equations; lia).
    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [exact NEc|]. all: split; [clear -Dc; lia|].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_hi; [clear -Z1 Z3 KAJ KEJ KCJ; lia| clear -Z2; lia| clear -Z1 Z3 KBJ KDJ; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -KAJ KEJ KCJ JMSB; lia| clear; lia| clear -KBJ KDJ JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia]. }
  (* [comment removed for export] *)
  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (symmetry; exact LENO).
  assert (LCS : Z.of_nat (length cs') = a_nsec st - 1).
  { pose proof (Permutation_length PD) as PL. cbn [length] in PL. rewrite <- WL. clear -PL. lia. }
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE); [reflexivity|].
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  assert (WFA : asec_wf L st' cs').
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec set_live st' st1]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    split; [exact LCS|]. split; [clear -WB I64b; lia|].
    split. { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PD| right; exact Hc]. }
    split; [inversion NDcs; assumption|].
    destruct WD as [_ DJ]. intros ci cj Hi Hj NE. apply DJ; [| | exact NE]; (eapply Permutation_in; [exact PD| right; assumption]). }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]|].   (* [comment removed for export] *)
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L cs' m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM in Hx.
    unfold AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
    assert (SX : 2148238848 <= shad x /\ shad x + 1 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -Hx ATR; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: { (* [comment removed for export] *)
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, AIMG_HI, KLS; exact Hx) HFh).
    2,4: eapply Permutation_Forall; [exact PD|]; constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec set_live st' st1].
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| exact SHZn]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec set_live st' st1].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  - (* [comment removed for export] *)
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO.
             eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    (nd_pre (PER j c Hj') 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    (nd_pre (CHK j mb' ms' n' Hj' NEji) 6%nat; intros Wj _ Dj DCj DSj DHj; nd_post).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  - (* [comment removed for export] *)
    (nd_pre (List.nth_error_split order i NTH) 4%nat; intros o1 rest EO LO1; nd_post).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    + (* [comment removed for export] *)
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      assert (NEli : (length order - 1)%nat <> i) by (clear -NE; lia).
      (nd_pre (PER _ _ NTHL) 3%nat; intros lvl LVl CHl; nd_post). exists lvl. split; [rewrite (LVE _ _ NTHL NEli); exact LVl|].
      (nd_pre (CHK _ lmb lms ln NTHL NEli) 6%nat; intros Wj _ Dj DCj DSj _; nd_post).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      (nd_pre (PER j c Hj') 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      (nd_pre (CHK j mb' ms' n' Hj' NEji) 6%nat; intros Wj _ Dj DCj DSj DHj; nd_post).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End Zd1.
#[using="HL DEPD AFKD CI_OK CI_OK2"] Theorem afree_sec_big : ltac:(let t := eval cbv delta [afree_sec_big__stmt] in afree_sec_big__stmt in exact t).
Proof. exact afree_sec_big__body. Qed.
End S.
End CANSEC2.
(* [comment removed for export] *)

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
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_afree_iseg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_front.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_asecdealloc.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_arecsec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_aputrec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrameD.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecRecycle.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

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

#[using="Type"] Lemma afree_big_eq : forall st (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n -> a_qloc_bytes st <= Q_CACHE ->
  afree st (Some p) = large_dealloc (set_live (delete p (a_live st)) st) mb ms (fun st2 => aret st2).
Proof.
  intros st p mb ms n LIVE NB QB. unfold afree. rewrite LIVE. cbn [chunk_size].
  replace (n <=? Q_MAX) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
  unfold recycle_chunk, large_dealloc.
  replace (a_qloc_bytes (set_nsec (a_nsec (set_live (delete p (a_live st)) st) - 1) (set_live (delete p (a_live st)) st))) with (a_qloc_bytes st) by reflexivity.
  replace (Q_CACHE <? a_qloc_bytes st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition bigW (sp t mb ms PA idx last nodes store : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (0xafc00, 0xafc00 + 0x81030); (0x13e488, 0x13e48c); (t + 2800, t + 3169);
   (0x1808c8, 0x5d0910); (nodes, nodes + 1048576); (store, store + 8388608);
   (0xab410, 0xab419); (0xab428, 0xab438); (0xab640, 0xab644); (0xab658, 0xab668);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)].

End CANSEC1.
(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rec rl_skel (cs : constant FSet.t) (t : constr) : bool :=
  if zt_plain_arith_s cs t then true else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h args =>
      if lt_is_ref h reference:(or) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(and) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else if lt_is_ref h reference:(not) then rl_skel cs (Array.get args 0)
      else if lt_is_ref h reference:(iff) then (if rl_skel cs (Array.get args 0) then rl_skel cs (Array.get args 1) else false)
      else false
  | Constr.Unsafe.Prod b c =>
      if Constr.Unsafe.noccurn 1 c then (if rl_skel cs (Constr.Binder.type b) then rl_skel cs c else false) else false
  | _ => false
  end.
Local Ltac2 rl_prune () : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if rl_skel cs ty then None else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac rl_prune := ltac2:(Control.enter rl_prune).
Set Default Proof Mode "Classic".
Local Ltac rl_lia := rl_prune; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; rl_lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rl_lia ] end ].
Ltac kf := cbn [fst snd]; unfold AQ_MAX, AQ_MIN, AQ_MAXC, AQ_MUTEX, AQ_GCACHE, aq_tcache, AINSTANCE, ATP88, ATSD, AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIMG_HI, K_HIGH_MEM in *; repeat split; first [ lia_rel | lia ].

Ltac find_ivb s H :=
  first [ apply Exists_cons_hd; cbn [fst snd]; split; apply Z.le_refl
        | apply Exists_cons_hd; cbn [fst snd]; solve [clear -s H; lia]
        | apply Exists_cons_tl; find_ivb s H ].
Ltac solve_sub_fpb s H :=
  apply sub_fp_by_incl; repeat (apply Forall_cons; [find_ivb s H|]); apply Forall_nil.

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition afree_sec_big__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> Q_MAX < n ->
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
Variable L : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 42).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 43).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'afree_sec_big__stmt 44).
#[using="HL DEPD AFKD CI_OK CI_OK2"] Lemma afree_sec_big__body : ltac:(let T := type of (fun (h : afree_sec_big__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (tr, (mb, ms))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NBIG AH HIN MI ST BOT LO TP Ha0 AUNW S0NE RA4 RANE SP16 RSTK.
  assert (UNWX : exists trt, afree_unw RNG lo m (al_top L) sp s0 ra trt /\ In (AFREE_PC :: trt) (al_U L)).
  { destruct AUNW as [(BT & UC & LTR & TRU & RTOP)|(TOPLE & SPLT & TRU)]; [exists (bv_unsigned ra :: tr); split; [left; exists tr; split; [reflexivity|]; split; [exact UC|]; split; [exact LTR|]; split; [exact BT| exact RTOP]| exact TRU] | exists (@nil Z); split; [right; auto| exact TRU]]. }
  (nd_pre UNWX 3%nat; intros trt FUNW TRU; nd_post).
  (nd_pre AH 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD. destruct HQ as [Q AQ].
  (* [comment removed for export] *)
  (nd_pre (freed_block_sec L st X LB p mb ms n A n WF BL HIN LIVE) 3%nat; intros EA _ WFch; nd_post).
  (nd_pre (sec_wf1_facts' L mb ms n WFch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. (pose proof (ablk_int _ _ MLO) as ndP__; nd_pre ndP__ 6%nat; intros kM KAM KBM KEM KCM KDM; nd_post).   (* [comment removed for export] *)
  (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros SC_t SC_c SC_s SC_p SC_n SC_st SC_f SC_d SC_tls SC_ahmx; nd_post).
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SB1 SB2 SB3 SB4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u.   (* [comment removed for export] *)
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni Na [kN NBND]; nd_post). (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si Sa [kS SBND]; nd_post).   (* [comment removed for export] *)
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi OPa [kP OPs]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci Ca [kC CBND]; nd_post). (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros Ti4 Ta4 [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.
  assert (SP47 : bv_unsigned sp < 2^47) by (eapply afree_unw_sp47; [exact FUNW| exact STK2]).
  (* [comment removed for export] *)
  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT HRT2 RT3) as PRM.
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS0. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof HK2 as HK. rw_split HK 1%nat HK1 HKF.
  pose proof GOT as GOT6. rw_split GOT 1%nat GOTa GOTr. rw_split GOTr 1%nat GF GOTx. clear GOTa GOTx.
  pose proof INST as INST0. (nd_pre INST0 9%nat; intros I32 I48 I64 I72 I112 I680 I984 I40 I56; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  (nd_pre NUM 5%nat; intros NB1 NB2 NF NC NM; nd_post).
  pose proof (batches_bytes_lb (a_qloc st) ltac:(apply Forall_app in NF; exact (proj1 NF))) as LLB. rewrite <- NB1 in LLB.
  (* [comment removed for export] *)
  pose proof HS as HS0. (nd_pre HS0 5%nat; intros WFS _ SINST PZ SHZ; nd_post).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  (pose proof SINST as ndP__; nd_pre ndP__ 6%nat; intros I80 [srt ISRT] JST JBS PAD JGL; nd_post).
  (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) LIVE) 25%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 B1 B3 CX HUW UJ S1 S2 S3; nd_post).
  cbv zeta in H5, HUW, UJ, S2, S3.
  set (ch := CSec mb ms n) in *.
  assert (INo : In ch order) by (eapply nth_error_In; exact NTH).
  assert (IN : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| exact INo]).
  (* [comment removed for export] *)
  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. clear -NTHL IL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  (nd_pre (sec_wf1_facts' L lmb lms ln WFl) 12%nat; intros LAL LLO LCE LMSE LNB LRZ LMSB LMSAL _ _ LSCL _; nd_post).
  (pose proof (ablk_int _ _ LLO) as ndP__; nd_pre ndP__ 6%nat; intros kLl KALl KBLl KELl KCLl KDLl; nd_post).   (* [comment removed for export] *)
  (pose proof LSCL as ndP__; nd_pre ndP__ 10%nat; intros LC_t LC_c LC_s LC_p LC_n LC_st LC_f LC_d LC_l LC_ahmx; nd_post).      (* [comment removed for export] *)
  destruct (sec_shadow_cb m mb ms n true (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].
  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ (lmb + 32 <= al_nodes L \/ al_nodes L + 1048576 <= lmb) /\ (lmb + 32 <= al_store L \/ al_store L + 8388608 <= lmb)
   /\ tclr lmb 32).      (* [comment removed for export] *)
  { (nd_pre (PER _ _ NTHL) 3%nat; intros llv _ LCH; nd_post). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|].   (* [comment removed for export] *) all: split; [clear -LCE LMSB; lia|]. all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: split; [clear -LC_p LMSB WR WB; lia|].
    all: split; [clear -LC_n LMSB; lia|]. all: split; [clear -LC_st LMSB; lia|]. all: unfold tclr; clear -LC_l LMSB; lia. }
  (* [comment removed for export] *)
  pose proof ARNG as ARNG0. (nd_pre ARNG0 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDT RCLS RPA RSECS RPSH RTLS; nd_post).
  pose proof (proj1 (Forall_forall _ _) RSECS ch IN) as [RMB RSH]. unfold ch in RMB, RSH. cbn [sec_mb sec_ms] in RMB, RSH.
  (* [comment removed for export] *)
  rewrite (afree_big_eq st p mb ms n LIVE NBIG NC).
  set (st1 := set_live (delete p (a_live st)) st).
  (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_STACK, UDEPTH, Q_MAX, Q_CACHE, K_HIGH_MEM, AREQMAX in *.
  iprefix. eapply evtF_cut.
  { eapply (free_front_spec DI L (q_ia Q) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (al_t L) (al_ctx L) (mb + 6128) n b1 cx lo (al_top L) (al_bot L) uw sj trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- afree_unw _ _ _ _ _ _ _ _ => exact FUNW
         | |- In _ _ => exact TRU
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ = true -> _ => exact IAM
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (_ + 6128 + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         end.
    all: try lazymatch goal with
         | |- @eq word _ _ => first [exact TP | rewrite Ha0, EA; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
         | |- _ \/ _ => first [exact CL5 | exact DL7 | exact DL8 | exact DL9 | exact DL10
                             | clear -SC_t MSB; lia | clear -SC_c MSB; lia | clear -SC_n MSB; lia | clear -SC_st MSB; lia | clear -D_t_c; lia]
         | |- rng _ (_ + 6128) _ => eapply rng_sub; [exact RMB| clear; lia| clear -MSB; lia]
         | |- rng _ (al_ctx _) _ => eapply rng_sub; [exact RCTX| clear; lia| clear; lia]
         | |- rng _ _ _ => assumption
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- tclr (al_nodes _) _ => exact (tclr_nodes L ALO)      (* [comment removed for export] *)
         | |- tclr (al_store _) _ => exact (tclr_store L ALO)
         | |- tclr _ _ => unfold tclr; clear -SC_tls MSB; lia
         end.
    all: try assumption.
    all: try (unfold AIMG_HI; generalize NB N6 NMS MLO MCE MAL LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL1u TL4u TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B1 CX RA4; clear; intros; Z.div_mod_to_equations; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PFR. unfold free_front_post in PFR.
  (nd_pre PFR 15%nat; intros id t0a t1a t2a a6a a7a t3a t4a t5a t6a m1 sj1 tb1 junk2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MUf WMf MIf STf IDR HD1 FC1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 SS1 TB1 LTB1 FRS1 DEP1; nd_post).
  apply evtF_done.
  (* [comment removed for export] *)
  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
  assert (SHR : 2148239360 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)   (* [comment removed for export] *)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof QK as QKx. xport QKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof QC as QCx. xport QCx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t DL7 DL8 NBND SBND; kf).
  pose proof I32 as I32x. xport I32x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I64 as I64x. xport I64x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I72 as I72x. xport I72x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I112 as I112x. xport I112x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof ISRT as ISRTx. xport ISRTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof I680 as I680x. xport I680x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof PAD as PADx. xport PADx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TI as TIx. xport TIx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof TK as TKx. xport TKx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof T88 as T88x. xport T88x MUf WMf ltac:(pose proof (tclr_nodes L ALO) as XN; pose proof (tclr_store L ALO) as XS; unfold tclr in XN, XS;      (* [comment removed for export] *)
                                                  clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND SC_tls XN XS; kf).
  pose proof TSD as TSDx. xport TSDx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf).
  pose proof CT as CTx. xport CTx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3 CL5 SC_c DL9 DL10 NBND SBND; kf).
  pose proof U64 as U64x. xport U64x MUf WMf ltac:(rewrite length_map; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 OP OPi OPa OPs D_t_p SC_p D_n_p D_s_p LENO WB WR NBND SBND; kf).
  pose proof H1 as H1x. xport H1x MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SC_t SC_n SC_st NBND SBND; kf).
  pose proof SH as SHx. xport SHx MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 SHR NBND SBND; kf).
  pose proof JST as JSTx. eapply (junk_frame _ m m1) in JSTx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  pose proof JGL as JGLx. eapply (junk_frame _ m m1) in JGLx; [| exact MUf | exact WMf | intros _; cbn; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf].
  assert (PC1 : poison_cells m1).
  { eapply poison_cells_frame2; [exact PC | exact MUf | exact WMf |].
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (PRM1 : premap_cells m1).
  { eapply premap_cells_frameD; [exact PRM | exact MUf | ..]; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf. }
  assert (HRO1 : arelro0 m1).
  { eapply arelro0_munch; [exact HRO | exact MUf |]. unfold ARELRO_LO, ARELRO_HI.
    repeat (apply Forall_cons; [cbn [fst snd]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 NBND SBND; kf|]). apply Forall_nil. }
  assert (LHDR1 : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells asegs m1 lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)
   /\ tclr lmb 32).
  { intros NE. (nd_pre (LHDR NE) 10%nat; intros L1 L2 L3 L4 L5 L6 L7 L8 L9 L10; nd_post). atop_facts.
    (pose proof (ablk_int _ _ L2) as ndP__; nd_pre ndP__ 6%nat; intros kL KAL KBL KEL KCL KDL; nd_post).   (* [comment removed for export] *)
    xport L1 MUf WMf ltac:(clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB DL1 DL2 DL3 DL4 DL5 DL6 L2 KAL KBL KEL KCL KDL L3 L4 L5 L8 L9 NBND SBND; kf).
    repeat (split; [assumption|]). first [exact L7 | exact L10]. }
  clear LHDR.
  (* [comment removed for export] *)
  name_sp sp (-2128).
  eapply (put_passthru_spec RNG (fun st2 => aret st2) st1 _ _ sp0 gp tp) with
     (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj1) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 3) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj)
     (nb := Z.of_nat (length (a_qloc st))) (fst0 := qfirst L (q_loc Q)) (lst := qlast L (q_loc Q)) (qb := a_qloc_bytes st).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite Hsp; exact STf
       | |- mem_inv _ _ => exact MIf
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact HRO1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- junk_at _ _ 32 => exact JSTx
       | |- junk_at _ _ 16 => exact JGLx
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680x| exact PADx]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD1
       | |- rw_cells _ _ _ [CB _ _] => exact SHx
       | |- rw_cells _ _ (_ + 152) _ => exact CTx
       | |- rw_cells _ _ (_ + 80) _ => exact QCx
       | |- rw_cells _ _ _ _ => first [eassumption | exact QKx | exact I32x | exact I64x | exact I72x | exact I112x | exact ISRTx | exact TIx | exact TKx | exact T88x | exact TSDx | exact H1x]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64x
       | |- u64arr _ _ _ _ => exact STATS1
       | |- length _ = _ => exact LSJ1
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map; exact LENO
       | |- _ -> _ /\ _ => exact LHDR1
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RSECS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- tclr (al_ptr_array _) _ => eapply tclr_sub; [exact (tclr_ptr L ALO) | clear; lia | clear -WR; lia]      (* [comment removed for export] *)
       | |- tclr _ _ => exact SC_tls
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ (_ - _) => rewrite Hsp; eapply rng_sub; [exact RSTK| clear; lia | clear -LO; lia]
       | |- rng _ (shad _) _ => rewrite shlen_div; exact RSH
       | |- rng _ (al_ptr_array _) _ => exact RPA
       | |- rng _ (al_t _) _ => exact RT4
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ _ _ => exact RMB
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia   (* [comment removed for export] *)
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: try rewrite Hsp.
  all: unfold K_HIGH_MEM, AREQMAX in *.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- _ => try first [ assumption | exact SC_t | exact CL5
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -SP47 LO BOT STK3; lia | clear -OC CBND Ci; lia | clear -OT TBND TIMG; lia | clear -OP OPi OPa OPs WR WB; lia | clear -IL LENO; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -LLB NC; unfold Q_CACHE, Q_BATCH_BYTES in *; lia | clear; rewrite unsigned_lit by lia; lia
                       | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia
                       | clear -LC_t LMSB; lia | clear -LCE LMSB; lia ]
       end.
  (* [comment removed for export] *)
  intros RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' LE1 HF PP TC'.
  cbv beta. apply implS_ret.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  (nd_pre PP 12%nat; intros MU2 MI' ST' NSC' SRT' JST' MTX' JGL' ARR' LHDR' [sj' [STATS' LSJ']] SHZ'; nd_post).
  unfold putrec_W in MU2.
  unname_sp.
  (* [comment removed for export] *)
  apply rw_cells_of_u64arr in TB1. rewrite LTB1 in TB1.
  eapply (cells_frameD _ m1 m') in SS1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in TB1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in FRS1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in FL1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  eapply (cells_frameD _ m1 m') in UW1; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR LC_t SC_t D_t_p; kf].
  eapply (stk_transportD _ _ m1 m') in IAS1; [| exact MU2| cbn [disjoint_from]; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR; kf].
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at asegs m' (0xafc08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { intros j Hj. eapply bytes_at_agree; [exact (IAM1 j Hj)|].
    intros ii Hi. apply MU2. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by (clear -Hj Hi; lia).
    clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hj Hi. kf. }
  clear IAM1.
  assert (DEP' : ADEPOT DI L m').
  { eapply DEPD; [exact DEP1| exact MU2|].
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; clear -LO BOT STK3 TL1 TL2 TL1u TL4u MLO ML1 ML3 KAM KBM KEM KCM KDM MCE MSB OP OPi OPa OPs WR WB IL LENO LLO KALl KBLl KELl KCLl KDLl LCE LMSB SHR Hq DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 D_n_p D_s_p SC_n SC_st LC_n LC_st LMSB NBND SBND; kf |]).
    apply Forall_nil. }
  clear DEP1.
  replace (ret_pc (Z_to_bv 64 353172)) with (Z_to_bv 64 353172) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  eapply evtF_mono.
  { eapply (ficptD_spec RNG' sp gp tp); [exact ST' | atop_facts; clear -BOT STK3; lia | clear -LO; lia | exact MI'
      | eexists; split; [exact SS1 | reflexivity]
      | eexists; split; [replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by (clear; lia); exact TB1 | reflexivity]
      | exact FRS1 | eapply rng_fp_le; [exact LE| exact RIMG] | eapply rng_fp_le; [exact LE| exact RTLS] | eapply rng_fp_le; [exact LE| exact RSTK] ]. }
  cbv beta. intros ms3 [-> ST3].
  (* [comment removed for export] *)
  unfold afree_post. split; [exact LE|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST3|].
  (* [comment removed for export] *)
  assert (MU : munch (bigW (bv_unsigned sp) (al_t L) mb ms (al_ptr_array L) (Z.of_nat i) lmb (al_nodes L) (al_store L)) m m').
  { unfold bigW. eapply munch_trans; [| eapply munch_weaken; [| exact MU2]]. eapply munch_weaken; [| exact MUf]. all: solve_sub_fpb sp MSB. }
  clear MU2 MUf. unfold bigW in MU.
  (* [comment removed for export] *)
  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD. pose proof (ao_res_hi L ALO) as RHI. pose proof atop_range as ATR.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_nodes_res L ALO) as D_n_r. pose proof (ad_store_res L ALO) as D_s_r.
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p. pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_r, D_p_r, D_n_r, D_s_r, D_t_f, D_f_p, D_n_f, D_s_f, D_t_d, D_d_p, D_n_d, D_s_d, D_c_n, D_c_s.
  (pose proof LSCL as ndP__; nd_pre ndP__ 4%nat; intros _ _ LC_r _; nd_post).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_s as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH3 : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI ATR. Z.div_mod_to_equations. lia. }
  (nd_pre RSH3 3%nat; intros SR1 SR2 SR3; nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFi OFa [kF FBND]; nd_post).   (* [comment removed for export] *)
  assert (FSH : 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFi OFa ATR. Z.div_mod_to_equations. lia. }
  assert (SHCE : shad mb + shlen ms <= shad ATOP /\ 17594064011264 <= shad ATOP <= 17594332446720) by (rewrite !shad_div, shlen_div; unfold ASHOFF in *; clear -MCE MAL8 MSAL ATR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, SHCE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- LENO; clear -IL; lia).
  (* [comment removed for export] *)
  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall Ad kk, 0x10000 <= Ad -> 0 <= kk ->      (* [comment removed for export] *)
            (Ad + kk <= 0xab410 \/ (0xab668 <= Ad /\ Ad + kk <= 0xafc00) \/ (0x130c30 <= Ad /\ Ad + kk <= 0x13e488)
             \/ (0x13e48c <= Ad /\ Ad + kk <= 0x1808c8) \/ (0x5d0910 <= Ad /\ Ad + kk <= AIMG_HI)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (K_stack : forall Ad kk, bv_unsigned sp <= Ad -> 0 <= kk -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 LO BOT STK3 TL2 OP OPi OPa OPs LCE LMSB MCE SHR DL2 DL5 I64b WB WR ATR. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_t : forall Ad kk, al_t L <= Ad -> 0 <= kk -> (Ad + kk <= al_t L + 2800 \/ (al_t L + 3169 <= Ad /\ Ad + kk <= al_t L + 4096)) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 TL1 TL2 TL1u TL4u DL7 DL8 D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_ctx : forall Ad kk, al_ctx L <= Ad -> 0 <= kk -> Ad + kk <= al_ctx L + 65536 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OC CBND Ci D_t_c D_c_p D_c_n D_c_s LC_c SC_c SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_tls : forall Ad kk, ATPv + -200 <= Ad -> 0 <= kk -> Ad + kk <= ATPv + 312 -> disjoint_from Wd Ad kk).      (* [comment removed for export] *)
  { pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_ptr L ALO) as D_l_p. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
    unfold adisj in D_l_t, D_l_p, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
    intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 D_l_t D_l_p D_l_n D_l_s LC_l SC_tls SHR I64b WR WB MSB LMSB TL1 TLN ATR0. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_res : forall Ad kk, al_res L <= Ad -> 0 <= kk -> Ad + kk <= al_res L + 137439023104 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 ORS RHI D_t_r D_p_r D_n_r D_s_r LC_r SC_s SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_shres : forall Ad kk, shad (al_res L) <= Ad -> 0 <= kk -> Ad + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 SR1 SR2 SR3 SHSEP SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (K_hi : forall Ad kk, (Ad + kk <= 2147446784 \/ 17594333495296 <= Ad) -> 0 <= kk -> (6307840 <= Ad /\ Ad + kk <= ATOP) ->
            (Ad + kk <= mb \/ mb + ms <= Ad) -> (Ad + kk <= lmb + 24 \/ lmb + 32 <= Ad) ->
            (Ad + kk <= al_t L \/ al_t L + 4096 <= Ad) -> (Ad + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= Ad) ->
            (Ad + kk <= al_nodes L \/ al_nodes L + 1048576 <= Ad) -> (Ad + kk <= al_store L \/ al_store L + 8388608 <= Ad) ->
            disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 LO BOT STK3 SHR I64b WR WB ATR. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_sh : forall Ad kk, 2147446784 <= Ad -> 0 <= kk -> Ad + kk <= 17594333495296 ->      (* [comment removed for export] *)
            (Ad + kk <= shad mb \/ shad mb + shlen ms <= Ad) -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  assert (K_pa : forall Ad kk, al_ptr_array L + 8 * a_nsec st <= Ad -> 0 <= kk -> Ad + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd Ad kk).
  { intros Ad kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 LO BOT STK3 OP OPi OPa OPs D_t_p D_n_p D_s_p LC_p SC_p SHR I64b WR WB MSB LMSB TL1. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 OFK OFi FBND D_t_f D_f_p D_n_f D_s_f LC_f SC_f SHR I64b WR WB TL1 LMSB MSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros ODi ODa [kD DBND] [jD DIMG]; nd_post). clear -LO BOT STK3 OD ODi DBND DIMG D_t_d D_d_p D_n_d D_s_d LC_d SC_d SHR I64b WR WB TL1 LMSB MSB. repeat match goal with |- _ /\ _ => split end; lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -LO BOT STK3 FSH SHSEPF SHR TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM DL1 DL4 I64b NBND SBND ATR WR WB LMSB MSB. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  pose proof (ao_space L ALO) as RSP'.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }
  (* [comment removed for export] *)
  set (st' := set_nsec (a_nsec st1 - 1) st1) in *.
  assert (PD : Permutation (ch :: sec_chunks_of st') (sec_chunks_of st)).
  { apply (sec_chunks_of_delete_sec st st' p mb ms n LIVE); [reflexivity| apply Permutation_refl]. }
  assert (NDcs : List.NoDup (ch :: sec_chunks_of st')) by (destruct WD as [ND _]; exact (Permutation_NoDup (Permutation_sym PD) ND)).
  assert (NOTIN : ~ In ch (sec_chunks_of st')) by (inversion NDcs; assumption).
  (* [comment removed for export] *)
  split.
  { intros a Ha CLa.
    assert (E : m' (wa a) = m (wa a)).
    { apply MU. rewrite wa_unsigned by exact Ha. eapply (disjoint_outside Wd a 1); [| clear; lia].
      destruct CLa as [CLa|TL].
      2:{ (* [comment removed for export] *)
          destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
          4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_ptr L ALO) as DA2. pose proof (ad_ahm_nodes L ALO) as DA3. pose proof (ad_ahm_store L ALO) as DA4.
              unfold adisj in DA1, DA2, DA3, DA4. (pose proof SCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ SC_ahm; nd_post). (pose proof LSCL as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ LC_ahm; nd_post).
              apply K_hi; clear -IM OAH OAHI DA1 DA2 DA3 DA4 SC_ahm LC_ahm LMSB; lia. }
          3:{ unfold AIMSH_LO, AIMSH_LEN in IM. pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
              apply K_sh; clear -IM SDM MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia. }
          - apply K_tls; clear -T; lia.
          - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
            apply K_sh; [clear -TS1; lia | clear; lia | clear -TS2 SHCE; lia |].
            destruct (tls_shadow_apart ta mb ms Hta ltac:(clear -MSB; lia)) as [D|D]; [| left; clear -D; lia | right; exact D].
            destruct SC_tls as [D|D]; [right; split; [exact D| exact MAL8] | left; exact D]. }
      destruct CLa as [STa | [CIa | [BLK | SHD]]].
      - apply K_stack; clear -STa; lia.
      - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 6%nat; intros Q1 Q2 Q3 Q4 Q5 Q6; nd_post).
        pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q7. cbn [fst snd] in *. unfold AINSTANCE in Q7.
        apply K_img; unfold AIMG_HI in *; clear -R Q1 Q2 Q3 Q4 Q5 Q6 Q7; lia.
      - (nd_pre BLK 3%nat; intros b Hb R; nd_post). apply In_lb_remove in Hb. destruct Hb as [Hb NK].
        destruct b as [[p'|cls] A' n']; cbn [ab_addr ab_size ab_kind] in R, NK.
        + destruct (proj1 BL p' A' n' Hb) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA' & G')].
          * destruct (BB y Hy) as [B1' B2']. pose proof (awf_fits L st X y WF Hy) as FT. unfold xb_fits in FT. rewrite Sy in FT.
            unfold xb_user in Uy. apply K_res; clear -R B1' B2' FT Uy Ny; lia.
          * assert (NEp : p' <> p) by (intros ->; apply NK; reflexivity).
            assert (INc : In (CSec mb' ms' n') (sec_chunks_of st')).
            { apply (live_sec_in st' p'). cbn [a_live st' set_nsec set_live st1]. rewrite lookup_delete_ne by (intros E; exact (NEp (eq_sym E))). exact Lp. }
            assert (NEc : CSec mb' ms' n' <> ch) by (intros E; apply NOTIN; rewrite <- E; exact INc).
            assert (INc0 : In (CSec mb' ms' n') (sec_chunks_of st)) by (eapply Permutation_in; [exact PD| right; exact INc]).
            destruct WD as [_ DJ]. destruct (DJ _ _ INc0 IN NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
            all: (nd_pre (sec_wf1_facts' L mb' ms' n' G') 13%nat; intros _ JLO JCE _ JNB _ JMSB _ JNMS _ (JC_t & _ & _ & JC_p & JC_n & JC_st & _) _ JN6; nd_post).
            all: (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
            all: assert (INo' : In (CSec mb' ms' n') order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact INc0]).
            all: assert (DLj : CSec mb' ms' n' = CSec lmb lms ln \/ (mb' + ms' <= lmb \/ lmb + lms <= mb'))
                   by (destruct (achunk_eq_dec (CSec mb' ms' n') (CSec lmb lms ln)) as [E|NE']; [left; exact E| right; destruct WDo as [_ DJo]; destruct (DJo _ _ INo' INl NE') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1]]).
            all: unfold SEC_UOFF, K_HIGH_MEM in *.
            all: apply K_hi; try (clear -R EA' KAJ KBJ KEJ KCJ KDJ JCE JNMS JN6 Dc JC_t JC_p JC_n JC_st; lia).
            all: destruct DLj as [EE|DLj]; [injection EE as <- <- <-; clear -R EA'; lia| clear -R EA' JNMS JN6 DLj LMSB; lia].
        + (nd_pre (proj1 (proj2 BL) cls A' n' Hb) 3%nat; intros F1 F2 F3; nd_post). eapply disjoint_from_sub; [exact K_fake| clear -R F1; lia| clear -R F3; lia| clear; lia].
      - (nd_pre SHD 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->). pose proof (shad_div a') as SD. unfold ASHOFF in SD.
        destruct Ha' as [STa | [CIa | FK]].
        + atop_facts. apply K_sh; [clear -STa SD LO BOT ATR; Z.div_mod_to_equations; lia| clear; lia| clear -STa SD; Z.div_mod_to_equations; lia| clear -STa SD SHCE LO BOT ATR; right; rewrite !shad_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia].   (* [comment removed for export] *)
        + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 4%nat; intros Q1 Q2 Q3 _; nd_post). cbn [fst snd] in *.
          pose proof (shad_div mb) as SDM. unfold ASHOFF, AIMG_HI in *.
          apply K_sh; clear -R SD SDM Q1 Q3 MLO ML1 ML3 KAM KBM KEM KCM KDM; Z.div_mod_to_equations; lia.
        + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). apply In_lb_remove in Hin. destruct Hin as [Hin _].
          (nd_pre (proj1 (proj2 BL) cls FA sz Hin) 3%nat; intros F1 F2 F3; nd_post).
          pose proof (shad_div (al_fake L)) as SDF. pose proof (shlen_div 11571200) as SLF. unfold ASHOFF in SDF.
          eapply disjoint_from_sub; [exact K_shfake| clear -R F1 SD SDF; Z.div_mod_to_equations; lia| clear -R F3 SD SDF SLF FAL8; Z.div_mod_to_equations; lia| clear; lia]. }
    split; [exact E|]. intros Hw. rewrite (wview_agree asegs m m' (wa a) E). exact Hw. }
  (* [comment removed for export] *)
  split; [exact ALO|].
  split.
  { (* [comment removed for export] *) eapply arng_mono; [exact LE|]. eapply (arng_sub L RNG st st'); [intros c Hc; reflexivity| reflexivity| | exact ARNG].
    intros c Hc. eapply Permutation_in; [exact PD| right; exact Hc]. }
  split.
  2: { (* [comment removed for export] *)
       eapply (hf_blocks _ HL); cbn [ah_fake AHQ].
       - eapply AFKD; [exact HFK| exact MU| |].
         + pose proof (proj1 (disjoint_from_Forall _ _ _) K_fake) as F1. pose proof (proj1 (disjoint_from_Forall _ _ _) K_shfake) as F2.
           pose proof (proj1 (disjoint_from_Forall _ _ _) K_dtls) as F3.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xa7668 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
           pose proof (tclr_cell_in (-8) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF5a GF5b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + -8) 16 GF5a ltac:(clear; lia) GF5b)) as F5.
           pose proof (tclr_cell_in (8) 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF6a GF6b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + 8) 8 GF6a ltac:(clear; lia) GF6b)) as F6.
           pose proof (tclr_cell_in (296) 8 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [GF7a GF7b].
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_tls (ATPv + 296) 8 GF7a ltac:(clear; lia) GF7b)) as F7.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x1405b1 1 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F8.
           pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x13e498 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F9.
           unfold fake_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
           rewrite Forall_forall in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). specialize (F5 _ Hin).
           specialize (F6 _ Hin). specialize (F7 _ Hin). specialize (F8 _ Hin). specialize (F9 _ Hin). cbn [fst snd] in F1, F2, F3, F4, F5, F6, F7, F8, F9.
           repeat (lazymatch goal with |- _ /\ _ => split end);
             lazymatch goal with      (* [comment removed for export] *)
             | |- context [ATPv + -8] => first [exact F5 | clear -F5; lia]
             | |- context [ATPv + 8] => first [exact F6 | clear -F6; lia]
             | |- context [ATPv + 296] => first [exact F7 | clear -F7; lia]
             | |- _ => first [clear -F1; lia| clear -F2; lia| clear -F3; lia| clear -F4; lia| clear -F8; lia| clear -F9; lia]
             end.
         + pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L + 48) 16 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
           eapply Forall_impl; [| exact F1]. cbv beta. intros iv Hiv. clear -Hiv. lia.
       - intros c F0 n0. rewrite In_lb_remove. cbn [ab_kind]. split; [intros [H _]; exact H| intros H; split; [exact H| discriminate]]. }
  exists X. split.
  2: { eapply (ablocks_free_sec L st X LB p mb ms n st' X LIVE WF); [reflexivity| intros y Hy; exact Hy| exact BL]. }
  (* [comment removed for export] *)
  split. { eapply (awf_delete_sec L st X p mb ms n st' WF LIVE); reflexivity. }
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia | apply K_tls; clear; lia] |]). apply Forall_nil. }
  split. { (* [comment removed for export] *) unfold ainstance. cbn [a_nres a_nsec set_nsec set_live st' st1]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. { (* [comment removed for export] *) unfold athread.
           split; [eapply cells_frameD; [exact T0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           exact UW1. }
  split.
  { (* [comment removed for export] *)
    intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. (pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. (pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  (* [comment removed for export] *)
  split.
  { exists (mkQConc (q_loc Q) (q_glob Q) true (q_pend Q)). unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend a_qloc a_qloc_bytes a_qglob a_qglob_bytes set_nsec set_live st' st1].
    assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from Wd (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
    { intros q Hq. (nd_pre (qcoupled_bslot_busy L st X Q q CP Hq) 5%nat; intros b Hb Sb Cb Kb; nd_post).
      destruct (BB b Hb) as [B1' B2']. unfold xb_alloc in B1', B2'. rewrite Cb, Kb in B1'. rewrite Cb, Kb, size_of_class_24 in B2'.
      unfold abatch_addr, Q_BATCH_BYTES. apply K_res; [exact B1'| clear; lia| exact B2']. }
    split; [eapply aquar_glob_const_frameD; [exact MU| exact (conj QK MX)| |]; apply K_img; clear; unfold AQ_MAX, AQ_MUTEX, AIMG_HI; lia|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj QC ABL)| unfold aq_tcache; apply K_t; clear; lia| intros q Hq; apply DQ; apply in_app_iff; left; exact Hq]|].
    split; [eapply aqcache_frameD; [exact MU| exact (conj GCQ ABG)| apply K_img; clear; unfold AQ_GCACHE, AIMG_HI; lia| intros q Hq; apply DQ; apply in_app_iff; right; exact Hq]|].
    split; [split; [exact FL1| split; [exact IAS1| intros _; exact IAM2]]|].
    split; [exact CP| exact (conj NB1 (conj NB2 (conj NF (conj NC NM))))]. }
  (* [comment removed for export] *)
  split.
  2: { (* [comment removed for export] *)
       split; [exact DEP'|].
       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact HRT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }
  (* [comment removed for export] *)
  cbn [ah_sec AHQ]. unfold ASEC_of. set (cs' := sec_chunks_of st') in *.
  (* [comment removed for export] *)
  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ CSec mb' ms' n' <> ch
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall Ad kk, mb' + 32 <= Ad -> 0 < kk -> Ad + kk <= mb' + ms' -> disjoint_from Wd Ad kk)
          /\ (forall Ad kk, shad mb' <= Ad -> 0 < kk -> Ad + kk <= shad mb' + ms' / 8 -> disjoint_from Wd Ad kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    (nd_pre (sec_wf1_facts' L mb' ms' n' Wj) 12%nat; intros JAL JLO JCE _ _ _ JMSB _ _ _ JSCL _; nd_post).
    (nd_pre JSCL 7%nat; intros JC_t _ _ JC_p JC_n JC_st _; nd_post). unfold K_HIGH_MEM in JLO, JCE.
    (pose proof (ablk_int _ _ JLO) as ndP__; nd_pre ndP__ 6%nat; intros kJ KAJ KBJ KEJ KCJ KDJ; nd_post).   (* [comment removed for export] *)
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 2148239360 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)      (* [comment removed for export] *)
           by (rewrite shad_div; unfold ASHOFF; clear -KBJ KDJ JMSB ATR; Z.div_mod_to_equations; lia).
    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [exact NEc|]. all: split; [clear -Dc; lia|].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_hi; [clear -Z1 Z3 KAJ KEJ KCJ; lia| clear -Z2; lia| clear -Z1 Z3 KBJ KDJ; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia| clear -Z1 Z3 JC_n; lia| clear -Z1 Z3 JC_st; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros Ad kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -KAJ KEJ KCJ JMSB; lia| clear; lia| clear -KBJ KDJ JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia| clear -JC_n JMSB; lia| clear -JC_st JMSB; lia]. }
  (* [comment removed for export] *)
  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (symmetry; exact LENO).
  assert (LCS : Z.of_nat (length cs') = a_nsec st - 1).
  { pose proof (Permutation_length PD) as PL. cbn [length] in PL. rewrite <- WL. clear -PL. lia. }
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall j c, nth_error order j = Some c -> j <> i -> (sec_live st' c <-> sec_live st c)).
  { intros j c Hj NEj. apply (sec_live_other st p mb ms n st' c LIVE); [reflexivity|].
    intros E. apply NEj. destruct WDo as [ND _].
    apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH. unfold ch. rewrite E. reflexivity. }
  assert (WFA : asec_wf L st' cs').
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec set_live st' st1]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    split; [exact LCS|]. split; [clear -WB I64b; lia|].
    split. { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PD| right; exact Hc]. }
    split; [inversion NDcs; assumption|].
    destruct WD as [_ DJ]. intros ci cj Hi Hj NE. apply DJ; [| | exact NE]; (eapply Permutation_in; [exact PD| right; assumption]). }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -LO BOT STK3 TL1 TBND TIMG OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM SHR DL3 DL6 Ni Si I64b NBND SBND; repeat match goal with |- _ /\ _ => split end; first [exact I | lia]]|].   (* [comment removed for export] *)
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L cs' m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM in Hx.
    unfold AIMG_HI, KLS in Hx.   (* [comment removed for export] *)
    assert (SX : 2148239360 <= shad x /\ shad x + 1 <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -Hx ATR; Z.div_mod_to_equations; lia).
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: { (* [comment removed for export] *)
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, AIMG_HI, KLS; exact Hx) HFh).
    2,4: eapply Permutation_Forall; [exact PD|]; constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 LO BOT STK3 TL1 TBND OP OPi OPa OPs LLO KALl KBLl KELl KCLl KDLl MLO ML1 ML3 KAM KBM KEM KCM KDM I64b MAL8 MSAL SMB SLM SHR DL1 DL4 NBND SBND ATR WR WB LMSB; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec set_live st' st1].
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| exact SHZn]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec set_live st' st1].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  - (* [comment removed for export] *)
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO.
             eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    (nd_pre (PER j c Hj') 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    (nd_pre (CHK j mb' ms' n' Hj' NEji) 6%nat; intros Wj _ Dj DCj DSj DHj; nd_post).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  - (* [comment removed for export] *)
    (nd_pre (List.nth_error_split order i NTH) 4%nat; intros o1 rest EO LO1; nd_post).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PD]].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    + (* [comment removed for export] *)
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      assert (NEli : (length order - 1)%nat <> i) by (clear -NE; lia).
      (nd_pre (PER _ _ NTHL) 3%nat; intros lvl LVl CHl; nd_post). exists lvl. split; [rewrite (LVE _ _ NTHL NEli); exact LVl|].
      (nd_pre (CHK _ lmb lms ln NTHL NEli) 6%nat; intros Wj _ Dj DCj DSj _; nd_post).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      (nd_pre (PER j c Hj') 3%nat; intros lvj LVj CHj; nd_post). exists lvj. split; [rewrite (LVE j c Hj' NEji); exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      (nd_pre (CHK j mb' ms' n' Hj' NEji) 6%nat; intros Wj _ Dj DCj DSj DHj; nd_post).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End Zd1.
#[using="HL DEPD AFKD CI_OK CI_OK2"] Theorem afree_sec_big : ltac:(let t := eval cbv delta [afree_sec_big__stmt] in afree_sec_big__stmt in exact t).
Proof. exact afree_sec_big__body. Qed.
End S.
End CANSEC2.
(* [comment removed for export] *)
End TwB.
End ASF_big.

(* [comment removed for export] *)
Module ADfn_arepR.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AImg AProto ABase. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adeallocfn_icptR__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfn_icptR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.
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
Notation AHQm := (OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.AHQm DI ASEC AFK).
Let AHQm_laws := OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.AHQm_laws DI ASEC AFK HL.
Let aheap_pres_refill := OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.aheap_pres_refill CI CI_OK CI_OK2.

(* [comment removed for export] *)
Definition dfn_mid_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo lst nx bsz SO : Z)
         (hs : list word) (l1 l2 : list xbusy),
  let st1 := set_live (delete p (a_live st)) st in
  let X1 := xquar X c k n b1 ctx l1 l2 in
  let Q1 := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q) in
  alayout_ok L -> arng L RNG st -> AREP AHQ L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms1,
    dfn_to_refill_post DI L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n b1 ctx lo lst nx bsz SO hs m ms1 ->
       AREP (AHQm Q1) L st1 X1 (ms_mem ms1)
    /\ ablocks L st1 X1 (lb_remove p LB) /\ AFK L (lb_remove p LB) (ms_mem ms1)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m (ms_mem ms1).

Hypothesis MID : dfn_mid_stmt.
Hypothesis STORE_R : OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.store_freeR_stmt DI ASEC AFK CI.
Hypothesis REFILL : forall Q1, refill_stmt (AHQm Q1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_refill__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  (Q_CACHE < a_qloc_bytes st + (n + 8192) -> a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P AHQ L RNG st LB m -> In (HB p A n) LB ->
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
        (epostF (afree_post CI (AHEAP_P AHQ) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 41).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 42).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 43).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 44).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 45).
Variable c : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 46).
Let full := match a_qloc st with [] => false | _ :: _ => true end.
Let bsz := b_size (List.last (a_qloc st) dummy_batch).
#[using="HL CI_OK CI_OK2 aheap_pres_refill MID STORE_R REFILL full bsz"] Lemma dfn_refill__body : ltac:(let T := type of (fun (h : dfn_refill__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo SO pc trt tb c) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (SO, (pc, (trt, (tb, c))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE N1 EA CNT0 NOREC AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RSO.
  assert (RA4 : True) by exact I.
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
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
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
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
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
  { eapply (dfn_to_refill_spec DI L full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) (fhm L c k n) n b1 ctx lo
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz SO (1 + Z.of_nat (length trt)) pc uw _ _ _ _ sj tb hs (block_shadow_bytes n) trt).
    all: rewrite ?EHM.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- if _ then _ else _ => exact FULL'
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ (shad _) _ => eapply rw_cells_addr_eq; [exact SHU| f_equal; lia]
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ - 16 + 16) [C8 _] => eapply rw_cells_addr_eq; [exact HUW| lia]
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, <- Uy; subst AB UB; apply Z_to_bv_eqm; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia] | reflexivity]   (* [comment removed for export] *)
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
    all: try (clear -LTRT; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PTR.
  pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst 0 bsz SO hs l1 l2
              ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1) as MIDI.
  rewrite EHM in MIDI. specialize (MIDI PTR). (nd_pre MIDI 4%nat; intros ARm BLm FKm HPm; nd_post).
  unfold dfn_to_refill_post in PTR.
  (nd_pre PTR 16%nat; intros id t0a t1a t2a a4a a5a a6a a7a t3a t4a t5a t6a m1 sj1 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MUf WMf MIf STf IDR HD1 FC1 SH1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 FRP1 FRE1 LBS1 DEP1; nd_post).
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
    assert (KHI : forall Ad sz, bv_unsigned sp + -144 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
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
      eapply (dfn_from_refill_spec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
                (al_t L) (fhm L c k n) n b1 ctx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
                nx bs cn sb id bb SO mx cz sj0 ix sjr chs hs0 j0)
    end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact STr | exact IAS1]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MIr
         | |- ADEPOT _ _ _ => exact HDr
         | |- u64arr _ _ (_ + 2800) _ => exact STATSr
         | |- u64arr _ _ _ _ => exact CHr
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
         | |- rw_cells _ _ (_ + -80) _ => exact FRP1
         | |- rw_cells _ _ (_ + -144) _ => exact FRE1
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
  eapply (aheap_pres_refill L st1 X1 (lb_remove p LB) sp (bv_unsigned sp + -144) lo m1 m');
    [exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia].
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2 aheap_pres_refill MID STORE_R REFILL"] Theorem dfn_refill : ltac:(let t := eval cbv delta [dfn_refill__stmt] in dfn_refill__stmt in exact t).
Proof. exact dfn_refill__body. Qed.
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
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfn_icptR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.TwB.
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
Notation AHQm := (OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB.AHQm DI ASEC AFK).
Let AHQm_laws := OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB.AHQm_laws DI ASEC AFK HL.
Let aheap_pres_refill := OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB.aheap_pres_refill CI CI_OK CI_OK2.

(* [comment removed for export] *)
Definition dfn_mid_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (c k n b1 ctx A lo lst nx bsz SO : Z)
         (hs : list word) (l1 l2 : list xbusy),
  let st1 := set_live (delete p (a_live st)) st in
  let X1 := xquar X c k n b1 ctx l1 l2 in
  let Q1 := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q) in
  alayout_ok L -> arng L RNG st -> AREP AHQ L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  x_busy X = l1 ++ bfreed p c k n b1 ctx :: l2 -> In (HB p A n) LB -> 1 <= n ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  forall ms1,
    dfn_to_refill_post DI L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) (fhm L c k n) n b1 ctx lo lst nx bsz SO hs m ms1 ->
       AREP (AHQm Q1) L st1 X1 (ms_mem ms1)
    /\ ablocks L st1 X1 (lb_remove p LB) /\ AFK L (lb_remove p LB) (ms_mem ms1)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m (ms_mem ms1).

Hypothesis MID : dfn_mid_stmt.
Hypothesis STORE_R : OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB.store_freeR_stmt DI ASEC AFK CI.
Hypothesis REFILL : forall Q1, refill_stmt (AHQm Q1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_refill__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (c : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CPrim c n) -> 1 <= n ->
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  (Q_CACHE < a_qloc_bytes st + (n + 8192) -> a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P AHQ L RNG st LB m -> In (HB p A n) LB ->
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
        (epostF (afree_post CI (AHEAP_P AHQ) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 DEALLOCATE_ENTRY) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 41).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 42).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 43).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 44).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 45).
Variable c : ltac2:(SecDietF.SzSecF.ty 'dfn_refill__stmt 46).
Let full := match a_qloc st with [] => false | _ :: _ => true end.
Let bsz := b_size (List.last (a_qloc st) dummy_batch).
#[using="HL CI_OK CI_OK2 aheap_pres_refill MID STORE_R REFILL full bsz"] Lemma dfn_refill__body : ltac:(let T := type of (fun (h : dfn_refill__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo SO pc trt tb c) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (SO, (pc, (trt, (tb, c))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE N1 EA CNT0 NOREC AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RSO.
  assert (RA4 : True) by exact I.
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
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
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
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
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
  { eapply (dfn_to_refill_spec DI L full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) (fhm L c k n) n b1 ctx lo
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz SO (1 + Z.of_nat (length trt)) pc uw _ _ _ _ sj tb hs (block_shadow_bytes n) trt).
    all: rewrite ?EHM.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- if _ then _ else _ => exact FULL'
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ (shad _) _ => eapply rw_cells_addr_eq; [exact SHU| f_equal; lia]
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ - 16 + 16) [C8 _] => eapply rw_cells_addr_eq; [exact HUW| lia]
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, <- Uy; subst AB UB; apply Z_to_bv_eqm; first [(generalize N1 N0 NQM N65 HM16 HLO HHI ABCE ABUB ABHM S8 RUP RUP8 LO BOT SP47 STK1 STK2 STK3 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6 B10 LLB NC NM LF64 LST64 RA4; clear; intros; lia) | lia] | reflexivity]   (* [comment removed for export] *)
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
    all: try (clear -LTRT; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PTR.
  pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst 0 bsz SO hs l1 l2
              ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1) as MIDI.
  rewrite EHM in MIDI. specialize (MIDI PTR). (nd_pre MIDI 4%nat; intros ARm BLm FKm HPm; nd_post).
  unfold dfn_to_refill_post in PTR.
  (nd_pre PTR 16%nat; intros id t0a t1a t2a a4a a5a a6a a7a t3a t4a t5a t6a m1 sj1 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MUf WMf MIf STf IDR HD1 FC1 SH1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 FRP1 FRE1 LBS1 DEP1; nd_post).
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
    assert (KHI : forall Ad sz, bv_unsigned sp + -144 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
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
      eapply (dfn_from_refill_spec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
                (al_t L) (fhm L c k n) n b1 ctx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
                nx bs cn sb id bb SO mx cz sj0 ix sjr chs hs0 j0)
    end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact STr | exact IAS1]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | unfold ablk; right; generalize HLO HHI; try generalize EHM; clear; unfold fhm; intros; lia]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MIr
         | |- ADEPOT _ _ _ => exact HDr
         | |- u64arr _ _ (_ + 2800) _ => exact STATSr
         | |- u64arr _ _ _ _ => exact CHr
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
         | |- rw_cells _ _ (_ + -80) _ => exact FRP1
         | |- rw_cells _ _ (_ + -144) _ => exact FRE1
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
  eapply (aheap_pres_refill L st1 X1 (lb_remove p LB) sp (bv_unsigned sp + -144) lo m1 m');
    [exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia].
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2 aheap_pres_refill MID STORE_R REFILL"] Theorem dfn_refill : ltac:(let t := eval cbv delta [dfn_refill__stmt] in dfn_refill__stmt in exact t).
Proof. exact dfn_refill__body. Qed.
End S.
End CANSEC1.
End TwB.
End ADfn_arepR.

(* [comment removed for export] *)
Module ADfn_mid.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AImg AProto ABase. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst AMalloc_iface. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead F_afree_tail. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adeallocfn_icptR__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeMid OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfn_icptR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfn_arepR.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation WfM sp t UB gq nodes store :=
  ([(sp - 4096, sp); (0xaf800, 0x130830); (0x13e088, 0x13e08c); (ADEPOT_LO, ADEPOT_HI);
    (t + 2800, t + 3169); (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

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
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                                  /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                                  /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.

Definition dfn_mid_kit__stmt : Prop := dfn_mid_stmt DI ASEC AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 1).
Variable full : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 6).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 7).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 8).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 9).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 10).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 11).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 12).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 13).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 14).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 15).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 16).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 17).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 21).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 22).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 23).
Variable X : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 24).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 25).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 26).
Variable c : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 27).
Variable k : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 28).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 29).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 30).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 31).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 32).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 33).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 34).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 35).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 36).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 37).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 38).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 39).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 40).
Let st1 := set_live (delete p (a_live st)) st.
Let X1 := xquar X c k n b1 ctx l1 l2.
Let QM := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let gq := shlen (rup n 8).
#[using="HL CI_OK st1 X1 QM S AB UB gq"] Lemma dfn_mid_kit__body : ltac:(let T := type of (fun (h : dfn_mid_kit__stmt) => h L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst nx bsz SO hs l1 l2) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (full, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (c, (k, (n, (b1, (ctx, (A, (lo, (lst, (nx, (bsz, (SO, (hs, (l1, l2))))))))))))))))))))))))))))))))))))))))) as _.
  unfold dfn_mid_stmt. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1 PM. unfold AFREE_STACK in LO.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (xquar X c k n b1 ctx l1 l2) X1.
  chg (mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)) QM.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros LIVE N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X0; unfold adisj in X0; clear -X0; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros _ _ UJR LH SHA _ SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  unfold dfn_to_refill_post in PM. rewrite EHM in PM.
  (nd_pre PM 16%nat; intros id t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU WM MI' ST' IDR HDR' FC' SH' STATS' LSJ' UW' FL' IAS' IAM' FRP' FRE' LBS' DEP'; nd_post).
  cbn [ms_mem MS].
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  chg (shlen (rup n 8)) gq. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
  (* [comment removed for export] *)
  assert (MUn : munch (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsM (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S)).
  { unfold kfactsM. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *; sg_destr; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  pose proof (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KM_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KM_t _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KM_res _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KM_obj _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KM_objL _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
  assert (WF' : awf L st1 X1) by (apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity).
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st1 m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st1 X1 m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | reflexivity | reflexivity | reflexivity |].
      unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc'; lia.
    - eapply junk_frame; [exact CSTATS | exact MUn | exact WM | intros _; apply Kt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  idtac "CHECKPOINT-M1".
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st1 m' c'' /\ afreearray L st1 X1 m' c'' /\ aslots L st1 X1 m' c'' /\ aslot_shadow L st1 X1 m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; clear -Hc'' RSP G6 S8 EUB RES RHI; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia |].
        pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SLOTS | apply NDS | reflexivity | reflexivity | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bquar. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|]. split.
          -- assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia].
          -- intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia |].
        pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        clear -D ABUB S8 EUB. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
          unfold slot_shadow_bytes, bquar. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left. assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|].
          assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
          { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
            rewrite <- EAB, <- ES in D. exact D. }
          pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
          apply Kshad.
          -- rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
          -- rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
          -- apply shlen_nonneg. clear -T16; lia.
          -- rewrite EGQ. destruct DW as [D|D].
             ++ left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
             ++ right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  idtac "CHECKPOINT-M2".
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st1 m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | reflexivity | reflexivity | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  idtac "CHECKPOINT-M3".
  (* [comment removed for export] *)
  assert (HS' : ASEC L st1 X1 m').
  { eapply (hs_frame _ HL L st st1 X X1 m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_nil.
    - eapply (sec_same_free st p c n); [exact LIVE| apply same_core_refl| apply Permutation_refl]. }
  assert (BL' : ablocks L st1 X1 (lb_remove p LB)) by (exact (ablocks_xquar L st X p c k n b1 ctx l1 l2 XB LB st1 eq_refl BL)).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]).
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  idtac "CHECKPOINT-M4".
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ P1 P2 P3 P4 P5 P6 _; nd_post).
    rewrite size_of_class_24 in P2, P6. unfold abatch_addr. unfold K_SPACE_SIZE in P6. change (2^37) with 137438953472 in P6.
    generalize P1 P2 P5 P6 RSP; clear; intros. lia. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq. destruct (BGEO q Hq) as [F3 F4]. pose proof (SEPQ q Hq) as SQ. apply Kres; clear -F3 F4 RES RHI SQ ABUB S8 EUB; lia. }
  assert (HQ' : AQUAR_at L st1 X1 QM m').
  { subst QM. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
    change (a_qloc st1) with (a_qloc st). change (a_qglob st1) with (a_qglob st). change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aquar_glob_const_frame _ m m' MUn WM); [exact (conj QK MX) | apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia | apply Kimg; clear; unfold AQ_MUTEX, AIMG_HI; lia].
    - eapply (aqcache_frame L _ m m' MUn WM); [exact (conj QC ABL) | unfold aq_tcache; apply Kt; clear; lia |].
      intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. left. exact Hq.
    - eapply (aqcache_frame L _ m m' MUn WM); [exact (conj GCQ ABG) | apply Kimg; clear; unfold AQ_GCACHE, AINSTANCE, AIMG_HI; lia |].
      intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. right. exact Hq.
    - split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. cbn. lia.
    - subst X1. eapply (qcoupled_pend L st st1 X); [exact CP | reflexivity | reflexivity | | |].
      + exact (HQ_xquar X p c k n b1 ctx l1 l2 XB).
      + exact (HB_xquar X p c k n b1 ctx l1 l2 XB).
      + exact (FQ_X L st X p c k n b1 ctx l1 l2 XB WF).
    - exact NUM. }
  idtac "CHECKPOINT-M5".
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BLive p) by (rewrite Sb; intros E; apply NEp; congruence).
        pose proof (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia | clear -D9 FIT ABUB S8 EUB; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  split; [| split; [exact BL'| split; [exact HFK'|]]].
  - split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
  - eapply (aheap_pres_mid CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem dfn_mid_kit : ltac:(let t := eval cbv delta [dfn_mid_kit__stmt] in dfn_mid_kit__stmt in exact t).
Proof. exact dfn_mid_kit__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.AFreeStoreK.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.AFreeStore.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeMid.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfn_icptR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_fast__A3W.ADfn_arepR.TwB.
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac sg_set := let GG := fresh "GG" in (match goal with |- ?G => set (GG := G) end).
Local Ltac sg_unset := match goal with |- ?G => is_var G; subst G end.
Local Ltac sg_destr := sg_set; repeat match goal with H : _ /\ _ |- _ => destruct H end; sg_unset.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation WfM sp t UB gq nodes store :=
  ([(sp - 4096, sp); (0xafc00, 0x130c30); (0x13e488, 0x13e48c); (ADEPOT_LO, ADEPOT_HI);
    (t + 2800, t + 3169); (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

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
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                                  /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                                  /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.

Definition dfn_mid_kit__stmt : Prop := dfn_mid_stmt DI ASEC AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 1).
Variable full : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 2).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 3).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 4).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 5).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 6).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 7).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 8).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 9).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 10).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 11).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 12).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 13).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 14).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 15).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 16).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 17).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 18).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 19).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 20).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 21).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 22).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 23).
Variable X : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 24).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 25).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 26).
Variable c : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 27).
Variable k : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 28).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 29).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 30).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 31).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 32).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 33).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 34).
Variable nx : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 35).
Variable bsz : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 36).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 37).
Variable hs : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 38).
Variable l1 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 39).
Variable l2 : ltac2:(SecDietF.SzSecF.ty 'dfn_mid_kit__stmt 40).
Let st1 := set_live (delete p (a_live st)) st.
Let X1 := xquar X c k n b1 ctx l1 l2.
Let QM := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let gq := shlen (rup n 8).
#[using="HL CI_OK st1 X1 QM S AB UB gq"] Lemma dfn_mid_kit__body : ltac:(let T := type of (fun (h : dfn_mid_kit__stmt) => h L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst nx bsz SO hs l1 l2) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (full, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (Q, (p, (c, (k, (n, (b1, (ctx, (A, (lo, (lst, (nx, (bsz, (SO, (hs, (l1, l2))))))))))))))))))))))))))))))))))))))))) as _.
  unfold dfn_mid_stmt. 
  cbv zeta. intros ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1 PM. unfold AFREE_STACK in LO.
  chg (set_live (delete p (a_live st)) st) st1.
  chg (xquar X c k n b1 ctx l1 l2) X1.
  chg (mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)) QM.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
  (pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as ndP__; nd_pre ndP__ 6%nat; intros LIVE N0 FIT0 B10 AT0 CTX0; nd_post).
  (pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 14%nat; intros HM16 UB16 ABUB ABHM HLO UBS ABCE HHI N65 NQM ABLO RUP RUP8 S8; nd_post).
  (pose proof (slot_geo L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 13%nat; intros S16 SM16 AL16 G1 G2 G3 G4 G5 G6 G7 G8 R8 M8; nd_post).
  (pose proof (slot_sep_objects L st X c k ALO WF HC KR) as ndP__; nd_pre ndP__ 5%nat; intros DT DC DN DSO DF; nd_post).
  (pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as ndP__; nd_pre ndP__ 9%nat; intros SE GR3 GE G0 GFS SHLO SHHI SHM1 SHM2; nd_post).
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  (pose proof (aobj4_int _ OT) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ OC ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ci _ [kC CBND]; nd_post). (pose proof (aobj_int _ _ ON ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Ni _ [kN NBND]; nd_post).
  (pose proof (aobj_int _ _ OS ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros Si _ [kS SBND]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X0; unfold adisj in X0; clear -X0; lia).
  box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
  box DT. box DC. box DN. box DSO. box DF.
  word_range sp SPR.
  chg (size_of_class c) S. chg (aslot_addr L c k) AB. chg (AB + rz_size n) UB.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
  assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  (nd_pre (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC)))))) 7%nat; intros _ _ UJR LH SHA _ SHR; nd_post).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. (nd_pre AQ0 6%nat; intros [QK MX] [QC ABL] [GCQ ABG] (FL & IAS & IAM) CP NUM; nd_post).
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ ND2 BSI _; nd_post).
  (* [comment removed for export] *)
  unfold dfn_to_refill_post in PM. rewrite EHM in PM.
  (nd_pre PM 16%nat; intros id t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU WM MI' ST' IDR HDR' FC' SH' STATS' LSJ' UW' FL' IAS' IAM' FRP' FRE' LBS' DEP'; nd_post).
  cbn [ms_mem MS].
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  chg (shlen (rup n 8)) gq. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
  (* [comment removed for export] *)
  assert (MUn : munch (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsM (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S)).
  { unfold kfactsM. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *; sg_destr; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  pose proof (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KM_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KM_t _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KM_res _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KM_obj _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KM_objL _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
  assert (WF' : awf L st1 X1) by (apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity).
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    (first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kimg; clear; unfold AIMG_HI; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | first [ apply Forall_cons; [cbn [fst snd]; first [ apply Kctx; clear; lia |apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |])] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]] | repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]) ]). apply Forall_nil. }
  assert (INST' : ainstance L st1 m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
  assert (THR' : athread L st1 X1 m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
    - intros c' Hc'. eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | reflexivity | reflexivity | reflexivity |].
      unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc'; lia.
    - eapply junk_frame; [exact CSTATS | exact MUn | exact WM | intros _; apply Kt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  idtac "CHECKPOINT-M1".
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L st1 m' c'' /\ afreearray L st1 X1 m' c'' /\ aslots L st1 X1 m' c'' /\ aslot_shadow L st1 X1 m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 4%nat; intros RI1 RI2 RI3 RI4; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      apply Kres; clear -Hc'' RSP G6 S8 EUB RES RHI; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia |].
        pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
      + assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
        { unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
        destruct FA1 as [FA1 FA2].
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SLOTS | apply NDS | reflexivity | reflexivity | |].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
          unfold aslot_busy, bquar. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
          rewrite <- EAB. fold S. rewrite <- EUB.
          split; [| split].
          -- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
             ++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8; unfold K_SPACE_SIZE in *; lia.
             ++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 Hp; unfold K_SPACE_SIZE in *; lia.
          -- exists 3. split; [reflexivity|]. exact HDR'.
          -- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
             apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
             ++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
             ++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
                apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 Hp; unfold K_SPACE_SIZE in *; lia.
        * (* [comment removed for export] *)
          left.
          assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|]. split.
          -- assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
             { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
               rewrite <- EAB, <- ES in D. exact D. }
             apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia].
          -- intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia |].
        pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        clear -D ABUB S8 EUB. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''.
        (pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
          subst c'' k''. right.
          subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
          unfold slot_shadow_bytes, bquar. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
          eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
                                       apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
          eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
                                       apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
          rewrite EGQ in SH'.
          replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
          rewrite EGQ in SHR, G0.
          replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
          pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
          assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
          replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
            by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
          rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
        * left. assert (T2 : (c =? c'') && (k =? k'') = false).
          { destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
          split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|].
          assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
          { pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
            rewrite <- EAB, <- ES in D. exact D. }
          pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
          apply Kshad.
          -- rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
          -- rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
          -- apply shlen_nonneg. clear -T16; lia.
          -- rewrite EGQ. destruct DW as [D|D].
             ++ left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
             ++ right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  idtac "CHECKPOINT-M2".
  (* [comment removed for export] *)
  assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st1 m' c'').
  { intros c'' Hc''. pose proof WF as WF0. (nd_pre WF0 7%nat; intros _ _ SAL _ _ PERC _; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
    eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | reflexivity | reflexivity | |].
    - intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
      assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
      destruct U0 as [U0 U0'].
      assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
      pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  idtac "CHECKPOINT-M3".
  (* [comment removed for export] *)
  assert (HS' : ASEC L st1 X1 m').
  { eapply (hs_frame _ HL L st st1 X X1 m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ SPal _; nd_post). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_nil.
    - eapply (sec_same_free st p c n); [exact LIVE| apply same_core_refl| apply Permutation_refl]. }
  assert (BL' : ablocks L st1 X1 (lb_remove p LB)) by (exact (ablocks_xquar L st X p c k n b1 ctx l1 l2 XB LB st1 eq_refl BL)).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi FKa [kF FBND]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. (pose proof (aobj4_int _ DTO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DBND] [jD DIMG]; nd_post). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
        - right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
        first [ solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia] | solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3 D_l_t; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3 D_l_n D_l_s; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [fu_lia|]); fu_lia]
              | solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3 D_l_r; repeat (split; [fu_lia|]); fu_lia]
              | match goal with |- ?G => idtac "FAKELEFT" G end ] | idtac]]]]]]]]]).
      apply Forall_nil.
    - intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
  idtac "CHECKPOINT-M4".
  (* [comment removed for export] *)
  assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
  { intros q Hq. (nd_pre (bslot_busy L st X Q CP q Hq) 5%nat; intros yq Hyq Syq Cyq Kyq; nd_post).
    pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
                  ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
    rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
  assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
      al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
  { intros q Hq. (pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ P1 P2 P3 P4 P5 P6 _; nd_post).
    rewrite size_of_class_24 in P2, P6. unfold abatch_addr. unfold K_SPACE_SIZE in P6. change (2^37) with 137438953472 in P6.
    generalize P1 P2 P5 P6 RSP; clear; intros. lia. }
  assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (abatch_addr L (qb_slot q)) 8192).
  { intros q Hq. destruct (BGEO q Hq) as [F3 F4]. pose proof (SEPQ q Hq) as SQ. apply Kres; clear -F3 F4 RES RHI SQ ABUB S8 EUB; lia. }
  assert (HQ' : AQUAR_at L st1 X1 QM m').
  { subst QM. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
    change (a_qloc st1) with (a_qloc st). change (a_qglob st1) with (a_qglob st). change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aquar_glob_const_frame _ m m' MUn WM); [exact (conj QK MX) | apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia | apply Kimg; clear; unfold AQ_MUTEX, AIMG_HI; lia].
    - eapply (aqcache_frame L _ m m' MUn WM); [exact (conj QC ABL) | unfold aq_tcache; apply Kt; clear; lia |].
      intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. left. exact Hq.
    - eapply (aqcache_frame L _ m m' MUn WM); [exact (conj GCQ ABG) | apply Kimg; clear; unfold AQ_GCACHE, AINSTANCE, AIMG_HI; lia |].
      intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. right. exact Hq.
    - split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. cbn. lia.
    - subst X1. eapply (qcoupled_pend L st st1 X); [exact CP | reflexivity | reflexivity | | |].
      + exact (HQ_xquar X p c k n b1 ctx l1 l2 XB).
      + exact (HB_xquar X p c k n b1 ctx l1 l2 XB).
      + exact (FQ_X L st X p c k n b1 ctx l1 l2 XB WF).
    - exact NUM. }
  idtac "CHECKPOINT-M5".
  (* [comment removed for export] *)
  assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (ab_addr blk) (ab_size blk)).
  { intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
    - destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
      + assert (NEq : xb_st b <> BLive p) by (rewrite Sb; intros E; apply NEp; congruence).
        pose proof (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
        destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
        unfold xb_user, xb_alloc in Ub. subst A' n'.
        set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
        (pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as ndP__; nd_pre ndP__ 12%nat; intros T16 TM16 TAL P1 P2 P3 P4 P5 P6 P7 P8 _; nd_post).
        pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
        apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia | clear -D9 FIT ABUB S8 EUB; lia].
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A' n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  split; [| split; [exact BL'| split; [exact HFK'|]]].
  - split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
  - eapply (aheap_pres_mid CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia].
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem dfn_mid_kit : ltac:(let t := eval cbv delta [dfn_mid_kit__stmt] in dfn_mid_kit__stmt in exact t).
Proof. exact dfn_mid_kit__body. Qed.
End S.
End CANSEC1.
End TwB.
End ADfn_mid.

(* [comment removed for export] *)
Module ADfnS_refill.
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
From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModelR AFreeRep. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tail. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adrain__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_tailR__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_fast__A3W. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASF_read. From OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_adeallocfn_icptR__A3W. Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_icpt OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfn_icptR OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.
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
Notation AHSm := (OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.AHSm DI AFK).

(* [comment removed for export] *)
Definition dfn_mid_stmtS : Prop :=
  forall (L : alayout) (RNG : footprint) (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo lst nx bsz SO : Z)
         (hs : list word),
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
    dfn_to_refill_post DI L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n b1 ctx lo lst nx bsz SO hs m ms1 ->
       AREP (AHSm (sec_chunks_of st) Q1) L st1 X (ms_mem ms1)
    /\ ablocks L st1 X (lb_remove p LB) /\ AFK L (lb_remove p LB) (ms_mem ms1)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m (ms_mem ms1).

Hypothesis MID : dfn_mid_stmtS.
Hypothesis STORE_R : OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.store_freeRS_stmt DI AFK CI.
(* [comment removed for export] *)
Hypothesis REFILL : forall cs Q1, refill_stmt (AHSm cs Q1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_sec_refill__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  (Q_CACHE < a_qloc_bytes st + (n + 8192) -> a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) <= Q_MAX) ->
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 41).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 42).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 43).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 44).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 45).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 46).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 47).
Let hm := mb + 6128.
Let full := match a_qloc st with [] => false | _ :: _ => true end.
Let bsz := b_size (List.last (a_qloc st) dummy_batch).
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL hm full bsz"] Lemma dfn_sec_refill__body : ltac:(let T := type of (fun (h : dfn_sec_refill__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo SO pc trt tb mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (SO, (pc, (trt, (tb, (mb, ms)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NQM EA CNT0 NOREC AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RSO.
  assert (RA4 : True) by exact I.
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
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
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
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
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
  { eapply (dfn_to_refill_spec DI L full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz SO (1 + Z.of_nat (length trt)) pc uw _ _ _ _ sj tb hs (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- if _ then _ else _ => exact FULL'
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, EAu; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
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
    all: try (clear -LTRT; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PTR.
  (pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 cx A lo lst 0 bsz SO hs
              ALO ARNG AR AQ BL HFK LIVE HIN NQM H5 B1 B3 CX CEIL LO ms1 PTR) as ndP__; nd_pre ndP__ 4%nat; intros ARm BLm FKm HPm; nd_post).
  unfold dfn_to_refill_post in PTR.
  (nd_pre PTR 16%nat; intros id t0a t1a t2a a4a a5a a6a a7a t3a t4a t5a t6a m1 sj1 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MUf WMf MIf STf IDR HD1 FC1 SH1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 FRP1 FRE1 LBS1 DEP1; nd_post).
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
    assert (KHI : forall Ad sz, bv_unsigned sp + -144 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
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
      eapply (dfn_from_refill_spec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
                (al_t L) hm n b1 cx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
                nx bs cn sb id bb SO mx cz sj0 ix sjr chs hs0 j0)
    end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact STr | exact IAS1]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0x | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MIr
         | |- ADEPOT _ _ _ => exact HDr
         | |- u64arr _ _ (_ + 2800) _ => exact STATSr
         | |- u64arr _ _ _ _ => exact CHr
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
         | |- rw_cells _ _ (_ + -80) _ => exact FRP1
         | |- rw_cells _ _ (_ + -144) _ => exact FRE1
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
  eapply (aheap_pres_refill CI CI_OK CI_OK2 L st1 X (lb_remove p LB) sp (bv_unsigned sp + -144) lo m1 m');
    [exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia].
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL"] Theorem dfn_sec_refill : ltac:(let t := eval cbv delta [dfn_sec_refill__stmt] in dfn_sec_refill__stmt in exact t).
Proof. exact dfn_sec_refill__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
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
Import OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModelR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_aalloc_s.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tail.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adrain__A3W.F_aenqueueR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_tailR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_tailR__A3W.F_afree_icptR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.F_afree_arepR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_read.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_fast.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_front.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_adeallocfn_icpt.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_adeallocfn_icptR__A3W.F_adeallocfn_icptR.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ADeallocFn_kit.TwB.
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
Notation AHSm := (OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB.AHSm DI AFK).

(* [comment removed for export] *)
Definition dfn_mid_stmtS : Prop :=
  forall (L : alayout) (RNG : footprint) (full : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo lst nx bsz SO : Z)
         (hs : list word),
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
    dfn_to_refill_post DI L full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n b1 ctx lo lst nx bsz SO hs m ms1 ->
       AREP (AHSm (sec_chunks_of st) Q1) L st1 X (ms_mem ms1)
    /\ ablocks L st1 X (lb_remove p LB) /\ AFK L (lb_remove p LB) (ms_mem ms1)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m (ms_mem ms1).

Hypothesis MID : dfn_mid_stmtS.
Hypothesis STORE_R : OssFuzzTheorems.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASF_fast__A3W.ASF_refill.TwB.store_freeRS_stmt DI AFK CI.
(* [comment removed for export] *)
Hypothesis REFILL : forall cs Q1, refill_stmt (AHSm cs Q1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dfn_sec_refill__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo SO pc : Z) (trt : list Z) (tb : list word) (mb ms : Z),
  (* [comment removed for export] *)
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  enq_is_app st = false -> c_count (get_cls st K_BATCH_CLASS) = 0 ->
  (Q_CACHE < a_qloc_bytes st + (n + 8192) -> a_qglob_bytes st + (a_qloc_bytes st + (n + 8192)) <= Q_MAX) ->
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
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 41).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 42).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 43).
Variable trt : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 44).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 45).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 46).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'dfn_sec_refill__stmt 47).
Let hm := mb + 6128.
Let full := match a_qloc st with [] => false | _ :: _ => true end.
Let bsz := b_size (List.last (a_qloc st) dummy_batch).
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL hm full bsz"] Lemma dfn_sec_refill__body : ltac:(let T := type of (fun (h : dfn_sec_refill__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo SO pc trt tb mb ms) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (n, (lo, (SO, (pc, (trt, (tb, (mb, ms)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros LIVE NQM EA CNT0 NOREC AH HIN MI ST BOT LO TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 FLAG1 SGE S47 SS TB LTB TRF TRU LTRT RSTK RSO.
  assert (RA4 : True) by exact I.
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
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SGE S47; lia).
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
  pose proof (aintal_flag_true _ _ FL FLAG1) as EIA. rewrite EIA in FL, IAM. specialize (IAM eq_refl).
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in FL, IAS, IAM. change (262144 / 8) with 32768 in IAM.
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
  { eapply (dfn_to_refill_spec DI L full RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              (al_t L) (al_ctx L) hm n b1 cx lo
              (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) lst (a_qloc_bytes st) 0 bsz SO (1 + Z.of_nat (length trt)) pc uw _ _ _ _ sj tb hs (block_shadow_bytes n) trt).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0' | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact HD
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- forall j, _ => exact IAM
         | |- rw_cells _ _ _ [C8 _; C4 _; C4 _] => exact SS
         | |- if _ then _ else _ => exact FULL'
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
         | |- rw_cells _ _ (shad _) _ => exact S2
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 16) [C8 _] => exact HUW
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _] => first [exact T0 | exact QK]
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5 | rewrite Ha1, EAu; subst hm; unfold SEC_UOFF; f_equal; clear; lia | reflexivity]
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
    all: try (clear -LTRT; lia).
    all: match goal with |- ?G => idtac "REMF" G end. }
  cbv beta. intros ms1 PTR.
  (pose proof (MID L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p mb ms n b1 cx A lo lst 0 bsz SO hs
              ALO ARNG AR AQ BL HFK LIVE HIN NQM H5 B1 B3 CX CEIL LO ms1 PTR) as ndP__; nd_pre ndP__ 4%nat; intros ARm BLm FKm HPm; nd_post).
  unfold dfn_to_refill_post in PTR.
  (nd_pre PTR 16%nat; intros id t0a t1a t2a a4a a5a a6a a7a t3a t4a t5a t6a m1 sj1 j0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MUf WMf MIf STf IDR HD1 FC1 SH1 STATS1 LSJ1 UW1 FL1 IAS1 IAM1 FRP1 FRE1 LBS1 DEP1; nd_post).
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
    assert (KHI : forall Ad sz, bv_unsigned sp + -144 <= Ad -> 0 <= sz -> disjoint_from W Ad sz);
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
      eapply (dfn_from_refill_spec DI L fu g RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m'
                (al_t L) hm n b1 cx lo (Z.of_nat (length (a_qloc st_r))) (qfirst L (q_loc Q1)) (qlast L (q_loc Q1)) (a_qloc_bytes st_r)
                nx bs cn sb id bb SO mx cz sj0 ix sjr chs hs0 j0)
    end.
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact STr | exact IAS1]
         | |- ablk _ (_ + 16 + rup _ 8) => first [assumption | exact HM0x | (try subst hm; eapply ablk_sub; [exact MLO| clear; lia| clear -NMS MSB MSAL N6 NB; unfold rup; Z.div_mod_to_equations; lia])]   (* [comment removed for export] *)
         | |- mem_inv _ _ => exact MIr
         | |- ADEPOT _ _ _ => exact HDr
         | |- u64arr _ _ (_ + 2800) _ => exact STATSr
         | |- u64arr _ _ _ _ => exact CHr
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
         | |- rw_cells _ _ (_ + -80) _ => exact FRP1
         | |- rw_cells _ _ (_ + -144) _ => exact FRE1
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
  eapply (aheap_pres_refill CI CI_OK CI_OK2 L st1 X (lb_remove p LB) sp (bv_unsigned sp + -144) lo m1 m');
    [exact ALO | exact WFm | exact BLm | exact MUr | exact WMr | exact CEIL | generalize LO; clear; intros; lia | clear; lia].
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2 MID STORE_R REFILL"] Theorem dfn_sec_refill : ltac:(let t := eval cbv delta [dfn_sec_refill__stmt] in dfn_sec_refill__stmt in exact t).
Proof. exact dfn_sec_refill__body. Qed.
End S.
End CANSEC1.
End TwB.
End ADfnS_refill.
