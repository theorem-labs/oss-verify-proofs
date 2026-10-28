(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition numr_scan_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbee74 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 (Z_to_bv 64 (e_THIS E)) xt4 xt5 xt6 F fc m1).

Definition numr_dot_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbd604 xra xt0 (Z_to_bv 64 (B (crs (rtxt E)) p)) xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 (Z_to_bv 64 (e_THIS E)) xt4 xt5 xt6 F fc m1).

Definition numr_frac_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbd60c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_ftail_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p r : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbed04 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa2 (Z_to_bv 64 (CP + r)) xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 (Z_to_bv 64 (r - p)) xt6 F fc m1).

Definition numr_ftail2_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p r : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbedc4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 (Z_to_bv 64 (r - p)) xt6 F fc m1).

Definition numr_expd_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg q0 : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa1 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbeec8 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + neg)) xa1 (Z_to_bv 64 (CP + q0)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_flt_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbf030 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + neg)) (Z_to_bv 64 (CP + p)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_int_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg p : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbef54 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 (Z_to_bv 64 (CP + p)) (Z_to_bv 64 (SHA (CP + p))) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 (Z_to_bv 64 (e_THIS E)) xt4 xt5 xt6 F fc m1).

Definition numr_range_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbfbb8 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_cmp_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg e : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xbfc6c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 (Z_to_bv 64 (e)) xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_write_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (neg : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xc287c xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_fin_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (r tw : Z) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xc28c4 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8 * tw)) (Z_to_bv 64 (e_TAPE E)) (Z_to_bv 64 (r)) (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_join_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xc2f14 xra xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_slowcall_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xe99dc (Z_to_bv 64 (0xc3d28)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) (Z_to_bv 64 (e_spa E + 272)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_fbcall_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 j272 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; CB 8 j272]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xe9abc (Z_to_bv 64 (0xc4098)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) (Z_to_bv 64 (e_spa E + 272)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_slowret_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (r : Z) (v : word) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; C8 v]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xc3d28 (Z_to_bv 64 (0xc3d28)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (r)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (CP)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition numr_fbret_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) (s : st) (r : Z) (v : word) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6
         j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j208 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMIR E CP (e_nxt0 E) [CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; C8 (Z_to_bv 64 (e_IDX E + 4)); C8 (Z_to_bv 64 (e_TAPE E + 8)); CB 8 j208; C8 v]
         ([]) fc m1 ->
    evt asegs Q (S2R E 0xc4098 (Z_to_bv 64 (0xc4098)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (r)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_FF E))) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_TAPE E + 8)) (Z_to_bv 64 (e_TAPE E)) xs7 (Z_to_bv 64 (CP)) xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).

