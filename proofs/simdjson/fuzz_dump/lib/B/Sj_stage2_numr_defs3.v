(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b Sj_stage2_numkit3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition rpro_new_k (E : s2env) (Q : machine_state -> Prop) : Prop :=
  forall xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs7 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0x10ac30 (Z_to_bv 64 (0xb7254)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (e_len E - e_off E 0 + 64)) (Z_to_bv 64 (0x2cf28)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (SHA (e_IDX E))) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_THIS E + 80))) xs7 (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_THIS E + 80)) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_IDX E)) xt3 xt4 xt5 xt6 F fc m1).

Definition rpro_ret1_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs7 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb7254 (Z_to_bv 64 (0xb7254)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (SHA (e_IDX E))) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (SHA (e_THIS E + 80))) xs7 (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_THIS E + 80)) (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_IDX E)) xt3 xt4 xt5 xt6 F fc m1).

Definition rpro_memcpy_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs8 xs9 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0x7e878 (Z_to_bv 64 (0xb7290)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) (Z_to_bv 64 (e_BUF E + e_off E 0)) (Z_to_bv 64 (e_len E - e_off E 0)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_len E)) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) xs6 (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_IDX E)) xt3 xt4 xt5 xt6 F fc m1).

Definition rpro_ret2_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs8 xs9 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0xb7290 (Z_to_bv 64 (0xb7290)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e_len E)) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) xs6 (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) (Z_to_bv 64 (e_IDX E)) xt3 xt4 xt5 xt6 F fc m1).

Definition rpro_memset_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs4 xs6 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; C8 (Z_to_bv 64 (e_TAPE E)); C8 (Z_to_bv 64 (e_TAPE E + 8)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    evt bsegs Q (S2R E 0x7ed14 (Z_to_bv 64 (0xb72b4)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP + (e_len E - e_off E 0))) (Z_to_bv 64 (32)) (Z_to_bv 64 (64)) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (Z.lxor CP 18446744073709551615)) (Z_to_bv 64 (SHA (e_FF E))) xs4 (Z_to_bv 64 (2147450880)) xs6 (Z_to_bv 64 (CP)) xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition rdelAc_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMXJ E fc m1 ->
    evt bsegs Q (S2R E 0x10ac6c (Z_to_bv 64 (0xb73b0)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition rdelB_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall err xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMX E err fc m1 ->
    (1 <= err < 64)%Z ->
    evt bsegs Q (S2R E 0x10ac6c (Z_to_bv 64 (0xbcc34)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition rdelC_k (E : s2env) (Q : machine_state -> Prop) (CP : Z) : Prop :=
  forall r tp xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; C8 (Z_to_bv 64 (tp)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    (0 <= r < 64)%Z ->
    (r = 0 -> tp = e_TAPE E + 24)%Z ->
    (r = 0 -> Z.of_nat (length (e_tws E)) = 3)%Z ->
    evt bsegs Q (S2R E 0x10ac6c (Z_to_bv 64 (0xbcc54)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) (Z_to_bv 64 (CP)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (r)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition rretA_k (E : s2env) (Q : machine_state -> Prop) : Prop :=
  forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMXJ E fc m1 ->
    evt bsegs Q (S2R E 0xb73b0 (Z_to_bv 64 (0xb73b0)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition rretB_k (E : s2env) (Q : machine_state -> Prop) : Prop :=
  forall err xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMX E err fc m1 ->
    (1 <= err < 64)%Z ->
    evt bsegs Q (S2R E 0xbcc34 (Z_to_bv 64 (0xbcc34)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Definition rretC_k (E : s2env) (Q : machine_state -> Prop) : Prop :=
  forall r tp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6
         j0 j8 j16 j24 j32 j40 j48 j56 j64 j72 j80 j88 j96 j104 j112 j120 j128 j136 j144 j152 j160 j168 j176 j200 j272 j288 j304 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    MEMI E (e_nxt0 E) [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24; CB 8 j32; CB 8 j40; CB 8 j48; CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; CB 8 j88; CB 8 j96; CB 8 j104; CB 8 j112; CB 8 j120; CB 8 j128; CB 8 j136; CB 8 j144; CB 8 j152; CB 8 j160; CB 8 j168; CB 8 j176; C8 (Z_to_bv 64 (tp)); C8 (Z_to_bv 64 (e_IDX E + 4)); CB 8 j200; CB 8 j272; CB 8 j288; CB 8 j304]
         ([]) fc m1 ->
    (0 <= r < 64)%Z ->
    (r = 0 -> tp = e_TAPE E + 24)%Z ->
    (r = 0 -> Z.of_nat (length (e_tws E)) = 3)%Z ->
    evt bsegs Q (S2R E 0xbcc54 (Z_to_bv 64 (0xbcc54)) xt0 xt1 xt2 (e_sp E) (Z_to_bv 64 (e_spa E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (r)) (Z_to_bv 64 (SHA (e_FF E))) xs4 xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (e_FF E)) xs11 xt3 xt4 xt5 xt6 F fc m1).

Lemma tape_img_unapp : forall E ws ss (m1 : mem),
  tape_img (gapp E ws ss) (e_tws (gapp E ws ss)) (e_sbs (gapp E ws ss)) m1 -> tape_img E (e_tws E) (e_sbs E) m1.
Proof.
  intros E ws ss m1 (T1 & T2 & T3 & T4 & S1 & S2 & SB). cbn [gapp s2_ghost e_tws e_sbs e_TAPE e_SBUF e_tcap e_scap] in *.
  rewrite twords_app in T1. rewrite zbytes_app in T2. apply bytes_at_app in T1. apply bytes_at_app in T2.
  rewrite length_app in T3, T4.
  split; [exact (proj1 T1)|]. split; [exact (proj1 T2)|]. split; [lia|]. split; [lia|]. split; [exact S1|]. split; [exact S2|].
  unfold bytes_ok in *. apply Forall_app in SB. exact (proj1 SB).
Qed.
Lemma MEMI_unapp : forall E ws ss nxt sl sc fc (m1 : mem), MEMI (gapp E ws ss) nxt sl sc fc m1 -> MEMI E nxt sl sc fc m1.
Proof.
  intros E ws ss nxt sl sc fc m1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & TI).
  repeat (split; [assumption|]). exact (tape_img_unapp E ws ss m1 TI).
Qed.
Lemma rdelAc_k_gapp : forall E Q CP ws ss, rdelAc_k E Q CP -> rdelAc_k (gapp E ws ss) Q CP.
Proof.
  intros E Q CP ws ss K. unfold rdelAc_k. intros until m1. intros HM. apply K.
  destruct HM as (nxt & sc & HM). do 29 (let j := fresh "j" in destruct HM as (j & HM)).
  unfold MEMXJ. do 31 eexists. exact (MEMI_unapp E ws ss _ _ _ _ _ HM).
Qed.
Lemma rdelB_k_gapp : forall E Q CP ws ss, rdelB_k E Q CP -> rdelB_k (gapp E ws ss) Q CP.
Proof.
  intros E Q CP ws ss K. unfold rdelB_k in *. intros until m1. intros HM HERR.
  destruct HM as (nxt & sc & HM). do 28 (let j := fresh "j" in destruct HM as (j & HM)).
  apply MEMI_unapp in HM.
  exact (K err xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs11 xt3 xt4 xt5 xt6 F fc m1
           ltac:(unfold MEMX; do 30 eexists; exact HM) HERR).
Qed.
