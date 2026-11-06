(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     L5Defs L5Core L5CoreKit L5CoreSpecsU L5DivSpecsU L5KnP L5ParseKit L5ParseSpecsU L5Bytes L5StrctorKitU L5UnwindSpecsU L5E2KitU L5E3US1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E3CU.
Import L5CSU L5PSU L5STRKU L5E2KU.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Section SCFG_2.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition assert_throw_req (LBT LB1 : list (Z * Z)) (R0 : bvmap 5 word) (M0 : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (S : Z) : Prop :=
  exists d1 d2 d3 d4 w960 w976 w552 w568 w576 w584 w592 w600 w608 w616 w624 w632 fb808 fb744 fb712 fb664 fb528 fb472 fb344 fb280 fb248 fb200 fb64,
     LBT = [(d1, 64); (d2, 64); (d3, 64); (d4, 64)]
  /\ getr R 2%bv = Z_to_bv 64 (S - 1008)
  /\ getr R 9%bv = Z_to_bv 64 (S + 64)
  /\ getr R 10%bv = Z_to_bv 64 16
  /\ getr R 3%bv = getr R0 3%bv
  /\ getr R 4%bv = getr R0 4%bv
  /\ 0 <= fb808 < 256 /\ Z.testbit fb808 0 = false
  /\ 0 <= fb744 < 256 /\ Z.testbit fb744 0 = true
  /\ 0 <= fb712 < 256 /\ Z.testbit fb712 0 = true
  /\ 0 <= fb664 < 256 /\ Z.testbit fb664 0 = false
  /\ 0 <= fb528 < 256 /\ Z.testbit fb528 0 = false
  /\ 0 <= fb472 < 256 /\ Z.testbit fb472 0 = false
  /\ 0 <= fb344 < 256 /\ Z.testbit fb344 0 = false
  /\ 0 <= fb280 < 256 /\ Z.testbit fb280 0 = false
  /\ 0 <= fb248 < 256 /\ Z.testbit fb248 0 = true
  /\ 0 <= fb200 < 256 /\ Z.testbit fb200 0 = true
  /\ 0 <= fb64 < 256 /\ Z.testbit fb64 0 = false
  /\ L5.u64_at RSEGS M (S - 952) 136456
  /\ L5.u64_at RSEGS M (S - 960) w960
  /\ L5.u64_at RSEGS M (S - 968) (S + 64)
  /\ L5.u64_at RSEGS M (S - 976) w976
  /\ L5.u64_at RSEGS M (S - 888) 141312
  /\ L5.u64_at RSEGS M (S - 896) (S - 528)
  /\ L5.u64_at RSEGS M (S - 904) (S + 64)
  /\ L5.u64_at RSEGS M (S - 912) (S + 64)
  /\ L5.u64_at RSEGS M (S - 536) 144836
  /\ L5.u64_at RSEGS M (S - 544) (S + 64)
  /\ L5.u64_at RSEGS M (S - 552) w552
  /\ L5.u64_at RSEGS M (S - 560) (S + 64)
  /\ L5.u64_at RSEGS M (S - 568) w568
  /\ L5.u64_at RSEGS M (S - 576) w576
  /\ L5.u64_at RSEGS M (S - 584) w584
  /\ L5.u64_at RSEGS M (S - 592) w592
  /\ L5.u64_at RSEGS M (S - 600) w600
  /\ L5.u64_at RSEGS M (S - 608) w608
  /\ L5.u64_at RSEGS M (S - 616) w616
  /\ L5.u64_at RSEGS M (S - 624) w624
  /\ L5.u64_at RSEGS M (S - 632) w632
  /\ L5.u64_at RSEGS M (S - 488) 143756
  /\ L5.u64_at RSEGS M (S - 496) (S + 64)
  /\ L5.u64_at RSEGS M (S - 424) 141856
  /\ L5.u64_at RSEGS M (S - 432) (S + 64)
  /\ L5.u64_at RSEGS M (S - 440) (S - 64)
  /\ L5.u64_at RSEGS M (S - 72) 140436
  /\ L5.u64_at RSEGS M (S - 80) (S + 64)
  /\ L5.u64_at RSEGS M (S - 88) (L5E2KU.U R0 9)
  /\ L5.u64_at RSEGS M (S - 96) (L5E2KU.U R0 18)
  /\ L5.u64_at RSEGS M (S - 104) (L5E2KU.U R0 19)
  /\ L5.u64_at RSEGS M (S - 112) (L5E2KU.U R0 20)
  /\ L5.u64_at RSEGS M (S - 120) (L5E2KU.U R0 21)
  /\ L5.u64_at RSEGS M (S - 128) (L5E2KU.U R0 22)
  /\ L5.u64_at RSEGS M (S - 136) (L5E2KU.U R0 23)
  /\ L5.u64_at RSEGS M (S - 144) (L5E2KU.U R0 24)
  /\ L5.u64_at RSEGS M (S - 152) (L5E2KU.U R0 25)
  /\ L5.u64_at RSEGS M (S - 160) (L5E2KU.U R0 26)
  /\ L5.u64_at RSEGS M (S - 168) (L5E2KU.U R0 27)
  /\ L5.u64_at RSEGS M (S - 24) 134416
  /\ L5.u64_at RSEGS M (S - 32) (S + 96)
  /\ L5.u64_at RSEGS M (S - 8) 133204
  /\ L5.u64_at RSEGS M (S - 16) (L5E2KU.U R0 8)
  /\ L5.u8_at RSEGS M (S - 808) fb808
  /\ L5.u8_at RSEGS M (S - 744) fb744
  /\ L5.u64_at RSEGS M (S - 720) d1
  /\ L5.u64_at RSEGS M (S - 728) 8
  /\ L5.u8_at RSEGS M (S - 712) fb712
  /\ L5.u64_at RSEGS M (S - 688) d2
  /\ L5.u64_at RSEGS M (S - 696) 8
  /\ L5.u8_at RSEGS M (S - 664) fb664
  /\ L5.u8_at RSEGS M (S - 528) fb528
  /\ L5.u8_at RSEGS M (S - 472) fb472
  /\ L5.u8_at RSEGS M (S - 344) fb344
  /\ L5.u8_at RSEGS M (S - 280) fb280
  /\ L5.u8_at RSEGS M (S - 248) fb248
  /\ L5.u64_at RSEGS M (S - 224) d3
  /\ L5.u64_at RSEGS M (S - 232) 8
  /\ L5.u8_at RSEGS M (S - 200) fb200
  /\ L5.u64_at RSEGS M (S - 176) d4
  /\ L5.u64_at RSEGS M (S - 184) 8
  /\ L5.u8_at RSEGS M (S - 64) fb64.

(* [comment removed for export] *)
Lemma u64_at_mod M a v : L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M a (v mod 2 ^ 64).
Proof.
  intros H. unfold L5.u64_at in *. replace (Z_to_bv 64 (v mod 2 ^ 64)) with (Z_to_bv 64 v). exact H.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section WithHeap.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis LYX : layoutx L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Theorem e3_chain : L5USU.e3_chain_spec_of L assert_throw_req HI.
Proof.
  intros fx R0 M0 R M model K LBT LB1 cr S st REQ H01 H02 H03 H04 XS AVTOP HH MOK HK0 STK S240 CR144 CR48 CR66 KE.
  destruct st as [gd fl av uid rnd canary hw]. cbn [L5USU.xs_av] in AVTOP.
  unfold L5USU.xs_pre, L5USU.lib_statics_at in XS. cbn [L5USU.xs_gd L5USU.xs_fl L5USU.xs_av L5USU.xs_uid L5USU.xs_rnd L5USU.xs_canary L5USU.xs_hw] in XS.
  pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold L5DSU.SCR_OPMOD in SLO, DEF.
  destruct REQ as (d1 & d2 & d3 & d4 & w960 & w976 & w552 & w568 & w576 & w584 & w592 & w600 & w608 & w616 & w624 & w632 & fb808 & fb744 & fb712 & fb664 & fb528 & fb472 & fb344 & fb280 & fb248 & fb200 & fb64 & ELBT & Q2 & Q9 & Q10 & Q3 & Q4 & Hr_fb808 & Hb_fb808 & Hr_fb744 & Hb_fb744 & Hr_fb712 & Hb_fb712 & Hr_fb664 & Hb_fb664 & Hr_fb528 & Hb_fb528 & Hr_fb472 & Hb_fb472 & Hr_fb344 & Hb_fb344 & Hr_fb280 & Hb_fb280 & Hr_fb248 & Hb_fb248 & Hr_fb200 & Hb_fb200 & Hr_fb64 & Hb_fb64 & c0_Sm952 & c0_Sm960 & c0_Sm968 & c0_Sm976 & c0_Sm888 & c0_Sm896 & c0_Sm904 & c0_Sm912 & c0_Sm536 & c0_Sm544 & c0_Sm552 & c0_Sm560 & c0_Sm568 & c0_Sm576 & c0_Sm584 & c0_Sm592 & c0_Sm600 & c0_Sm608 & c0_Sm616 & c0_Sm624 & c0_Sm632 & c0_Sm488 & c0_Sm496 & c0_Sm424 & c0_Sm432 & c0_Sm440 & c0_Sm72 & c0_Sm80 & c0_Sm88 & c0_Sm96 & c0_Sm104 & c0_Sm112 & c0_Sm120 & c0_Sm128 & c0_Sm136 & c0_Sm144 & c0_Sm152 & c0_Sm160 & c0_Sm168 & c0_Sm24 & c0_Sm32 & c0_Sm8 & c0_Sm16 & c0_Sm808w1 & c0_Sm744w1 & c0_Sm720 & c0_Sm728 & c0_Sm712w1 & c0_Sm688 & c0_Sm696 & c0_Sm664w1 & c0_Sm528w1 & c0_Sm472w1 & c0_Sm344w1 & c0_Sm280w1 & c0_Sm248w1 & c0_Sm224 & c0_Sm232 & c0_Sm200w1 & c0_Sm176 & c0_Sm184 & c0_Sm64w1). subst LBT. cbn [app] in HH, KE.
  rewrite L5CoreKit.L5K.rl2 in H02. rewrite L5CoreKit.L5K.rl3 in H03. rewrite L5CoreKit.L5K.rl4 in H04.
  rewrite L5CoreKit.L5K.rl2 in Q2. rewrite L5CoreKit.L5K.rl3 in Q3. rewrite L5CoreKit.L5K.rl4 in Q4. rewrite L5CoreKit.L5K.rl9 in Q9. rewrite L5CoreKit.L5K.rl10 in Q10.
  unfold L5USU.GP in H03. unfold TP in H04.
  (* [comment removed for export] *)
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as [WFB [ND _]].
  destruct (WFB (d1, 64) ltac:(left; reflexivity)) as (BR_d1 & DEFd1_0 & BA1). destruct (WFB (d2, 64) ltac:(right; left; reflexivity)) as (BR_d2 & DEFd2_0 & BA2).
  destruct (WFB (d3, 64) ltac:(right; right; left; reflexivity)) as (BR_d3 & DEFd3_0 & BA3). destruct (WFB (d4, 64) ltac:(do 3 right; left; reflexivity)) as (BR_d4 & DEFd4_0 & _).
  cbn [fst snd lb_remove app map] in BA1, BA2, BA3, ND.
  rewrite Z.eqb_refl in BA1.
  apply stdpp.list_relations.list.NoDup_cons in ND. destruct ND as [N1 ND]. apply stdpp.list_relations.list.NoDup_cons in ND. destruct ND as [N2 ND].
  apply stdpp.list_relations.list.NoDup_cons in ND. destruct ND as [N3 ND].
  assert (E12: d1 <> d2). { intros E. apply N1. rewrite E. left. } assert (E13: d1 <> d3). { intros E. apply N1. rewrite E. right. left. }
  assert (E14: d1 <> d4). { intros E. apply N1. rewrite E. right. right. left. }
  assert (E23: d2 <> d3). { intros E. apply N2. rewrite E. left. } assert (E24: d2 <> d4). { intros E. apply N2. rewrite E. right. left. }
  assert (E34: d3 <> d4). { intros E. apply N3. rewrite E. left. }
  rewrite (proj2 (Z.eqb_neq d1 d2) E12), Z.eqb_refl in BA2. rewrite (proj2 (Z.eqb_neq d1 d3) E13), (proj2 (Z.eqb_neq d2 d3) E23), Z.eqb_refl in BA3.
  pose proof (BA1 (d2, 64) ltac:(left; reflexivity)) as AP_d1_d2. pose proof (BA1 (d3, 64) ltac:(right; left; reflexivity)) as AP_d1_d3.
  pose proof (BA1 (d4, 64) ltac:(right; right; left; reflexivity)) as AP_d1_d4.
  pose proof (BA2 (d3, 64) ltac:(right; left; reflexivity)) as AP_d2_d3. pose proof (BA2 (d4, 64) ltac:(right; right; left; reflexivity)) as AP_d2_d4.
  pose proof (BA3 (d4, 64) ltac:(right; right; left; reflexivity)) as AP_d3_d4.
  cbn [fst snd] in AP_d1_d2, AP_d1_d3, AP_d1_d4, AP_d2_d3, AP_d2_d4, AP_d3_d4.
  assert (LBWF: L5PK.lb_wf L LB1). { intros b Hb. apply (L5PK.lb_wf_of_heap L HI _ cr M (m_vmmaps model) HIok HH). do 4 right. exact Hb. }
  assert (HQ0: L5C.hpres L LB1 S 10240 [(459776, 4); (462433, 6)] M M). { apply L5PK.hpres_refl. exact DEF. }
  unfold L5DSU.SCR_OPMOD, L5USU.xs_foot, L5USU.TOP_PAD, EH_UNCAUGHT, UW_FLAGS in KE.
  eapply (L5E3US1.seg1 L HI LY LYX HIok fx R0 R M model K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 (w960 mod 2 ^ 64) (w976 mod 2 ^ 64) (w552 mod 2 ^ 64) (w568 mod 2 ^ 64) (w576 mod 2 ^ 64) (w584 mod 2 ^ 64) (w592 mod 2 ^ 64) (w600 mod 2 ^ 64) (w608 mod 2 ^ 64) (w616 mod 2 ^ 64) (w624 mod 2 ^ 64) (w632 mod 2 ^ 64) fb808 fb744 fb712 fb664 fb528 fb472 fb344 fb280 fb248 fb200 fb64 HK0 H02 H03 H04 A16 SLO S240 STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb808 Hb_fb808 Hr_fb744 Hb_fb744 Hr_fb712 Hb_fb712 Hr_fb664 Hb_fb664 Hr_fb528 Hb_fb528 Hr_fb472 Hb_fb472 Hr_fb344 Hb_fb344 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb200 Hb_fb200 Hr_fb64 Hb_fb64 ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) Q2 ltac:(rewrite Q3; exact H03) ltac:(rewrite Q4; exact H04) Q9 Q10 c0_Sm952 (u64_at_mod _ _ _ c0_Sm960) c0_Sm968 (u64_at_mod _ _ _ c0_Sm976) c0_Sm888 c0_Sm896 c0_Sm904 c0_Sm912 c0_Sm536 c0_Sm544 (u64_at_mod _ _ _ c0_Sm552) c0_Sm560 (u64_at_mod _ _ _ c0_Sm568) (u64_at_mod _ _ _ c0_Sm576) (u64_at_mod _ _ _ c0_Sm584) (u64_at_mod _ _ _ c0_Sm592) (u64_at_mod _ _ _ c0_Sm600) (u64_at_mod _ _ _ c0_Sm608) (u64_at_mod _ _ _ c0_Sm616) (u64_at_mod _ _ _ c0_Sm624) (u64_at_mod _ _ _ c0_Sm632) c0_Sm488 c0_Sm496 c0_Sm424 c0_Sm432 c0_Sm440 c0_Sm72 c0_Sm80 c0_Sm88 c0_Sm96 c0_Sm104 c0_Sm112 c0_Sm120 c0_Sm128 c0_Sm136 c0_Sm144 c0_Sm152 c0_Sm160 c0_Sm168 c0_Sm24 c0_Sm32 c0_Sm8 c0_Sm16 c0_Sm808w1 c0_Sm744w1 c0_Sm720 c0_Sm728 c0_Sm712w1 c0_Sm688 c0_Sm696 c0_Sm664w1 c0_Sm528w1 c0_Sm472w1 c0_Sm344w1 c0_Sm280w1 c0_Sm248w1 c0_Sm224 c0_Sm232 c0_Sm200w1 c0_Sm176 c0_Sm184 c0_Sm64w1 XS DEF DEFd1_0 DEFd2_0 DEFd3_0 DEFd4_0 BR_d1 BR_d2 BR_d3 BR_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 HH MOK HQ0 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3CU.
