(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg HeapIface LibIface
     L5Defs L5Core L5CoreKit L5CoreSpecs L5DivSpecs L5KnP L5ParseKit L5ParseSpecs L5Bytes L5StrctorKit L5UnwindSpecs L5E2Kit L5E3S1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5E3C.
Import L5CS L5PS L5STRK L5E2K.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Section SCFG_2.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Definition assert_throw_req (LBT LB1 : list (Z * Z)) (R0 : bvmap 5 word) (M0 : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (S : Z) : Prop :=
  exists d1 d2 d3 d4 w856 w864 w872 w784 w488 w504 w512 w520 w528 w536 w544 w552 w560 w568 fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48,
     LBT = [(d1, 64); (d2, 64); (d3, 64); (d4, 64)]
  /\ getr R 2%bv = Z_to_bv 64 (S - 896)
  /\ getr R 8%bv = Z_to_bv 64 (S + 64)
  /\ getr R 10%bv = Z_to_bv 64 16
  /\ getr R 20%bv = Z_to_bv 64 (S - 584)
  /\ getr R 3%bv = getr R0 3%bv
  /\ getr R 4%bv = getr R0 4%bv
  /\ 0 <= fb696 < 256 /\ Z.testbit fb696 0 = false
  /\ 0 <= fb664 < 256 /\ Z.testbit fb664 0 = true
  /\ 0 <= fb632 < 256 /\ Z.testbit fb632 0 = true
  /\ 0 <= fb600 < 256 /\ Z.testbit fb600 0 = false
  /\ 0 <= fb464 < 256 /\ Z.testbit fb464 0 = false
  /\ 0 <= fb408 < 256 /\ Z.testbit fb408 0 = false
  /\ 0 <= fb280 < 256 /\ Z.testbit fb280 0 = false
  /\ 0 <= fb248 < 256 /\ Z.testbit fb248 0 = false
  /\ 0 <= fb216 < 256 /\ Z.testbit fb216 0 = true
  /\ 0 <= fb184 < 256 /\ Z.testbit fb184 0 = true
  /\ 0 <= fb48 < 256 /\ Z.testbit fb48 0 = false
  /\ L5.u64_at RSEGS M (S - 840) 135392
  /\ L5.u64_at RSEGS M (S - 848) (S + 64)
  /\ L5.u64_at RSEGS M (S - 856) w856
  /\ L5.u64_at RSEGS M (S - 864) w864
  /\ L5.u64_at RSEGS M (S - 872) w872
  /\ L5.u64_at RSEGS M (S - 776) 139520
  /\ L5.u64_at RSEGS M (S - 784) w784
  /\ L5.u64_at RSEGS M (S - 792) (S + 64)
  /\ L5.u64_at RSEGS M (S - 800) (S + 64)
  /\ L5.u64_at RSEGS M (S - 472) 142136
  /\ L5.u64_at RSEGS M (S - 480) (S + 64)
  /\ L5.u64_at RSEGS M (S - 488) w488
  /\ L5.u64_at RSEGS M (S - 496) (S + 64)
  /\ L5.u64_at RSEGS M (S - 504) w504
  /\ L5.u64_at RSEGS M (S - 512) w512
  /\ L5.u64_at RSEGS M (S - 520) w520
  /\ L5.u64_at RSEGS M (S - 528) w528
  /\ L5.u64_at RSEGS M (S - 536) w536
  /\ L5.u64_at RSEGS M (S - 544) w544
  /\ L5.u64_at RSEGS M (S - 552) w552
  /\ L5.u64_at RSEGS M (S - 560) w560
  /\ L5.u64_at RSEGS M (S - 568) w568
  /\ L5.u64_at RSEGS M (S - 424) 141264
  /\ L5.u64_at RSEGS M (S - 432) (S + 64)
  /\ L5.u64_at RSEGS M (S - 360) 139904
  /\ L5.u64_at RSEGS M (S - 368) (S + 64)
  /\ L5.u64_at RSEGS M (S - 376) (S - 48)
  /\ L5.u64_at RSEGS M (S - 56) 138528
  /\ L5.u64_at RSEGS M (S - 64) (S + 64)
  /\ L5.u64_at RSEGS M (S - 72) (L5E2K.U R0 9)
  /\ L5.u64_at RSEGS M (S - 80) (L5E2K.U R0 18)
  /\ L5.u64_at RSEGS M (S - 88) (L5E2K.U R0 19)
  /\ L5.u64_at RSEGS M (S - 96) (L5E2K.U R0 20)
  /\ L5.u64_at RSEGS M (S - 104) (L5E2K.U R0 21)
  /\ L5.u64_at RSEGS M (S - 112) (L5E2K.U R0 22)
  /\ L5.u64_at RSEGS M (S - 120) (L5E2K.U R0 23)
  /\ L5.u64_at RSEGS M (S - 128) (L5E2K.U R0 24)
  /\ L5.u64_at RSEGS M (S - 136) (L5E2K.U R0 25)
  /\ L5.u64_at RSEGS M (S - 144) (L5E2K.U R0 26)
  /\ L5.u64_at RSEGS M (S - 152) (L5E2K.U R0 27)
  /\ L5.u64_at RSEGS M (S - 8) 132608
  /\ L5.u64_at RSEGS M (S - 16) (L5E2K.U R0 8)
  /\ L5.u8_at RSEGS M (S - 696) fb696
  /\ L5.u8_at RSEGS M (S - 664) fb664
  /\ L5.u64_at RSEGS M (S - 640) d1
  /\ L5.u64_at RSEGS M (S - 648) 8
  /\ L5.u8_at RSEGS M (S - 632) fb632
  /\ L5.u64_at RSEGS M (S - 608) d2
  /\ L5.u64_at RSEGS M (S - 616) 8
  /\ L5.u8_at RSEGS M (S - 600) fb600
  /\ L5.u8_at RSEGS M (S - 464) fb464
  /\ L5.u8_at RSEGS M (S - 408) fb408
  /\ L5.u8_at RSEGS M (S - 280) fb280
  /\ L5.u8_at RSEGS M (S - 248) fb248
  /\ L5.u8_at RSEGS M (S - 216) fb216
  /\ L5.u64_at RSEGS M (S - 192) d3
  /\ L5.u64_at RSEGS M (S - 200) 8
  /\ L5.u8_at RSEGS M (S - 184) fb184
  /\ L5.u64_at RSEGS M (S - 160) d4
  /\ L5.u64_at RSEGS M (S - 168) 8
  /\ L5.u8_at RSEGS M (S - 48) fb48.

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

Theorem e3_chain : L5US.e3_chain_spec_of L assert_throw_req HI.
Proof.
  intros fx R0 M0 R M model K LBT LB1 cr S st REQ H01 H02 H03 H04 XS AVTOP HH MOK HK0 STK S240 CR144 CR48 CR66 KE.
  destruct st as [gd fl av uid rnd canary hw]. cbn [L5US.xs_av] in AVTOP.
  unfold L5US.xs_pre, L5US.lib_statics_at in XS. cbn [L5US.xs_gd L5US.xs_fl L5US.xs_av L5US.xs_uid L5US.xs_rnd L5US.xs_canary L5US.xs_hw] in XS.
  pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold L5DS.SCR_OPMOD in SLO, DEF.
  destruct REQ as (d1 & d2 & d3 & d4 & w856 & w864 & w872 & w784 & w488 & w504 & w512 & w520 & w528 & w536 & w544 & w552 & w560 & w568 & fb696 & fb664 & fb632 & fb600 & fb464 & fb408 & fb280 & fb248 & fb216 & fb184 & fb48 & ELBT & Q2 & Q8 & Q10 & Q20 & Q3 & Q4 & Hr_fb696 & Hb_fb696 & Hr_fb664 & Hb_fb664 & Hr_fb632 & Hb_fb632 & Hr_fb600 & Hb_fb600 & Hr_fb464 & Hb_fb464 & Hr_fb408 & Hb_fb408 & Hr_fb280 & Hb_fb280 & Hr_fb248 & Hb_fb248 & Hr_fb216 & Hb_fb216 & Hr_fb184 & Hb_fb184 & Hr_fb48 & Hb_fb48 & c0_Sm840 & c0_Sm848 & c0_Sm856 & c0_Sm864 & c0_Sm872 & c0_Sm776 & c0_Sm784 & c0_Sm792 & c0_Sm800 & c0_Sm472 & c0_Sm480 & c0_Sm488 & c0_Sm496 & c0_Sm504 & c0_Sm512 & c0_Sm520 & c0_Sm528 & c0_Sm536 & c0_Sm544 & c0_Sm552 & c0_Sm560 & c0_Sm568 & c0_Sm424 & c0_Sm432 & c0_Sm360 & c0_Sm368 & c0_Sm376 & c0_Sm56 & c0_Sm64 & c0_Sm72 & c0_Sm80 & c0_Sm88 & c0_Sm96 & c0_Sm104 & c0_Sm112 & c0_Sm120 & c0_Sm128 & c0_Sm136 & c0_Sm144 & c0_Sm152 & c0_Sm8 & c0_Sm16 & c0_Sm696w1 & c0_Sm664w1 & c0_Sm640 & c0_Sm648 & c0_Sm632w1 & c0_Sm608 & c0_Sm616 & c0_Sm600w1 & c0_Sm464w1 & c0_Sm408w1 & c0_Sm280w1 & c0_Sm248w1 & c0_Sm216w1 & c0_Sm192 & c0_Sm200 & c0_Sm184w1 & c0_Sm160 & c0_Sm168 & c0_Sm48w1). subst LBT. cbn [app] in HH, KE.
  rewrite L5CoreKit.L5K.rl2 in H02. rewrite L5CoreKit.L5K.rl3 in H03. rewrite L5CoreKit.L5K.rl4 in H04.
  rewrite L5CoreKit.L5K.rl2 in Q2. rewrite L5CoreKit.L5K.rl3 in Q3. rewrite L5CoreKit.L5K.rl4 in Q4. rewrite L5CoreKit.L5K.rl8 in Q8. rewrite L5CoreKit.L5K.rl10 in Q10. rewrite L5CoreKit.L5K.rl20 in Q20.
  unfold L5US.GP in H03. unfold TP in H04.
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
  assert (HQ0: L5C.hpres L LB1 S 10240 [(456960, 4); (459617, 6)] M M). { apply L5PK.hpres_refl. exact DEF. }
  unfold L5DS.SCR_OPMOD, L5US.xs_foot, L5US.TOP_PAD, EH_UNCAUGHT, UW_FLAGS in KE.
  eapply (L5E3S1.seg1 L HI LY LYX HIok fx R0 R M model K LB1 cr gd fl S av uid rnd canary hw d1 d2 d3 d4 (w856 mod 2 ^ 64) (w864 mod 2 ^ 64) (w872 mod 2 ^ 64) (w784 mod 2 ^ 64) (w488 mod 2 ^ 64) (w504 mod 2 ^ 64) (w512 mod 2 ^ 64) (w520 mod 2 ^ 64) (w528 mod 2 ^ 64) (w536 mod 2 ^ 64) (w544 mod 2 ^ 64) (w552 mod 2 ^ 64) (w560 mod 2 ^ 64) (w568 mod 2 ^ 64) fb696 fb664 fb632 fb600 fb464 fb408 fb280 fb248 fb216 fb184 fb48 HK0 H02 H03 H04 A16 SLO S240 STOP AVTOP LBWF CR144 CR48 CR66 Hr_fb696 Hb_fb696 Hr_fb664 Hb_fb664 Hr_fb632 Hb_fb632 Hr_fb600 Hb_fb600 Hr_fb464 Hb_fb464 Hr_fb408 Hb_fb408 Hr_fb280 Hb_fb280 Hr_fb248 Hb_fb248 Hr_fb216 Hb_fb216 Hr_fb184 Hb_fb184 Hr_fb48 Hb_fb48 ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) Q2 ltac:(rewrite Q3; exact H03) ltac:(rewrite Q4; exact H04) Q8 Q10 Q20 c0_Sm840 c0_Sm848 (u64_at_mod _ _ _ c0_Sm856) (u64_at_mod _ _ _ c0_Sm864) (u64_at_mod _ _ _ c0_Sm872) c0_Sm776 (u64_at_mod _ _ _ c0_Sm784) c0_Sm792 c0_Sm800 c0_Sm472 c0_Sm480 (u64_at_mod _ _ _ c0_Sm488) c0_Sm496 (u64_at_mod _ _ _ c0_Sm504) (u64_at_mod _ _ _ c0_Sm512) (u64_at_mod _ _ _ c0_Sm520) (u64_at_mod _ _ _ c0_Sm528) (u64_at_mod _ _ _ c0_Sm536) (u64_at_mod _ _ _ c0_Sm544) (u64_at_mod _ _ _ c0_Sm552) (u64_at_mod _ _ _ c0_Sm560) (u64_at_mod _ _ _ c0_Sm568) c0_Sm424 c0_Sm432 c0_Sm360 c0_Sm368 c0_Sm376 c0_Sm56 c0_Sm64 c0_Sm72 c0_Sm80 c0_Sm88 c0_Sm96 c0_Sm104 c0_Sm112 c0_Sm120 c0_Sm128 c0_Sm136 c0_Sm144 c0_Sm152 c0_Sm8 c0_Sm16 c0_Sm696w1 c0_Sm664w1 c0_Sm640 c0_Sm648 c0_Sm632w1 c0_Sm608 c0_Sm616 c0_Sm600w1 c0_Sm464w1 c0_Sm408w1 c0_Sm280w1 c0_Sm248w1 c0_Sm216w1 c0_Sm192 c0_Sm200 c0_Sm184w1 c0_Sm160 c0_Sm168 c0_Sm48w1 XS DEF DEFd1_0 DEFd2_0 DEFd3_0 DEFd4_0 BR_d1 BR_d2 BR_d3 BR_d4 AP_d1_d2 AP_d1_d3 AP_d1_d4 AP_d2_d3 AP_d2_d4 AP_d3_d4 HH MOK HQ0 KE).
Qed.
End WithHeap.
End SCFG_2.
End L5E3C.
