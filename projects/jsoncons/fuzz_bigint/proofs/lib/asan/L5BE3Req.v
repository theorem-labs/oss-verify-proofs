(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA LibIface
     AsanAcct L5Defs L5Kn L5KnA L5Core L5Words L5LazyA L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5CoreBB0 L5DivLeafSpecsAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivInnerSpecsAB0.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5BE3R.
Import L5A. Import L5CA. Import L5CSA. Import L5CB. Import L5DSA. Import L5DIA.
Section SCFG_1.
Context {SCFG_P : ScfgP}.
Section Specs.
Variables (L : asan_layout) (ar : asan_run).

(* [comment removed for export] *)
Definition assert_throw_regsB (R0 R : bvmap 5 word) (S_ xo F1c F1d F3b : Z) : Prop :=
     getr R 2%bv = Z_to_bv 64 (S_ - 1296) /\ getr R 3%bv = getr R0 3%bv /\ getr R 4%bv = getr R0 4%bv
  /\ getr R 10%bv = Z_to_bv 64 16
  /\ getr R 8%bv = Z_to_bv 64 (S_ - 1168) /\ getr R 9%bv = Z_to_bv 64 (S_ - 1296)
  /\ getr R 18%bv = Z_to_bv 64 F1d /\ getr R 19%bv = Z_to_bv 64 xo /\ getr R 20%bv = Z_to_bv 64 (F1d + 32)
  /\ getr R 21%bv = Z_to_bv 64 (xo + 8) /\ getr R 22%bv = Z_to_bv 64 (F1c / 8 + SB) /\ getr R 23%bv = Z_to_bv 64 (F1d / 8 + SB)
  /\ getr R 24%bv = Z_to_bv 64 F1d /\ getr R 25%bv = Z_to_bv 64 SB /\ getr R 26%bv = Z_to_bv 64 ((xo + 8) / 8 + SB) /\ getr R 27%bv = Z_to_bv 64 F3b.

Definition assert_throw_atB (LBT LB1 : list (Z * Z)) (FF : list fframe) (R0 : bvmap 5 word) (M0 : word -> option byte)
           (R : bvmap 5 word) (M : word -> option byte) (S_ xo : Z) (FR : list (Z * Z)) : Prop :=
  exists (F1a fl1a F3a fl3a F1b fl1b F3b fl3b F1c fl1c F1d fl1d d1 d2 d3 d4 qx bo : Z) (LB0 : list (Z * Z)) (lenX : nat)
         (w5 w10 xs fbx : Z) (fd0N fn0N fnN fdenN w1 : Z) (fd0 fn0 fn fden v0 v1 v2 v3 : Z) (nd0 nn0 nn nd : nat) (bq : L5.bigobj),
     FR = [(F1a, fl1a); (F3a, fl3a); (F1b, fl1b); (F3b, fl3b); (F1c, fl1c); (F1d, fl1d)]
  /\ LBT = [(d1, 64); (d2, 64); (d3, 64); (d4, 64)] /\ LB1 = (qx, 64) :: LB0
  /\ assert_throw_regsB R0 R S_ xo F1c F1d F3b
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 1176) RESERVE_RET /\ L5.u64_at RSEGS M (S_ - 1184) (S_ - 1040) /\ L5.u64_at RSEGS M (S_ - 1192) (S_ - 1168)
  /\ L5.u64_at RSEGS M (S_ - 1200) F1c /\ L5.u64_at RSEGS M (S_ - 1208) (2 ^ 64 - 1) /\ L5.u64_at RSEGS M (S_ - 1216) xo
  /\ L5.u64_at RSEGS M (S_ - 1224) (xo + 8) /\ L5.u64_at RSEGS M (S_ - 1232) (S F1c) /\ L5.u64_at RSEGS M (S_ - 1240) F1c
  /\ L5.u64_at RSEGS M (S_ - 1248) SB /\ L5.u64_at RSEGS M (S_ - 1256) (Z.of_nat lenX) /\ L5.u64_at RSEGS M (S_ - 1264) (S (xo + 8))
  /\ L5.u64_at RSEGS M (S_ - 1280) F1d
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 1048) RESIZE_RET_G /\ L5.u64_at RSEGS M (S_ - 1056) (S_ - 656) /\ L5.u64_at RSEGS M (S_ - 1064) (S_ - 1040)
  /\ L5.u64_at RSEGS M (S_ - 1072) (S F3b) /\ L5.u64_at RSEGS M (S_ - 1080) (F3b + 32) /\ L5.u64_at RSEGS M (S_ - 1088) 0
  /\ L5.u64_at RSEGS M (S_ - 1096) xo /\ L5.u64_at RSEGS M (S_ - 1104) F3b /\ L5.u64_at RSEGS M (S_ - 1112) SB
  /\ L5.u64_at RSEGS M (S_ - 1120) 0 /\ L5.u64_at RSEGS M (S_ - 1128) (F3b + 96) /\ L5.u64_at RSEGS M (S_ - 1136) (xo + 8)
  /\ L5.u64_at RSEGS M (S_ - 1144) F1c
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 664) DIV_RET_N /\ L5.u64_at RSEGS M (S_ - 672) (S_ - 560) /\ L5.u64_at RSEGS M (S_ - 680) (S_ - 656)
  /\ L5.u64_at RSEGS M (S_ - 688) F1b /\ L5.u64_at RSEGS M (S_ - 696) xo /\ L5.u64_at RSEGS M (S_ - 704) (S_ - 552)
  /\ L5.u64_at RSEGS M (S_ - 712) (F1b + 32) /\ L5.u64_at RSEGS M (S_ - 720) (S F1b) /\ L5.u64_at RSEGS M (S_ - 728) F1b
  /\ L5.u64_at RSEGS M (S_ - 736) RETIRE_MAGIC /\ L5.u64_at RSEGS M (S_ - 744) (F3a + 96) /\ L5.u64_at RSEGS M (S_ - 752) w10
  /\ L5.u64_at RSEGS M (S_ - 760) F3a
  /\ L5.u64_at RSEGS M (S_ - 1016) F3b /\ L5.u64_at RSEGS M (S_ - 992) F3b
  /\ L5.u64_at RSEGS M (S_ - 936) (F3b + 96) /\ L5.u64_at RSEGS M (S_ - 960) (F3b + 32) /\ L5.u64_at RSEGS M (S_ - 944) (F1b + 32)
  /\ L5.u64_at RSEGS M (S_ - 952) xo /\ L5.u64_at RSEGS M (S_ - 776) (F3b + 48)
  /\ L5.u64_at RSEGS M (S_ - 768) 1 /\ L5.u64_at RSEGS M (S_ - 928) 1 /\ L5.u64_at RSEGS M (S_ - 920) xo /\ L5.u64_at RSEGS M (S_ - 912) F3b
  /\ L5.u32_at RSEGS M (S_ - 876) 0
  /\ L5.big_at RSEGS M (S_ - 872) (L5.BO fd0N 1 (L5.BInl MWORD 0))
  /\ L5.big_at RSEGS M (S_ - 840) (L5.BO fn0N lenX (L5.BDyn 8 d1))
  /\ L5.big_at RSEGS M (F3b + 96) (L5.BO fnN 0 (L5.BDyn 8 d2)) /\ Z.testbit fnN 1 = false
  /\ L5.big_at RSEGS M (F3b + 32) (L5.BO fdenN 1 (L5.BInl MWORD w1)) /\ Z.testbit fdenN 1 = false
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 568) DIVEQ_RET /\ L5.u64_at RSEGS M (S_ - 576) xo /\ L5.u64_at RSEGS M (S_ - 584) xs
  /\ L5.u64_at RSEGS M (S_ - 592) (S F3a) /\ L5.u64_at RSEGS M (S_ - 600) xo /\ L5.u64_at RSEGS M (S_ - 608) (F1a + 32)
  /\ L5.u64_at RSEGS M (S_ - 616) w5 /\ L5.u64_at RSEGS M (S_ - 624) F3a /\ L5.u64_at RSEGS M (S_ - 632) SB
  /\ L5.u64_at RSEGS M (S_ - 640) (F3a + 32) /\ L5.u64_at RSEGS M (S_ - 648) F1b
  /\ zero_obj M (F1b + 32)
  (* [comment removed for export] *)
  /\ L5.u64_at RSEGS M (S_ - 504) UNNORM_RET /\ L5.u64_at RSEGS M (S_ - 512) (S_ - 112) /\ L5.u64_at RSEGS M (S_ - 520) (S_ - 496)
  /\ mword_obj M (S_ - 552) 0
  (* [comment removed for export] *)
  /\ divO_saves R0 M S_ F1a xo bo
  /\ L5.u64_at RSEGS M (S_ - 488) 1 /\ L5.u64_at RSEGS M (S_ - 472) F3a /\ L5.u64_at RSEGS M (S_ - 448) F3a
  /\ L5.u64_at RSEGS M (S_ - 392) (F3a + 96) /\ L5.u64_at RSEGS M (S_ - 416) (F3a + 32) /\ L5.u64_at RSEGS M (S_ - 400) xo
  /\ L5.u64_at RSEGS M (S_ - 408) (F1a + 32)
  /\ L5.u64_at RSEGS M (S_ - 376) xo /\ L5.u64_at RSEGS M (S_ - 368) F3a
  /\ L5.big_at RSEGS M (S_ - 328) (L5.BO fd0 nd0 (L5.BInl v0 v1))
  /\ L5.big_at RSEGS M (S_ - 296) (L5.BO fn0 nn0 (L5.BInl v2 v3))
  /\ L5.big_at RSEGS M (F3a + 96) (L5.BO fn nn (L5.BDyn 8 d3))
  /\ L5.big_at RSEGS M (F3a + 32) (L5.BO fden nd (L5.BDyn 8 d4))
  (* [comment removed for export] *)
  /\ opmod_frame R0 M S_ F1a
  /\ L5.big_at RSEGS M (F1a + 32) bq /\ L5.bo_dyn bq = false
  /\ L5.big_at RSEGS M xo (L5.BO fbx lenX (L5.BDyn 8 qx))
  (* [comment removed for export] *)
  /\ sh_rz M F1d /\ sh_rz M F1c /\ sh_div M F3b 0 0xf8 0xf8 0xf8 0xf8 /\ sh_op M F1b /\ sh_div M F3a 0 0xf8 0xf8 0xf8 0xf8 /\ sh_op M F1a
  (* [comment removed for export] *)
  /\ fr_live L ar (LBT ++ LB1) ((F1c, 1, S_ - 1136) :: (F3b, 3, S_ - 1008) :: (F1b, 1, S_ - 624) :: (F3a, 3, S_ - 464) :: (F1a, 1, S_ - 80) :: FF) M 1 F1d fl1d (S_ - 1264)
  /\ fr_live L ar (LBT ++ LB1) ((F3b, 3, S_ - 1008) :: (F1b, 1, S_ - 624) :: (F3a, 3, S_ - 464) :: (F1a, 1, S_ - 80) :: FF) M 1 F1c fl1c (S_ - 1136)
  /\ fr_live L ar (LBT ++ LB1) ((F1b, 1, S_ - 624) :: (F3a, 3, S_ - 464) :: (F1a, 1, S_ - 80) :: FF) M 3 F3b fl3b (S_ - 1008)
  /\ fr_live L ar (LBT ++ LB1) ((F3a, 3, S_ - 464) :: (F1a, 1, S_ - 80) :: FF) M 1 F1b fl1b (S_ - 624)
  /\ fr_live L ar (LBT ++ LB1) ((F1a, 1, S_ - 80) :: FF) M 3 F3a fl3a (S_ - 464)
  /\ fr_live L ar (LBT ++ LB1) FF M 1 F1a fl1a (S_ - 80).

End Specs.
End SCFG_1.
End L5BE3R.
