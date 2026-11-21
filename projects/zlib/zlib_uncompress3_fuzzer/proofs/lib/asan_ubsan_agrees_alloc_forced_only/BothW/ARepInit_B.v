(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoffBoth.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require HexScanFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma zscanN_fastE_p04 : forall s fuel base n, zscanN s fuel base n = HexScanFast.gscanN (HexScanFast.byte_zero s) fuel base n.
Proof. intros s fuel. induction fuel as [|f IH]; intros base n; cbn [zscanN HexScanFast.gscanN]; [reflexivity|]. rewrite !IH. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Let L := mkALayout (LV V) w U.

  Lemma arelro_init : arelro m.
  Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0xce000 0xd3000 IMG. apply IMG. lia. Qed.

  Lemma flags85_init : rw_cells bsegs m 0xd770d [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 882440) 8 (ZLit 72340172838010881)) F.
    assert (F' : rw_cells bsegs m 882440 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                          C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
    do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Lemma cflags34_init : rw_cells bsegs m 0x16ba0a [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 1489416) 8 (ZLit 128849084416)) F.
    assert (F' : rw_cells bsegs m 1489416 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
                                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
    do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Theorem arep_rt_init : arep_rt L m.
  Proof.
    unfold arep_rt.
    aimg V m HM 0xd1698 [C8 (Z_to_bv 64 0x169960)] I1.
    aimg V m HM 0xd16a8 [C8 (Z_to_bv 64 0x16b9e8); C8 (Z_to_bv 64 0xd76b8); C8 (Z_to_bv 64 0xd9eb8);
                          C8 (Z_to_bv 64 0xdaba8); C8 (Z_to_bv 64 0xdabb0); C8 (Z_to_bv 64 0xdaba0)] I2.
    aimg V m HM 0xd16d8 [C8 (Z_to_bv 64 0xd3570)] I3.
    aimg V m HM 0xd2220 [C8 (Z_to_bv 64 0xdab99)] I4.
    aimg V m HM 0xd2310 [C8 (Z_to_bv 64 0x10)] I5.
    aimg V m HM 0xd3568 [C8 (Z_to_bv 64 0xc79f4); C8 (Z_to_bv 64 0xc7df8)] I6.
    aimg V m HM 0xdaba8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
    aimg V m HM 0x15c120 [C1 (Z_to_bv 8 0)] I8.
    aimg V m HM 0x15c122 [C1 (Z_to_bv 8 0)] I9.
    aimg V m HM 0x16b980 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
    aimg V m HM 0x65d088 [C4 (Z_to_bv 64 0)] I11.
    mf V m HM (MCell (ZLit 882296) 8 (ZLit 1099511627776)) F1.
    mf V m HM (MCell (ZLit 882304) 2 (ZLit 16)) F2.
    mf V m HM (MCell (ZLit 882306) 2 (ZLit 2048)) F3.
    mf V m HM (MCell (ZLit 882308) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 882360) 4 (ZLit 4294967295)) F5.
    mf V m HM (MCell (ZLit 882364) 4 (ZLit 256)) F6.
    mf V m HM (MCell (ZLit 882368) 4 (ZLit 1024)) F7.
    mf V m HM (MCell (ZLit 882372) 4 (ZLit 16)) F8.
    mf V m HM (MCell (ZLit 882376) 4 (ZLit 2048)) F9.
    mf V m HM (MCell (ZLit 882404) 4 (ZLit 4096)) F10.
    mf V m HM (MCell (ZLit 882408) 8 (ZLit 816043786240)) F11.
    assert (F11' : rw_cells bsegs m 882408 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
    mf V m HM (MCell (ZLit 892600) 8 (ZLit 2147450880)) F12.
    mf V m HM (MCell (ZLit 890652) 1 (ZLit 1)) F13.
    mf V m HM (MCell (ZLit 890656) 1 (ZLit 1)) F14.
    mf V m HM (MCell (ZLit 890660) 4 (ZLit 0)) F15.
    mf V m HM (MCell (ZLit 895896) 1 (ZLit 1)) F16.
    mf V m HM (MCell (ZLit 895897) 1 (ZLit 1)) F17.
    mf V m HM (MCell (ZLit 895904) 8 (ZLit 140737488355327)) F18.
    mf V m HM (MCell (ZLit 895932) 4 (ZLit 30)) F19.
    mf V m HM (MCell (ZLit 1425697) 1 (ZLit 1)) F20.
    mf V m HM (MCell (ZLit 1481056) 8 (ZLit 4096)) F21.
    mf V m HM (MCell (ZLit 1489416) 8 (ZLit 128849084416)) F22.
    mf V m HM (MCell (ZLit 1489504) 8 (ZLit 18446744073709551615)) F23.
    mf V m HM (MCell (ZLit 6672416) 8 (ZLit 6808608)) F24.
    mf V m HM (MCell (ZLit 6808608) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 8)) 4 (ZLit 0)) F26.
    mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 152)) 8 (ZMul (ZLit 4096) (ZV 227))) F27.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|]. split; [exact I6|].
    split; [apply rw_cells_cons; [exact F1| apply rw_cells_cons; [exact F2| apply rw_cells_cons; [exact F3| exact F4]]]|].
    split; [apply rw_cells_cons; [exact F5| apply rw_cells_cons; [exact F6| apply rw_cells_cons; [exact F7| apply rw_cells_cons; [exact F8| exact F9]]]]|].
    split; [apply rw_cells_cons; [exact F10| exact F11']|].
    split; [exact flags85_init|].
    split; [exact F12|]. split; [exact F13|]. split; [exact F14|]. split; [exact F15|].
    split; [apply rw_cells_cons; [exact F16| exact F17]|].
    split; [apply rw_cells_cons; [exact F18| exact I7]|].
    split; [exact F19|].
    split; [apply rw_cells_cons; [exact I8| apply rw_cells_cons; [exact F20| exact I9]]|].
    split; [exact F21|]. split; [exact I10|]. split; [exact F22|]. split; [exact cflags34_init|]. split; [exact F23|].
    split; [exact F24|]. split; [exact F25|]. split; [exact I11|]. split; [exact F26| exact F27].
  Qed.

  Theorem arep_rt2_init : arep_rt2 m.
  Proof.
    unfold arep_rt2.
    mf V m HM (MCell (ZLit 1489640) 8 (ZLit 16843009)) F1.
    assert (F1' : rw_cells bsegs m 1489640 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
    do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
    mf V m HM (MCell (ZLit 1489528) 8 (ZLit 0)) F2.
    aimg V m HM 0xd3428 [C8 (Z_to_bv 64 0xc78f8)] I1.
    split; [exact F1'|]. split; [exact F2| exact I1].
  Qed.

  Theorem arep_rt3_init : arep_rt3 m.
  Proof.
    unfold arep_rt3.
    aimg V m HM 0xd3458 [C8 (Z_to_bv 64 0xc7340); C8 (Z_to_bv 64 0xc4230)] I1.
    aimg V m HM 0xd3438 [C8 (Z_to_bv 64 0xcd0f8)] I2.
    aimg V m HM 0xd3440 [C8 (Z_to_bv 64 0xc3ffc)] I3.
    aimg V m HM 0xd3518 [C8 (Z_to_bv 64 0xc8280)] I4.
    aimg V m HM 0xd3428 [C8 (Z_to_bv 64 0xc78f8)] I5.
    mf V m HM (MCell (ZLit 1489464) 8 (ZLit 4294967296)) F1.
    mf V m HM (MCell (ZLit 1489632) 8 (ZLit 72340172838076673)) F2.
    mf V m HM (MCell (ZLit 892608) 4 (ZLit 1)) F3.
    mf V m HM (MCell (ZLit 882456) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 1481048) 4 (ZLit 0)) F5.
    aimg V m HM 0xd1698 [C8 (Z_to_bv 64 0x169960); C8 (Z_to_bv 64 0xd35a8)] I6.
    aimg V m HM 0xd35a8 [C8 (Z_to_bv 64 0x1a078)] I7.
    mf V m HM (MCell (ZLit 1481056) 8 (ZLit 4096)) F6.
    mf V m HM (MCell (ZLit 1489600) 8 (ZLit 1103823372544)) F7.
    mf V m HM (MCell (ZLit 1489624) 8 (ZLit 72339073309605888)) F8.
    mf V m HM (MCell (ZLit 6804280) 8 (ZLit 4096)) F10.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].
  Qed.

  Theorem ainstance_init : ainstance L (ST0 V) m.
  Proof.
    unfold ainstance, AINSTANCE.
    mf V m HM (MCell (ZLit 878712) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
    mf V m HM (MCell (ZLit 878728) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
    mf V m HM (MCell (ZLit 878744) 8 (ZLit 4096)) F3.
    mf V m HM (MCell (ZLit 878752) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
    aimg V m HM 0xd68c8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
    mf V m HM (MCell (ZLit 879360) 1 (ZLit 0)) F6.
    aimg V m HM 0xd6c30 [C1 (Z_to_bv 8 0)] I7.
    mf V m HM (MCell (ZLit 878720) 4 (ZLit 18446744073709551615)) F8.
    assert (F8' : rw_cells bsegs m 878720 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
    mf V m HM (MCell (ZLit 878736) 1 (ZLit 0)) F9.
    assert (ESB : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (unfold al_space_beg; cbn [al_V L LV Nat.eqb]; lia).
    split; [rewrite ESB; exact F1|].
    split; [rewrite ESB; unfold K_SPACE_SIZE; replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
                                                 with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia; exact F2|].
    split; [exact F3|]. split; [exact F4|]. split; [exact I5|]. split; [exact F6|]. split; [exact I7|]. split; [exact F8'| exact F9].
  Qed.

  Theorem aquar_glob_const_init : aquar_glob_const m.
  Proof.
    unfold aquar_glob_const, AQ_MAX, AQ_MUTEX.
    mf V m HM (MCell (ZLit 879472) 8 (ZLit 268435456)) F1.
    mf V m HM (MCell (ZLit 879480) 8 (ZLit 241591905)) F2.
    mf V m HM (MCell (ZLit 879488) 8 (ZLit 1048576)) F3.
    mf V m HM (MCell (ZLit 879560) 1 (ZLit 0)) F4.
    mf V m HM (MCell (ZLit 879561) 1 (ZLit 0)) F5.
    aimg V m HM 0xd6bca [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
    split.
    - apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
    - apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
  Qed.

  Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
  Proof.
    unfold aqcache, AQ_GCACHE. aimg V m HM 0xd6bd0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
    split; [exact IG| exact Logic.I].
  Qed.

  Lemma aia_scan : zscanN Tgt_zlib_uncompress3_fuzzer_both_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.
  Proof. rewrite zscanN_fastE_p04. apply HexScanFast.zscanN_of_I; [vm_cast_no_check (eq_refl true) | vm_compute; reflexivity]. Qed.

  Theorem aintal_init : aintal false m.
  Proof.
    unfold aintal, AIA_FLAG.
    aimg V m HM 0x169948 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
    split; [exact I1|]. split; [| intros; discriminate].
    mimg V m HM 0xdb0c0 (0xdb0c0 + 0x81030) IMG. mwr V m HM (ZLit 843776) 5959864 W.
    assert (EQN : Z.of_N (Z.to_N AIA_SIZE) = AIA_SIZE) by (apply Z2N.id; unfold AIA_SIZE; lia).
    pose proof (img_zero_stk (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) m AIA_BASE aia_scan) as K. rewrite EQN in K.
    apply K.
    - unfold AIA_BASE, SEG3. reflexivity.
    - unfold AIA_BASE, AIA_SIZE. lia.
    - intros i Hi. apply IMG. unfold AIA_BASE, AIA_SIZE in Hi. lia.
    - eapply wr_at_sub; [exact W| unfold AIA_BASE; lia| unfold AIA_BASE; lia| unfold AIA_BASE, AIA_SIZE; lia].
  Qed.
End B.
End CANSEC1.
