(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AS Require Import MainExport MainFactsAsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Let L := mkALayout (LV V) w U.

  Lemma arelro_init : arelro m.
  Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0x99000 0x9b000 IMG. apply IMG. lia. Qed.

  Lemma flags85_init : rw_cells asegs m 0x9f24d [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 651848) 8 (ZLit 72340172838010881)) F.
    assert (F' : rw_cells asegs m 651848 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                          C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
    do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Lemma cflags34_init : rw_cells asegs m 0x13354a [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 1258824) 8 (ZLit 128849084416)) F.
    assert (F' : rw_cells asegs m 1258824 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
                                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
    do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Theorem arep_rt_init : arep_rt L m.
  Proof.
    unfold arep_rt.
    aimg V m HM 0x99768 [C8 (Z_to_bv 64 0x1314a0)] I1.
    aimg V m HM 0x99778 [C8 (Z_to_bv 64 0x133528); C8 (Z_to_bv 64 0x9f1f8); C8 (Z_to_bv 64 0xa19f8);
                          C8 (Z_to_bv 64 0xa26e8); C8 (Z_to_bv 64 0xa26f0); C8 (Z_to_bv 64 0xa26e0)] I2.
    aimg V m HM 0x997a8 [C8 (Z_to_bv 64 0x9b5e8)] I3.
    aimg V m HM 0x9a2f0 [C8 (Z_to_bv 64 0xa26d9)] I4.
    aimg V m HM 0x9a3e0 [C8 (Z_to_bv 64 0x10)] I5.
    aimg V m HM 0x9b5e0 [C8 (Z_to_bv 64 0x92ab8); C8 (Z_to_bv 64 0x92ebc)] I6.
    aimg V m HM 0xa26e8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
    aimg V m HM 0x123c60 [C1 (Z_to_bv 8 0)] I8.
    aimg V m HM 0x123c62 [C1 (Z_to_bv 8 0)] I9.
    aimg V m HM 0x1334c0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
    aimg V m HM 0x5d49a0 [C4 (Z_to_bv 64 0)] I11.
    mf V m HM (MCell (ZLit 651704) 8 (ZLit 1099511627776)) F1.
    mf V m HM (MCell (ZLit 651712) 2 (ZLit 16)) F2.
    mf V m HM (MCell (ZLit 651714) 2 (ZLit 2048)) F3.
    mf V m HM (MCell (ZLit 651716) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 651768) 4 (ZLit 4294967295)) F5.
    mf V m HM (MCell (ZLit 651772) 4 (ZLit 256)) F6.
    mf V m HM (MCell (ZLit 651776) 4 (ZLit 1024)) F7.
    mf V m HM (MCell (ZLit 651780) 4 (ZLit 16)) F8.
    mf V m HM (MCell (ZLit 651784) 4 (ZLit 2048)) F9.
    mf V m HM (MCell (ZLit 651812) 4 (ZLit 4096)) F10.
    mf V m HM (MCell (ZLit 651816) 8 (ZLit 816043786240)) F11.
    assert (F11' : rw_cells asegs m 651816 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
    mf V m HM (MCell (ZLit 662008) 8 (ZLit 2147450880)) F12.
    mf V m HM (MCell (ZLit 660060) 1 (ZLit 1)) F13.
    mf V m HM (MCell (ZLit 660064) 1 (ZLit 1)) F14.
    mf V m HM (MCell (ZLit 660068) 4 (ZLit 0)) F15.
    mf V m HM (MCell (ZLit 665304) 1 (ZLit 1)) F16.
    mf V m HM (MCell (ZLit 665305) 1 (ZLit 1)) F17.
    mf V m HM (MCell (ZLit 665312) 8 (ZLit 140737488355327)) F18.
    mf V m HM (MCell (ZLit 665340) 4 (ZLit 30)) F19.
    mf V m HM (MCell (ZLit 1195105) 1 (ZLit 1)) F20.
    mf V m HM (MCell (ZLit 1250464) 8 (ZLit 4096)) F21.
    mf V m HM (MCell (ZLit 1258824) 8 (ZLit 128849084416)) F22.
    mf V m HM (MCell (ZLit 1258912) 8 (ZLit 18446744073709551615)) F23.
    mf V m HM (MCell (ZLit 6113592) 8 (ZLit 6249784)) F24.
    mf V m HM (MCell (ZLit 6249784) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
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
    mf V m HM (MCell (ZLit 1259048) 8 (ZLit 16843009)) F1.
    assert (F1' : rw_cells asegs m 1259048 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
    do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
    mf V m HM (MCell (ZLit 1258936) 8 (ZLit 0)) F2.
    aimg V m HM 0x9b4a8 [C8 (Z_to_bv 64 0x929bc)] I1.
    split; [exact F1'|]. split; [exact F2| exact I1].
  Qed.

  Theorem arep_rt3_init : arep_rt3 m.
  Proof.
    unfold arep_rt3.
    aimg V m HM 0x9b4d8 [C8 (Z_to_bv 64 0x92408); C8 (Z_to_bv 64 0x8f2f8)] I1.
    aimg V m HM 0x9b4b8 [C8 (Z_to_bv 64 0x981bc)] I2.
    aimg V m HM 0x9b4c0 [C8 (Z_to_bv 64 0x8f070)] I3.
    aimg V m HM 0x9b590 [C8 (Z_to_bv 64 0x93344)] I4.
    aimg V m HM 0x9b4a8 [C8 (Z_to_bv 64 0x929bc)] I5.
    mf V m HM (MCell (ZLit 1258872) 8 (ZLit 4294967296)) F1.
    mf V m HM (MCell (ZLit 1259040) 8 (ZLit 72340172838076673)) F2.
    mf V m HM (MCell (ZLit 662016) 4 (ZLit 1)) F3.
    mf V m HM (MCell (ZLit 651864) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 1250456) 4 (ZLit 0)) F5.
    aimg V m HM 0x99768 [C8 (Z_to_bv 64 0x1314a0); C8 (Z_to_bv 64 0x9b620)] I6.
    aimg V m HM 0x9b620 [C8 (Z_to_bv 64 0x191bf)] I7.
    mf V m HM (MCell (ZLit 1250464) 8 (ZLit 4096)) F6.
    mf V m HM (MCell (ZLit 1259008) 8 (ZLit 1103823372544)) F7.
    mf V m HM (MCell (ZLit 1259032) 8 (ZLit 72339073309605888)) F8.
    mf V m HM (MCell (ZLit 6245456) 8 (ZLit 4096)) F10.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].
  Qed.

  Theorem ainstance_init : ainstance L (ST0 V) m.
  Proof.
    unfold ainstance, AINSTANCE.
    mf V m HM (MCell (ZLit 648120) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
    mf V m HM (MCell (ZLit 648136) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
    mf V m HM (MCell (ZLit 648152) 8 (ZLit 4096)) F3.
    mf V m HM (MCell (ZLit 648160) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
    aimg V m HM 0x9e408 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
    mf V m HM (MCell (ZLit 648768) 1 (ZLit 0)) F6.
    aimg V m HM 0x9e770 [C1 (Z_to_bv 8 0)] I7.
    mf V m HM (MCell (ZLit 648128) 4 (ZLit 18446744073709551615)) F8.
    assert (F8' : rw_cells asegs m 648128 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
    mf V m HM (MCell (ZLit 648144) 1 (ZLit 0)) F9.
    assert (ESB : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (unfold al_space_beg; cbn [al_V L LV Nat.eqb]; lia).
    split; [rewrite ESB; exact F1|].
    split; [rewrite ESB; unfold K_SPACE_SIZE; replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
                                                 with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia; exact F2|].
    split; [exact F3|]. split; [exact F4|]. split; [exact I5|]. split; [exact F6|]. split; [exact I7|]. split; [exact F8'| exact F9].
  Qed.

  Theorem aquar_glob_const_init : aquar_glob_const m.
  Proof.
    unfold aquar_glob_const, AQ_MAX, AQ_MUTEX.
    mf V m HM (MCell (ZLit 648880) 8 (ZLit 268435456)) F1.
    mf V m HM (MCell (ZLit 648888) 8 (ZLit 241591905)) F2.
    mf V m HM (MCell (ZLit 648896) 8 (ZLit 1048576)) F3.
    mf V m HM (MCell (ZLit 648968) 1 (ZLit 0)) F4.
    mf V m HM (MCell (ZLit 648969) 1 (ZLit 0)) F5.
    aimg V m HM 0x9e70a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
    split.
    - apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
    - apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
  Qed.

  Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
  Proof.
    unfold aqcache, AQ_GCACHE. aimg V m HM 0x9e710 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
    split; [exact IG| exact Logic.I].
  Qed.

  Lemma aia_scan : zscanN Tgt_checksum_fuzzer_asan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.
  Proof. vm_compute. reflexivity. Qed.

  Theorem aintal_init : aintal false m.
  Proof.
    unfold aintal, AIA_FLAG.
    aimg V m HM 0x131488 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
    split; [exact I1|]. split; [| intros; discriminate].
    mimg V m HM 0xa2c00 (0xa2c00 + 0x81030) IMG. mwr V m HM (ZLit 626688) 5618128 W.
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
