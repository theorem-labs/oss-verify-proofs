(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import STree AsanCtrl AsanEmbed. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.X2W.Spec Require Import AsanHandoffBoth.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require HexScanFast.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.AS Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import BImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.X2W.BothW Require Import ARepInit_A.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma zscanN_fastE_p04 : forall s fuel base n, zscanN s fuel base n = HexScanFast.gscanN (HexScanFast.byte_zero s) fuel base n.
Proof. intros s fuel. induction fuel as [|f IH]; intros base n; cbn [zscanN HexScanFast.gscanN]; [reflexivity|]. rewrite !IH. reflexivity. Qed.

Section CANSEC1. Context {rc : runConstT}.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Let L := mkALayout (LV V) w U.

  Lemma arelro_init : arelro m.
  Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0xcd000 0xd3000 IMG. apply IMG. lia. Qed.

  (* [comment removed for export] *)
  Lemma flags85_init : rw_cells bsegs m 0xd73cd [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 881608) 8 (ZLit 72340172838010881)) F.
    assert (F' : rw_cells bsegs m 881608 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                          C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
    do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Lemma cflags34_init : rw_cells bsegs m 0x16b6ca [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 1488584) 8 (ZLit 128849084416)) F.
    assert (F' : rw_cells bsegs m 1488584 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
                                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
    do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Theorem arep_rt_init : arep_rt L m.
  Proof.
    unfold arep_rt.
    aimg V m HM 0xd1380 [C8 (Z_to_bv 64 0x169620)] I1.
    aimg V m HM 0xd1390 [C8 (Z_to_bv 64 0x16b6a8); C8 (Z_to_bv 64 0xd7378); C8 (Z_to_bv 64 0xd9b78);
                          C8 (Z_to_bv 64 0xda868); C8 (Z_to_bv 64 0xda870); C8 (Z_to_bv 64 0xda860)] I2.
    aimg V m HM 0xd13c0 [C8 (Z_to_bv 64 0xd3258)] I3.
    aimg V m HM 0xd1f08 [C8 (Z_to_bv 64 0xda859)] I4.
    aimg V m HM 0xd1ff8 [C8 (Z_to_bv 64 0x10)] I5.   (* [comment removed for export] *)
    aimg V m HM 0xd3250 [C8 (Z_to_bv 64 0xc76dc); C8 (Z_to_bv 64 0xc7ae0)] I6.
    aimg V m HM 0xda868 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
    aimg V m HM 0x15bde0 [C1 (Z_to_bv 8 0)] I8.
    aimg V m HM 0x15bde2 [C1 (Z_to_bv 8 0)] I9.
    aimg V m HM 0x16b640 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
    aimg V m HM 0x65cd48 [C4 (Z_to_bv 64 0)] I11.
    mf V m HM (MCell (ZLit 881464) 8 (ZLit 1099511627776)) F1.
    mf V m HM (MCell (ZLit 881472) 2 (ZLit 16)) F2.
    mf V m HM (MCell (ZLit 881474) 2 (ZLit 2048)) F3.
    mf V m HM (MCell (ZLit 881476) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 881528) 4 (ZLit 4294967295)) F5.
    mf V m HM (MCell (ZLit 881532) 4 (ZLit 256)) F6.
    mf V m HM (MCell (ZLit 881536) 4 (ZLit 1024)) F7.
    mf V m HM (MCell (ZLit 881540) 4 (ZLit 16)) F8.
    mf V m HM (MCell (ZLit 881544) 4 (ZLit 2048)) F9.
    mf V m HM (MCell (ZLit 881572) 4 (ZLit 4096)) F10.
    mf V m HM (MCell (ZLit 881576) 8 (ZLit 816043786240)) F11.
    assert (F11' : rw_cells bsegs m 881576 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
    mf V m HM (MCell (ZLit 891768) 8 (ZLit 2147450880)) F12.
    mf V m HM (MCell (ZLit 889820) 1 (ZLit 1)) F13.
    mf V m HM (MCell (ZLit 889824) 1 (ZLit 1)) F14.
    mf V m HM (MCell (ZLit 889828) 4 (ZLit 0)) F15.
    mf V m HM (MCell (ZLit 895064) 1 (ZLit 1)) F16.
    mf V m HM (MCell (ZLit 895065) 1 (ZLit 1)) F17.
    mf V m HM (MCell (ZLit 895072) 8 (ZLit 140737488355327)) F18.
    mf V m HM (MCell (ZLit 895100) 4 (ZLit 30)) F19.
    mf V m HM (MCell (ZLit 1424865) 1 (ZLit 1)) F20.
    mf V m HM (MCell (ZLit 1480224) 8 (ZLit 4096)) F21.
    mf V m HM (MCell (ZLit 1488584) 8 (ZLit 128849084416)) F22.
    mf V m HM (MCell (ZLit 1488672) 8 (ZLit 18446744073709551615)) F23.
    mf V m HM (MCell (ZLit 6671584) 8 (ZLit 6807776)) F24.
    mf V m HM (MCell (ZLit 6807776) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
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
    mf V m HM (MCell (ZLit 1488808) 8 (ZLit 16843009)) F1.
    assert (F1' : rw_cells bsegs m 1488808 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
    do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
    mf V m HM (MCell (ZLit 1488696) 8 (ZLit 0)) F2.
    aimg V m HM 0xd3110 [C8 (Z_to_bv 64 0xc75e0)] I1.
    split; [exact F1'|]. split; [exact F2| exact I1].
  Qed.

  Theorem arep_rt3_init : arep_rt3 m.
  Proof.
    unfold arep_rt3.
    aimg V m HM 0xd3140 [C8 (Z_to_bv 64 0xc7028); C8 (Z_to_bv 64 0xc3f18)] I1.
    aimg V m HM 0xd3120 [C8 (Z_to_bv 64 0xccde0)] I2.
    aimg V m HM 0xd3128 [C8 (Z_to_bv 64 0xc3ce4)] I3.
    aimg V m HM 0xd3200 [C8 (Z_to_bv 64 0xc7f68)] I4.
    aimg V m HM 0xd3110 [C8 (Z_to_bv 64 0xc75e0)] I5.
    mf V m HM (MCell (ZLit 1488632) 8 (ZLit 4294967296)) F1.
    mf V m HM (MCell (ZLit 1488800) 8 (ZLit 72340172838076673)) F2.
    mf V m HM (MCell (ZLit 891776) 4 (ZLit 1)) F3.
    mf V m HM (MCell (ZLit 881624) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 1480216) 4 (ZLit 0)) F5.
    (* [comment removed for export] *)
    aimg V m HM 0xd1380 [C8 (Z_to_bv 64 0x169620); C8 (Z_to_bv 64 0xd3290)] I6.
    aimg V m HM 0xd3290 [C8 (Z_to_bv 64 0x1a093)] I7.
    mf V m HM (MCell (ZLit 1480224) 8 (ZLit 4096)) F6.
    mf V m HM (MCell (ZLit 1488768) 8 (ZLit 1103823372544)) F7.
    mf V m HM (MCell (ZLit 1488792) 8 (ZLit 72339073309605888)) F8.
    (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 6803448) 8 (ZLit 4096)) F10.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].   (* [comment removed for export] *)
  Qed.

  Theorem ainstance_init : ainstance L (ST0 V) m.
  Proof.
    unfold ainstance, AINSTANCE.
    mf V m HM (MCell (ZLit 877880) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
    mf V m HM (MCell (ZLit 877896) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
    mf V m HM (MCell (ZLit 877912) 8 (ZLit 4096)) F3.
    mf V m HM (MCell (ZLit 877920) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
    aimg V m HM 0xd6588 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
    mf V m HM (MCell (ZLit 878528) 1 (ZLit 0)) F6.
    aimg V m HM 0xd68f0 [C1 (Z_to_bv 8 0)] I7.
    mf V m HM (MCell (ZLit 877888) 4 (ZLit 18446744073709551615)) F8.
    assert (F8' : rw_cells bsegs m 877888 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
    mf V m HM (MCell (ZLit 877904) 1 (ZLit 0)) F9.
    assert (ESB : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (unfold al_space_beg; cbn [al_V L LV Nat.eqb]; lia).
    split; [rewrite ESB; exact F1|].
    split; [rewrite ESB; unfold K_SPACE_SIZE; replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
                                                 with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia; exact F2|].
    split; [exact F3|]. split; [exact F4|]. split; [exact I5|]. split; [exact F6|]. split; [exact I7|]. split; [exact F8'| exact F9].
  Qed.

  (* [comment removed for export] *)
  Theorem aquar_glob_const_init : aquar_glob_const m.
  Proof.
    unfold aquar_glob_const, AQ_MAX, AQ_MUTEX.
    mf V m HM (MCell (ZLit 878640) 8 (ZLit 268435456)) F1.
    mf V m HM (MCell (ZLit 878648) 8 (ZLit 241591905)) F2.
    mf V m HM (MCell (ZLit 878656) 8 (ZLit 1048576)) F3.
    mf V m HM (MCell (ZLit 878728) 1 (ZLit 0)) F4.
    mf V m HM (MCell (ZLit 878729) 1 (ZLit 0)) F5.
    aimg V m HM 0xd688a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
    split.
    - apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
    - apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
  Qed.

  Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
  Proof.
    unfold aqcache, AQ_GCACHE. aimg V m HM 0xd6890 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
    split; [exact IG| exact Logic.I].
  Qed.

  (* [comment removed for export] *)
  Lemma aia_scan : zscanN TgtO_zlib_uncompress_fuzzer_both_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.   (* [comment removed for export] *)
  Proof. rewrite zscanN_fastE_p04. apply HexScanFast.zscanN_of_I; [vm_cast_no_check (eq_refl true) | vm_compute; reflexivity]. Qed.   (* [comment removed for export] *)

  Theorem aintal_init : aintal false m.
  Proof.
    unfold aintal, AIA_FLAG.
    aimg V m HM 0x169608 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
    split; [exact I1|]. split; [| intros; discriminate].
    mimg V m HM 0xdad80 (0xdad80 + 0x81030) IMG. mwr V m HM (ZLit 839680) 5963128 W.
    (* [comment removed for export] *)
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
(* [comment removed for export] *)
