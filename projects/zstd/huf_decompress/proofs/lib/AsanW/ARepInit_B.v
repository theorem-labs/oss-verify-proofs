(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the main entry's recorded facts read as the main entry keeps them: AMKN, APKN, imported from MainEntry; all 14 recorded proofs replaced by written proofs (arelro_init, flags85_init, arep_rt_init and 11 more); ported by content from zstd_frame_info's file of the same role, with this binary's addresses and names). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import AsanHexScan.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) AMKN.
  Hypothesis HP : Forall (pfact_ok V) APKN.
  Let L := mkALayout (LV V) w U.

  Lemma arelro_init : arelro m.
  Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0xaf000 0xb1000 IMG. apply IMG.
lia. Qed.

  (* [comment removed for export] *)
  Lemma flags85_init : rw_cells asegs m 0xb51cd [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 741832) 8 (ZLit 72340172838010881)) F.
    assert (F' : rw_cells asegs m 741832 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                          C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
    do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Lemma cflags34_init : rw_cells asegs m 0x1494ca [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 1348808) 8 (ZLit 128849084416)) F.
    assert (F' : rw_cells asegs m 1348808 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
                                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
    do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Theorem arep_rt_init : arep_rt L m.
  Proof.
    unfold arep_rt.
    aimg V m HM 0xaf708 [C8 (Z_to_bv 64 0x147420)] I1.
    aimg V m HM 0xaf718 [C8 (Z_to_bv 64 0x1494a8); C8 (Z_to_bv 64 0xb5178); C8 (Z_to_bv 64 0xb7978); C8 (Z_to_bv 64 0xb8668); C8 (Z_to_bv 64 0xb8670); C8 (Z_to_bv 64 0xb8660)] I2.
    aimg V m HM 0xaf748 [C8 (Z_to_bv 64 0xb15a8)] I3.
    aimg V m HM 0xb0290 [C8 (Z_to_bv 64 0xb8659)] I4.
    aimg V m HM 0xb0380 [C8 (Z_to_bv 64 0x10)] I5.   (* [comment removed for export] *)
    aimg V m HM 0xb15a0 [C8 (Z_to_bv 64 0xa8a58); C8 (Z_to_bv 64 0xa8e5c)] I6.
    aimg V m HM 0xb8668 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
    aimg V m HM 0x139be0 [C1 (Z_to_bv 8 0)] I8.
    aimg V m HM 0x139be2 [C1 (Z_to_bv 8 0)] I9.
    aimg V m HM 0x149440 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
    aimg V m HM 0x5ea920 [C4 (Z_to_bv 64 0)] I11.
    mf V m HM (MCell (ZLit 741688) 8 (ZLit 1099511627776)) F1.
    mf V m HM (MCell (ZLit 741696) 2 (ZLit 16)) F2.
    mf V m HM (MCell (ZLit 741698) 2 (ZLit 2048)) F3.
    mf V m HM (MCell (ZLit 741700) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 741752) 4 (ZLit 4294967295)) F5.
    mf V m HM (MCell (ZLit 741756) 4 (ZLit 256)) F6.
    mf V m HM (MCell (ZLit 741760) 4 (ZLit 1024)) F7.
    mf V m HM (MCell (ZLit 741764) 4 (ZLit 16)) F8.
    mf V m HM (MCell (ZLit 741768) 4 (ZLit 2048)) F9.
    mf V m HM (MCell (ZLit 741796) 4 (ZLit 4096)) F10.
    mf V m HM (MCell (ZLit 741800) 8 (ZLit 816043786240)) F11.
    assert (F11' : rw_cells asegs m 741800 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
    mf V m HM (MCell (ZLit 751992) 8 (ZLit 2147450880)) F12.
    mf V m HM (MCell (ZLit 750044) 1 (ZLit 1)) F13.
    mf V m HM (MCell (ZLit 750048) 1 (ZLit 1)) F14.
    mf V m HM (MCell (ZLit 750052) 4 (ZLit 0)) F15.
    mf V m HM (MCell (ZLit 755288) 1 (ZLit 1)) F16.
    mf V m HM (MCell (ZLit 755289) 1 (ZLit 1)) F17.
    mf V m HM (MCell (ZLit 755296) 8 (ZLit 140737488355327)) F18.
    mf V m HM (MCell (ZLit 755324) 4 (ZLit 30)) F19.
    mf V m HM (MCell (ZLit 1285089) 1 (ZLit 1)) F20.
    mf V m HM (MCell (ZLit 1340448) 8 (ZLit 4096)) F21.
    mf V m HM (MCell (ZLit 1348808) 8 (ZLit 128849084416)) F22.
    mf V m HM (MCell (ZLit 1348896) 8 (ZLit 18446744073709551615)) F23.   (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 6203576) 8 (ZLit 6339768)) F24.
    mf V m HM (MCell (ZLit 6339768) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
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
    mf V m HM (MCell (ZLit 1349032) 8 (ZLit 16843009)) F1.
    assert (F1' : rw_cells asegs m 1349032 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
    do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
    mf V m HM (MCell (ZLit 1348920) 8 (ZLit 0)) F2.
    aimg V m HM 0xb1550 [C8 (Z_to_bv 64 0xa92e4)] I1.
    split; [exact F1'|]. split; [exact F2| exact I1].
  Qed.

  Theorem arep_rt3_init : arep_rt3 m.
  Proof.
    unfold arep_rt3.
    aimg V m HM 0xb1498 [C8 (Z_to_bv 64 0xa83a8); C8 (Z_to_bv 64 0xa5298)] I1.
    aimg V m HM 0xb1478 [C8 (Z_to_bv 64 0xae15c)] I2.
    aimg V m HM 0xb1480 [C8 (Z_to_bv 64 0xa5010)] I3.
    aimg V m HM 0xb1550 [C8 (Z_to_bv 64 0xa92e4)] I4.
    aimg V m HM 0xb1468 [C8 (Z_to_bv 64 0xa895c)] I5.
    mf V m HM (MCell (ZLit 1348856) 8 (ZLit 4294967296)) F1.
    mf V m HM (MCell (ZLit 1349024) 8 (ZLit 72340172838076673)) F2.
    mf V m HM (MCell (ZLit 752000) 4 (ZLit 1)) F3.
    mf V m HM (MCell (ZLit 741848) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 1340440) 4 (ZLit 0)) F5.
    (* [comment removed for export] *)
    aimg V m HM 0xaf708 [C8 (Z_to_bv 64 0x147420); C8 (Z_to_bv 64 0xb15e0)] I6.
    aimg V m HM 0xb15e0 [C8 (Z_to_bv 64 0x19227)] I7.
    mf V m HM (MCell (ZLit 1340448) 8 (ZLit 4096)) F6.
    mf V m HM (MCell (ZLit 1348992) 8 (ZLit 1103823372544)) F7.
    mf V m HM (MCell (ZLit 1349016) 8 (ZLit 72339073309605888)) F8.
    (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 6335440) 8 (ZLit 4096)) F10.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].   (* [comment removed for export] *)
  Qed.

  Theorem ainstance_init : ainstance L (ST0 V) m.
  Proof.
    unfold ainstance, AINSTANCE.
    mf V m HM (MCell (ZLit 738104) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
    mf V m HM (MCell (ZLit 738120) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
    mf V m HM (MCell (ZLit 738136) 8 (ZLit 4096)) F3.
    mf V m HM (MCell (ZLit 738144) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
    aimg V m HM 0xb4388 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
    mf V m HM (MCell (ZLit 738752) 1 (ZLit 0)) F6.
    aimg V m HM 0xb46f0 [C1 (Z_to_bv 8 0)] I7.
    mf V m HM (MCell (ZLit 738112) 4 (ZLit 18446744073709551615)) F8.
    assert (F8' : rw_cells asegs m 738112 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
    mf V m HM (MCell (ZLit 738128) 1 (ZLit 0)) F9.
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
    mf V m HM (MCell (ZLit 738864) 8 (ZLit 268435456)) F1.
    mf V m HM (MCell (ZLit 738872) 8 (ZLit 241591905)) F2.
    mf V m HM (MCell (ZLit 738880) 8 (ZLit 1048576)) F3.
    mf V m HM (MCell (ZLit 738952) 1 (ZLit 0)) F4.
    mf V m HM (MCell (ZLit 738953) 1 (ZLit 0)) F5.
    aimg V m HM 0xb468a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
    split.
    - apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
    - apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
  Qed.

  Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
  Proof.
    unfold aqcache, AQ_GCACHE. aimg V m HM 0xb4690 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
    split; [exact IG| exact Logic.I].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma zscanN_S : forall s f base n, zscanN s (Datatypes.S f) base n =
    (if N.eqb n 0 then true else if N.eqb n 1 then byte_zero s base
     else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool).
  Proof. reflexivity. Qed.
  Lemma zscanN_complete : forall s f base n,
    (n <= 2 ^ N.of_nat f)%N -> (forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0)) -> zscanN s (Datatypes.S f) base n = true.
  Proof.
    intros s f. induction f as [|f IH]; intros base n Hn Hz; rewrite zscanN_S;
      (destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|]); destruct (N.eqb_spec n 1) as [E1|N1].
1, 3: (pose proof (Hz 0%N ltac:(lia)) as Z0; rewrite N.add_0_r in Z0; unfold byte_zero; rewrite Z0; reflexivity).
    - exfalso. change (2 ^ N.of_nat 0)%N with 1%N in Hn. lia.
    - cbv iota zeta. rewrite N.div2_div. rewrite Nat2N.inj_succ, N.pow_succ_r' in Hn.
      pose proof (N.div_mod n 2 ltac:(lia)) as DM. pose proof (N.mod_lt n 2 ltac:(lia)) as ML.
      set (h := (n / 2)%N) in *. set (r := (n mod 2)%N) in *. set (p := (2 ^ N.of_nat f)%N) in *. clearbody h r p.
      apply andb_true_intro. split; apply IH.
      + lia.
      + intros i Hi. apply Hz. lia.
      + lia.
      + intros i Hi. rewrite <- N.add_assoc. apply Hz. lia.
  Qed.
  Lemma aia_scan63 : zscanZ Asan_seg_bytes_003 (AIA_BASE - SEG3) AIA_SIZE = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
  Lemma aia_scan : zscanN Asan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.   (* [comment removed for export] *)
  Proof.
    apply (zscanN_complete _ 63).
    - apply N.leb_le. vm_compute. reflexivity.
    - intros i Hi. apply (zscanZ_sound _ _ _ aia_scan63). unfold AIA_BASE, SEG3, AIA_SIZE in *.
lia.
  Qed.

  Theorem aintal_init : aintal false m.
  Proof.
    unfold aintal, AIA_FLAG.
    aimg V m HM 0x147408 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
    split; [exact I1|]. split; [| intros; discriminate].
    mimg V m HM 0xb8b80 (0xb8b80 + 0x81030) IMG. mwr V m HM (ZLit 716800) 5618000 W.
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
