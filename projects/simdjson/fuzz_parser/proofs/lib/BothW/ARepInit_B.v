(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoffBoth.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AsanHexScan.   (* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Let L := mkALayout (LV V) w U.

  Lemma arelro_init : arelro m.
  Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0x10f000 0x114000 IMG. apply IMG. lia. Qed.

  (* [comment removed for export] *)
  Lemma flags85_init : rw_cells bsegs m 0x118ecd [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 1150664) 8 (ZLit 72340172838010881)) F.
    assert (F' : rw_cells bsegs m 1150664 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                          C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
    do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Lemma cflags34_init : rw_cells bsegs m 0x1ad1ca [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 1757640) 8 (ZLit 128849084416)) F.
    assert (F' : rw_cells bsegs m 1757640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
                                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
    do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  Theorem arep_rt_init : arep_rt L m.
  Proof.
    unfold arep_rt.
    aimg V m HM 0x112a60 [C8 (Z_to_bv 64 0x1ab120)] I1.
    aimg V m HM 0x112a70 [C8 (Z_to_bv 64 0x1ad1a8); C8 (Z_to_bv 64 0x118e78); C8 (Z_to_bv 64 0x11b678);
                          C8 (Z_to_bv 64 0x11c368); C8 (Z_to_bv 64 0x11c370); C8 (Z_to_bv 64 0x11c360)] I2.
    aimg V m HM 0x112aa0 [C8 (Z_to_bv 64 0x1149c8)] I3.
    aimg V m HM 0x1135e8 [C8 (Z_to_bv 64 0x11c359)] I4.
    aimg V m HM 0x1136d8 [C8 (Z_to_bv 64 0x10)] I5.   (* [comment removed for export] *)
    aimg V m HM 0x1149c0 [C8 (Z_to_bv 64 0x108898); C8 (Z_to_bv 64 0x108c9c)] I6.
    aimg V m HM 0x11c368 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
    aimg V m HM 0x19d8e0 [C1 (Z_to_bv 8 0)] I8.
    aimg V m HM 0x19d8e2 [C1 (Z_to_bv 8 0)] I9.
    aimg V m HM 0x1ad140 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
    aimg V m HM 0x64ea00 [C4 (Z_to_bv 64 0)] I11.   (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 1150520) 8 (ZLit 1099511627776)) F1.
    mf V m HM (MCell (ZLit 1150528) 2 (ZLit 16)) F2.
    mf V m HM (MCell (ZLit 1150530) 2 (ZLit 2048)) F3.
    mf V m HM (MCell (ZLit 1150532) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 1150584) 4 (ZLit 4294967295)) F5.
    mf V m HM (MCell (ZLit 1150588) 4 (ZLit 256)) F6.
    mf V m HM (MCell (ZLit 1150592) 4 (ZLit 1024)) F7.
    mf V m HM (MCell (ZLit 1150596) 4 (ZLit 16)) F8.
    mf V m HM (MCell (ZLit 1150600) 4 (ZLit 2048)) F9.
    mf V m HM (MCell (ZLit 1150628) 4 (ZLit 4096)) F10.
    mf V m HM (MCell (ZLit 1150632) 8 (ZLit 816043786240)) F11.
    assert (F11' : rw_cells bsegs m 1150632 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
    mf V m HM (MCell (ZLit 1160824) 8 (ZLit 2147450880)) F12.
    mf V m HM (MCell (ZLit 1158876) 1 (ZLit 1)) F13.
    mf V m HM (MCell (ZLit 1158880) 1 (ZLit 1)) F14.
    mf V m HM (MCell (ZLit 1158884) 4 (ZLit 0)) F15.
    mf V m HM (MCell (ZLit 1164120) 1 (ZLit 1)) F16.
    mf V m HM (MCell (ZLit 1164121) 1 (ZLit 1)) F17.
    mf V m HM (MCell (ZLit 1164128) 8 (ZLit 140737488355327)) F18.
    mf V m HM (MCell (ZLit 1164156) 4 (ZLit 30)) F19.
    mf V m HM (MCell (ZLit 1693921) 1 (ZLit 1)) F20.
    mf V m HM (MCell (ZLit 1749280) 8 (ZLit 4096)) F21.
    mf V m HM (MCell (ZLit 1757640) 8 (ZLit 128849084416)) F22.
    mf V m HM (MCell (ZLit 1757728) 8 (ZLit 18446744073709551615)) F23.   (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 6613400) 8 (ZLit 6749592)) F24.
    mf V m HM (MCell (ZLit 6749592) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
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
    split; [exact F24|]. split; [exact F25|]. split; [exact I11|]. split; [exact F26|]. split; [exact F27|].
    (* [comment removed for export] *) (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 1158848) 8 (ZLit 1158856)) X1.
    mf V m HM (MCell (ZLit 1158856) 8 (ZMul (ZLit 4096) (ZV 207))) X2.
    mf V m HM (MZero (ZMul (ZLit 4096) (ZV 207)) 3727360) XZ.
    mwr V m HM (ZMul (ZLit 4096) (ZV 207)) 3727360 XW.
    pose proof (proj1 XW) as XP.   (* [comment removed for export] *)
    assert (XE : al_xr L = 4096 * V 207%nat) by reflexivity.
    split; [apply rw_cells_cons; [exact X1| exact X2]|].
    split; (apply zcells; [reflexivity| |];
      [ cbn [cells_size csize Nat.add]; intros i Hi; rewrite XE, <- Z.add_assoc; apply XZ; lia
      | rewrite XE; eapply wr_at_sub; [exact XW| lia| lia| cbn; lia] ]).
  Qed.

  Theorem arep_rt2_init : arep_rt2 m.
  Proof.
    unfold arep_rt2.
    mf V m HM (MCell (ZLit 1757864) 8 (ZLit 16843009)) F1.
    assert (F1' : rw_cells bsegs m 1757864 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
    do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
    mf V m HM (MCell (ZLit 1757752) 8 (ZLit 0)) F2.
    aimg V m HM 0x114940 [C8 (Z_to_bv 64 0x1091c8)] I1.
    split; [exact F1'|]. split; [exact F2| exact I1].
  Qed.

  Theorem arep_rt3_init : arep_rt3 m.
  Proof.
    unfold arep_rt3.
    aimg V m HM 0x1148a0 [C8 (Z_to_bv 64 0x106534); C8 (Z_to_bv 64 0x100da8)] I1.
    aimg V m HM 0x114880 [C8 (Z_to_bv 64 0x10e084)] I2.
    aimg V m HM 0x114888 [C8 (Z_to_bv 64 0x100a4c)] I3.
    aimg V m HM 0x114970 [C8 (Z_to_bv 64 0x109124)] I4.
    aimg V m HM 0x114870 [C8 (Z_to_bv 64 0x10879c)] I5.
    mf V m HM (MCell (ZLit 1757688) 8 (ZLit 4294967296)) F1.
    mf V m HM (MCell (ZLit 1757856) 8 (ZLit 72340172838076673)) F2.
    mf V m HM (MCell (ZLit 1160832) 4 (ZLit 1)) F3.
    mf V m HM (MCell (ZLit 1150680) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 1749272) 4 (ZLit 0)) F5.
    (* [comment removed for export] *)
    aimg V m HM 0x112a60 [C8 (Z_to_bv 64 0x1ab120); C8 (Z_to_bv 64 0x114a00)] I6.
    aimg V m HM 0x114a00 [C8 (Z_to_bv 64 0x1a4c3)] I7.
    mf V m HM (MCell (ZLit 1749280) 8 (ZLit 4096)) F6.
    mf V m HM (MCell (ZLit 1757824) 8 (ZLit 1103823372544)) F7.
    mf V m HM (MCell (ZLit 1757848) 8 (ZLit 72339073309605888)) F8.
    (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 6745264) 8 (ZLit 4096)) F10.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].   (* [comment removed for export] *)
  Qed.

  Theorem ainstance_init : ainstance L (ST0 V) m.
  Proof.
    unfold ainstance, AINSTANCE.
    mf V m HM (MCell (ZLit 1146936) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
    mf V m HM (MCell (ZLit 1146952) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
    mf V m HM (MCell (ZLit 1146968) 8 (ZLit 4096)) F3.
    mf V m HM (MCell (ZLit 1146976) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
    aimg V m HM 0x118088 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
    mf V m HM (MCell (ZLit 1147584) 1 (ZLit 0)) F6.
    aimg V m HM 0x1183f0 [C1 (Z_to_bv 8 0)] I7.
    mf V m HM (MCell (ZLit 1146944) 4 (ZLit 18446744073709551615)) F8.
    assert (F8' : rw_cells bsegs m 1146944 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
    mf V m HM (MCell (ZLit 1146960) 1 (ZLit 0)) F9.
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
    mf V m HM (MCell (ZLit 1147696) 8 (ZLit 268435456)) F1.
    mf V m HM (MCell (ZLit 1147704) 8 (ZLit 241591905)) F2.
    mf V m HM (MCell (ZLit 1147712) 8 (ZLit 1048576)) F3.
    mf V m HM (MCell (ZLit 1147784) 1 (ZLit 0)) F4.
    mf V m HM (MCell (ZLit 1147785) 1 (ZLit 0)) F5.
    aimg V m HM 0x11838a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
    split.
    - apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
    - apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
  Qed.

  Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
  Proof.
    unfold aqcache, AQ_GCACHE. aimg V m HM 0x118390 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
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
  Lemma aia_scan63 : zscanZ AsanUbsan_seg_bytes_003 (AIA_BASE - SEG3) AIA_SIZE = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
  Lemma aia_scan : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.   (* [comment removed for export] *)
  Proof.
    apply (zscanN_complete _ 63).
    - apply N.leb_le. vm_compute. reflexivity.
    - intros i Hi. apply (zscanZ_sound _ _ _ aia_scan63). unfold AIA_BASE, SEG3, AIA_SIZE in *. lia.
  Qed.

  Theorem aintal_init : aintal false m.
  Proof.
    unfold aintal, AIA_FLAG.
    aimg V m HM 0x1ab108 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
    split; [exact I1|]. split; [| intros; discriminate].
    mimg V m HM 0x11c880 (0x11c880 + 0x81030) IMG. mwr V m HM (ZLit 1110016) 5634608 W.
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
