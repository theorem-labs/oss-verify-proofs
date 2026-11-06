(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoffBoth.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import AsanHexScan.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section B.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
  Let L := mkALayout (LV V) w U.

  #[using="V HM"] Lemma arelro_init : arelro m.
  Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0x98000 0x9a000 IMG. apply IMG. Local Ltac2 Set LiaHints.tbl := fun () => "0010>17541226634.11000004S2Hi".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="V HM"] Lemma flags85_init : rw_cells bsegs m 0x9e88d [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 649352) 8 (ZLit 72340172838010881)) F.
    assert (F' : rw_cells bsegs m 649352 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                          C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
    do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  #[using="V HM"] Lemma cflags34_init : rw_cells bsegs m 0x132b8a [C1 (Z_to_bv 8 1)].
  Proof.
    mf V m HM (MCell (ZLit 1256328) 8 (ZLit 128849084416)) F.
    assert (F' : rw_cells bsegs m 1256328 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
                                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
    do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
  Qed.

  #[using="HM"] Theorem arep_rt_init : arep_rt L m.
  Proof.
    unfold arep_rt.
    Local Ltac2 Set LiaHints.tbl := fun () => "00F0>1377061413.17 16003788870.1623199128234.1225161481134.1826978046899.1430431308598.9 31094863665.1233691634194.8 35992941867.113847795240.14 38640002610.1339303292350.1741310991031.1044381153821.1645023093129.8 45410798256.1146644802221.9 50915084588.1056966356021.1858686173884.1559436548521.1361566423335.1500000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00FSSSSSSSSSSSSSSSSSSSSSS".
aimg V m HM 0x98ff0 [C8 (Z_to_bv 64 0x130ae0)] I1.
    aimg V m HM 0x99000 [C8 (Z_to_bv 64 0x132b68); C8 (Z_to_bv 64 0x9e838); C8 (Z_to_bv 64 0xa1038);
                          C8 (Z_to_bv 64 0xa1d28); C8 (Z_to_bv 64 0xa1d30); C8 (Z_to_bv 64 0xa1d20)] I2.
    aimg V m HM 0x99030 [C8 (Z_to_bv 64 0x9ae98)] I3.
    aimg V m HM 0x99b78 [C8 (Z_to_bv 64 0xa1d19)] I4.
    aimg V m HM 0x99c68 [C8 (Z_to_bv 64 0x10)] I5.   (* [comment removed for export] *)
    aimg V m HM 0x9ae90 [C8 (Z_to_bv 64 0x92340); C8 (Z_to_bv 64 0x92744)] I6.
    aimg V m HM 0xa1d28 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
    aimg V m HM 0x1232a0 [C1 (Z_to_bv 8 0)] I8.
    aimg V m HM 0x1232a2 [C1 (Z_to_bv 8 0)] I9.
    aimg V m HM 0x132b00 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
    aimg V m HM 0x5d3fe0 [C4 (Z_to_bv 64 0)] I11.
    mf V m HM (MCell (ZLit 649208) 8 (ZLit 1099511627776)) F1.
    mf V m HM (MCell (ZLit 649216) 2 (ZLit 16)) F2.
    mf V m HM (MCell (ZLit 649218) 2 (ZLit 2048)) F3.
    mf V m HM (MCell (ZLit 649220) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 649272) 4 (ZLit 4294967295)) F5.
    mf V m HM (MCell (ZLit 649276) 4 (ZLit 256)) F6.
    mf V m HM (MCell (ZLit 649280) 4 (ZLit 1024)) F7.
    mf V m HM (MCell (ZLit 649284) 4 (ZLit 16)) F8.
    mf V m HM (MCell (ZLit 649288) 4 (ZLit 2048)) F9.
    mf V m HM (MCell (ZLit 649316) 4 (ZLit 4096)) F10.
    mf V m HM (MCell (ZLit 649320) 8 (ZLit 816043786240)) F11.
    assert (F11' : rw_cells bsegs m 649320 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
    mf V m HM (MCell (ZLit 659512) 8 (ZLit 2147450880)) F12.
    mf V m HM (MCell (ZLit 657564) 1 (ZLit 1)) F13.
    mf V m HM (MCell (ZLit 657568) 1 (ZLit 1)) F14.
    mf V m HM (MCell (ZLit 657572) 4 (ZLit 0)) F15.
    mf V m HM (MCell (ZLit 662808) 1 (ZLit 1)) F16.
    mf V m HM (MCell (ZLit 662809) 1 (ZLit 1)) F17.
    mf V m HM (MCell (ZLit 662816) 8 (ZLit 140737488355327)) F18.
    mf V m HM (MCell (ZLit 662844) 4 (ZLit 30)) F19.
    mf V m HM (MCell (ZLit 1192609) 1 (ZLit 1)) F20.
    mf V m HM (MCell (ZLit 1247968) 8 (ZLit 4096)) F21.
    mf V m HM (MCell (ZLit 1256328) 8 (ZLit 128849084416)) F22.
    mf V m HM (MCell (ZLit 1256416) 8 (ZLit 18446744073709551615)) F23.   (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 6111096) 8 (ZLit 6247288)) F24.
    mf V m HM (MCell (ZLit 6247288) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
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
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="V HM"] Theorem arep_rt2_init : arep_rt2 m.
  Proof.
    unfold arep_rt2.
    mf V m HM (MCell (ZLit 1256552) 8 (ZLit 16843009)) F1.
    assert (F1' : rw_cells bsegs m 1256552 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                           C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
    do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
    mf V m HM (MCell (ZLit 1256440) 8 (ZLit 0)) F2.
    aimg V m HM 0x9ae40 [C8 (Z_to_bv 64 0x92bcc)] I1.
    split; [exact F1'|]. split; [exact F2| exact I1].
  Qed.

  #[using="V HM"] Theorem arep_rt3_init : arep_rt3 m.
  Proof.
    unfold arep_rt3.
    Local Ltac2 Set LiaHints.tbl := fun () => "00>0>14834049170.8 15823510576.1116774697009.1223358015789.9 33693841321.1843307926710.9 44851299242.1245029481522.1848461589171.1961803785.8    63337322167.1063708898731.1168466658604.107781709096.19 00000100200300400500600700800900:00;00<00=00>SSSSSSSSSSSSSS".
aimg V m HM 0x9ad88 [C8 (Z_to_bv 64 0x91c90); C8 (Z_to_bv 64 0x8eb80)] I1.
    aimg V m HM 0x9ad68 [C8 (Z_to_bv 64 0x97a44)] I2.
    aimg V m HM 0x9ad70 [C8 (Z_to_bv 64 0x8e8f8)] I3.
    aimg V m HM 0x9ae40 [C8 (Z_to_bv 64 0x92bcc)] I4.
    aimg V m HM 0x9ad58 [C8 (Z_to_bv 64 0x92244)] I5.
    mf V m HM (MCell (ZLit 1256376) 8 (ZLit 4294967296)) F1.
    mf V m HM (MCell (ZLit 1256544) 8 (ZLit 72340172838076673)) F2.
    mf V m HM (MCell (ZLit 659520) 4 (ZLit 1)) F3.
    mf V m HM (MCell (ZLit 649368) 1 (ZLit 1)) F4.
    mf V m HM (MCell (ZLit 1247960) 4 (ZLit 0)) F5.
    (* [comment removed for export] *)
    aimg V m HM 0x98ff0 [C8 (Z_to_bv 64 0x130ae0); C8 (Z_to_bv 64 0x9aed0)] I6.
    aimg V m HM 0x9aed0 [C8 (Z_to_bv 64 0x191d0)] I7.
    mf V m HM (MCell (ZLit 1247968) 8 (ZLit 4096)) F6.
    mf V m HM (MCell (ZLit 1256512) 8 (ZLit 1103823372544)) F7.
    mf V m HM (MCell (ZLit 1256536) 8 (ZLit 72339073309605888)) F8.
    (* [comment removed for export] *)
    mf V m HM (MCell (ZLit 6242960) 8 (ZLit 4096)) F10.
    split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].   (* [comment removed for export] *)
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="HM"] Theorem ainstance_init : ainstance L (ST0 V) m.
  Proof.
    unfold ainstance, AINSTANCE.
    mf V m HM (MCell (ZLit 645624) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
    mf V m HM (MCell (ZLit 645640) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
    mf V m HM (MCell (ZLit 645656) 8 (ZLit 4096)) F3.
    mf V m HM (MCell (ZLit 645664) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
    Local Ltac2 Set LiaHints.tbl := fun () => "0060>15823297713.1232015047853.1840579035048.1444676257413.1953129759283.1463709078826.12000001002003004005006SSSSSS".
aimg V m HM 0x9da48 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
    mf V m HM (MCell (ZLit 646272) 1 (ZLit 0)) F6.
    aimg V m HM 0x9ddb0 [C1 (Z_to_bv 8 0)] I7.
    mf V m HM (MCell (ZLit 645632) 4 (ZLit 18446744073709551615)) F8.
    assert (F8' : rw_cells bsegs m 645632 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
    mf V m HM (MCell (ZLit 645648) 1 (ZLit 0)) F9.
    assert (ESB : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (unfold al_space_beg; cbn [al_V L LV Nat.eqb]; lia).
    split; [rewrite ESB; exact F1|].
    split; [rewrite ESB; unfold K_SPACE_SIZE; replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
                                                 with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia; exact F2|].
    split; [exact F3|]. split; [exact F4|]. split; [exact I5|]. split; [exact F6|]. split; [exact I7|]. split; [exact F8'| exact F9].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="V HM"] Theorem aquar_glob_const_init : aquar_glob_const m.
  Proof.
    unfold aquar_glob_const, AQ_MAX, AQ_MUTEX.
    mf V m HM (MCell (ZLit 646384) 8 (ZLit 268435456)) F1.
    mf V m HM (MCell (ZLit 646392) 8 (ZLit 241591905)) F2.
    mf V m HM (MCell (ZLit 646400) 8 (ZLit 1048576)) F3.
    mf V m HM (MCell (ZLit 646472) 1 (ZLit 0)) F4.
    mf V m HM (MCell (ZLit 646473) 1 (ZLit 0)) F5.
    aimg V m HM 0x9dd4a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
    split.
    - apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
    - apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
  Qed.

  #[using="HM"] Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
  Proof.
    unfold aqcache, AQ_GCACHE. aimg V m HM 0x9dd50 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
    split; [exact IG| exact Logic.I].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Type"] Lemma zscanN_S : forall s f base n, zscanN s (Datatypes.S f) base n =
    (if N.eqb n 0 then true else if N.eqb n 1 then byte_zero s base
     else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool).
  Proof. reflexivity. Qed.
  #[using="Type"] Lemma zscanN_complete : forall s f base n,
    (n <= 2 ^ N.of_nat f)%N -> (forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0)) -> zscanN s (Datatypes.S f) base n = true.
  Proof.
    intros s f. induction f as [|f IH]; intros base n Hn Hz; rewrite zscanN_S;
      (destruct (N.eqb_spec n 0) as [E0|N0]; [reflexivity|]); destruct (N.eqb_spec n 1) as [E1|N1].
    Local Ltac2 Set LiaHints.tbl := fun () => "0090>1555117470.22 2425002723.15 2425002723.17 53768766698.2457001272293.2259308546384.1563864666001.1863864818093.1765102975469.2400000:00A00H00U00_00i01001401AS2Hn2DM2MLS2Hn2E1S2Hn2E1S2Hn2DM2ML2HiS2Hn2DM2MLS2Hn2N02N1S2Hn2DMS2HnS2Hn2DM2ML2Hi".
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
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
  #[using="Type"] Lemma aia_scan63 : zscanZ AsanUbsan_seg_bytes_003 (AIA_BASE - SEG3) AIA_SIZE = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
  #[using="Type"] Lemma aia_scan : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.   (* [comment removed for export] *)
  Proof.
    apply (zscanN_complete _ 63).
    - apply N.leb_le. vm_compute. reflexivity.
    - intros i Hi. apply (zscanZ_sound _ _ _ aia_scan63). unfold AIA_BASE, SEG3, AIA_SIZE in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59804363688.10000004S2Hi".
lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="V HM"] Theorem aintal_init : aintal false m.
  Proof.
    unfold aintal, AIA_FLAG.
    Local Ltac2 Set LiaHints.tbl := fun () => "0080>18598518035.1321934995593.8 23196675079.1127089761250.1329262450962.8 34186381473.1552185698487.1366832021741.1300000500600700<00=00E00J00OS3EQNSSS3EQNSS3EQN2HiS3EQNS3EQN".
aimg V m HM 0x130ac8 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
    split; [exact I1|]. split; [| intros; discriminate].
    mimg V m HM 0xa2240 (0xa2240 + 0x81030) IMG. mwr V m HM (ZLit 622592) 5619728 W.
    (* [comment removed for export] *)
    assert (EQN : Z.of_N (Z.to_N AIA_SIZE) = AIA_SIZE) by (apply Z2N.id; unfold AIA_SIZE; lia).
    pose proof (img_zero_stk (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) m AIA_BASE aia_scan) as K. rewrite EQN in K.
    apply K.
    - unfold AIA_BASE, SEG3. reflexivity.
    - unfold AIA_BASE, AIA_SIZE. lia.
    - intros i Hi. apply IMG. unfold AIA_BASE, AIA_SIZE in Hi. lia.
    - eapply wr_at_sub; [exact W| unfold AIA_BASE; lia| unfold AIA_BASE; lia| unfold AIA_BASE, AIA_SIZE; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End B.
End CANSEC1.
(* [comment removed for export] *)
