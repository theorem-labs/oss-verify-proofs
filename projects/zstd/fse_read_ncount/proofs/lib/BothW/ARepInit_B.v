(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoffBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AsanHexScan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section B.
Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
Let L := mkALayout (LV V) w U.
#[using="V HM"] Lemma arelro_init : arelro m.
Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0x99000 0x9b000 IMG. apply IMG. Local Ltac2 Set LiaHints.tbl := fun () => "0010>17541226634.11000004S2Hi".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Lemma flags85_init : rw_cells bsegs m 0x9fd8d [C1 (Z_to_bv 8 1)].
Proof.
mf V m HM (MCell (ZLit 654728) 8 (ZLit 72340172838010881)) F.
assert (F' : rw_cells bsegs m 654728 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
Qed.
#[using="V HM"] Lemma cflags34_init : rw_cells bsegs m 0x13408a [C1 (Z_to_bv 8 1)].
Proof.
mf V m HM (MCell (ZLit 1261704) 8 (ZLit 128849084416)) F.
assert (F' : rw_cells bsegs m 1261704 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
Qed.
#[using="HM"] Theorem arep_rt_init : arep_rt L m.
Proof.
unfold arep_rt.
Local Ltac2 Set LiaHints.tbl := fun () => "00F0>12770589751.1016493176585.8 18388828701.1620874996659.142564944561.12 27628333351.1532704268988.1533206320574.173507196714.12 35825648165.1738279670312.1440087773842.8 43030252982.9 47026528946.1350768103494.1650858914869.1851239168683.1152875340333.9 57137234348.1059606201262.185977720617.13 65732481328.1100000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00FSSSSSSSSSSSSSSSSSSSSSS".
aimg V m HM 0x998f0 [C8 (Z_to_bv 64 0x131fe0)] I1.
aimg V m HM 0x99900 [C8 (Z_to_bv 64 0x134068); C8 (Z_to_bv 64 0x9fd38); C8 (Z_to_bv 64 0xa2538);
C8 (Z_to_bv 64 0xa3228); C8 (Z_to_bv 64 0xa3230); C8 (Z_to_bv 64 0xa3220)] I2.
aimg V m HM 0x99930 [C8 (Z_to_bv 64 0x9b778)] I3.
aimg V m HM 0x9a478 [C8 (Z_to_bv 64 0xa3219)] I4.
aimg V m HM 0x9a568 [C8 (Z_to_bv 64 0x10)] I5.
aimg V m HM 0x9b770 [C8 (Z_to_bv 64 0x92c40); C8 (Z_to_bv 64 0x93044)] I6.
aimg V m HM 0xa3228 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
aimg V m HM 0x1247a0 [C1 (Z_to_bv 8 0)] I8.
aimg V m HM 0x1247a2 [C1 (Z_to_bv 8 0)] I9.
aimg V m HM 0x134000 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
aimg V m HM 0x5d54e0 [C4 (Z_to_bv 64 0)] I11.
mf V m HM (MCell (ZLit 654584) 8 (ZLit 1099511627776)) F1.
mf V m HM (MCell (ZLit 654592) 2 (ZLit 16)) F2.
mf V m HM (MCell (ZLit 654594) 2 (ZLit 2048)) F3.
mf V m HM (MCell (ZLit 654596) 1 (ZLit 1)) F4.
mf V m HM (MCell (ZLit 654648) 4 (ZLit 4294967295)) F5.
mf V m HM (MCell (ZLit 654652) 4 (ZLit 256)) F6.
mf V m HM (MCell (ZLit 654656) 4 (ZLit 1024)) F7.
mf V m HM (MCell (ZLit 654660) 4 (ZLit 16)) F8.
mf V m HM (MCell (ZLit 654664) 4 (ZLit 2048)) F9.
mf V m HM (MCell (ZLit 654692) 4 (ZLit 4096)) F10.
mf V m HM (MCell (ZLit 654696) 8 (ZLit 816043786240)) F11.
assert (F11' : rw_cells bsegs m 654696 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
mf V m HM (MCell (ZLit 664888) 8 (ZLit 2147450880)) F12.
mf V m HM (MCell (ZLit 662940) 1 (ZLit 1)) F13.
mf V m HM (MCell (ZLit 662944) 1 (ZLit 1)) F14.
mf V m HM (MCell (ZLit 662948) 4 (ZLit 0)) F15.
mf V m HM (MCell (ZLit 668184) 1 (ZLit 1)) F16.
mf V m HM (MCell (ZLit 668185) 1 (ZLit 1)) F17.
mf V m HM (MCell (ZLit 668192) 8 (ZLit 140737488355327)) F18.
mf V m HM (MCell (ZLit 668220) 4 (ZLit 30)) F19.
mf V m HM (MCell (ZLit 1197985) 1 (ZLit 1)) F20.
mf V m HM (MCell (ZLit 1253344) 8 (ZLit 4096)) F21.
mf V m HM (MCell (ZLit 1261704) 8 (ZLit 128849084416)) F22.
mf V m HM (MCell (ZLit 1261792) 8 (ZLit 18446744073709551615)) F23.
mf V m HM (MCell (ZLit 6116472) 8 (ZLit 6252664)) F24.
mf V m HM (MCell (ZLit 6252664) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
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
mf V m HM (MCell (ZLit 1261928) 8 (ZLit 16843009)) F1.
assert (F1' : rw_cells bsegs m 1261928 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
mf V m HM (MCell (ZLit 1261816) 8 (ZLit 0)) F2.
aimg V m HM 0x9b720 [C8 (Z_to_bv 64 0x934cc)] I1.
split; [exact F1'|]. split; [exact F2| exact I1].
Qed.
#[using="V HM"] Theorem arep_rt3_init : arep_rt3 m.
Proof.
unfold arep_rt3.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>10235435819.1110669353136.1114776008329.8 16499563186.1823358016424.1930431308598.9 33693693482.123674308370.8  40081317673.1843307927091.1945029301681.1246644802221.9 48785213356.1050460637751.1000000100200300400500600700800900:00;00<00=00>SSSSSSSSSSSSSS".
aimg V m HM 0x9b668 [C8 (Z_to_bv 64 0x92590); C8 (Z_to_bv 64 0x8f480)] I1.
aimg V m HM 0x9b648 [C8 (Z_to_bv 64 0x98344)] I2.
aimg V m HM 0x9b650 [C8 (Z_to_bv 64 0x8f1f8)] I3.
aimg V m HM 0x9b720 [C8 (Z_to_bv 64 0x934cc)] I4.
aimg V m HM 0x9b638 [C8 (Z_to_bv 64 0x92b44)] I5.
mf V m HM (MCell (ZLit 1261752) 8 (ZLit 4294967296)) F1.
mf V m HM (MCell (ZLit 1261920) 8 (ZLit 72340172838076673)) F2.
mf V m HM (MCell (ZLit 664896) 4 (ZLit 1)) F3.
mf V m HM (MCell (ZLit 654744) 1 (ZLit 1)) F4.
mf V m HM (MCell (ZLit 1253336) 4 (ZLit 0)) F5.
aimg V m HM 0x998f0 [C8 (Z_to_bv 64 0x131fe0); C8 (Z_to_bv 64 0x9b7b0)] I6.
aimg V m HM 0x9b7b0 [C8 (Z_to_bv 64 0x192be)] I7.
mf V m HM (MCell (ZLit 1253344) 8 (ZLit 4096)) F6.
mf V m HM (MCell (ZLit 1261888) 8 (ZLit 1103823372544)) F7.
mf V m HM (MCell (ZLit 1261912) 8 (ZLit 72339073309605888)) F8.
mf V m HM (MCell (ZLit 6248336) 8 (ZLit 4096)) F10.
split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HM"] Theorem ainstance_init : ainstance L (ST0 V) m.
Proof.
unfold ainstance, AINSTANCE.
mf V m HM (MCell (ZLit 651000) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
mf V m HM (MCell (ZLit 651016) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
mf V m HM (MCell (ZLit 651032) 8 (ZLit 4096)) F3.
mf V m HM (MCell (ZLit 651040) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>29762387242.1232015047853.1844676257413.1947026283059.1458560902321.125977868200.14 000001002003004005006SSSSSS".
aimg V m HM 0x9ef48 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
mf V m HM (MCell (ZLit 651648) 1 (ZLit 0)) F6.
aimg V m HM 0x9f2b0 [C1 (Z_to_bv 8 0)] I7.
mf V m HM (MCell (ZLit 651008) 4 (ZLit 18446744073709551615)) F8.
assert (F8' : rw_cells bsegs m 651008 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
mf V m HM (MCell (ZLit 651024) 1 (ZLit 0)) F9.
assert (ESB : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (unfold al_space_beg; cbn [al_V L LV Nat.eqb]; lia).
split; [rewrite ESB; exact F1|].
split; [rewrite ESB; unfold K_SPACE_SIZE; replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia; exact F2|].
split; [exact F3|]. split; [exact F4|]. split; [exact I5|]. split; [exact F6|]. split; [exact I7|]. split; [exact F8'| exact F9].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Theorem aquar_glob_const_init : aquar_glob_const m.
Proof.
unfold aquar_glob_const, AQ_MAX, AQ_MUTEX.
mf V m HM (MCell (ZLit 651760) 8 (ZLit 268435456)) F1.
mf V m HM (MCell (ZLit 651768) 8 (ZLit 241591905)) F2.
mf V m HM (MCell (ZLit 651776) 8 (ZLit 1048576)) F3.
mf V m HM (MCell (ZLit 651848) 1 (ZLit 0)) F4.
mf V m HM (MCell (ZLit 651849) 1 (ZLit 0)) F5.
aimg V m HM 0x9f24a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
split.
- apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
- apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
Qed.
#[using="HM"] Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
Proof.
unfold aqcache, AQ_GCACHE. aimg V m HM 0x9f250 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
split; [exact IG| exact Logic.I].
Qed.
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
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
#[using="Type"] Lemma aia_scan : zscanN AsanUbsan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.
Proof.
apply (zscanN_complete _ 63).
- apply N.leb_le. vm_compute. reflexivity.
- intros i Hi. apply (zscanZ_sound _ _ _ aia_scan63). unfold AIA_BASE, SEG3, AIA_SIZE in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>25527853992.10000004S2Hi".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Theorem aintal_init : aintal false m.
Proof.
unfold aintal, AIA_FLAG.
Local Ltac2 Set LiaHints.tbl := fun () => "0080>15825559689.8 17416972471.1322219873250.1323196675079.1136368206061.1353375354131.1363706880274.8 7104325793.15 00000100600;00<00A00F00G00OSS3EQNS3EQNSS3EQNS3EQNSS3EQN2Hi".
aimg V m HM 0x131fc8 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
split; [exact I1|]. split; [| intros; discriminate].
mimg V m HM 0xa3740 (0xa3740 + 0x81030) IMG. mwr V m HM (ZLit 626688) 5621008 W.
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
