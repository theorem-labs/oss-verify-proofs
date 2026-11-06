(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsAsan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AsanHexScan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase ABytes ACanary ALayout ARep AHeapP AQConst ARepQ ARepInit_kit ARepInit_A.
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
Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Let L := mkALayout (LV V) w U.
#[using="V HM"] Lemma arelro_init : arelro m.
Proof. intros i Hi. unfold ARELRO_LO, ARELRO_HI in Hi. mimg V m HM 0x99000 0x9b000 IMG. apply IMG. Local Ltac2 Set LiaHints.tbl := fun () => "0010>17541226634.11000004S2Hi".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Lemma flags85_init : rw_cells asegs m 0x9fccd [C1 (Z_to_bv 8 1)].
Proof.
mf V m HM (MCell (ZLit 654536) 8 (ZLit 72340172838010881)) F.
assert (F' : rw_cells asegs m 654536 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]) by recast F.
do 5 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
Qed.
#[using="V HM"] Lemma cflags34_init : rw_cells asegs m 0x133fca [C1 (Z_to_bv 8 1)].
Proof.
mf V m HM (MCell (ZLit 1261512) 8 (ZLit 128849084416)) F.
assert (F' : rw_cells asegs m 1261512 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 30);
C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F.
do 2 apply rw_cells_tl in F'. apply rw_cells_hd in F'. exact F'.
Qed.
#[using="HM"] Theorem arep_rt_init : arep_rt L m.
Proof.
unfold arep_rt.
Local Ltac2 Set LiaHints.tbl := fun () => "00F0>12365588907.111546486162.8  1548548645.17 16171065414.1618928829100.102166653628.15 24325931056.1125331116974.1833206320050.1335825648681.1339199269811.144004586024.14 447392821.18  48785213229.9 50460637878.9 51134662065.1251516437950.1751522768393.8 56581192221.1661338273079.1061733699879.1568294925866.1200000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00FSSSSSSSSSSSSSSSSSSSSSS".
aimg V m HM 0x99760 [C8 (Z_to_bv 64 0x131f20)] I1.
aimg V m HM 0x99770 [C8 (Z_to_bv 64 0x133fa8); C8 (Z_to_bv 64 0x9fc78); C8 (Z_to_bv 64 0xa2478);
C8 (Z_to_bv 64 0xa3168); C8 (Z_to_bv 64 0xa3170); C8 (Z_to_bv 64 0xa3160)] I2.
aimg V m HM 0x997a0 [C8 (Z_to_bv 64 0x9b5e8)] I3.
aimg V m HM 0x9a2e8 [C8 (Z_to_bv 64 0xa3159)] I4.
aimg V m HM 0x9a3d8 [C8 (Z_to_bv 64 0x10)] I5.
aimg V m HM 0x9b5e0 [C8 (Z_to_bv 64 0x92ab0); C8 (Z_to_bv 64 0x92eb4)] I6.
aimg V m HM 0xa3168 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I7.
aimg V m HM 0x1246e0 [C1 (Z_to_bv 8 0)] I8.
aimg V m HM 0x1246e2 [C1 (Z_to_bv 8 0)] I9.
aimg V m HM 0x133f40 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I10.
aimg V m HM 0x5d5420 [C4 (Z_to_bv 64 0)] I11.
mf V m HM (MCell (ZLit 654392) 8 (ZLit 1099511627776)) F1.
mf V m HM (MCell (ZLit 654400) 2 (ZLit 16)) F2.
mf V m HM (MCell (ZLit 654402) 2 (ZLit 2048)) F3.
mf V m HM (MCell (ZLit 654404) 1 (ZLit 1)) F4.
mf V m HM (MCell (ZLit 654456) 4 (ZLit 4294967295)) F5.
mf V m HM (MCell (ZLit 654460) 4 (ZLit 256)) F6.
mf V m HM (MCell (ZLit 654464) 4 (ZLit 1024)) F7.
mf V m HM (MCell (ZLit 654468) 4 (ZLit 16)) F8.
mf V m HM (MCell (ZLit 654472) 4 (ZLit 2048)) F9.
mf V m HM (MCell (ZLit 654500) 4 (ZLit 4096)) F10.
mf V m HM (MCell (ZLit 654504) 8 (ZLit 816043786240)) F11.
assert (F11' : rw_cells asegs m 654504 [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]) by recast F11.
mf V m HM (MCell (ZLit 664696) 8 (ZLit 2147450880)) F12.
mf V m HM (MCell (ZLit 662748) 1 (ZLit 1)) F13.
mf V m HM (MCell (ZLit 662752) 1 (ZLit 1)) F14.
mf V m HM (MCell (ZLit 662756) 4 (ZLit 0)) F15.
mf V m HM (MCell (ZLit 667992) 1 (ZLit 1)) F16.
mf V m HM (MCell (ZLit 667993) 1 (ZLit 1)) F17.
mf V m HM (MCell (ZLit 668000) 8 (ZLit 140737488355327)) F18.
mf V m HM (MCell (ZLit 668028) 4 (ZLit 30)) F19.
mf V m HM (MCell (ZLit 1197793) 1 (ZLit 1)) F20.
mf V m HM (MCell (ZLit 1253152) 8 (ZLit 4096)) F21.
mf V m HM (MCell (ZLit 1261512) 8 (ZLit 128849084416)) F22.
mf V m HM (MCell (ZLit 1261600) 8 (ZLit 18446744073709551615)) F23.
mf V m HM (MCell (ZLit 6116280) 8 (ZLit 6252472)) F24.
mf V m HM (MCell (ZLit 6252472) 8 (ZMul (ZLit 4096) (ZV 228))) F25.
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
mf V m HM (MCell (ZLit 1261736) 8 (ZLit 16843009)) F1.
assert (F1' : rw_cells asegs m 1261736 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) by recast F1.
do 4 apply rw_cells_tl in F1'. apply rw_cells_hd in F1'.
mf V m HM (MCell (ZLit 1261624) 8 (ZLit 0)) F2.
aimg V m HM 0x9b590 [C8 (Z_to_bv 64 0x9333c)] I1.
split; [exact F1'|]. split; [exact F2| exact I1].
Qed.
#[using="V HM"] Theorem arep_rt3_init : arep_rt3 m.
Proof.
unfold arep_rt3.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>10271076406.9 1548696617.18 16774697783.1042708860845.9 43030253363.1944851298476.1051516388274.1852457835697.1252875339944.1959226502064.116134527531.11 63339473289.8 64202667306.1268460425746.8 00000100200300400500600700800900:00;00<00=00>SSSSSSSSSSSSSS".
aimg V m HM 0x9b4d8 [C8 (Z_to_bv 64 0x92400); C8 (Z_to_bv 64 0x8f2f0)] I1.
aimg V m HM 0x9b4b8 [C8 (Z_to_bv 64 0x981b4)] I2.
aimg V m HM 0x9b4c0 [C8 (Z_to_bv 64 0x8f068)] I3.
aimg V m HM 0x9b590 [C8 (Z_to_bv 64 0x9333c)] I4.
aimg V m HM 0x9b4a8 [C8 (Z_to_bv 64 0x929b4)] I5.
mf V m HM (MCell (ZLit 1261560) 8 (ZLit 4294967296)) F1.
mf V m HM (MCell (ZLit 1261728) 8 (ZLit 72340172838076673)) F2.
mf V m HM (MCell (ZLit 664704) 4 (ZLit 1)) F3.
mf V m HM (MCell (ZLit 654552) 1 (ZLit 1)) F4.
mf V m HM (MCell (ZLit 1253144) 4 (ZLit 0)) F5.
aimg V m HM 0x99760 [C8 (Z_to_bv 64 0x131f20); C8 (Z_to_bv 64 0x9b620)] I6.
aimg V m HM 0x9b620 [C8 (Z_to_bv 64 0x192be)] I7.
mf V m HM (MCell (ZLit 1253152) 8 (ZLit 4096)) F6.
mf V m HM (MCell (ZLit 1261696) 8 (ZLit 1103823372544)) F7.
mf V m HM (MCell (ZLit 1261720) 8 (ZLit 72339073309605888)) F8.
mf V m HM (MCell (ZLit 6248144) 8 (ZLit 4096)) F10.
split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact I4|]. split; [exact I5|].
split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
split; [exact I6|]. split; [exact I7|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split; [apply premap_canary_any| exact F10].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HM"] Theorem ainstance_init : ainstance L (ST0 V) m.
Proof.
unfold ainstance, AINSTANCE.
mf V m HM (MCell (ZLit 650808) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))) F1.
mf V m HM (MCell (ZLit 650824) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))) F2.
mf V m HM (MCell (ZLit 650840) 8 (ZLit 4096)) F3.
mf V m HM (MCell (ZLit 650848) 8 (ZMul (ZLit 4096) (ZV 226))) F4.
Local Ltac2 Set LiaHints.tbl := fun () => "0060>16499563059.1428036263089.1232015047853.1840081317800.1444676257413.1963865754922.12000001002003004005006SSSSSS".
aimg V m HM 0x9ee88 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] I5.
mf V m HM (MCell (ZLit 651456) 1 (ZLit 0)) F6.
aimg V m HM 0x9f1f0 [C1 (Z_to_bv 8 0)] I7.
mf V m HM (MCell (ZLit 650816) 4 (ZLit 18446744073709551615)) F8.
assert (F8' : rw_cells asegs m 650816 [C4 (Z_to_bv 64 4294967295)]) by recast F8.
mf V m HM (MCell (ZLit 650832) 1 (ZLit 0)) F9.
assert (ESB : al_space_beg L = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (unfold al_space_beg; cbn [al_V L LV Nat.eqb]; lia).
split; [rewrite ESB; exact F1|].
split; [rewrite ESB; unfold K_SPACE_SIZE; replace (4096 * V 208%nat + -4096 * V 209%nat + 65536 + 2 ^ 37)
with (4096 * V 208%nat + -4096 * V 209%nat + 137439019008) by lia; exact F2|].
split; [exact F3|]. split; [exact F4|]. split; [exact I5|]. split; [exact F6|]. split; [exact I7|]. split; [exact F8'| exact F9].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Theorem aquar_glob_const_init : aquar_glob_const m.
Proof.
unfold aquar_glob_const, AQ_MAX, AQ_MUTEX.
mf V m HM (MCell (ZLit 651568) 8 (ZLit 268435456)) F1.
mf V m HM (MCell (ZLit 651576) 8 (ZLit 241591905)) F2.
mf V m HM (MCell (ZLit 651584) 8 (ZLit 1048576)) F3.
mf V m HM (MCell (ZLit 651656) 1 (ZLit 0)) F4.
mf V m HM (MCell (ZLit 651657) 1 (ZLit 0)) F5.
aimg V m HM 0x9f18a [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I6.
split.
- apply rw_cells_cons; [exact F1|]. apply rw_cells_cons; [exact F2| exact F3].
- apply rw_cells_cons; [exact F4|]. apply rw_cells_cons; [exact F5| exact I6].
Qed.
#[using="HM"] Theorem aqcache_glob_init : aqcache L m AQ_GCACHE [] [] 0.
Proof.
unfold aqcache, AQ_GCACHE. aimg V m HM 0x9f190 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] IG.
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
#[using="Type"] Lemma aia_scan63 : zscanZ Asan_seg_bytes_003 (AIA_BASE - SEG3) AIA_SIZE = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
#[using="Type"] Lemma aia_scan : zscanN Asan_seg_bytes_003 64 (Z.to_N (AIA_BASE - SEG3)) (Z.to_N AIA_SIZE) = true.
Proof.
apply (zscanN_complete _ 63).
- apply N.leb_le. vm_compute. reflexivity.
- intros i Hi. apply (zscanZ_sound _ _ _ aia_scan63). unfold AIA_BASE, SEG3, AIA_SIZE in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>66242812840.10000004S2Hi".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Theorem aintal_init : aintal false m.
Proof.
unfold aintal, AIA_FLAG.
Local Ltac2 Set LiaHints.tbl := fun () => "0080>13277214957.1318767818003.1323196675079.1129423329554.8 31723267042.1334143512713.8 42526599329.1552024377527.1300000500:00;00<00A00B00J00OS3EQNS3EQNSSS3EQNSS3EQN2HiS3EQN".
aimg V m HM 0x131f08 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] I1.
split; [exact I1|]. split; [| intros; discriminate].
mimg V m HM 0xa3680 (0xa3680 + 0x81030) IMG. mwr V m HM (ZLit 626688) 5620816 W.
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
