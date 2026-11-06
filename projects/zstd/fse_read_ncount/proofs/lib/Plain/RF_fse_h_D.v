(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Stdio_pure.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_h_model RF_fse_h_tail RF_fse_h_cmp.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Startup_B.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_D_ENTRY : Z := 0x1366c.
Definition PC_D_EXIT_RA : Z := 0x13718.
Definition PFREE_D : Z := 0x14ecc.
Lemma le4_exists : forall bs : list byte, length bs = 4%nat -> exists w : word, le4 w = bs.
Proof.
intros bs L. destruct bs as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try discriminate L.
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in R0, R1, R2, R3. cbn in R0, R1, R2, R3.
exists (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)).
unfold le4. cbn [Z_to_le_bytes]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>11447729963.3030163642507.3737865240588.9 63368414635.9 9311791775.9  00000A00j00m010013S1L1H2H02H42H52H9S1L2R01H2H02H42H52H93H103H142R12R22R33H15S1LS1LS1L".
rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
f_equal; [|f_equal; [|f_equal; [|f_equal]]].
- rewrite <- (byte_of_unsigned b0) at 2. apply Z_to_bv8_mod. change (2^8) with 256. Z.div_mod_to_equations. lia.
- rewrite <- (byte_of_unsigned b1) at 2. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. Z.div_mod_to_equations. lia.
- rewrite <- (byte_of_unsigned b2) at 2. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. Z.div_mod_to_equations. lia.
- rewrite <- (byte_of_unsigned b3) at 2. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^24) with 16777216. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stk_of_u8arr : forall m A bs n, u8arr psegs m A bs -> Z.of_nat (length bs) = n -> stk psegs m A (A + n).
Proof.
intros m A bs n H L. apply rw_cells_of_u8arr in H. apply stk_of_rw_cells in H. cbn [cells_size csize] in H.
rewrite Nat.add_0_r, L in H. exact H.
Qed.
Definition phaseD_post (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SP P BUFF bsz lo : Z) (m : fmem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 t3 t4 t5 t6 : word) (m' : fmem),
ms' = MS (mkR (Z_to_bv 64 PC_D_EXIT_RA) (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) s1
(Z_to_bv 64 BUFF) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 BUFF) s4 s5 s6 s7
s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFREE_D) fc None m' (seg_rom psegs)
/\ munch [(P + 8, P + 16); (BUFF, BUFF + bsz); (SP - 224, SP + 1560)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
/\ stk psegs m' lo (SP + 1560).
Section PhaseD.
Hypothesis U32R : prod_u32r_stmt.
Hypothesis READ : fse_read_stmt.
Hypothesis ISERR : fse_iserror_stmt.
#[using="READ ISERR"] Lemma phaseD2 :
forall (gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : fmem) (SP P D BUFF : Z) (pl : list Z) (lo : Z)
(tl msv dsz bsz rem rem' : Z) (nc data junk buf' : list Z) (j16 jtl rtjunk : list byte)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem) ->
Forall (fun c => 0 <= c < 256) pl ->
Forall (fun c => 0 <= c < 256) junk -> zlen junk = bsz - dsz ->
u8arr psegs m1 BUFF (map (Z_to_bv 8) (data ++ junk)) ->
rw_cells psegs m1 SP [CB 16 j16; CB 4 jtl; C4 (Z_to_bv 64 255); CB 512 rtjunk] ->
u8arr psegs m1 (SP + 536) (u16s (map (Z_to_bv 64) nc)) ->
u8arr psegs m1 (SP + 1048) (map (Z_to_bv 8) buf') -> length buf' = 512%nat ->
stk psegs m1 lo SP -> lo <= SP - 224 -> 0 < SP -> SP mod 16 = 0 -> SP + 1632 < 2^64 ->
0 < BUFF -> BUFF + bsz <= lo ->
munch [(P + 8, P + 16); (BUFF, BUFF + bsz); (SP - 224, SP + 1560)] m m1 -> wmono psegs m m1 -> mem_inv psegs m1 ->
evt psegs (phaseD_post gp tp s8 s9 s10 s11 F fc SP P BUFF bsz lo m)
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 msv) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 tl) (Z_to_bv 64 BUFF) (Z_to_bv 64 dsz) (Z_to_bv 64 bsz) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x136a8) fc None m1 (seg_rom psegs)).
Proof.
intros until x31. intros EA PLB JB JL BA FRLO NCA DATAA LB' ST LO SP0 SPAL SPH B0 BLO MU WM MI.
assert (LMB : length (map (Z_to_bv 8) buf') = 512%nat) by (rewrite length_map; exact LB').
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
Local Ltac2 Set LiaHints.tbl := fun () => "01E0?10371679818.13210871190032.10411072576307.1041129604201.132 1130080104.85  11420940021.10411561081958.10413232899144.1041343986644.120 15815041557.10417311699531.12217703102171.10418297518805.1211837569603.118 18469897329.12618920014474.13219767382474.13219959518368.11823488499343.93 23490659993.71 26687900821.12328432205992.12028847124063.12129835094129.12630035463766.10430392619093.12132061670026.13232194916428.1043259212812.104 35814255920.11836703307711.10436755987125.10438362842763.12138526085142.98 3940774346.132 39583388471.11840948155018.13240977174107.10442619122122.13242766780469.10443237124459.1044330389258.132 43861027327.99 45472432761.12145923269312.12046073141494.12046224418443.12148399076102.13250381875480.12150807941630.1185085507072.120 51361574950.10451468416745.13251469252072.85 51820927409.1205183897129.104 51840276309.10452225599816.12152293769064.10452579502455.12152579502455.12252579502455.12354469909.121   55403097984.12055601123541.12256103075578.13256104009211.85 56964589203.11857017606329.11857083350539.12359314923118.119596204072.104  59720953941.12160164869122.10462655459299.10462679802304.12062686362581.12363950883096.12164276678536.12165842329083.12066070830614.11866317973795.11867036774546.12167691177611.1217949567253.121 00000U01701b02D02H02n03P04A04B04d05F05h06J06o07Q08308X09=09J09S0:50:W0;`0<B0<l0=V0>80>f0?T0?U0?V0@<0@i0A@0Ae0BJ0Bl0Bm0CR0D80D90D^0E:0En0F\0GJ0GK0H00HZ0I?0Ia0JC0Je0Ji0L10Lb0MD0Mf0NW0NX0NY0NZ0OD0P20P30PU0PY0Q>0Qc0RE0S90Sj0TL0U:0Ul0VN0VO0W10WS0WT0WU0X:0X\0YF0YhS2LO2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43F113LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F4S3SP02F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2JL3SP04SPAL2F42F63LRJ4LRT03LRT5LMBUF5LMRT04LMNCFS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F22F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2LO2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F42F63LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT0S3LB'3LMBS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2JL3LB'2LO3SP03BLO3LMB2F42F63LTL3LRJ4LRT03RTT3LRT5LMBUF5LMRT04LMNC3FRS1HS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS3SP03SPH2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS3LB'3LMB2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2LO3BLO2F43LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCS2LO3BLO2F43LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCSSS3SP02F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2JL2F42F63LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCS2JL2F42F93LRJ4LRT03LRTS2LO2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F22F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCFS2LO2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS3SP02F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCFS2LO2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2JL2F42F63LRJ4LRT03LRT4LBUFS2LO3SP03BLO2F43LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNC1HS2LO3BLO2F43LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCS2LO3BLO2F43LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCFS2LO2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS3LB'3LMB2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F42F63LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F4S2JL3LB'2LO3SP03BLO3LMB2F42F63LTL3LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNC3FRSS2JL3BLO2F42F63LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2JL3SP04SPAL2F42F63LRJ4LRT03LRT5LMBUF5LMRT04LMNCFFFS3LB'3LMB2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2LO3BLO2F43LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCFS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F4S2F12F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F22F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS3LB'3LMB2F43LTL3LRJ4LRT03RTT3LRT5LMBUF5LMRT04LMNC1KS2JL3SP04SPAL2F42F63LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2LO3BLO2F43LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCS2LO3SPH3BLO2F43LRJ4LRT03LRT4LBUF5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCFS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCFSS2F22F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS3LB'3LMB2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNCS2F43LRJ4LRT03LRT5LMBUF5LMRT04LMNC".
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & F7 & F8 & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
apply (proj1 (Stdio_pure.rw_cells_app _ _ _ [CB 16 _] _)) in FRLO. destruct FRLO as [J16 FRLO]. cbn [cells_size csize Nat.add] in FRLO.
apply (proj1 (Stdio_pure.rw_cells_app _ _ _ [CB 4 _] _)) in FRLO. destruct FRLO as [TLC FRLO]. cbn [cells_size csize Nat.add] in FRLO.
apply (proj1 (Stdio_pure.rw_cells_app _ _ _ [C4 _] _)) in FRLO. destruct FRLO as [MSVC RTC]. cbn [cells_size csize Nat.add] in RTC.
replace (SP + Z.of_nat 16) with (SP + 16) in * by lia.
replace (SP + 16 + Z.of_nat 4) with (SP + 20) in * by lia.
replace (SP + 20 + Z.of_nat 4) with (SP + 24) in * by lia.
assert (LTL : length jtl = 4%nat) by (destruct TLC as [[[Hn _] _] _]; exact Hn).
destruct (le4_exists jtl LTL) as (tl0 & ETL).
assert (TLC' : rw_cells psegs m1 (SP + 16) [C4 tl0]).
{ eapply Stdio_pure.rw_cells_recast; [exact TLC| cbn; repeat split| cbn [cells_bytes cbytes]; rewrite ETL; reflexivity| reflexivity]. }
clear TLC.
assert (LRJ : length rtjunk = 512%nat) by (destruct RTC as [[[Hn _] _] _]; exact Hn).
destruct (u16s_of_bytes 256 rtjunk ltac:(rewrite LRJ; reflexivity)) as (rt0 & LRT0 & RT0S & ERT).
apply u8arr_of_rw_cells in RTC. rewrite ERT in RTC.
pose proof (fseB_round_trip pl (zlen pl) junk rt0 AB ltac:(lia)) as RTT. rewrite EA in RTT.
destruct (RTT ltac:(apply Forall_all_bytes; exact JB) LRT0) as (rt & RD & LRT & AGREE & _).
zstep. zstep. zstep. zstep. zstep. zstep.
assert (LBUF : zlen (data ++ junk) = bsz) by (rewrite length_app; unfold FseNCount.Zlength in F9; lia).
assert (LMBUF : length (map (Z_to_bv 8) (data ++ junk)) = Z.to_nat bsz) by (rewrite length_map; lia).
assert (LMRT0 : length (map (Z_to_bv 64) rt0) = 256%nat) by (rewrite length_map; exact LRT0).
assert (LMNC : length (map (Z_to_bv 64) nc) = 256%nat) by (rewrite length_map; exact F4).
assert (FRS : FSE_READ_STACK = 224) by reflexivity.
assert (BYT : Forall (fun c => 0 <= c < 256) (data ++ junk)).
{ apply Forall_app. split; [apply all_bytes_Forall; exact F10| exact JB]. }
unfold fse_read_stmt, PFSE_READ in READ.
call (READ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ SP (SP + 24) (SP + 20) (SP + 16) BUFF
rt0 rt (data ++ junk) 255 msv tl dsz lo tl0);
[ first [ exact (proj1 BA) | assumption | reflexivity | lia | rewrite LBUF; lia | rewrite FRS; lia | rewrite LBUF, FRS; lia | rewrite LBUF; reflexivity
| right; lia | left; rewrite LBUF, FRS; lia | right; rewrite LBUF; lia | Z.div_mod_to_equations; lia ] .. | ].
rename PC0 into RTA. rename PC1 into MSVC2. rename POST into TLC2. rename PC into ST. rename MI0 into MI.
zstep. zstep.
unfold fse_iserror_stmt, PFSE_ISERROR in ISERR.
call_pure (ISERR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dsz); [lia| reflexivity|].
replace (2^64 - 119 <=? dsz) with false by (symmetry; apply Z.leb_gt; lia). cbn [Z.b2z].
zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
zstep. if_cases K. { exfalso. revert K. rewrite bv_eqb_refl. discriminate. } clear K.
zstep.
rewrite Stdio_pure.sx32_small by (change (2^31) with 2147483648; lia).
zstep. if_cases K. { exfalso. revert K. rewrite bv_eqb_refl. discriminate. } clear K.
zstep. rewrite Stdio_pure.sx32_small by (change (2^31) with 2147483648; lia).
zstep. if_cases K. { exfalso. revert K. rewrite bv_eqb_refl. discriminate. } clear K.
zstep. zstep. zstep.
eapply (cmp_loop gp tp _ _ _ _ _ _ _ s8 s9 s10 s11 F fc _ SP (SP + 536) (SP + 24) nc rt msv _
ltac:(lia) F4 LRT (proj1 NCA) (proj1 RTA) AGREE 257%nat 0); [lia| lia|].
intros y1 y5 y6 y7 y10 y13 y14 y15 y16 y17 y28 y29 y30 y31.
zstep. zstep.
apply evt_done. unfold phaseD_post, PC_D_EXIT_RA, PFREE_D.
do 21 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
apply stk_of_rw_cells in J16. cbn [cells_size csize Nat.add] in J16.
apply stk_of_rw_cells in TLC2. cbn [cells_size csize Nat.add] in TLC2.
apply stk_of_rw_cells in MSVC2. cbn [cells_size csize Nat.add] in MSVC2.
apply (stk_of_u8arr _ _ _ 512) in RTA; [| rewrite u16s_length, length_map, LRT; reflexivity].
apply (stk_of_u8arr _ _ _ 512) in NCA; [| rewrite u16s_length, LMNC; reflexivity].
apply (stk_of_u8arr _ _ _ 512) in DATAA; [| rewrite LMB; reflexivity].
replace (SP + 1048 + 512) with (SP + 1560) in DATAA by lia.
replace (SP + 536 + 512) with (SP + 1048) in NCA by lia.
replace (SP + 24 + 512) with (SP + 536) in RTA by lia.
replace (SP + 20 + Z.of_nat 4) with (SP + 24) in MSVC2 by lia.
replace (SP + 16 + Z.of_nat 4) with (SP + 20) in TLC2 by lia.
replace (SP + Z.of_nat 16) with (SP + 16) in J16 by lia.
eapply stk_merge; [| exact DATAA| lia].
eapply stk_merge; [| exact NCA| lia].
eapply stk_merge; [| exact RTA| lia].
eapply stk_merge; [| exact MSVC2| lia].
eapply stk_merge; [| exact TLC2| lia].
eapply stk_merge; [exact ST| exact J16| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="U32R READ ISERR"] Theorem phaseD_proof :
forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D BUFF : Z) (pl : list Z) (lo : Z)
(tl msv dsz bsz rem : Z) (nc data buf' : list Z) (j16 jtl rtjunk bjunk : list byte),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem) ->
length buf' = 512%nat -> firstn (Z.to_nat dsz) buf' = data ->
rw_cells psegs m BUFF [CB (Z.to_nat bsz) bjunk] ->
rw_cells psegs m SP [CB 16 j16; CB 4 jtl; C4 (Z_to_bv 64 255); CB 512 rtjunk] ->
u8arr psegs m (SP + 536) (u16s (map (Z_to_bv 64) nc)) ->
u8arr psegs m (SP + 1048) (map (Z_to_bv 8) buf') ->
prod_at m P D rem -> payload_at m D pl ->
stk psegs m lo SP -> lo <= SP - 224 -> 0 < SP -> SP mod 16 = 0 -> SP + 1632 < 2^64 ->
P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) -> 0 < P -> P mod 8 = 0 -> 0 < D ->
0 < BUFF -> BUFF + bsz <= lo -> (BUFF + bsz <= P \/ P + 16 <= BUFF) -> (BUFF + bsz <= D \/ D + zlen pl <= BUFF) ->
mem_inv psegs m ->
evt psegs (phaseD_post gp tp s8 s9 s10 s11 F fc SP P BUFF bsz lo m)
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 msv) (Z_to_bv 64 BUFF) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 tl) s3 (Z_to_bv 64 dsz) (Z_to_bv 64 bsz) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_D_ENTRY) fc None m (seg_rom psegs)).
Proof.
intros until bjunk. intros EA LB' FB' BLK FRLO NCA DATAA PR PL ST LO SP0 SPAL SPH PLO DLO DP P0 PAL D0 B0 BLO BP BD MI.
destruct PL as [PAY PLB].
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
Local Ltac2 Set LiaHints.tbl := fun () => "00g0?12058208169.11315274897990.11119421216629.13919948753055.11119959127831.94 19962924073.12220487660218.11220500423599.94 22073804078.11122468029787.13923490659993.76 26640609441.11328382404904.11330031381839.11130501862762.13930508451647.93 31067389780.11231067389780.11332994942837.13933006350464.13933318008459.11133549284273.11334356490401.11336889281389.92 38538448787.11138931029844.1124123162460.139 42006909334.11042276177632.11145059154957.13946111935835.13946634523813.11348419668922.11349030893556.11151345347566.11152977819942.11153424153439.1125342792905.111 54827913903.11454827913903.14155126430173.94 55254765727.11155257533481.12255342297995.14158841842865.13961785434775.14162836098605.94 62900777713.14162949785596.11164024439260.14164966907740.13965149139998.94 65490502138.11165527262281.11167103711776.11100000U01601^02=02V03503T03m03n04J04O05305I05m06I06f07J07n08V09>09_09`0:@0:W0;60;Z0<B0<X0<Y0<Z0=60=70=X0=Y0>50>W0?80?Z0@@0@^0A80A[0B@0B`0CH0Cf0DJ0Dh0EH0Eh0FP0G80GY0H80H[S3LB'2BD4LENP2F42F63F114LMNC3LMB4LSRCS3LB'2F42F64LMNC3LMB4LSRC5LREST1KS3LB'2LO3BLO2F42F64LMNC3LMB4LSRC5LREST1KS3LB'2F42F64LMNC3LMB4LSRC5LRESTS3LB'2F42F64LMNC3LMB4LSRCS3LB'2F42F64LMNC3LMB4LSRC5LRESTS3LB'2F42F64LMNC3LMB4LSRC5LRESTS3LB'2F42F64LMNC3LMB4LSRCFS3LB'2F44LMNC3LMB4LSRC5LRESTS3LB'S3LB'2LO3BLO2F42F63F114LMNC3LMB4LSRCS3LB'2F44LMNC3LMB4LSRCS3LB'3SP03SPH2F44LMNC3LMB4LSRC5LRESTS3LB'2F44LMNC3LMB4LSRC5LRESTS3LB'2F42F63F114LMNC3LMB4LSRCS3LB'2LO3BLO2F42F63F114LMNC3LMB4LSRCS3LB'2LO3BLO2F42F63F114LMNC3LMB4LSRCS3LB'2LO3BLO2F42F64LMNC3LMB4LSRC5LREST1KS3LB'2LO3BLO2F42F64LMNC3LMB4LSRC5LREST1KS3LB'2F42F64LMNC3LMB4LSRC5LREST1KFS3LB'2BP2F42F63F114LMNC3LMB4LSRCS3LB'2F42F62F94LMNC3LMBS3LB'2LO2F44LMNC3LMB4LSRC5LRESTS3LB'2LO3BLO2F42F63F114LMNC3LMB4LSRCS3LB'2LO3PLO2F42F64LMNC3LMB4LSRC5LREST1KS3LB'2F44LMNC3LMB4LSRCFFS3LB'2F44LMNC3LMB4LSRC5LRESTFS3LB'2F42F64LMNC3LMB4LSRC5LREST1KFS3LB'2F44LMNC3LMB4LSRC5LRESTS3LB'2F43F114LMNC3LMB4LSRC5LREST1KS3LB'3BLO2F42F63F114LMNC3LMB4LSRCS3LB'2F43F114LMNC3LMB4LSRC5LREST1KS3LB'2LO3BLO2F42F63F114LMNC3LMB4LSRC1HS3LB'2F44LMNC3LMB4LSRC5LREST1HS3LB'3SPH2F44LMNC3LMB4LSRCS3LB'2F42F63F114LMNC3LMB4LSRC5LRESTS3LB'2F42F63F114LMNC3LMB4LSRC5LREST1KS3LB'2F43F124LMNC3LMB4LSRC5LRESTS3LB'2LO3PLO2F42F64LMNC3LMB4LSRC5LREST1KS3LB'2F44LMNC3LMB4LSRC5LREST1HS3LB'2LO3BLO2F42F63F114LMNC3LMB4LSRCS3LB'2F44LMNC3LMB4LSRC5LREST1HS3LB'2F43F124LMNC3LMB4LSRC5LRESTS3LB'2F43F114LMNC3LMB4LSRC5LRESTS3LB'2LO3PLO2F42F64LMNC3LMB4LSRC5LREST1KS3LB'2LO3SPH3BLO2F42F63F114LMNC3LMB4LSRCS3LB'2F42F64LMNC3LMB4LSRC5LREST1KS3LB'2F42F64LMNC3LMB4LSRC5LRESTS3LB'2B03BLO2F44LMNC3LMB4LSRC5LREST".
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & F7 & F8 & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG, FseNCount.Zlength in *.
assert (LMNC : length (map (Z_to_bv 64) nc) = 256%nat) by (rewrite length_map; exact F4).
assert (LMB : length (map (Z_to_bv 8) buf') = 512%nat) by (rewrite length_map; exact LB').
pose proof (munch_refl [(P + 8, P + 16); (BUFF, BUFF + bsz); (SP - 224, SP + 1560)] m) as MU. pose proof (wmono_refl psegs m) as WM.
unfold PC_D_ENTRY. unfold prod_at in PR.
pose proof (proj1 DATAA) as SRC0. rewrite <- (firstn_skipn (Z.to_nat dsz) buf') in SRC0. rewrite map_app, FB' in SRC0.
apply bytes_at_app in SRC0. destruct SRC0 as [SRC _].
assert (LSRC : length (map (Z_to_bv 8) data) = Z.to_nat dsz) by (rewrite length_map; lia).
apply (rw_cells_split_CB _ _ _ [] _ _ _ [Z.to_nat dsz; Z.to_nat (bsz - dsz)]%nat) in BLK; [| cbn; lia]. cbn [mk_CB_cells app] in BLK.
apply (proj1 (Stdio_pure.rw_cells_app _ _ _ [CB _ _] _)) in BLK. destruct BLK as [DST DREST]. cbn [cells_size csize Nat.add] in DREST.
replace (BUFF + Z.of_nat (Z.to_nat dsz + 0)) with (BUFF + dsz) in DREST by lia.
zstep. zstep. zstep. zstep.
call (Startup_B.rmemcpy_specZ BUFF (SP + 1048) dsz); [exact SRC | exact LSRC | exact DST | right; lia | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
rename PC into DST. rename MI0 into MI. clear POST.
set (rest := firstn (Z.to_nat (bsz - dsz)) (skipn (Z.to_nat dsz) bjunk)) in *.
assert (LREST : length rest = Z.to_nat (bsz - dsz)) by (destruct DREST as [[[Hn _] _] _]; exact Hn).
assert (BA : u8arr psegs x13 BUFF (map (Z_to_bv 8) data ++ rest)).
{ pose proof (proj2 (Stdio_pure.rw_cells_app psegs x13 BUFF [CB (Z.to_nat dsz) (map (Z_to_bv 8) data)] [CB (Z.to_nat (bsz - dsz)) rest])) as AP.
cbn [cells_size csize Nat.add] in AP. replace (BUFF + Z.of_nat (Z.to_nat dsz + 0)) with (BUFF + dsz) in AP by lia.
specialize (AP (conj DST DREST)). cbn [app] in AP.
pose proof (rw_cells_merge psegs x13 BUFF [] [CB (Z.to_nat dsz) (map (Z_to_bv 8) data); CB (Z.to_nat (bsz - dsz)) rest] []) as MG.
rewrite app_nil_r in MG. specialize (MG AP). clear AP. rename MG into AP. cbn [app cells_size csize cells_bytes cbytes Nat.add] in AP.
apply u8arr_of_rw_cells in AP. rewrite app_nil_r in AP. exact AP. }
clear DST DREST.
zstep.
if_cases K; zify_cond K.
-
assert (EQ : bsz = dsz) by lia.
destruct rest as [|? ?]; [| cbn in LREST; lia]. rewrite app_nil_r in BA.
eapply (phaseD2 gp tp s8 s9 s10 s11 F fc m x13 SP P D BUFF pl lo tl msv dsz bsz rem rem nc data [] buf');
try eassumption; try lia; [constructor| cbn; lia| rewrite app_nil_r; exact BA].
-
zstep. zstep.
replace (bsz - dsz) with (Z.of_nat (Z.to_nat (bsz - dsz))) by lia.
replace (BUFF + dsz) with (BUFF + (dsz + zlen (@nil Z))) by (cbn; lia).
eapply (tail_loop U32R gp tp s8 s9 s10 s11 F fc x13 SP P D BUFF pl data msv tl dsz bsz lo _
ltac:(lia) ltac:(lia) PLO DLO DP ltac:(lia) BP BD F9 PLB P0 PAL D0 (Z.to_nat (bsz - dsz)) rem [] rest);
[ lia | exact LREST | cbn; lia | lia | lia | | ].
+
rewrite app_nil_r. split; [exact BA|]. split; [exact PR|]. split; [exact PAY|]. split; [exact ST|].
split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
+ intros m2 junkF remF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 ET (BA2 & PR2 & PAY2 & ST2 & MU2 & WM2 & MI2) RF.
rewrite app_nil_r in BA2.
pose proof (fseB_tail_spec pl rem dsz bsz AB ltac:(lia) ltac:(lia)) as TS. unfold fseB_tail in TS. rewrite ET in TS.
destruct TS as (TS1 & TS2 & TS3).
clear BA PR PAY ST MI.
transport_after_call psegs x13 m2 MU2 WM2.
eapply (phaseD2 gp tp s8 s9 s10 s11 F fc m m2 SP P D BUFF pl lo tl msv dsz bsz rem remF nc data junkF buf');
try eassumption; try lia; try (apply all_bytes_Forall; exact TS2); try exact TS1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End PhaseD.
