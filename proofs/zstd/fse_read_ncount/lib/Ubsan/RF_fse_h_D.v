(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Stdio_pure.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_h_model RF_fse_h_tail RF_fse_h_cmp.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Startup_B.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition PC_D_ENTRY : Z := 0x136b0.
Definition PC_D_EXIT_RA : Z := 0x1379c.
Definition PFREE_D : Z := 0x151b4.
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
Lemma stk_of_u8arr : forall m A bs n, u8arr usegs m A bs -> Z.of_nat (length bs) = n -> stk usegs m A (A + n).
Proof.
intros m A bs n H L. apply rw_cells_of_u8arr in H. apply stk_of_rw_cells in H. cbn [cells_size csize] in H.
rewrite Nat.add_0_r, L in H. exact H.
Qed.
Definition phaseD_post (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SP P BUFF bsz lo : Z) (m : fmem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word) (m' : fmem),
ms' = MS (mkR (Z_to_bv 64 PC_D_EXIT_RA) (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) s1
(Z_to_bv 64 BUFF) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 BUFF) s4 s5 s6 s7
s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFREE_D) fc None m' (seg_rom usegs)
/\ munch [(P + 8, P + 16); (BUFF, BUFF + bsz); (SP - 256, SP + 1560)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (SP + 1560).
Section PhaseD.
Hypothesis U32R : prod_u32r_stmt.
Hypothesis READ : fse_read_stmt.
Hypothesis ISERR : fse_iserror_stmt.
#[using="READ ISERR"] Lemma phaseD2 :
forall (gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m m1 : fmem) (SP P D BUFF : Z) (pl : list Z) (lo : Z)
(tl msv dsz bsz rem rem' : Z) (nc data junk buf' : list Z) (j16 jtl rtjunk : list byte)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x28 x29 x30 x31 : word),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem) ->
Forall (fun c => 0 <= c < 256) pl ->
Forall (fun c => 0 <= c < 256) junk -> zlen junk = bsz - dsz ->
u8arr usegs m1 BUFF (map (Z_to_bv 8) (data ++ junk)) ->
rw_cells usegs m1 SP [CB 16 j16; CB 4 jtl; C4 (Z_to_bv 64 255); CB 512 rtjunk] ->
u8arr usegs m1 (SP + 536) (u16s (map (Z_to_bv 64) nc)) ->
u8arr usegs m1 (SP + 1048) (map (Z_to_bv 8) buf') -> length buf' = 512%nat ->
stk usegs m1 lo SP -> lo <= SP - 256 -> 0 < SP -> SP mod 16 = 0 -> SP + 1632 < 2^64 ->
0 < BUFF -> BUFF + bsz <= lo ->
munch [(P + 8, P + 16); (BUFF, BUFF + bsz); (SP - 256, SP + 1560)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
evt usegs (phaseD_post gp tp s10 s11 F fc SP P BUFF bsz lo m)
(MS (mkR x1 (Z_to_bv 64 SP) gp tp x5 x6 x7 (Z_to_bv 64 P) (Z_to_bv 64 tl) x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 msv) (Z_to_bv 64 BUFF) (Z_to_bv 64 dsz) (Z_to_bv 64 bsz) x22 x23 x24 x25 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 0x1370c) fc None m1 (seg_rom usegs)).
Proof.
intros until x31. intros EA PLB JB JL BA FRLO NCA DATAA LB' ST LO SP0 SPAL SPH B0 BLO MU WM MI.
assert (LMB : length (map (Z_to_bv 8) buf') = 512%nat) by (rewrite length_map; exact LB').
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
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
assert (TLC' : rw_cells usegs m1 (SP + 16) [C4 tl0]).
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
assert (FRS : FSE_READ_STACK = 256) by reflexivity.
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
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
assert (EA2 : Z.shiftr (Z.land (0 - (SP + 536)) 18446744073709551615) 1 = (2^64 - (SP + 536)) / 2 - 0).
{ change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_unique (0 - (SP + 536)) (2^64) (-1) (2^64 - (SP + 536))) by lia. change (2^1) with 2. rewrite Z.sub_0_r. reflexivity. }
assert (EA3 : Z.shiftr (Z.land (0 - (SP + 24)) 18446744073709551615) 1 = (2^64 - (SP + 24)) / 2 - 0).
{ change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_unique (0 - (SP + 24)) (2^64) (-1) (2^64 - (SP + 24))) by lia. change (2^1) with 2. rewrite Z.sub_0_r. reflexivity. }
assert (E4 : Z.land (msv + 1) 4294967295 = msv + 1 - 0).
{ change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia. }
assert (A2B : 256 <= (2^64 - (SP + 536)) / 2 <= 2^63) by (clear - SP0 SPH; Z.div_mod_to_equations; lia).
assert (A3B : 256 <= (2^64 - (SP + 24)) / 2 <= 2^63) by (clear - SP0 SPH; Z.div_mod_to_equations; lia).
rewrite EA2, EA3, E4. clear EA2 EA3 E4.
replace (Z_to_bv 64 (SP + 536)) with (Z_to_bv 64 (SP + 536 + 2 * 0)) by (f_equal; lia).
replace (Z_to_bv 64 (SP + 24)) with (Z_to_bv 64 (SP + 24 + 2 * 0)) by (f_equal; lia).
eapply (cmp_loop gp tp _ _ _ _ _ _ _ _ _ _ s10 s11 F fc _ SP (SP + 536) (SP + 24) nc rt msv _
ltac:(lia) F4 LRT (proj1 NCA) (proj1 RTA) AGREE 257%nat 0 ((2^64 - (SP + 536)) / 2) ((2^64 - (SP + 24)) / 2)); [lia| lia| lia| lia|].
intros y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31.
zstep. zstep.
apply evt_done. unfold phaseD_post, PC_D_EXIT_RA, PFREE_D.
do 23 eexists. split; [reflexivity|].
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
Qed.
#[using="U32R READ ISERR"] Theorem phaseD_proof :
forall (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP P D BUFF : Z) (pl : list Z) (lo : Z)
(tl msv dsz bsz rem : Z) (nc data buf' : list Z) (j16 jtl rtjunk bjunk : list byte),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem) ->
length buf' = 512%nat -> firstn (Z.to_nat dsz) buf' = data ->
rw_cells usegs m BUFF [CB (Z.to_nat bsz) bjunk] ->
rw_cells usegs m SP [CB 16 j16; CB 4 jtl; C4 (Z_to_bv 64 255); CB 512 rtjunk] ->
u8arr usegs m (SP + 536) (u16s (map (Z_to_bv 64) nc)) ->
u8arr usegs m (SP + 1048) (map (Z_to_bv 8) buf') ->
prod_at m P D rem -> payload_at m D pl ->
stk usegs m lo SP -> lo <= SP - 256 -> 0 < SP -> SP mod 16 = 0 -> SP + 1632 < 2^64 ->
P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) -> 0 < P -> P mod 8 = 0 -> 0 < D ->
0 < BUFF -> BUFF + bsz <= lo -> (BUFF + bsz <= P \/ P + 16 <= BUFF) -> (BUFF + bsz <= D \/ D + zlen pl <= BUFF) ->
mem_inv usegs m ->
evt usegs (phaseD_post gp tp s10 s11 F fc SP P BUFF bsz lo m)
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 tl) (Z_to_bv 64 BUFF) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 msv) s3 (Z_to_bv 64 dsz) (Z_to_bv 64 bsz) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PC_D_ENTRY) fc None m (seg_rom usegs)).
Proof.
intros until bjunk. intros EA LB' FB' BLK FRLO NCA DATAA PR PL ST LO SP0 SPAL SPH PLO DLO DP P0 PAL D0 B0 BLO BP BD MI.
destruct PL as [PAY PLB].
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & F7 & F8 & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG, FseNCount.Zlength in *.
assert (LMNC : length (map (Z_to_bv 64) nc) = 256%nat) by (rewrite length_map; exact F4).
assert (LMB : length (map (Z_to_bv 8) buf') = 512%nat) by (rewrite length_map; exact LB').
pose proof (munch_refl [(P + 8, P + 16); (BUFF, BUFF + bsz); (SP - 256, SP + 1560)] m) as MU. pose proof (wmono_refl usegs m) as WM.
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
assert (BA : u8arr usegs x13 BUFF (map (Z_to_bv 8) data ++ rest)).
{ pose proof (proj2 (Stdio_pure.rw_cells_app usegs x13 BUFF [CB (Z.to_nat dsz) (map (Z_to_bv 8) data)] [CB (Z.to_nat (bsz - dsz)) rest])) as AP.
cbn [cells_size csize Nat.add] in AP. replace (BUFF + Z.of_nat (Z.to_nat dsz + 0)) with (BUFF + dsz) in AP by lia.
specialize (AP (conj DST DREST)). cbn [app] in AP.
pose proof (rw_cells_merge usegs x13 BUFF [] [CB (Z.to_nat dsz) (map (Z_to_bv 8) data); CB (Z.to_nat (bsz - dsz)) rest] []) as MG.
rewrite app_nil_r in MG. specialize (MG AP). clear AP. rename MG into AP. cbn [app cells_size csize cells_bytes cbytes Nat.add] in AP.
apply u8arr_of_rw_cells in AP. rewrite app_nil_r in AP. exact AP. }
clear DST DREST.
zstep.
if_cases K; zify_cond K.
-
assert (EQ : bsz = dsz) by lia.
destruct rest as [|? ?]; [| cbn in LREST; lia]. rewrite app_nil_r in BA.
eapply (phaseD2 gp tp s10 s11 F fc m x13 SP P D BUFF pl lo tl msv dsz bsz rem rem nc data [] buf');
try eassumption; try lia; [constructor| cbn; lia| rewrite app_nil_r; exact BA].
-
zstep. zstep. zstep. zstep.
replace (0 <? BUFF) with true by (symmetry; apply Z.ltb_lt; lia). change (Z.b2z true) with 1.
replace (bsz - dsz) with (Z.of_nat (Z.to_nat (bsz - dsz))) by lia.
replace (BUFF + dsz) with (BUFF + (dsz + zlen (@nil Z))) by (cbn; lia).
eapply (tail_loop U32R gp tp s10 s11 F fc x13 SP P D BUFF pl data msv tl dsz bsz lo _
ltac:(lia) ltac:(lia) PLO DLO DP ltac:(lia) BP BD F9 PLB P0 PAL D0 (Z.to_nat (bsz - dsz)) rem [] rest);
[ lia | exact LREST | cbn; lia | lia | lia | | ].
+
rewrite app_nil_r. split; [exact BA|]. split; [exact PR|]. split; [exact PAY|]. split; [exact ST|].
split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
+ intros m2 junkF remF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y24 y25 y28 y29 y30 y31 ET (BA2 & PR2 & PAY2 & ST2 & MU2 & WM2 & MI2) RF.
rewrite app_nil_r in BA2.
pose proof (fseB_tail_spec pl rem dsz bsz AB ltac:(lia) ltac:(lia)) as TS. unfold fseB_tail in TS. rewrite ET in TS.
destruct TS as (TS1 & TS2 & TS3).
clear BA PR PAY ST MI.
transport_after_call usegs x13 m2 MU2 WM2.
eapply (phaseD2 gp tp s10 s11 F fc m m2 SP P D BUFF pl lo tl msv dsz bsz rem remF nc data junkF buf');
try eassumption; try lia; try (apply all_bytes_Forall; exact TS2); try exact TS1.
Qed.
End PhaseD.
