(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseWriteModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_write_A RF_fse_write_B.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Section WR.
Variables (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP BUF NC : Z)
(buf0 buf' nc : list Z) (msv tl n lo : Z).
Hypothesis BUF0 : u8arr psegs m BUF (map (Z_to_bv 8) buf0).
Hypothesis BUFB : Forall (fun c => 0 <= c < 256) buf0.
Hypothesis NCB : bytes_at psegs m NC (u16s (map (Z_to_bv 64) nc)).
Hypothesis NCR : Forall (fun c => - 32768 <= c < 32768) nc.
Hypothesis WOK : write_ncount buf0 nc msv tl = Ok (buf', n).
Hypothesis MSV : 0 <= msv <= 255.
Hypothesis TL : 0 <= tl < 2^32.
Hypothesis BSZ : zlen buf0 <= 65536.
Hypothesis ST : stk psegs m lo SP.
Hypothesis LO : lo <= SP - 80.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis SEPB : BUF + zlen buf0 <= SP - 80 \/ SP <= BUF.
Hypothesis SEPN : NC + 2 * zlen nc <= SP - 80 \/ SP <= NC.
Hypothesis SEPBN : NC + 2 * zlen nc <= BUF \/ BUF + zlen buf0 <= NC.
Hypothesis MI : mem_inv psegs m.
Collection WRC := ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ LO RSP SEPB SEPN SEPBN.
Notation POST := (fse_write_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP BUF buf0 buf' n lo m).
Notation bsz := (zlen buf0).
Notation asz := (msv + 1).
Notation W := [(BUF, BUF + bsz); (SP - 80, SP)].
Notation FRAMEC := (RF_fse_write_A.FRAMEC s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
Notation MINV := (RF_fse_write_A.MINV s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m SP BUF NC buf0 nc lo).
Section LOOP.
Variable safe : bool.
Notation A_ l := (l ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ LO RSP SEPB SEPN SEPBN safe).
Notation B_ l := (A_ l).
Notation WST pc mm x8 x9 x11 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 :=
(MS (mkR ra (Z_to_bv 64 (SP + -80)) gp tp (Z_to_bv 64 asz) (Z_to_bv 64 1) (Z_to_bv 64 17) x8 x9 (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 NC) x13
(Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 (Z.b2z safe)) (Z_to_bv 64 BUF) x17 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11
(Z_to_bv 64 15) (Z_to_bv 64 3) (Z_to_bv 64 asz) (Z_to_bv 64 65535))
F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
Lemma wr_loop : forall f s sf m1 X (x21 x22 x23 x24 x25 : word),
winv asz bsz s -> (w_symbol s <? asz) && (1 <? w_remaining s) = true -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
MINV m1 (w_buf s) ->
wloop nc asz bsz safe f s = Ok sf ->
(forall m2 X' (y8 y9 y18 y19 y20 y22 y23 y24 y25 : word), winv asz bsz sf -> MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evt psegs POST (WST 0x13ba4 m2 y8 y9 (Z_to_bv 64 (BUF + w_out sf)) (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 X')
y18 y19 y20 (Z_to_bv 64 (w_remaining sf)) y22 y23 y24 y25)) ->
evt psegs POST (WST 0x139c8 m1 (Z_to_bv 64 (w_nbBits s)) (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (BUF + w_out s))
(Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X) (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 s))))
(Z_to_bv 64 (w_remaining s)) (Z_to_bv 64 (w_symbol s)) x21 x22 x23 x24 x25).
Proof using WRC.
induction f as [|f IH]; intros s sf m1 X x21 x22 x23 x24 x25 WI CND RX EX MV WL K; [cbn in WL; discriminate|].
rewrite wloop_S in WL. rewrite CND in WL. apply bind_inv in WL. destruct WL as (fl & WB & WL).
apply andb_true_iff in CND. destruct CND as [CS CR]. apply Z.ltb_lt in CS. apply Z.ltb_lt in CR.
unfold wbody in WB. apply bind_inv in WB. destruct WB as (fl0 & ZB & WB).
assert (CNT : forall sa m2 X2 (y20 y21 y22 y23 : word), fl0 = Cont sa -> winv asz bsz sa -> w_symbol sa < asz -> same_ctl s sa ->
MINV m2 (w_buf sa) -> 0 <= X2 < 2^64 -> X2 mod 2^32 = w_bitStream sa ->
evt psegs POST (WST 0x13ae0 m2 (Z_to_bv 64 (w_nbBits s)) (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (BUF + w_out sa))
(Z_to_bv 64 (w_bitCount sa)) (Z_to_bv 64 X2) (Z_to_bv 64 (w_symbol sa)) (Z_to_bv 64 (w_remaining s))
y20 y21 y22 y23 x24 x25)).
{ intros sa m2 X2 y20 y21 y22 y23 -> WIA SYA (C1 & C2 & C3 & C4) MV2 RX2 EX2.
apply bind_inv in WB. destruct WB as (sc & CB & WB). apply bind_inv in WB. destruct WB as (sd & FL & WB). injection WB as <-.
pose proof (wcount_flush_facts nc asz bsz safe sa sc sd CB FL WIA SYA NCR) as (WID & SYD & CTL).
rewrite <- C1, <- C2, <- C3.
eapply (B_ wr_count sa sc sd); [exact WIA | exact SYA | exact RX2 | exact EX2 | exact MV2 | exact CB | exact FL | | ].
- intros m3 X3 z21 z22 z23 z24 z25 CND3 MV3 RX3 EX3.
eapply (IH sd sf); [exact WID | exact CND3 | exact RX3 | exact EX3 | exact MV3 | exact WL | exact K].
- intros m3 X3 z8 z9 z18 z19 z20 z22 z23 z24 z25 CND3 MV3 RX3 EX3.
destruct f as [|f']; [cbn in WL; discriminate|]. rewrite wloop_S in WL. rewrite CND3 in WL. injection WL as <-.
apply K; assumption. }
destruct (w_previousIs0 s) eqn:P0; cbn [negb Z.b2z].
-
zstep. zstep. if_true.
pose proof (wzero_block_facts nc asz bsz safe s fl0 ZB WI CS) as ZF.
eapply (B_ wr_zero s fl0); [exact WI | exact CS | exact RX | exact EX | exact MV | exact ZB | | ].
+ intros sa m2 X' y20 y21 y22 y23 -> MV2 RX2 EX2. destruct ZF as (WIA & CTL & SYA & _).
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>15945006257.951741865054.95 22621431600.9126101251455.9531838395048.9534108802824.9546794069123.9554288074796.955433691304.95 64374068984.9500000100600;00?00C00M00Q00Y00]00bSS3MSVS3SYAS2RBS2BCS2RO2RB2BCS2ROS2RM3NBIS2RMS3NBI".
eapply (CNT sa); [reflexivity | exact WIA | lia | exact CTL | exact MV2 | exact RX2 | exact EX2].
+ intros sa y18 y20 y22 y23 ->. destruct ZF as (SYA & BUA & OUA & BSA & BCA & (C1 & C2 & C3 & C4)).
injection WB as <-. injection WL as <-.
rewrite <- OUA, <- BCA, <- C1.
apply K; [ | rewrite BUA; exact MV | exact RX | rewrite BSA; exact EX].
destruct WI as (LB & RO & RB & BC & SY & RM & NBI & TH).
unfold winv. rewrite BUA, OUA, BSA, BCA, SYA, C1, C2, C3. repeat split; try assumption; try lia.
-
injection ZB as <-.
zstep. zstep. if_false. zstep. zstep.
eapply (CNT s); [reflexivity | exact WI | exact CS | unfold same_ctl; repeat split | exact MV | exact RX | exact EX].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_finish : forall sf m1 X (y8 y9 y18 y19 y20 y22 y23 y24 y25 : word),
winv asz bsz sf -> MINV m1 (w_buf sf) -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream sf ->
wfinish bsz safe sf = Ok (buf', n) ->
evt psegs POST (WST 0x13ba4 m1 y8 y9 (Z_to_bv 64 (BUF + w_out sf)) (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 X)
y18 y19 y20 (Z_to_bv 64 (w_remaining sf)) y22 y23 y24 y25).
Proof using WRC.
intros sf m1 X y8 y9 y18 y19 y20 y22 y23 y24 y25 WI MV RX EX WF.
pose proof WI as (LB & RO & RB & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & FA & SA & MUA & WMA & MIA).
pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold RF_fse_write_A.FRAMEC in FA.
unfold wfinish in WF.
destruct (Z.eqb_spec (w_remaining sf) 1) as [R1|R1]; [| cbn in WF; discriminate]. cbn [negb] in WF.
destruct (negb safe && (bsz - 2 <? w_out sf)) eqn:CK; [discriminate|].
apply bind_inv in WF. destruct WF as (b1 & S1 & WF). apply bind_inv in WF. destruct WF as (b2 & S2 & WF).
apply store_inv in S1. destruct S1 as [O1 ->]. apply store_inv in S2. destruct S2 as [O2 ->].
unfold FseNCount.Zlength in O1, O2. rewrite Zupd_length in O2. injection WF as EB EN.
assert (STORES : forall (z12 : word), evt psegs POST
(MS (mkR ra (Z_to_bv 64 (SP + -80)) gp tp (Z_to_bv 64 asz) (Z_to_bv 64 1) (Z_to_bv 64 17) y8 y9 (Z_to_bv 64 (-1))
(Z_to_bv 64 (BUF + w_out sf)) z12 (Z_to_bv 64 (w_bitCount sf))
(Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 (Z.b2z safe)) (Z_to_bv 64 BUF) (Z_to_bv 64 X) y18 y19 y20
(Z_to_bv 64 (w_remaining sf)) y22 y23 y24 y25 s10 s11 (Z_to_bv 64 15) (Z_to_bv 64 3) (Z_to_bv 64 asz) (Z_to_bv 64 65535))
F (Z_to_bv 64 0x13bbc) fc None m1 (seg_rom psegs))).
{ intros z12.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00f0?11184970978.97 11491562097.10711554597849.98 11872430787.97 13070568592.97 13072942494.96 17313728113.10717952961.95    18579966.96    21378391498.96 21378557049.98 29784300397.96 30037003821.98 31075518971.96 31946920049.1063214378781.96  3214378781.97  3299130737.106 36313996657.10537421852671.96 44319248497.10644538507633.10545590131725.98 45596907405.10945781994147.96 46400804433.10946787787121.10649170713844.97 492464117.98   49423367528.96 50082197726.96 51456153639.11051458250793.10751818759664.97 52523538196.97 55885669803.95 56567948472.96 59308611795.96 59308611920.98 59361912177.10461237818317.10661750125354.96 61752089371.95 63256608377.95 63368167069.96 63368316718.98 63370508179.97 63374621462.97 64799663456.96 65825736534.96 7223574812.95  913132285.97   9581028844.97  9847945609.97  00000700;00D00V00`00j00n01501<01C01J01N01R01d01h02502B02F02J02N02R02V02c03003:03G03K03^03n04804<04C04J04T04[04_04f05305=05A05E05L05S05Z05^05b05f05j06=06m07107507?07oS2BC2NBS2NBS2NB1H2H0S4SEPB2O22LB2RO2NBS2O12O22NBS2O12O22NBS2NBS2O12NBS2O12NBS2BC2NBS2BC2NBS2NBS2NBS4SEPB2O22LB2RO2NBS2NBS2O12O22LB2NBS2O12O22LB2NBS2NBS2NBS2NBS2NBS2NBS2O22RO2BB2NBS2O22RO2BB2NBS2RO2BB2NBS2O22RO2BB2NBS2NBS5SEPBN2O22LB2RO2NBS2O22LB2RO2BB2NBS2O22BB2NBS2NBS2BC2NBS2BC2NBS2O22BB2NBS2LO2NBS2NBS2RM2NBS2RM2NB2R12J0S2CK2NB2J1S2NBS2NBS2BC2NBS2BC2NBS2BC2NBS2NBS2NBS2NBS2NBS5SEPBN2O22LB2RO2NBS2TL4SEPB4SEPN5SEPBN2RX2EX2O22LB2RO2RB2BC3NBI2NBS2NBS2NBS2RO2BB2NBS2TL4SEPB4SEPN5SEPBN2RX2EX2O22LB2RO2RB2BC3NBI2NB".
zstep.
rewrite (swrap32_small (w_bitCount sf + 7)) by lia.
replace (Z.shiftr (w_bitCount sf + 7) 31) with 0
by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; change (2^31) with 2147483648; lia).
rewrite (swrap32_small 0) by lia.
u8_sok BA (w_out sf). zstep.
u8_store BA (w_out sf) (to_byte (w_bitStream sf)). { unfold to_byte. rewrite <- EX. change (2^32) with 4294967296. lia. }
u8_sok BA (w_out sf + 1). zstep.
u8_store BA (w_out sf + 1) (to_byte (w_bitStream sf / 2^8)).
{ unfold to_byte. rewrite <- EX. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^8) with 256. lia. }
zstep. zstep. zstep. zstep. zstep.
assert (EQ10 : BUF + w_out sf - BUF + bv_swrap 32 (Z.shiftr (bv_swrap 32 (w_bitCount sf + 7)) 3) = w_out sf + Z.quot (w_bitCount sf + 7) 8).
{ rewrite (swrap32_small (w_bitCount sf + 7)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
pose proof (Z.div_pos (w_bitCount sf + 7) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (w_bitCount sf + 7) 8 100 ltac:(lia) ltac:(lia)).
rewrite swrap32_small by lia. rewrite Z.quot_div_nonneg by lia. lia. }
rewrite EQ10.
rewrite EN.
do 10 zstep. zstep.
release_frame FA SA SP.
zstep.
apply evt_done. unfold fse_write_post. do 14 eexists. eexists. split; [reflexivity|].
split; [exact MUA|]. split; [exact WMA|]. split; [exact MIA|]. split; [exact SA|]. rewrite <- EB. exact BA. }
zstep. zstep. if_cases J0; zify_cond J0; [exfalso; lia|].
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
- rewrite (ite_true _ safe _ _ SAFE). apply STORES.
- apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
rewrite SAFE in CK. cbn [negb andb] in CK. apply Z.ltb_ge in CK.
zstep. if_cases J1; zify_cond J1; [| exfalso; lia]. apply STORES.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma winit_ok : forall buf, 5 <= tl <= 12 ->
winit buf tl = Ok (mkW buf 0 (tl - 5) 4 0 (2^tl + 1) (2^tl) (tl + 1) false).
Proof using WRC.
intros buf TLR. unfold winit, assert, FSE_MIN_TABLELOG.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25924166697.5628559041944.5632883044276.5650550177429.5600000100500:00BSS2TLS3TLRS2TL3TLR".
replace ((0 <=? tl) && (tl <? 31)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [bind]. rewrite shl32_ok by lia. cbn [bind]. change (2^0) with 1.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). rewrite Z.mul_1_r.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). rewrite Z.add_0_l.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_main : write_ncount_generic buf0 nc msv tl safe = Ok (buf', n) -> 5 <= tl <= 12 ->
evt psegs POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BUF) (Z_to_bv 64 bsz) (Z_to_bv 64 NC) (Z_to_bv 64 msv) (Z_to_bv 64 tl)
(Z_to_bv 64 (Z.b2z safe)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x13944) fc None m (seg_rom psegs)).
Proof using All.
intros GOK TLR.
unfold write_ncount_generic in GOK. cbv zeta in GOK. rewrite (winit_ok buf0 TLR) in GOK. cbn [bind] in GOK.
apply bind_inv in GOK. destruct GOK as (sf & WL & WF). unfold FseNCount.Zlength in WL, WF.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl psegs m) as WM.
pose proof ST as (LO0 & _ & _).
pose proof (u8arr_bound _ _ _ _ BUF0) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NCB) as NB. rewrite u16s_length, length_map in NB.
assert (P2 : 32 <= 2^tl <= 4096).
{ Local Ltac2 Set LiaHints.tbl := fun () => "01S0>10781403858.6911046723646.7811491562097.8011622788908.7912016405382.6713061480274.8014237910487.7814344564414.7715045097248.6917313728113.801733665624.81 1744646265.69 17633598892.7717734619607.8018434612386.7919605464236.6820784203991.7722163107130.7723663395372.8024284429257.6924630998586.7525711131602.77259870074.69  2599566312.81 28251215826.7728288724648.6928994804584.6930196181434.8031946920049.783216443911.75 3216443911.77 3216443911.78 3216443911.79 3216443911.80 32651489978.793274817021.68 3299130737.77 33680001082.7734797494257.6935212070529.8135278693467.6936313996657.7737317581271.8038209628588.7738503264702.7539308953552.6539371410135.7539879683282.7540437312978.7840825509068.6941415891836.6342132435540.6442547251747.8342560149147.6542764144210.7842831019478.7944054420798.8044319248497.7944538507633.7845221239098.7745457187060.6345833747067.8346787787121.754828536023.78 48394734674.7948583643552.7948635769742.7950246044844.7750552041877.6951144367575.7951261860670.8051480017111.7751508994135.6454256680510.795597182636.75 56256852268.78563227834.78  5635726270.77 56813015230.7857745675194.8058827657960.6959314923118.6559361912177.7759849776017.8160159124953.6861237818317.7961896502994.7762278264748.7862380487789.6962907701586.8062973644631.6963186903767.7764403865340.6364794602131.796701218494.77 68305851436.807612119637.71 8583720762.78 9911230265.69 00000400=00A00E00I00R00V00_00c00g00o01701;01?01H01P01T01Y01]01e01j02302702;02D02K02R02W02[02_02c02g02k02o03403<03@03E03I03J03Q03U03Y03]03f03m04104:04C04G04K04f04n05605?05D05M05Q05U05Z05b05i05m06106:06>06G06K06V06Z06c06g06o07807<07@07E07N07W07\07`07j07n08508@08D08M08Q08U08^08f08j09209609?09C09K09P09WS2NBS4SEPN2NBS2NBS2HBS2NBS4SEPB2NBS2NBS4SEPN2NBS2NBS2NBS3MSV2NBS3MSV2NBS2HBS2NBS4SEPN2NBS3TLR2NBS2NBS3RSPS2HBS3TLR2NBS3RSPS4SEPB2NBS2NBS2NBS4SEPB2NBS2NB2P2S2NB2P2S3RSPS2NBS2NBS2NBS2NBS2NBS2NBS3RSPS3MSV2NBS2NBS3RSPS2NBFS2TL2NBS2NBS2NBS2HBS4SEPN2NBS2LO2NBS2NBS4SEPB2NBS4SEPB2NBS2NBS2NBS2TL4SEPB4SEPN5SEPBN3TLR2NBS3MSV2NBS3MSV2NBS4SEPB2NBS3RSPS4SEPN2NBS2NBS2NBS3RSPS3TLR2NBS2NB2P2S2NBS2NBS4SEPB2NBS2HBS4SEPB2NBS2HBS2TL3TLR2NBS2NBS4SEPN2NBS2NBS3MSV2NBS4SEPN2NBS2HBS2HBS3RSPS4SEPN2NBS4SEPN2NBS3RSPS2NBS3MSV2NB1KS2NBS2TL2NBS2TL3TLR2NBS2NBS4SEPB2NBS2HBS2NBS4SEPB2NBS3TLR2NBS2NBS3TLR2NBS2NBS4SEPN2NBS2HBS3MSV2NBS3RSPS2TL2NB".
split; [change 32 with (2^5)| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia. }
zstep. zstep. sw32 (msv + 1). zstep. zstep.
if_cases K; zify_cond K. { exfalso. lia. }
carve_frame 80%nat ST.
apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
do 11 zstep.
do 12 zstep. rewrite sllw_pow2 by lia.
zstep. zstep. rewrite (Z.mod_small asz 4294967296) by lia. zstep. zstep. rewrite lor_pow2_1 by lia. zstep. zstep.
set (s0w := mkW buf0 0 (tl - 5) 4 0 (2^tl + 1) (2^tl) (tl + 1) false) in *.
replace (tl + -5) with (tl - 5) by lia.
eapply (evt_eq psegs _ _ (WST 0x139c8 m1 (Z_to_bv 64 (w_nbBits s0w)) (Z_to_bv 64 (w_threshold s0w)) (Z_to_bv 64 (BUF + w_out s0w))
(Z_to_bv 64 (w_bitCount s0w)) (Z_to_bv 64 (tl - 5)) (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 s0w))))
(Z_to_bv 64 (w_remaining s0w)) (Z_to_bv 64 (w_symbol s0w)) s5 s6 s7 s8 s9)).
{ cbn [s0w w_nbBits w_threshold w_out w_bitCount w_previousIs0 w_remaining w_symbol negb Z.b2z].
replace (BUF + 0) with BUF by lia. reflexivity. }
eapply (wr_loop _ s0w sf); [ | | | | | exact WL | ].
- unfold winv, s0w, FseNCount.Zlength. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
change (2^32) with 4294967296. replace (tl + 1 - 1) with tl by lia. repeat split; lia.
- cbn [s0w w_symbol w_remaining]. apply andb_true_iff. split; apply Z.ltb_lt; lia.
- change (2^64) with 18446744073709551616. lia.
- cbn [s0w w_bitStream]. apply Z.mod_small. change (2^32) with 4294967296. lia.
- cbn [s0w w_buf]. unfold RF_fse_write_A.MINV, RF_fse_write_A.FRAMEC.
split; [exact BUF0|]. split; [exact NCB|]. split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
- intros m2 X' y8 y9 y18 y19 y20 y22 y23 y24 y25 WIF MV2 RX2 EX2.
eapply (wr_finish sf); [exact WIF | exact MV2 | exact RX2 | exact EX2 | exact WF].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
Lemma lxor_b2z_1 : forall b : bool, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof using Type. intros [|]; reflexivity. Qed.
Lemma wr_body : evt psegs POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BUF) (Z_to_bv 64 bsz) (Z_to_bv 64 NC) (Z_to_bv 64 msv) (Z_to_bv 64 tl)
a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFSE_WRITE) fc None m (seg_rom psegs)).
Proof using All.
unfold PFSE_WRITE.
pose proof WOK as WOK'. unfold write_ncount, FSE_MAX_TABLELOG, FSE_MIN_TABLELOG in WOK'.
destruct (Z.ltb_spec 12 tl) as [TL12|TL12]; [discriminate|].
destruct (Z.ltb_spec tl 5) as [TL5|TL5]; [discriminate|].
assert (GOK : write_ncount_generic buf0 nc msv tl (negb (FseNCount.Zlength buf0 <? write_bound msv tl)) = Ok (buf', n)).
{ destruct (FseNCount.Zlength buf0 <? write_bound msv tl); exact WOK'. }
clear WOK'. unfold FseNCount.Zlength in GOK.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>10519033705.6010915936140.6011160981061.6611556852459.6016083456460.6723284431177.6029782203372.6036401657508.6741155690197.5941162082021.6042549348909.7045876098888.6059308628304.5859314923118.5759851873177.7059854341935.5759860645905.5867176411828.677604033872.59 00000300400500B00G00T00U00V00`00j00o01001801@01D01H01L01M01RS1BSFS3MSV2TL2K21BS3BSZS3MSV2TL2K21BSFS4TL123TL5S4TL123TL5S3MSVSS3TL52K1S4TL121KS2TLS2TLS2TLSS3MSV".
if_cases K; zify_cond K; [| exfalso; lia].
zstep. zstep. if_cases K1; zify_cond K1; [| exfalso; lia].
zstep. if_cases K2; zify_cond K2.
-
do 7 zstep.
assert (B : 0 <= (msv + 1) * tl + 6 < 4294967296) by nia.
rewrite (Z.mod_small ((msv + 1) * tl + 6) 18446744073709551616) by lia.
rewrite wrap32_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite swrap32_small by lia.
rewrite (Z.mod_small (((msv + 1) * tl + 6) / 8 + 3) 18446744073709551616) by lia.
replace (((msv + 1) * tl + 6) / 8 + 3) with (write_bound msv tl).
2:{ unfold write_bound, FSE_NCOUNTBOUND. rewrite (proj2 (Z.eqb_neq msv 0) K2).
replace ((msv + 1) * tl + 4 + 2) with ((msv + 1) * tl + 6) by lia. lia. }
rewrite lxor_b2z_1. zstep.
apply (wr_main _ GOK). lia.
-
do 4 zstep.
replace 512 with (write_bound msv tl) by (unfold write_bound, FSE_NCOUNTBOUND; rewrite (proj2 (Z.eqb_eq msv 0) K2); reflexivity).
rewrite lxor_b2z_1.
apply (wr_main _ GOK). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WR.
Theorem fse_write_proof : fse_write_stmt.
Proof.
intros until lo. intros BUF0 BUFB NCB NCR WOK MSV TL BSZ _ _ _ _ _ ST LO RSP SEPB SEPN SEPBN MI -> -> -> -> ->.
unfold FSE_WRITE_STACK in *.
eapply wr_body; eassumption.
Qed.
