(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWriteModel FseWalkArith.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AF_fse_iface AF_fse_write_A.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Section CANSEC1. Context {rc : runConstT}.
Section WR.
Variables (RNG : footprint)
(ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (SP BUF NC : Z)
(buf0 buf' nc : list Z) (msv tl n lo : Z).
Hypothesis BUF0 : u8arr bsegs m BUF (map (Z_to_bv 8) buf0).
Hypothesis BUFB : Forall (fun c => 0 <= c < 256) buf0.
Hypothesis NCB : bytes_at bsegs m NC (u16s (map (Z_to_bv 64) nc)).
Hypothesis NCR : Forall (fun c => - 32768 <= c < 32768) nc.
Hypothesis WOK : write_ncount buf0 nc msv tl = Ok (buf', n).
Hypothesis MSV : 0 <= msv <= 255.
Hypothesis TL : 0 <= tl < 2^32.
Hypothesis BSZ : zlen buf0 <= 65536.
Hypothesis BUFNZ : 0 < BUF.
Hypothesis NCNZ : 0 < NC.
Hypothesis NCEV : NC mod 2 = 0.
Hypothesis ST : stk bsegs m lo SP.
Hypothesis LO : lo <= SP - 144.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis SEPB : BUF + zlen buf0 <= SP - 144 \/ SP <= BUF.
Hypothesis SEPN : NC + 2 * zlen nc <= SP - 144 \/ SP <= NC.
Hypothesis SEPBN : NC + 2 * zlen nc <= BUF \/ BUF + zlen buf0 <= NC.
Hypothesis MI : mem_inv bsegs m.
Hypothesis BLKB : ablk BUF (BUF + zlen buf0).
Hypothesis BLKN : ablk NC (NC + 2 * zlen nc).
Hypothesis BUF8 : BUF mod 8 = 0.
Hypothesis NC8 : NC mod 8 = 0.
Hypothesis KLO : KHIGH <= lo.
Hypothesis GOT : rt_got m.
Hypothesis SHB : rt_shbase m.
Hypothesis UNB : unpoisoned m BUF (BUF + zlen buf0).
Hypothesis UNN : unpoisoned m NC (NC + 2 * zlen nc).
Hypothesis RI : rng_aimg RNG.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RB : rng RNG BUF (zlen buf0).
Hypothesis RBS : rng RNG (shad BUF) (nshad (zlen buf0)).
Hypothesis RN : rng RNG NC (2 * zlen nc).
Hypothesis RNS : rng RNG (shad NC) (nshad (2 * zlen nc)).
Collection WRC := RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ BUFNZ NCNZ NCEV LO RSP SEPB SEPN SEPBN BLKB BLKN BUF8 NC8 KLO UNB UNN RI RSTK RB RBS RN RNS.
Notation POST := (fse_write_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP BUF buf0 buf' n lo m).
Notation bsz := (zlen buf0).
Notation asz := (msv + 1).
Ltac lts_lit K := unfold bv_lts in K; rewrite !signed_lit in K by lia; zify_bool K.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
Notation FRAMEC := (AF_fse_write_A.FRAMEC ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 msv).
Notation MINV := (AF_fse_write_A.MINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP BUF NC buf0 nc msv lo).
Notation A0_ l := (l RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ BUFNZ NCNZ NCEV LO RSP SEPB SEPN SEPBN BLKB BLKN BUF8 NC8 KLO UNB UNN RI RSTK RB RBS RN RNS).
Ltac minv_close BA NA FA SA MUA WMA MIA :=
split; [exact BA|]; split; [exact NA|]; split; [eexists; exact FA|]; split; [exact SA|]; split; [exact MUA|]; split; [exact WMA| exact MIA].
Section LOOP.
Variable safe : bool.
Notation A_ l := (A0_ l safe).
Notation BST pc mm x8 x10 x11 x13 x14 x17 x20 x22 x26 x27 x28 x29 x30 x31 :=
(MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 2147450880) (Z_to_bv 64 asz)
x8 (Z_to_bv 64 0) x10 x11 (Z_to_bv 64 NC) x13 x14 (Z_to_bv 64 (Z.b2z safe)) (Z_to_bv 64 BUF) x17
(Z_to_bv 64 (18446744073709551615 - NC)) (Z_to_bv 64 (BUF + bsz)) x20 (Z_to_bv 64 31) x22 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3))
(Z_to_bv 64 3) x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
Ltac wrap17 := let v := reg_val 17%Z in
lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
Lemma wr_count : forall s sc sd m1 X (x10 x13 x14 x20 x22 x28 x30 : word),
winv asz bsz s -> w_symbol s < asz -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s -> MINV m1 (w_buf s) ->
wcount_block nc s = Ok sc -> wflush_if bsz safe sc = Ok sd ->
(forall m2 X' (y10 y14 y20 y22 y27 y30 : word), (w_symbol sd <? asz) && (1 <? w_remaining sd) = true ->
MINV m2 (w_buf sd) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sd ->
evtF bsegs RNG POST (BST 0x816cc m2 (Z_to_bv 64 (w_remaining sd)) y10 (Z_to_bv 64 (BUF + w_out sd))
(Z_to_bv 64 (Z.b2z (negb (w_previousIs0 sd)))) y14 (Z_to_bv 64 X') y20 y22 (Z_to_bv 64 (w_threshold sd))
y27 (Z_to_bv 64 (w_symbol sd)) (Z_to_bv 64 (w_bitCount sd)) y30 (Z_to_bv 64 (w_nbBits sd)))) ->
(forall m2 X' (y10 y13 y14 y20 y22 y26 y27 y28 y30 y31 : word), (w_symbol sd <? asz) && (1 <? w_remaining sd) = false ->
MINV m2 (w_buf sd) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sd ->
evtF bsegs RNG POST (BST 0x81a2c m2 (Z_to_bv 64 (w_remaining sd)) y10 (Z_to_bv 64 (BUF + w_out sd)) y13 y14 (Z_to_bv 64 X') y20 y22 y26
y27 y28 (Z_to_bv 64 (w_bitCount sd)) y30 y31)) ->
evtF bsegs RNG POST (BST 0x81890 m1 (Z_to_bv 64 (w_remaining s)) x10 (Z_to_bv 64 (BUF + w_out s)) x13 x14 (Z_to_bv 64 X) x20 x22
(Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (w_symbol s)) x28 (Z_to_bv 64 (w_bitCount s)) x30 (Z_to_bv 64 (w_nbBits s))).
Proof using WRC.
intros s sc sd m1 X x10 x13 x14 x20 x22 x28 x30 WI SYA RX EX MV CB FL KL KE.
pose proof WI as (LB & RO & RBt & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & [junk8 FA] & SA & MUA & WMA & MIA). unfold AF_fse_write_A.FRAMEC in FA.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof (ablk_lin _ _ BLKN) as LN. pose proof (ablk_lin _ _ BLKB) as LBK. unfold KHIGH, AIMG_HI in *.
destruct (A0_ inv_shadow _ MUA) as [_ UN1].
pose proof (wcount_flush_facts nc asz bsz safe s sc sd CB FL WI SYA NCR) as (WID & SYD & CTL).
pose proof (wcount_block_inv nc s sc CB) as CI. cbv zeta in CI. destruct CI as (thr' & nb' & LR & BCR & R1 & SHR & ESC).
unfold FseNCount.Zlength in LR.
pose proof (Forall_Znth _ _ (w_symbol s) NCR LR) as CR. cbv beta in CR.
set (count := Znth (w_symbol s) nc) in *.
set (rem' := w_remaining s - (if count <? 0 then - count else count)) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0380?10088275704.167101404446.155  11149532066.15511605658482.13212326019099.15913070568592.16413071252774.16314210624796.15314362626257.2251496497253.169 15581734044.13115640690308.15915641300924.16016011609646.15516220248490.13216344464487.14816344464487.15316845815291.16017316818848.16817316818851.17117316818852.16817316818852.17017316818853.16817316818853.17017316818854.17417316818862.16717322642469.15019122513057.13719489965100.16719618399908.18319618399908.18519628467489.15319845525539.15520290755674.16221444785427.13822131842618.15822448268900.16023740125337.13623746424098.15023746424227.15125894145885.15426832177436.1572688573304.156 28707550835.17329646625990.19529782367974.17329782367974.18029782367974.18430047557315.16431139597467.15131145898401.15231183134347.1583214378781.160 3214378781.164 32313870464.1583405217491.164 34497014984.15535206187911.16535212070535.16236145266549.15236202861644.15436202861644.15636441195080.17936441195080.18337424340807.16337497742200.15537497742200.15937780117686.16738954701265.14939124915372.15439159981841.15839572309083.22139721191329.15440244715328.15340829096497.20241415991886.13241422282358.13141730628386.15641962099515.15741968874935.16641968874939.17842132582609.15542132582867.16542132828756.15142132828885.15042134123218.15442134701907.15242134702548.15942558040485.15342637760174.15843342475915.14943366962096.15743467007921.1534399294143.155 44478585536.15444478585536.15544927972769.17044927972772.16944927972775.16645589988655.15845590082573.15645590082700.16045590083339.16545596907402.17745596907402.17947160934811.15247171887386.18147428594747.16747788875075.16247826599073.15247828435871.15648613897335.17848725293998.15148725325126.18049170713844.164492328663.158  49423367528.16050986760084.15551818759664.16452074235539.17152074235540.1705222230152.162 52525112630.16753508216724.17153508216726.16753728626131.16654284662033.12954309134369.17054309134372.16954309134375.16654320121386.16054375738212.15654475752564.16155489968753.16355590205916.15255894028037.15355935222439.16956736913462.18256862664155.20257237357528.16558061619888.15359310676440.20259310676568.22159310676568.22559314873579.14959314873579.15059314873579.15159314873579.15259314873579.15359314873579.15459314873579.15659314873579.15759314873579.15859314873579.15959314873579.16159314873579.16659426274467.14859437227814.16659437227814.16859437227814.17459437227814.17659588178615.16760245107413.16961165640298.15561286691612.1566168199299.150 6168200069.148 61814822930.15363986878663.15564407683373.17964407683373.18364407683375.17264794109999.16364799663456.16064821634246.17164899638539.16766149329422.18666638920312.1716758013062.156 67945040387.13868017740606.17968017740606.18368189636813.17968189636813.18368189636815.1727647152021.137 8401265577.155 8470943414.152 8601353904.159 8929201440.151 8929347755.157 8935173669.168 8935173670.167 8935173671.166 8935173675.178 913132285.164  9448783535.221 9448783535.225 9544766530.153 9581028844.164 00000400e01_01e02c02m03703;03C03D03L03V03`04^04f05d05k06l07707>07F07M07U07\08Z09T09[0:?0;R0<H0=>0><0>D0>K0?B0?I0@<0A90A]0BA0BI0Bm0D60E60F80F<0F@0FD0GE0GM0GU0HV0IW0J[0Jb0Jf0Jm0Kn0Ko0L80L<0L@0LA0LB0LF0LN0LV0LZ0L^0Lh0N40N<0NC0OC0OJ0ON0OR0OV0O]0O^0O_0Ph0Qi0R\0SO0TX0UO0V\0Vd0Vk0WX0X<0XC0XJ0XT0X^0X_0X`0Xa0YW0ZM0[F0\?0]50]k0^70^@0^A0_B0_J0_R0`X0aO0bS0cQ0dJ0e90e@0eo0g30h70h>0hB0hF0hJ0hN0hV0hW0hX0hY0h`0hd0ie0ii0jk0k50k60l:0lN0lW0l`0mX0nZ0oe10[10b11511<11H11R11]12V12]12g13^14R15E16;17117g18]18a18b19S19[1:E1:l1;31;=1<N1=_1>g1@71A51B91Bb1Cd1Ce1Ci1D`1Da1Db1Dc1Dd1De1Dl1E31E71E>1F81F91G01Gg1Gh1Gi1Gm1H:1HN1HR1IES2NBS5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2RM3NBI2NB3NB'3RMX2G1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RX32E1S2NB1HS5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2RM3NBI2TH2NB2CR3NB'3RMX2G12J13EC2S2RO2NB2O1S2RO2NB2O1S2NBS2NB3SR2FS3NBI2NBS2RO2NB2O1S2RO2NB2O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RC23RX32N1S3NBI2NBS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN3SYA2RX2LB2BC2SY3NBI2NB2LR3NB'S2RM2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S2BC2NB3NBIS2RM2NBS2NB3THRS2RM2NBS2NB3THRS2BC2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2SY3NBI2NB2LN3LBK2LR3NB'3RX3S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2SY3NBI2NB2LN3LBK2LR3NB'S2BC2NBS5BUFNZ4NCNZ2RX2BC3NBI2NB2CR3NB'3RMXS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2NB3LBK2LR3NB'3RB13RX12O02O12G12G23CK2S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3LBK3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3LBK3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2SY3NBI2NB2LN3LBK2LR3NB'3RX3S3NBI2NBS2LO2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3BCR3NB'S2NB2J1S5BUFNZ4NCNZ2LO3KLO2RX2BC3NBI2NB3LBK3NB'3RB13RX12O0S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2RM3NBI2TH2NB2LR3NB'3THRS5BUFNZ4NCNZ2RX2BC3NBI2NB3BCR3NB'2H1S5BUFNZ4NCNZ2RX2BC3NBI2NB3BCR3NB'2H1S2NB3THRS5BUFNZ4NCNZ2RX2BC2RM3NBI2NB3NB'3RMXS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2BC3NBI2NB2LN3SYD2LR3NB'2G1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2BC3NBI2NB2LN2LR3NB'2G1S4NCNZ4NCEV4SEPB4SEPN5SEPBN2LB2BC3NBI2NB3SYD2LR3NB'2G12G31H2H03H24S2NBS2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S2NB3RC2S2NB3RC2S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC3NBI2NB3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC3NBI2NB2LR3NB'3RB13RX12O02O1S2RO2NBS2NBS2NB2J1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1FS2NB4RBC1S2NBS2NBFFS2NBS2NB3THRS2NB3THRS2NBS2NBS2NB2R12RRS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2NB2LN3SYD2LR3NB'2G12G32CKS2NB3SR1S2NB2J1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2BC3NBI2NB2LN2LR3NB'2G1S2NB2SRS2NBS2NBS2NBS2NB2G7FFS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2BC3NBI2NB2LN3SYD2LR3NB'2G1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'S5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2BC3NBI2NB2LN3SYD2LR3NB'2G1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RX3S5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2BC3NBI2NB2LN3SYD2LR3NB'3RMX2G1S3MSV2NBS2NB2J1S5BUFNZ4NCNZ2LO3KLO2RX2LB2BC3NBI2NB2LN3NB'2G1S5BUFNZ4NCNZ2RX2BC2RM3NBI2NB3NB'3RMXS2NB2CRS2NB2J1S2NB2R12RRS2NB2R12RRFFFS5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3LBK3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3LBK3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3LBK3NB'3RB13RX12O02O12LRS5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3LBK2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3LBK3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3LBK3NB'3RB13RX12O02O1S2NB2H34RBC1S2NB4RBC1FS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S2NB3RMXS2NB3RMXS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2TH2NB2LN2LR2CR3NB'2G12J1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RC2S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC3NBI2NB2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3LBK2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2RX2LB2BC3NBI2NB3LBK3NB'3RB13RX12O1S2NB2J1S5BUFNZ4NCNZ2RX2LB2BC3NBI2NB3LBK3NB'3RB13RX12O1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2TH2NB2LN2LR3NB'3THR2G1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2TH2NB2LN2LR3NB'3THR2G1S2RO2NBS2NBS2NBS2NBS2NBS3NBI2NBFFFS2NB2G8S2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S2NBS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN3SYA2RX2LB2BC2SY3NBI2NB2LR3NB'3RX3S2NB2R12RRFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC3NBI2NB2LR3NB'3RB13RX12O02O1S4NCNZ2NB2G32CK1G2H0S2NB4RBC1S2NB4RBC1S4NCNZ4SEPB4SEPN5SEPBN2LB2BC3NBI2NB2LR3NB'2G12G32CK1G2G'S2LO4SEPB4SEPN5SEPBN3KLO2LB2BC3NBI2NB3LBK2LR3NB'2O02O12G13CK11G2G'S2LO4SEPB4SEPN5SEPBN3KLO2LB2BC3NBI2NB3LBK2LR3NB'2O02O12G12G23CK22G43G4'3H39S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'2G1S2NB2G2S2NB3BCR2H14NCNZ2G3S2NB2H2S2NB1G2J32H3S2NB2R12J0S2NB3THR2G5S5BUFNZ4NCNZ2LO3KLO2RX2BC3NBI2NB3LBK3NB'3RB13RX12O02G12G6S2NB2G7S2NB2OE2BOS5BUFNZ4NCNZ2RX2LB2BC3NBI2NB3LBK3NB'3RB13RX12O12G21H2G8S5BUFNZ4NCNZ2RX2LB2BC3NBI2NB3LBK3NB'3RB13RX12O12G31HS5BUFNZ4NCNZ2LO4SEPN3KLO2RX2LB3NBI2NB2LN3LBK2LR3NB'S5BUFNZ4NCNZ2LO4SEPN3KLO2RX2LB3NBI2NB2LN3LBK2LR3NB'2G1S5BUFNZ4NCNZ2LO4SEPN3KLO2RX2LB3NBI2NB2LN3LBK2LR3NB'2G1S5BUFNZ4NCNZ2LO4SEPN3KLO2RX2LB3NBI2NB2LN3LBK2LR3NB'2G1S5BUFNZ4NCNZ2LO4SEPN3KLO2RX2LB3NBI2NB2LN3LBK2LR3NB'2G1S2NBFS5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2RM3NBI2NB3NB'3RMX2G1S2NB3THRS5BUFNZ4NCNZ2RX2LB3NBI2NB2LN3LBK2LR3NB'2G1S5BUFNZ4NCNZ2RX2LB3NBI2NB2LN3LBK2LR3NB'S2NB2G1S2NB2R12J2S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC3NBI2NB3LBK2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC3NBI2NB3LBK2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3NC83KLO2RX2LB2RO2BC3NBI2NB2LN3SYD2LR3NB'S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2NB3LBK2LR3NB'3RB13RX12O02O12G13CK1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2TH2NB2LN2LR3NB'3THR2G1S5BUFNZ4NCNZ2RX2BC3NBI2NB3NB'3RB13EX13RX1S4NCNZ4NCEV4SEPB4SEPN5SEPBN2LB2BC3NBI2NB3SYD2LR3NB'2G12G31H2H03H19FS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3BCR3NB'FFFFFS2NB2CRS2NB2J2S2NBS2NB2CRS2NB2H25BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB3NBI2LR3BCR3NB'2H1FS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB3NBI2NB2LR3BCR3NB'2H1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB3NBI2NB2LR3BCR3NB'2H1FFS2NBS2NB3CK11G2H0S2NB2G12G23CK22G42H0S2NBS5BUFNZ4NCNZ2LO3KLO2RX2BC3NBI2NB3LBK3NB'3RB13RX12O0".
pose proof (shrink_facts _ _ _ _ _ _ SHR R1 ltac:(lia) TH) as (NB' & TH').
assert (THR : 1 <= w_threshold s <= 4096).
{ rewrite TH. pose proof (Z.pow_pos_nonneg 2 (w_nbBits s - 1) ltac:(lia) ltac:(lia)). split; [lia|]. change 4096 with (2^12). apply Z.pow_le_mono_r; lia. }
pose proof (u16_znth bsegs m1 NC nc (w_symbol s) (Z_to_bv 64 (NC + 2 * w_symbol s)) NA LR ltac:(reflexivity)) as RD.
set (mx := 2 * w_threshold s - 1 - w_remaining s) in *.
set (count2 := if w_threshold s <=? count + 1 then count + 1 + mx else count + 1) in *.
set (bs1 := u32 (w_bitStream s + u32 (u32 count2 * 2 ^ w_bitCount s))) in *.
set (bc1 := w_bitCount s + w_nbBits s - (if count2 <? mx then 1 else 0)) in *.
assert (RMX : - 8192 <= mx <= 8192) by (subst mx; lia).
assert (RC2 : - 50000 <= count2 < 50000) by (subst count2; destruct (w_threshold s <=? count + 1); lia).
assert (RBC1 : 0 <= bc1 <= 44) by (subst bc1; destruct (count2 <? mx); lia).
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
destruct CTL as (CT1 & CT2 & CT3 & CT4). rewrite ESC in CT1, CT2, CT3, CT4.
cbn [w_remaining w_threshold w_nbBits w_previousIs0] in CT1, CT2, CT3, CT4.
assert (RR : 1 <= rem' <= 8192) by (rewrite <- CT1; destruct WID as (_ & _ & _ & _ & _ & RQ & _); exact RQ).
assert (TAIL : forall m2 X3 (y10 y13 y30 : word), MINV m2 (w_buf sd) -> 0 <= X3 < 2^64 -> X3 mod 2^32 = w_bitStream sd ->
evtF bsegs RNG POST (BST 0x819cc m2 (Z_to_bv 64 rem') y10 (Z_to_bv 64 (BUF + w_out sd)) y13 (Z_to_bv 64 count2) (Z_to_bv 64 X3)
(Z_to_bv 64 count) x22 (Z_to_bv 64 thr') (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 bc1)
(Z_to_bv 64 (w_bitCount sd)) y30 (Z_to_bv 64 nb'))).
{ intros m2 X3 y10 y13 y30 MV2 RX3 EX3.
zstep. sw32 (w_symbol s + 1). zstep.
if_cases J1; zify_cond J1.
- rewrite <- CT1.
apply KE; [ | exact MV2 | exact RX3 | exact EX3].
rewrite SYD. replace (w_symbol s + 1 <? asz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- zstep. zstep.
replace (0 <? (count2 + -1) mod 18446744073709551616) with (negb (count2 =? 1)).
2:{ destruct (Z.eqb_spec count2 1) as [E1|N1]; cbn [negb]; symmetry; [apply Z.ltb_ge| apply Z.ltb_lt]; lia. }
zstep. zstep.
if_cases J2; zify_cond J2.
+ rewrite <- CT1, <- CT2, <- CT3, <- CT4, <- SYD.
apply KL; [ | exact MV2 | exact RX3 | exact EX3].
rewrite SYD, CT1. replace (w_symbol s + 1 <? asz) with true by (symmetry; apply Z.ltb_lt; lia).
replace (1 <? rem') with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+ rewrite <- CT1. zstep.
apply KE; [ | exact MV2 | exact RX3 | exact EX3].
rewrite CT1. replace (1 <? rem') with false by (symmetry; apply Z.ltb_ge; lia). apply andb_false_r. }
assert (P70 : forall (y10 y30 : word), evtF bsegs RNG POST
(BST 0x81960 m1 (Z_to_bv 64 rem') y10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 count2) (Z_to_bv 64 count2) (Z_to_bv 64 X)
(Z_to_bv 64 count) x22 (Z_to_bv 64 thr') (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 bc1) (Z_to_bv 64 (w_bitCount s)) y30 (Z_to_bv 64 nb'))).
{ intros y10 y30.
zstep. zstep.
pose proof (container_add X (w_bitStream s) count2 (w_bitCount s) BCR EX) as EX1. fold bs1 in EX1.
assert (RX1 : 0 <= (bv_swrap 32 (Z.shiftl (count2 mod 18446744073709551616) (w_bitCount s mod 32)) + X) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap17. revert EX1 RX1. generalize ((bv_swrap 32 (Z.shiftl (count2 mod 18446744073709551616) (w_bitCount s mod 32)) + X) mod 2^64). intros X1 EX1 RX1.
zstep. zstep.
pose proof FL as FL'. rewrite ESC in FL'. apply wflush_if_inv in FL'. cbn [w_bitCount] in FL'.
if_cases J3; lts_lit J3.
-
destruct FL' as [[G _]|[_ ESD]]; [exfalso; lia|]. subst sd.
zstep.
eapply TAIL; [cbn [w_buf]; exact MV | exact RX1 | cbn [w_bitStream]; exact EX1].
- destruct FL' as [[_ FLH]|[G _]]; [| exfalso; lia].
apply wflush_inv in FLH. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FLH.
destruct FLH as (OE & O0 & O1 & ESD). unfold FseNCount.Zlength in O1. subst sd.
pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof SA as (LO0 & _ & _).
assert (FLUSH : evtF bsegs RNG POST
(BST 0x8197c m1 (Z_to_bv 64 rem') (Z_to_bv 64 17) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 count2) (Z_to_bv 64 count2) (Z_to_bv 64 X1)
(Z_to_bv 64 count) x22 (Z_to_bv 64 thr') (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 bc1) (Z_to_bv 64 (w_bitCount s)) y30 (Z_to_bv 64 nb'))).
{ zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
destruct (A0_ inv_shadow _ MUA) as [UB1 _].
destruct (A0_ chk_out m1 (BUF + w_out s) UB1 ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN1 : forall (y10 y13 : word), evtF bsegs RNG POST
(BST 0x81990 m1 (Z_to_bv 64 rem') y10 (Z_to_bv 64 (BUF + w_out s)) y13 (Z_to_bv 64 count2) (Z_to_bv 64 X1)
(Z_to_bv 64 count) x22 (Z_to_bv 64 thr') (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 bc1) (Z_to_bv 64 (w_bitCount s)) y30 (Z_to_bv 64 nb'))).
{ intros y10' y13. clear RDB1 CK1 SR1 b1.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep.
destruct (A0_ inv_shadow _ MUA) as [UB2 _].
lazymatch type of UB2 with unpoisoned ?mm _ _ =>
destruct (A0_ chk_out mm (BUF + w_out s + 1) UB2 ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2) end.
zstep. zstep. zstep. rewrite sxb_sval.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JOIN2 : forall (z10 z29 : word), evtF bsegs RNG POST
(BST 0x819ac mm (Z_to_bv 64 rem') z10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s + 1)) (Z_to_bv 64 count2) (Z_to_bv 64 X1)
(Z_to_bv 64 count) x22 (Z_to_bv 64 thr') (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 bc1) z29 y30 (Z_to_bv 64 nb'))) end.
{ intros z10 z29. clear RDB2 CK2 SR2 b2.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. change (2^8) with 256. lia. }
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
zstep. zstep. sw32 (bc1 + -16).
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep.
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
setreg 11%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
replace (bc1 + -16) with (bc1 - 16) by lia.
eapply TAIL; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA
| change (2^32) with 4294967296 in RB3; change (2^64) with 18446744073709551616; lia
| cbn [w_bitStream]; apply Z.mod_small; exact RB3 ]. }
zstep. if_cases G4; zify_cond G4.
+ zstep. zstep. if_cases G4'; zify_lts G4'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN2.
+ apply JOIN2. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN1.
+ apply JOIN1. }
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
+ rewrite (ite_true _ safe _ _ SAFE). apply FLUSH.
+ apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
destruct OE as [OE|OE]; [congruence|].
zstep. if_false. zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply FLUSH. }
assert (P1C : forall (y10 y14 y30 : word), evtF bsegs RNG POST
(BST 0x8190c m1 (Z_to_bv 64 (w_remaining s)) y10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 count2) y14 (Z_to_bv 64 X)
(Z_to_bv 64 count) x22 (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 mx) (Z_to_bv 64 (w_bitCount s)) y30
(Z_to_bv 64 (w_nbBits s)))).
{ intros y10 y14 y30.
zstep. if_cases H1; zify_cond H1; [exfalso; lia|].
zstep. zstep. sw32 (w_bitCount s + w_nbBits s).
zstep. if_cases H2; zify_cond H2; [exfalso; lia|].
zstep. sw32 (w_bitCount s + w_nbBits s). zstep. sw32 count2.
zstep. rewrite slt_lit_rr by lia.
zstep. rewrite (zb_b2z_if (count2 <? mx)). fold bc1. rewrite (FseWalkKit.swrap32_small bc1) by lia.
zstep. fold bc1.
zstep. if_cases H3; zify_cond H3; [exfalso; lia|].
zstep. rewrite sraiw31_sign by lia.
zstep. zstep. zstep. rewrite abs_via_sign by (fold rem'; lia). fold rem'.
zstep. if_cases J0; lts_lit J0; [exfalso; lia|].
zstep.
if_cases J1; lts_lit J1.
-
rewrite shrink_S in SHR. replace (rem' <? w_threshold s) with false in SHR by (symmetry; apply Z.ltb_ge; lia).
injection SHR as <- <-. apply P70.
- eapply (A_ wr_shrink 63%nat rem' (w_threshold s) (w_nbBits s) thr' nb'); [lia | lia | lia | exact TH | exact SHR | ].
intros y10'. apply P70. }
zstep. zstep. rewrite zext32_sh31 by lia. zstep.
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. zstep. zstep.
replace (NC + 2 * w_symbol s <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. change (Z.lxor 1 0) with 1.
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
zstep. rewrite land_1_mod2.
assert (EV : (NC + 2 * w_symbol s) mod 2 = 0) by (Z.div_mod_to_equations; lia).
zstep. if_cases G4; zify_cond G4; [exfalso; apply G4; exact EV|].
destruct (unpoisoned_check_rd bsegs m1 NC (NC + 2 * zlen nc) (NC + 2 * w_symbol s) 2 UN1 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK).
unfold shad, ASHOFF in RDB. replace (2147450880 + Z.shiftr (NC + 2 * w_symbol s) 3) with (Z.shiftr (NC + 2 * w_symbol s) 3 + 2147450880) in RDB by lia.
pose proof (sval_range b) as SR.
zstep. zstep. zstep. rewrite sxb_sval.
assert (CHKD : forall (y10 y14 : word), evtF bsegs RNG POST
(BST 0x818cc m1 (Z_to_bv 64 (w_remaining s)) y10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (NC + 2 * w_symbol s)) y14 (Z_to_bv 64 X)
x20 x22 (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (w_symbol s)) x28 (Z_to_bv 64 (w_bitCount s)) x30 (Z_to_bv 64 (w_nbBits s)))).
{ intros y10 y14. clear RDB CK SR b.
zstep. zstep. sw32 (w_threshold s + 1073741824).
zstep. if_cases G5; lts_lit G5; [exfalso; lia|].
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2. sw32 (w_threshold s * 2).
zstep. sw32 (w_threshold s * 2 + -1).
zstep. if_cases G6; lts_lit G6; [exfalso; lia|].
zstep. sw32 mx. zstep. setreg 14%Z (Z_to_bv 64 mx) ltac:(f_equal; subst mx; lia).
zstep. if_cases G7; zify_cond G7; [exfalso; lia|].
zstep. fold count. rewrite sx16_short by exact CR.
zstep. zstep.
if_cases J1; lts_lit J1.
-
assert (EC2 : count2 = count + 1) by (subst count2; replace (w_threshold s <=? count + 1) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
rewrite <- EC2. apply P1C.
- assert (EC2 : count2 = count + 1 + mx) by (subst count2; replace (w_threshold s <=? count + 1) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
zstep. zstep. sw32 (count + 1 + mx).
zstep. if_cases G8; zify_cond G8; [exfalso; lia|].
zstep. rewrite <- EC2. apply P1C. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply CHKD.
+ apply CHKD.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
End WR.
End CANSEC1.
