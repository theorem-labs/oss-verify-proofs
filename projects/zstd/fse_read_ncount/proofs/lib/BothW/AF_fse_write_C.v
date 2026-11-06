(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWriteModel FseWalkArith.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AF_fse_iface AF_fse_write_A AF_fse_write_B AF_fse_write_B2.
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
Notation W := [(BUF, BUF + bsz); (SP - 144, SP)].
Ltac lts_lit K := unfold bv_lts in K; rewrite !signed_lit in K by lia; zify_bool K.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
Notation FRAMEC := (AF_fse_write_A.FRAMEC ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 msv).
Notation MINV := (AF_fse_write_A.MINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP BUF NC buf0 nc msv lo).
Notation A0_ l := (l RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ BUFNZ NCNZ NCEV LO RSP SEPB SEPN SEPBN BLKB BLKN BUF8 NC8 KLO UNB UNN RI RSTK RB RBS RN RNS).
Section LOOP.
Variable safe : bool.
Notation A_ l := (A0_ l safe).
Notation BST pc mm x8 x10 x11 x13 x14 x17 x20 x22 x26 x27 x28 x29 x30 x31 :=
(MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 2147450880) (Z_to_bv 64 asz)
x8 (Z_to_bv 64 0) x10 x11 (Z_to_bv 64 NC) x13 x14 (Z_to_bv 64 (Z.b2z safe)) (Z_to_bv 64 BUF) x17
(Z_to_bv 64 (18446744073709551615 - NC)) (Z_to_bv 64 (BUF + bsz)) x20 (Z_to_bv 64 31) x22 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3))
(Z_to_bv 64 3) x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
Lemma wr_loop : forall f s sf m1 X (x10 x14 x20 x22 x27 x30 : word),
winv asz bsz s -> (w_symbol s <? asz) && (1 <? w_remaining s) = true -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
MINV m1 (w_buf s) ->
wloop nc asz bsz safe f s = Ok sf ->
(forall m2 X' (y10 y13 y14 y20 y22 y26 y27 y28 y30 y31 : word), winv asz bsz sf -> MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evtF bsegs RNG POST (BST 0x81a2c m2 (Z_to_bv 64 (w_remaining sf)) y10 (Z_to_bv 64 (BUF + w_out sf)) y13 y14 (Z_to_bv 64 X') y20 y22 y26
y27 y28 (Z_to_bv 64 (w_bitCount sf)) y30 y31)) ->
evtF bsegs RNG POST (BST 0x816cc m1 (Z_to_bv 64 (w_remaining s)) x10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 s))))
x14 (Z_to_bv 64 X) x20 x22 (Z_to_bv 64 (w_threshold s)) x27 (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_bitCount s)) x30
(Z_to_bv 64 (w_nbBits s))).
Proof using WRC.
induction f as [|f IH]; intros s sf m1 X x10 x14 x20 x22 x27 x30 WI CND RX EX MV WL K; [cbn in WL; discriminate|].
rewrite wloop_S in WL. rewrite CND in WL. apply bind_inv in WL. destruct WL as (fl & WB & WL).
apply andb_true_iff in CND. destruct CND as [CS CR]. apply Z.ltb_lt in CS. apply Z.ltb_lt in CR.
unfold wbody in WB. apply bind_inv in WB. destruct WB as (fl0 & ZB & WB).
assert (CNT : forall sa m2 X2 (y10 y13 y14 y20 y22 y28 y30 : word), fl0 = Cont sa -> winv asz bsz sa -> w_symbol sa < asz -> same_ctl s sa ->
MINV m2 (w_buf sa) -> 0 <= X2 < 2^64 -> X2 mod 2^32 = w_bitStream sa ->
evtF bsegs RNG POST (BST 0x81890 m2 (Z_to_bv 64 (w_remaining s)) y10 (Z_to_bv 64 (BUF + w_out sa)) y13 y14 (Z_to_bv 64 X2) y20 y22
(Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (w_symbol sa)) y28 (Z_to_bv 64 (w_bitCount sa)) y30 (Z_to_bv 64 (w_nbBits s)))).
{ intros sa m2 X2 y10 y13 y14 y20 y22 y28 y30 -> WIA SYA (C1 & C2 & C3 & C4) MV2 RX2 EX2.
apply bind_inv in WB. destruct WB as (sc & CB & WB). apply bind_inv in WB. destruct WB as (sd & FL & WB). injection WB as <-.
pose proof (wcount_flush_facts nc asz bsz safe sa sc sd CB FL WIA SYA NCR) as (WID & SYD & CTL).
rewrite <- C1, <- C2, <- C3.
eapply (A_ wr_count sa sc sd); [exact WIA | exact SYA | exact RX2 | exact EX2 | exact MV2 | exact CB | exact FL | | ].
- intros m3 X3 z10 z14 z20 z22 z27 z30 CND3 MV3 RX3 EX3.
eapply (IH sd sf); [exact WID | exact CND3 | exact RX3 | exact EX3 | exact MV3 | exact WL | exact K].
- intros m3 X3 z10 z13 z14 z20 z22 z26 z27 z28 z30 z31 CND3 MV3 RX3 EX3.
destruct f as [|f']; [cbn in WL; discriminate|]. rewrite wloop_S in WL. rewrite CND3 in WL. injection WL as <-.
apply K; assumption. }
destruct (w_previousIs0 s) eqn:P0; cbn [negb Z.b2z].
-
zstep. zstep. if_true.
pose proof (wzero_block_facts nc asz bsz safe s fl0 ZB WI CS) as ZF.
eapply (A_ wr_zero s fl0); [exact WI | exact CS | exact RX | exact EX | exact MV | exact ZB | | ].
+ intros sa m2 X' y10 y13 y14 y20 y22 y28 y30 -> MV2 RX2 EX2. destruct ZF as (WIA & CTL & SYA & _).
Local Ltac2 Set LiaHints.tbl := fun () => "00:0?15945006900.1201741865947.120 22621431600.11526101251834.12031838394669.12034108802189.12046794069766.12054288075689.1205433691949.120 64374068605.12000000100600;00@00D00O00S00[00_00dSS3MSVS3SYAS3RB0S2BCS2RO3RB02BCS2ROS2RM3NBIS2RMS3NBI".
eapply (CNT sa); [reflexivity | exact WIA | lia | exact CTL | exact MV2 | exact RX2 | exact EX2].
+ intros sa y10 y13 y14 y20 y22 y27 y28 y30 ->. destruct ZF as (SYA & BUA & OUA & BSA & BCA & (C1 & C2 & C3 & C4)).
injection WB as <-. injection WL as <-.
rewrite <- OUA, <- BCA, <- C1.
apply K; [ | rewrite BUA; exact MV | exact RX | rewrite BSA; exact EX].
destruct WI as (LB & RO & RB0 & BC & SY & RM & NBI & TH).
unfold winv. rewrite BUA, OUA, BSA, BCA, SYA, C1, C2, C3. repeat split; try assumption; try lia.
-
injection ZB as <-.
zstep. zstep. if_false. zstep. zstep.
eapply (CNT s); [reflexivity | exact WI | exact CS | unfold same_ctl; repeat split | exact MV | exact RX | exact EX].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Notation FST pc mm x8 x10 x11 x12 x13 x14 x17 x20 x22 x26 x27 x28 x29 x30 x31 :=
(MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 2147450880) (Z_to_bv 64 asz)
x8 (Z_to_bv 64 0) x10 x11 x12 x13 x14 (Z_to_bv 64 (Z.b2z safe)) (Z_to_bv 64 BUF) x17
(Z_to_bv 64 (18446744073709551615 - NC)) (Z_to_bv 64 (BUF + bsz)) x20 (Z_to_bv 64 31) x22 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3))
(Z_to_bv 64 3) x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
Lemma wr_finish : forall sf m1 X (y10 y13 y14 y20 y22 y26 y27 y28 y30 y31 : word),
winv asz bsz sf -> MINV m1 (w_buf sf) -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream sf ->
wfinish bsz safe sf = Ok (buf', n) ->
evtF bsegs RNG POST (BST 0x81a2c m1 (Z_to_bv 64 (w_remaining sf)) y10 (Z_to_bv 64 (BUF + w_out sf)) y13 y14 (Z_to_bv 64 X) y20 y22 y26
y27 y28 (Z_to_bv 64 (w_bitCount sf)) y30 y31).
Proof using WRC.
intros sf m1 X y10 y13 y14 y20 y22 y26 y27 y28 y30 y31 WI MV RX EX WF.
pose proof WI as (LB & RO & RB0 & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & [junk8 FA] & SA & MUA & WMA & MIA).
pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold AF_fse_write_A.FRAMEC in FA.
pose proof (ablk_lin _ _ BLKB) as LBK. unfold KHIGH, AIMG_HI in *.
unfold wfinish in WF.
destruct (Z.eqb_spec (w_remaining sf) 1) as [R1|R1]; [| cbn in WF; discriminate]. cbn [negb] in WF.
destruct (negb safe && (bsz - 2 <? w_out sf)) eqn:CK; [discriminate|].
apply bind_inv in WF. destruct WF as (b1' & S1 & WF). apply bind_inv in WF. destruct WF as (b2' & S2 & WF).
apply store_inv in S1. destruct S1 as [O1 ->]. apply store_inv in S2. destruct S2 as [O2 ->].
unfold FseNCount.Zlength in O1, O2. rewrite Zupd_length in O2. injection WF as EB EN.
assert (STORES : forall (z10 : word), evtF bsegs RNG POST
(BST 0x81a94 m1 (Z_to_bv 64 (w_remaining sf)) z10 (Z_to_bv 64 (BUF + w_out sf)) y13 y14 (Z_to_bv 64 X) y20 y22 y26
y27 y28 (Z_to_bv 64 (w_bitCount sf)) y30 y31)).
{ intros z10.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "01i0?10103301745.14210169003235.13010292415313.17510874618225.14611052334449.14511603159087.12613070568592.12813071039912.12713132286321.14813641502800.14516833298545.14416845815291.12317264948958.14318018497.122   18579966.123   19618399910.14519618399910.14719618399915.14819717304359.12121376456769.13121376456769.13421784509941.13322850410584.1342342125137.144 23750833521.14825874552945.14728562676326.12929649045467.17029782367974.13129782367974.14129782367974.14829789957598.14330047557315.12830612494298.13531183134347.1213214378781.123 3214378781.128 32975921830.1343405217491.128 34505888990.13434782976604.14136441195080.14736441195082.14036550167505.14437424291785.12739007437868.13140885788250.13042133893843.12743512528241.14643872227792.14545003960670.14345590082573.11945590082700.12445590131725.12145590132491.12345596907402.14045596907402.14245781994147.12346400804439.1494641771472.145 46789618904.14747788875075.12648418880380.13048725325126.14449170713844.128492463347.123  49423367528.1234951779697.144 51456153637.14651456153638.14651456153638.14951492745329.14851779495256.14751818759664.12851887071601.1445222230152.126 54068232019.14654074976984.1475410806385.146 55640242158.13456557946559.14456567948472.11956736913471.14256786391833.15058921220944.13459310676440.17059310676440.17559314873579.12059314873579.12259314873579.12359314873579.12459314873579.12559314873579.13059314873579.13459314873579.13559391421809.13659531741972.13561752040220.12761756581537.13163039641456.13363046449009.14963046449011.15063374621462.13163374621462.13464407683373.14764407683375.14064799663456.12365581502065.14565829850067.1246758013062.130 68017740604.14068017740606.14768189636813.14768189636815.1407902984234.134 813866930.131  913132285.128  9448783151.170 9448783151.175 9581028844.128 9959957318.130 00000400j01201601:02B02L02V02Z02a02e03X03_03f03m04[05I05J05Q05X05_05f05j06106506906o07707;07?07C07J08=08D09709m0:c0:g0:k0:o0;60;70;80;?0;C0<N0<U0=K0=O0=V0=]0>K0?90?g0@U0AC0B10BY0C@0CG0CN0DA0DH0E>0F10F<0F`0Fd0Fk0G20G90G=0GD0Gh0Gl0H30H:0HA0HE0HL0HS0HZ0IP0IW0JB0K=0LA0M50Mf0Mm0N70N`0Ng0OU0O\0O`0Og0On0P50Pf0QW0RH0RL0RP0SV0T\0UO0US0VL0VP0VQ0VR0VS0VT0V[0Vb0Vf0W30WG0Wo0X3S2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB02BC3NBI2NBS2NB3SR2S2NBS2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2O22LB2RO3RB02BC3NBI2NB3LBK2G13CK1S2O12O22NBS2O12O22NBS2NBS2LO2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS2LO2NBS2O12NBS2O12NBS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKFS2O12NBS2BC2NBS2BC2NBS2NB2RQS2NBS2LO2NBS2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB02BC3NBI2NBS2NB3SR1S2NBS2NBS2NBS2LO2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS2LO2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O12O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O12O22LB2RO3RB03NBI2NBS2NBS2NBS2NBS2LO2NBFFS2LO2NBS2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2O22LB2RO3RB02BC3NBI2NB3LBK2G12G23CK2S2BC2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB02BC3NBI2NBS2NBS2LO2NBS2LO2NBS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2RX2O22LB2RO3RB03NBI2NB3LBKS2LO2NBS2LO2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS2BC2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O12O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS2NB3LBK2J1S5BUFNZ4NCNZ2RX2O22LB3RB03NBI2NB3LBKS2NBS2BC2NBS2BC2NBS2BC2NBS2NBS2LO2NBS5BUFNZ4NCNZ2RX2O22LB3RB03NBI2NB3LBKS2NBS2O12NBS2LO2NBS2LO2NBS2NBS2BC2NBS2BC2NBS2RM2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O12O22LB2RO3RB03NBI2NBS2NB2RQS5BUFNZ4NCNZ2LO3KLO2RX2RO3RB02BC3NBI2NB3LBKS2LO4SEPB4SEPN5SEPBN3KLO2O22LB2RO2BC3NBI2NB3LBK2G13CK11G2G'S2LO4SEPB4SEPN5SEPBN3KLO2O22LB2RO2BC3NBI2NB3LBK2G12G23CK22G43G4'3H29S5BUFNZ4NCNZ2LO3KLO2RX2RO3RB03NBI2NB3LBK2G12RM2R12J0S5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBK2J1S2NB2J2S2CK2NB2J3S5BUFNZ4NCNZ2RX2O22LB3RB03NBI2NB3LBK2G21HS2NB2G3S5BUFNZ4NCNZ2LO3KLO2RX2RO3RB02BC3NBI2NB3LBK2G4S2NB2G5S2NBS2LO2NBS2BC2NBS2BC2NBS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBK2RQS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBK2RQS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBK2RQS2NBS2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2O22LB2RO3RB02BC3NBI2NB3LBKS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2O22LB2RO3RB02BC3NBI2NB3LBKS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2EX2O22LB2RO3RB02BC3NBI2NBS2NBFFFFS2BC2NBS2BC2NBS2NBS2NB3CK11G2H0S2NB2G12G23CK22G42H0S5BUFNZ4NCNZ2LO3KLO2RX2RO3RB03NBI2NB3LBKS2NB".
if_cases G1; zify_cond G1; [exfalso; lia|].
destruct (A0_ inv_shadow _ MUA) as [UB1 _].
destruct (A0_ chk_out m1 (BUF + w_out sf) UB1 ltac:(lia) ltac:(lia)) as (c1 & RDB1 & CK1 & SR1).
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN1 : forall (v10 v12 : word), evtF bsegs RNG POST
(FST 0x81aa8 m1 (Z_to_bv 64 (w_remaining sf)) v10 (Z_to_bv 64 (BUF + w_out sf)) v12 y13 y14 (Z_to_bv 64 X) y20 y22 y26
y27 y28 (Z_to_bv 64 (w_bitCount sf)) y30 y31)).
{ intros v10 v12. clear RDB1 CK1 SR1 c1.
zstep.
u8_sok BA (w_out sf). zstep.
u8_store BA (w_out sf) (to_byte (w_bitStream sf)). { unfold to_byte. rewrite <- EX. change (2^32) with 4294967296. lia. }
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep.
destruct (A0_ inv_shadow _ MUA) as [UB2 _].
lazymatch type of UB2 with unpoisoned ?mm _ _ =>
destruct (A0_ chk_out mm (BUF + w_out sf + 1) UB2 ltac:(lia) ltac:(lia)) as (c2 & RDB2 & CK2 & SR2) end.
zstep. zstep. zstep. rewrite sxb_sval.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JOIN2 : forall (w10 w13 : word), evtF bsegs RNG POST
(FST 0x81ac8 mm (Z_to_bv 64 (w_remaining sf)) w10 (Z_to_bv 64 (BUF + w_out sf)) (Z_to_bv 64 (BUF + w_out sf + 1)) w13 y14
(Z_to_bv 64 X) y20 y22 y26 y27 y28 (Z_to_bv 64 (w_bitCount sf)) y30 y31)) end.
{ intros w10 w13. clear RDB2 CK2 SR2 c2.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX.
zstep. sw32 (w_bitCount sf + 7).
u8_sok BA (w_out sf + 1). zstep.
u8_store BA (w_out sf + 1) (to_byte (w_bitStream sf / 2^8)). { unfold to_byte. change (2^8) with 256. lia. }
zstep. if_cases G3; lts_lit G3; [exfalso; lia|].
zstep. zstep.
assert (E61 : Z.shiftr (Z.shiftl (w_bitCount sf + 7) 1 mod 18446744073709551616) 61 = 0).
{ rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
rewrite Z.mod_small by lia. apply Z.div_small. change (2^61) with 2305843009213693952. lia. }
rewrite E61.
zstep. zstep.
rewrite (FseWalkKit.swrap32_small (w_bitCount sf + 7)) by lia. rewrite (Z.shiftr_div_pow2 (w_bitCount sf + 7) 3) by lia. change (2^3) with 8.
set (q := (w_bitCount sf + 7) / 8).
assert (RQ : 0 <= q < 5) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (FseWalkKit.swrap32_small q) by lia.
zstep.
zstep. if_cases G4; zify_cond G4; [exfalso; lia|].
zstep. zstep. zstep. zstep.
replace (Z.lxor (w_bitCount sf + 7) 9223372036854775808 <? 9223372036854775801) with false.
2:{ symmetry. apply Z.ltb_ge. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia.
change (2^63) with 9223372036854775808. lia. }
replace (q + (BUF + w_out sf) <? q) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [Z.b2z]. change (Z.lxor (Z.lxor 0 0) 1) with 1.
zstep. if_cases G5; zify_cond G5; [exfalso; lia|].
zstep. zstep.
assert (EQ10 : q + (BUF + w_out sf) - BUF = w_out sf + Z.quot (w_bitCount sf + 7) 8).
{ subst q. rewrite Z.quot_div_nonneg by lia. lia. }
rewrite EQ10, EN.
do 13 zstep. zstep.
release_frame FA SA SP.
zstep.
apply evtF_done. unfold fse_write_postA. do 14 eexists. eexists. split; [reflexivity|].
split; [exact MUA|]. split; [exact WMA|]. split; [exact MIA|]. split; [exact SA|]. rewrite <- EB. exact BA. }
zstep. if_cases G4; zify_cond G4.
+ zstep. zstep. if_cases G4'; zify_lts G4'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN2.
+ apply JOIN2. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN1.
+ apply JOIN1. }
zstep. zstep. if_cases J0; zify_cond J0; [exfalso; lia|].
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
- rewrite (ite_true _ safe _ _ SAFE). apply STORES.
- apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
rewrite SAFE in CK. cbn [negb andb] in CK. apply Z.ltb_ge in CK.
zstep. zstep. if_cases J1; zify_cond J1; [exfalso; lia|].
zstep. zstep. if_cases J2; zify_cond J2; [exfalso; lia|].
zstep. if_cases J3; zify_cond J3; [| exfalso; lia]. apply STORES.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma winit_ok : forall buf, 5 <= tl <= 12 ->
winit buf tl = Ok (mkW buf 0 (tl - 5) 4 0 (2^tl + 1) (2^tl) (tl + 1) false).
Proof using WRC.
intros buf TLR. unfold winit, assert, FSE_MIN_TABLELOG.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25924166697.7628559041944.7632883044276.7650550177429.7600000100500:00BSS2TLS3TLRS2TL3TLR".
replace ((0 <=? tl) && (tl <? 31)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [bind]. rewrite shl32_ok by lia. cbn [bind]. change (2^0) with 1.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). rewrite Z.mul_1_r.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). rewrite Z.add_0_l.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_main : write_ncount_generic buf0 nc msv tl safe = Ok (buf', n) -> 5 <= tl <= 12 ->
evtF bsegs RNG POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BUF) (Z_to_bv 64 bsz) (Z_to_bv 64 NC) (Z_to_bv 64 msv) (Z_to_bv 64 tl)
(Z_to_bv 64 (Z.b2z safe)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x815ec) fc None m (seg_rom bsegs)).
Proof using All.
intros GOK TLR.
Local Ltac2 Set LiaHints.tbl := fun () => "03J0?10103301745.97 10304119358.98 10521085166.98 10555493932.97 10787530696.95 10874618225.99 11046723646.10611052334449.98 11506956223.94 11561346476.96 11712726766.99 12685940462.98 12754397655.97 13061480274.97 13132286321.99 13641502815.97 1388995953.107 14069196844.10514344564414.98 14520362430.99 15043033658.95 1579170362.99  16583212204.99 16616899182.98 16776327022.98 16833298545.98 17098239598.98 17264948959.97 1733665630.108 1738456419.95  17586965036.98 1792056942.98  17939878638.1071892362350.98  19553650907.10619611527606.94 19622476014.10719961167854.98 20096786092.98 20288658515.1042036978988.106 21059896146.98 21155567546.98 21743028078.98 22163107130.98 22604489004.98 23388622039.99 2342125151.97  23750833521.99 24018786414.98 24024940759.10524278038227.95 24481201518.98 24630998586.98 2489482711.106 25345943790.99 253673568.95   25711131602.98 25792608750.99 25874552945.98 25941301719.1052599566318.108 26105479980.98 28180366214.89 28251215826.10528290589618.95 28615432108.99 28793946177.94 28913119921.10628996933234.95 29531591534.10529661450967.99 29789957598.98 29870281326.10630196181434.97 30610397139.10432024593055.93 3216443911.105 3216443911.106 3216443911.107 3216443911.96  3216443911.97  3216443911.98  3216443911.99  32651489978.98 32716547054.1053276943591.94  32831583703.98 33680001082.10734640905260.98 34782976604.96 34803553003.95 34873960919.98 35212070535.10835276564801.95 36550167519.97 37898509015.10738503264702.98 39302330479.87 39849574766.10539879683282.98 40372058839.99 40437312978.99 40651844268.99 40818989526.95 41299948232.94 41422282358.87 42132582996.92 42132587124.93 42251415634.98 42376778734.99 42547251748.10742560149147.93 42764144210.106428937943.98   43072771152.92 43512528241.96 43872227806.98 44054420798.10544595781586.96 44752146798.97 44956307390.99 45003960671.97 45175508922.76 45221239098.1054544698796.98  45450798590.87 45590082573.91 45596907406.10545599004552.99 45833747069.10646232973498.98 46390900177.91 46398707289.1024641771484.95  46679433004.98 46787521758.98 47600378606.99 48394734674.98 48424436030.98 48593432558.99 4951779697.99  49778780654.98 49860545874.98 502383731.108  50554043535.95 50855256279.96 51063131630.96 51261860670.97 51492745329.98 51508748375.92 51781592415.97 51887071601.98 52131809393.10652525112625.10652692323756.10552715537106.99 53435771095.98 53508216721.10653510313881.10253766521426.98 54068232031.97 54077074142.98 5410806385.98  54256680510.98 54261855034.99 54292472122.96 54682826094.98 55223534865.92 55331181010.99 55489968753.10556007886318.10556154365143.99 563227834.106  5635726270.107 56813015230.99 57745675194.10557839797358.98 58821271538.95 59314873579.92 59314873579.93 59314873579.94 59391421809.10559849776016.10759849776018.10560156864707.94 60694337006.99 61172417726.99 61537339863.98 6158262275.108 6158262277.106 6170132030.94  61896502994.10762084694894.97 62312967610.98 62374525934.96 62382487927.95 62907701586.10562979965517.95 64401800182.87 64728735916.1076537483326.98  65581502065.98 65805175866.99 66739245758.96 6701218494.105 6718328279.98  68276981970.99 68415022551.98 6867211502.99  705257278.98   7612119643.101 8047786924.99  8583720762.99  8657468248.105 9193927790.106 9610135226.98  9909228067.95  00000400=00V00]00a00e00n01201;01B01[02402802A02E02L02P02W02`02i02m03503<03U03n04204K04R04Z04b04i05B05[06406;06C06\07507<07C07J07S07[08408<08C08G08N08R08k08o09709P09X09\0:50:90:B0:[0:_0:c0:g0:n0;20;;0;B0;I0;i0;m0<40<M0<Q0<X0=10=90=@0=K0=O0=S0=W0=[0=_0=c0=g0=o0>H0>P0>T0>\0>c0>j0>n0?20?30?:0?A0?E0?N0?U0?n0@70@;0@D0@K0@O0@o0A30AX0B=0BF0B_0Bg0Bo0C80C<0CF0CJ0CQ0CZ0Cc0D<0DE0DL0DQ0DY0D`0Dh0EH0Eh0FH0FO0FW0G00GI0GP0GW0G^0H70H@0HI0Hb0Hf0I?0IH0Ik0J60J:0JS0J\0J`0Jh0Jo0K30K70K;0KB0KK0KO0KS0KW0K`0Kg0Kn0L20L;0LC0LK0Ld0MD0MM0MQ0Mj0Mn0N60N?0NH0NP0Ni0Nm0O70O>0OH0OL0OS0OZ0Oe0P>0PG0PK0Ph0QE0Qd0Qm0RF0RN0Rg0Rn0S70S?0SG0SN0SW0S[0Sc0Sl0T50T90TB0TF0T_0Th0U00U70U?0UF0U_0Ug0UnS2NBS4SEPN2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NB2HBS2NBS2NBS4SEPN2NBS2NBS4NCNZ2NBS2NB2HBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS4SEPB2NBS2NBS2LO2NBS2NBS2NB2HBS4SEPN2NBS4SEPN2NBS2NBS3RSP2NBS2NB2HBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2LO2NBS3MSV2NBS3MSV2NBS2NB2HBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2LO2NBS3TLR2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NB2HBS2LO2NBS2NB2HBS4SEPB2NBS3RSP2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3RSP2NBS2NB2HBS2NBS2LO2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS3TLR2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3RSP2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS4SEPB2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS2NBS2NBS2NB2HBS2NBS4SEPB2NBS2NB2P2S2NB2HBS2TL5BUFNZ4NCNZ2LO3KLO2B22NB3LBKS2NBS2NB2P2S2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS2LO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3RSP2NBS2LO2NBS2TL3TLR2NBS2NBS2NBS2NBS2NBS2NBS2NBS2NBS3RSP2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3MSV2NBS2NBS3RSP2NBS2NB2HBS2LO2NBS2NBS2NBFS2TL2NBS2LO2NBS2NBS4SEPN2NBS2LO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPB2NBS2NBS4SEPB2NBS2NB2HBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2B22NB3LBKS2NBS2TL5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2B22NBS2TL5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2B22NBS4SEPB2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3MSV2NBS3MSV2NBS4SEPB2NBS2NBS5BUFNZ2NBS2NBS2LO2NBS4SEPN2NBS4SEPB2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPN2NBS2LO2NBS3MSVS3RSP2NBS2NB2HBS3TLR2NBS2TL5BUFNZ4NCNZ2LO3KLO2B22NB3LBKS2TL5BUFNZ4NCNZ2LO3KLO2B22NB3LBKS2TL5BUFNZ4NCNZ2LO3KLO2B22NB3LBKS2NB2P2S3RSP2NBS2TL5BUFNZ4NCNZ2B22NB3LBKS2TL5BUFNZ4NCNZ2B22NB3LBKS2LO2NBS2NB2HBS2LO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPB2NBS4SEPN2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPB2NBS2TL5BUFNZ4NCNZ2LO3KLO2B22BB2NB3LBKS2TL3TLR2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPN2NBS2NBS3MSV2NBS2LO2NBS2NBS2NBS2NBS2NB2HBS4SEPB2NBS2NBS2NBS2NBS4SEPB2NBS2LO2NBS2LO2NBS2NBS4SEPN2NBS3RSP2NBS3RSP2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2B22NB3LBKS4SEPB2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS3RSP2NBS4SEPN2NBS4SEPN2NBS3RSP2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS2B22NB2G1S2NB2G2S3MSV2NB1KS2NBS2TL2NBS2TL2NBS2TL3TLR2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPN2NBS2NBS2TL5BUFNZ4NCNZ2B22NB3LBK3LNKS2TL5BUFNZ4NCNZ2B22NB3LBK3LNKS2TL5BUFNZ4NCNZ2B22NB3LBK3LNK1HS4SEPB2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3RSP2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2B22NBS4SEPB2NBS3TLR2NBS3TLR2NBS2NB2HBS4SEPN2NBS2NBS3RSP2NBS4SEPN2NBS4SEPN2NBS2NBS4SEPB2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPN2NBS3MSV2NBS2NB2HBS3RSP2NBS2LO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3RSP2NBS2TL2NB".
pose proof (write_generic_bsz _ _ _ _ _ _ _ GOK TLR ltac:(lia) NCR) as B2. unfold FseNCount.Zlength in B2.
unfold write_ncount_generic in GOK. cbv zeta in GOK. rewrite (winit_ok buf0 TLR) in GOK. cbn [bind] in GOK.
apply bind_inv in GOK. destruct GOK as (sf & WL & WF). unfold FseNCount.Zlength in WL, WF.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof ST as (LO0 & _ & _).
pose proof (u8arr_bound _ _ _ _ BUF0) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NCB) as NB. rewrite u16s_length, length_map in NB.
pose proof (ablk_lin _ _ BLKB) as LBK. pose proof (ablk_lin _ _ BLKN) as LNK. unfold KHIGH, AIMG_HI in *.
assert (P2 : 32 <= 2^tl <= 4096).
{ split; [change 32 with (2^5)| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia. }
carve_frame 144%nat ST.
apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
do 14 zstep.
zstep. zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. zstep. zstep. zstep.
replace (0 <? BUF) with true by (symmetry; apply Z.ltb_lt; lia).
replace (BUF + bsz <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [Z.b2z]. change (Z.lxor 1 0) with 1.
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. sw32 (msv + 1). zstep. if_cases K; zify_cond K; [exfalso; lia|].
do 18 zstep. rewrite sllw_pow2 by lia.
do 3 zstep. rewrite (Z.mod_small asz 4294967296) by lia.
do 2 zstep. rewrite lor_pow2_1 by lia.
do 10 zstep.
replace (BUF + bsz <? 2) with false in * by (symmetry; apply Z.ltb_ge; lia).
replace (BUF + bsz + -2 <? 1) with false in * by (symmetry; apply Z.ltb_ge; lia).
replace (0 <? NC) with true in * by (symmetry; apply Z.ltb_lt; lia).
cbn [Z.b2z] in *. change (Z.lxor 1 0) with 1 in *. change (Z.land (Z.lxor 0 18446744073709551615) 1) with 1 in *.
rewrite land_1_mod2, NCEV. rewrite (zb_lxor_ones NC) by lia. sw32 (tl + 1).
set (s0w := mkW buf0 0 (tl - 5) 4 0 (2^tl + 1) (2^tl) (tl + 1) false) in *.
replace (tl + -5) with (tl - 5) by lia.
eapply (evtF_eq bsegs _ _ _ (BST 0x816cc _ (Z_to_bv 64 (w_remaining s0w)) _ (Z_to_bv 64 (BUF + w_out s0w)) (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 s0w))))
_ (Z_to_bv 64 (tl - 5)) _ _ (Z_to_bv 64 (w_threshold s0w)) _ (Z_to_bv 64 (w_symbol s0w)) (Z_to_bv 64 (w_bitCount s0w)) _
(Z_to_bv 64 (w_nbBits s0w)))).
{ cbn [s0w w_nbBits w_threshold w_out w_bitCount w_previousIs0 w_remaining w_symbol negb Z.b2z].
replace (BUF + 0) with BUF by lia. reflexivity. }
eapply (wr_loop _ s0w sf); [ | | | | | exact WL | ].
- unfold winv, s0w, FseNCount.Zlength. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
change (2^32) with 4294967296. replace (tl + 1 - 1) with tl by lia. repeat split; lia.
- cbn [s0w w_symbol w_remaining]. apply andb_true_iff. split; apply Z.ltb_lt; lia.
- change (2^64) with 18446744073709551616. lia.
- cbn [s0w w_bitStream]. apply Z.mod_small. change (2^32) with 4294967296. lia.
- cbn [s0w w_buf]. unfold AF_fse_write_A.MINV, AF_fse_write_A.FRAMEC.
split; [exact BUF0|]. split; [exact NCB|]. split; [eexists; exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
- intros m2 X' y10 y13 y14 y20 y22 y26 y27 y28 y30 y31 WIF MV2 RX2 EX2.
eapply (wr_finish sf); [exact WIF | exact MV2 | exact RX2 | exact EX2 | exact WF].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
Lemma lxor_b2z_1 : forall b : bool, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof using Type. intros [|]; reflexivity. Qed.
Lemma wr_body : evtF bsegs RNG POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BUF) (Z_to_bv 64 bsz) (Z_to_bv 64 NC) (Z_to_bv 64 msv) (Z_to_bv 64 tl)
a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFSE_WRITE) fc None m (seg_rom bsegs)).
Proof using All.
unfold AFSE_WRITE.
pose proof WOK as WOK'. unfold write_ncount, FSE_MAX_TABLELOG, FSE_MIN_TABLELOG in WOK'.
destruct (Z.ltb_spec 12 tl) as [TL12|TL12]; [discriminate|].
destruct (Z.ltb_spec tl 5) as [TL5|TL5]; [discriminate|].
assert (GOK : write_ncount_generic buf0 nc msv tl (negb (FseNCount.Zlength buf0 <? write_bound msv tl)) = Ok (buf', n)).
{ destruct (FseNCount.Zlength buf0 <? write_bound msv tl); exact WOK'. }
clear WOK'. unfold FseNCount.Zlength in GOK.
zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>10519033705.8010915936140.8011160981061.8611556852459.8016083456460.8723284431177.8029782203372.8036401657508.8741155690197.7941162082021.8042549348909.9045876098888.8059308628304.7859314923118.7759851873177.9059854341935.7759860645905.7867176411828.877604033872.79 00000300400500C00H00V00W00X00b00l01101201:01B01F01J01N01O01TS1BSFS5BUFNZ4NCNZ1BS3BSZS5BUFNZ4NCNZ1BSFS4TL123TL5S4TL123TL5S3MSVSS3TL52K1S4TL121KS2TLS2TLS2TLSS3MSV".
if_cases K; zify_cond K; [| exfalso; lia].
zstep. zstep. if_cases K1; zify_cond K1; [| exfalso; lia].
zstep. if_cases K2; zify_cond K2.
-
do 4 zstep.
replace 512 with (write_bound msv tl) by (unfold write_bound, FSE_NCOUNTBOUND; rewrite (proj2 (Z.eqb_eq msv 0) K2); reflexivity).
rewrite lxor_b2z_1.
apply (wr_main _ GOK). lia.
-
do 7 zstep.
assert (B : 0 <= (msv + 1) * tl + 6 < 4294967296) by nia.
rewrite (Z.mod_small ((msv + 1) * tl + 6) 18446744073709551616) by lia.
rewrite wrap32_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite FseWalkKit.swrap32_small by lia.
rewrite (Z.mod_small (((msv + 1) * tl + 6) / 8 + 3) 18446744073709551616) by lia.
replace (((msv + 1) * tl + 6) / 8 + 3) with (write_bound msv tl).
2:{ unfold write_bound, FSE_NCOUNTBOUND. rewrite (proj2 (Z.eqb_neq msv 0) K2).
replace ((msv + 1) * tl + 4 + 2) with ((msv + 1) * tl + 6) by lia. lia. }
rewrite lxor_b2z_1. zstep.
apply (wr_main _ GOK). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WR.
#[using="Type"] Theorem fse_write_proofA : fse_write_stmtA.
Proof.
intros until lo. intros BUF0 BUFB NCB NCR WOK MSV TL BSZ BUFNZ NCNZ NCEV ST LO RSP SEPB SEPN SEPBN MI BLKB BLKN BUF8 NC8 KLO GOT SHB UNB UNN RI RSTK RB RBS RN RNS -> -> -> -> ->.
unfold FSE_WRITE_STACK_A in *.
eapply wr_body; eassumption.
Qed.
End CANSEC1.
