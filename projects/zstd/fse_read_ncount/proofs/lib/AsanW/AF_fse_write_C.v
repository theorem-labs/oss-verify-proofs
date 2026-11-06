(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWriteModel FseWalkArith.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AF_fse_iface AF_fse_write_A AF_fse_write_B.
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
Hypothesis BUF0 : u8arr asegs m BUF (map (Z_to_bv 8) buf0).
Hypothesis BUFB : Forall (fun c => 0 <= c < 256) buf0.
Hypothesis NCB : bytes_at asegs m NC (u16s (map (Z_to_bv 64) nc)).
Hypothesis NCR : Forall (fun c => - 32768 <= c < 32768) nc.
Hypothesis WOK : write_ncount buf0 nc msv tl = Ok (buf', n).
Hypothesis MSV : 0 <= msv <= 255.
Hypothesis TL : 0 <= tl < 2^32.
Hypothesis BSZ : zlen buf0 <= 65536.
Hypothesis BUFNZ : 0 < BUF.
Hypothesis NCNZ : 0 < NC.
Hypothesis NCEV : NC mod 2 = 0.
Hypothesis ST : stk asegs m lo SP.
Hypothesis LO : lo <= SP - 96.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis SEPB : BUF + zlen buf0 <= SP - 96 \/ SP <= BUF.
Hypothesis SEPN : NC + 2 * zlen nc <= SP - 96 \/ SP <= NC.
Hypothesis SEPBN : NC + 2 * zlen nc <= BUF \/ BUF + zlen buf0 <= NC.
Hypothesis MI : mem_inv asegs m.
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
Notation W := [(BUF, BUF + bsz); (SP - 96, SP)].
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
Notation FRAMEC := (AF_fse_write_A.FRAMEC ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10).
Notation MINV := (AF_fse_write_A.MINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m SP BUF NC buf0 nc lo).
Section LOOP.
Variable safe : bool.
Notation AST pc mm x5 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 :=
(MS (mkR ra (Z_to_bv 64 (SP + -96)) gp tp x5 (Z_to_bv 64 2147450880) (Z_to_bv 64 asz) (Z_to_bv 64 3) (Z_to_bv 64 65535)
(Z_to_bv 64 BUF) (Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 NC) x13 x14 (Z_to_bv 64 (Z.b2z safe)) x16 (Z_to_bv 64 (-1))
x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 (Z_to_bv 64 1) (Z_to_bv 64 17) (Z_to_bv 64 15) (Z_to_bv 64 asz))
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
Notation A_ l := (l RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ BUFNZ NCNZ NCEV LO RSP SEPB SEPN SEPBN BLKB BLKN BUF8 NC8 KLO UNB UNN RI RSTK RB RBS RN RNS).
Notation B_ l := (A_ l safe).
Lemma wr_loop : forall f s sf m1 X (x19 x23 x24 x25 x26 : word),
winv asz bsz s -> (w_symbol s <? asz) && (1 <? w_remaining s) = true -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
MINV m1 (w_buf s) ->
wloop nc asz bsz safe f s = Ok sf ->
(forall m2 X' (y14 y18 y19 y20 y21 y22 y24 y25 y26 : word), winv asz bsz sf -> MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evtF asegs RNG POST (AST 0x81a8c m2 (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 (BUF + w_out sf)) y14 (Z_to_bv 64 X') y18 y19 y20 y21 y22
(Z_to_bv 64 (w_remaining sf)) y24 y25 y26)) ->
evtF asegs RNG POST (AST 0x81768 m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 s))))
(Z_to_bv 64 X) (Z_to_bv 64 (w_nbBits s)) x19 (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (w_remaining s))
(Z_to_bv 64 (w_symbol s)) x23 x24 x25 x26).
Proof using WRC.
induction f as [|f IH]; intros s sf m1 X x19 x23 x24 x25 x26 WI CND RX EX MV WL K; [cbn in WL; discriminate|].
rewrite wloop_S in WL. rewrite CND in WL. apply bind_inv in WL. destruct WL as (fl & WB & WL).
apply andb_true_iff in CND. destruct CND as [CS CR]. apply Z.ltb_lt in CS. apply Z.ltb_lt in CR.
unfold wbody in WB. apply bind_inv in WB. destruct WB as (fl0 & ZB & WB).
assert (CNT : forall sa m2 X2 (y14 y22 y23 y24 y25 y26 : word), fl0 = Cont sa -> winv asz bsz sa -> w_symbol sa < asz -> same_ctl s sa ->
MINV m2 (w_buf sa) -> 0 <= X2 < 2^64 -> X2 mod 2^32 = w_bitStream sa ->
evtF asegs RNG POST (AST 0x818e0 m2 (Z_to_bv 64 (w_bitCount sa)) (Z_to_bv 64 (BUF + w_out sa)) y14 (Z_to_bv 64 X2) (Z_to_bv 64 (w_nbBits s))
(Z_to_bv 64 (w_symbol sa)) (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (w_remaining s)) y22 y23 y24 y25 y26)).
{ intros sa m2 X2 y14 y22 y23 y24 y25 y26 -> WIA SYA (C1 & C2 & C3 & C4) MV2 RX2 EX2.
apply bind_inv in WB. destruct WB as (sc & CB & WB). apply bind_inv in WB. destruct WB as (sd & FL & WB). injection WB as <-.
pose proof (wcount_flush_facts nc asz bsz safe sa sc sd CB FL WIA SYA NCR) as (WID & SYD & CTL).
rewrite <- C1, <- C2, <- C3.
eapply (B_ wr_count sa sc sd); [exact WIA | exact SYA | exact RX2 | exact EX2 | exact MV2 | exact CB | exact FL | | ].
- intros m3 X3 z19 z23 z24 z25 z26 CND3 MV3 RX3 EX3.
eapply (IH sd sf); [exact WID | exact CND3 | exact RX3 | exact EX3 | exact MV3 | exact WL | exact K].
- intros m3 X3 z14 z18 z19 z20 z21 z22 z24 z25 z26 CND3 MV3 RX3 EX3.
destruct f as [|f']; [cbn in WL; discriminate|]. rewrite wloop_S in WL. rewrite CND3 in WL. injection WL as <-.
apply K; assumption. }
destruct (w_previousIs0 s) eqn:P0; cbn [negb Z.b2z].
-
zstep. zstep. if_true.
pose proof (wzero_block_facts nc asz bsz safe s fl0 ZB WI CS) as ZF.
eapply (B_ wr_zero s fl0); [exact WI | exact CS | exact RX | exact EX | exact MV | exact ZB | | ].
+ intros sa m2 X' y14 y22 y23 y24 y25 y26 -> MV2 RX2 EX2. destruct ZF as (WIA & CTL & SYA & _).
Local Ltac2 Set LiaHints.tbl := fun () => "00:0?15945006258.1161741865053.116 22621431600.11326101251452.11631838395051.11634108802827.11646794069120.11654288074799.1165433691307.116 64374068987.11600000100600;00@00D00O00S00[00_00dSS3MSVS3SYAS3RB0S2BCS2RO3RB02BCS2ROS2RM3NBIS2RMS3NBI".
eapply (CNT sa); [reflexivity | exact WIA | lia | exact CTL | exact MV2 | exact RX2 | exact EX2].
+ intros sa y14 y19 y24 y25 y26 ->. destruct ZF as (SYA & BUA & OUA & BSA & BCA & (C1 & C2 & C3 & C4)).
injection WB as <-. injection WL as <-.
rewrite <- OUA, <- BCA. rewrite <- C1 at 2.
apply K; [ | rewrite BUA; exact MV | exact RX | rewrite BSA; exact EX].
destruct WI as (LB & RO & RB0 & BC & SY & RM & NBI & TH).
unfold winv. rewrite BUA, OUA, BSA, BCA, SYA, C1, C2, C3. repeat split; try assumption; try lia.
-
injection ZB as <-.
zstep. zstep. if_false. zstep. zstep.
eapply (CNT s); [reflexivity | exact WI | exact CS | unfold same_ctl; repeat split | exact MV | exact RX | exact EX].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Notation FST pc mm x5 x11 x12 x13 x14 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 :=
(MS (mkR ra (Z_to_bv 64 (SP + -96)) gp tp x5 (Z_to_bv 64 2147450880) (Z_to_bv 64 asz) (Z_to_bv 64 3) (Z_to_bv 64 65535)
(Z_to_bv 64 BUF) x11 x12 x13 x14 (Z_to_bv 64 (Z.b2z safe)) x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 (Z_to_bv 64 1) (Z_to_bv 64 17) (Z_to_bv 64 15) (Z_to_bv 64 asz))
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
Lemma wr_finish : forall sf m1 X (y14 y18 y19 y20 y21 y22 y24 y25 y26 : word),
winv asz bsz sf -> MINV m1 (w_buf sf) -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream sf ->
wfinish bsz safe sf = Ok (buf', n) ->
evtF asegs RNG POST (AST 0x81a8c m1 (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 (BUF + w_out sf)) y14 (Z_to_bv 64 X) y18 y19 y20 y21 y22
(Z_to_bv 64 (w_remaining sf)) y24 y25 y26).
Proof using WRC.
intros sf m1 X y14 y18 y19 y20 y21 y22 y24 y25 y26 WI MV RX EX WF.
pose proof WI as (LB & RO & RB0 & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & FA & SA & MUA & WMA & MIA).
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
assert (STORES : forall (z12 : word), evtF asegs RNG POST
(FST 0x81aa4 m1 (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 (BUF + bsz + -2)) z12 (Z_to_bv 64 (BUF + w_out sf)) y14 (Z_to_bv 64 X) (Z_to_bv 64 (-1))
y18 y19 y20 y21 y22 (Z_to_bv 64 (w_remaining sf)) y24 y25 y26)).
{ intros z12.
destruct (A_ inv_shadow _ MUA) as [UB1 _].
Local Ltac2 Set LiaHints.tbl := fun () => "01P0?10292415313.17111187069146.12611554597466.12711603159087.12313070568592.12413071056297.12313641502815.13216393397268.12517264948958.13318002113.119   18579966.120   19618399904.13919618399911.14219717304359.11821376456769.12521378557434.1272342125151.132 24232518001.13526798724209.13327517043963.12028562676326.12529649045467.16729782367974.12529782367974.13229782367974.13830037004206.12731183134347.1183214378781.120 3214378781.124 3405217491.124 34782976604.13136441195086.13736443292230.13136550167518.13337424275400.12339007438634.12743872227806.13345003960670.13345590131725.11945596907403.13645596907404.13845596907405.13645781994147.12046400804432.1384641771484.131 46564874353.13246787521745.13447788875075.12248727422281.13549170713844.124492464117.119  49423367528.12049741439345.13451456153639.13851458250794.13451781592414.13351818759664.1245222230152.122 54068232031.13254077074129.1345432979569.133 55889565713.12456567948472.11756736913460.13457877014385.13459310676440.16759310676440.17159314873579.11859314873579.12060245579230.12461198613617.13361756581537.12461756581537.12562947167693.13463253218243.12463368316589.12763368316718.12663374621462.12563430708081.13464405586211.13164407683371.13764799663456.12065829850067.12166840963185.13468015643440.13168017740600.13768187539651.13168189636811.1377227030694.124 7237347185.132 8316058051.124 8514435441.135 913132285.124  9448783151.167 9448783151.171 9581028844.124 00000800?00H01M01W01a01h01o02602=02D03203`03g03n04504<04@04D05705m06506906=06A06E07807n08d08h08o09009109809<0:A0:H0:O0;=0;k0<Y0=G0=o0>V0>]0>a0>h0?[0@Q0AD0B20BV0BZ0Ba0Bh0Bo0CS0CZ0Ca0Ch0Cl0D00D70Dm0E10E^0FM0FZ0Fd0Fh0Fl0G30G:0G>0GE0GI0GM0GQ0GU0H[0Ia0JT0KM0KQ0KR0KS0KT0KU0KY0K]0LP0LT0LX0Le0M30M[S2NB3SR2S2BC2NBS2NB1H2H0S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2O22LB2RO3RB02BC3NBI2NB3LBK3CK1S2O12O22NBS2O12O22NBS2LO2NBS2LO2NBS2LO2NBS2O12NBS2O12NBS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS2O12NBS2BC2NBS2BC2NBS2LO2NBS2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB02BC3NBI2NBS2NB3SR1S2NBS2NBS2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O12O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O12O22LB2RO3RB03NBI2NBS2NBS2LO2NBFFS2LO2NBS2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2O22LB2RO3RB02BC3NBI2NB3LBK3CK2S2LO2NBS2LO2NBS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2RX2O22LB2RO3RB03NBI2NB3LBKS2LO2NBS2NBS2LO2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O12O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ2LO3KLO2RX2O22LB2RO3RB03NBI2NB3LBKS5BUFNZ4NCNZ2RX2O22LB3RB03NBI2NB3LBKS2NBS2BC2NBS2BC2NBS2LO2NBS5BUFNZ4NCNZ2RX2O22LB3RB03NBI2NB3LBKS2O12NBS2LO2NBS2LO2NBS2NBS2NBS2RM2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O12O22LB2RO3RB03NBI2NBS2NBS4SEPB4SEPN5SEPBN2O22LB2RO2BC3NBI2NB3CK11G2G'S4SEPB4SEPN5SEPBN2O22LB2RO2BC3NBI2NB3CK22G23G2'S2RM2NB2R12J0S2CK2NB2J1S2NBS2NBS2BC2NBS2BC2NBS2NBS2BC2NBS2NBS2NBS2NBS2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2O22LB2RO3RB02BC3NBI2NB3LBKS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2O22LB2RO3RB02BC3NBI2NB3LBKS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2EX2O22LB2RO3RB02BC3NBI2NBS2NBFFFFS2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2O22LB2RO3RB03NBI2NBS2NBS2NBS2NB3CK11G2H0S2NB3CK22G22H0S5BUFNZ4NCNZ2LO3KLO2RX2RO3RB03NBI2NB3LBK".
destruct (A_ chk_out m1 (BUF + w_out sf) UB1 ltac:(lia) ltac:(lia)) as (c1 & RDB1 & CK1 & SR1).
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN1 : forall (z11 w12 : word), evtF asegs RNG POST
(FST 0x81ab4 m1 (Z_to_bv 64 (w_bitCount sf)) z11 w12 (Z_to_bv 64 (BUF + w_out sf)) y14 (Z_to_bv 64 X) (Z_to_bv 64 (-1))
y18 y19 y20 y21 y22 (Z_to_bv 64 (w_remaining sf)) y24 y25 y26)).
{ intros z11 w12. clear RDB1 CK1 SR1 c1.
u8_sok BA (w_out sf). zstep.
u8_store BA (w_out sf) (to_byte (w_bitStream sf)). { unfold to_byte. rewrite <- EX. change (2^32) with 4294967296. lia. }
zstep.
destruct (A_ inv_shadow _ MUA) as [UB2 _].
lazymatch type of UB2 with unpoisoned ?mm _ _ =>
destruct (A_ chk_out mm (BUF + w_out sf + 1) UB2 ltac:(lia) ltac:(lia)) as (c2 & RDB2 & CK2 & SR2) end.
zstep. zstep. zstep. rewrite sxb_sval.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JOIN2 : forall (v12 v14 : word), evtF asegs RNG POST
(FST 0x81acc mm (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 (BUF + w_out sf + 1)) v12 (Z_to_bv 64 (BUF + w_out sf)) v14 (Z_to_bv 64 X) (Z_to_bv 64 (-1))
y18 y19 y20 y21 y22 (Z_to_bv 64 (w_remaining sf)) y24 y25 y26)) end.
{ intros v12 v14. clear RDB2 CK2 SR2 c2.
zstep. zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX.
zstep.
rewrite (FseWalkKit.swrap32_small (w_bitCount sf + 7)) by lia.
replace (Z.shiftr (w_bitCount sf + 7) 31) with 0
by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; change (2^31) with 2147483648; lia).
rewrite (FseWalkKit.swrap32_small 0) by lia.
u8_sok BA (w_out sf + 1). zstep.
u8_store BA (w_out sf + 1) (to_byte (w_bitStream sf / 2^8)). { unfold to_byte. change (2^8) with 256. lia. }
zstep. zstep. zstep. zstep. zstep.
assert (EQ10 : BUF + w_out sf - BUF + bv_swrap 32 (Z.shiftr (bv_swrap 32 (w_bitCount sf + 7)) 3) = w_out sf + Z.quot (w_bitCount sf + 7) 8).
{ rewrite (FseWalkKit.swrap32_small (w_bitCount sf + 7)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
pose proof (Z.div_pos (w_bitCount sf + 7) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (w_bitCount sf + 7) 8 100 ltac:(lia) ltac:(lia)).
rewrite FseWalkKit.swrap32_small by lia. rewrite Z.quot_div_nonneg by lia. lia. }
rewrite EQ10.
rewrite EN.
zstep.
do 12 zstep. zstep.
release_frame FA SA SP.
zstep.
apply evtF_done. unfold fse_write_postA. do 14 eexists. eexists. split; [reflexivity|].
split; [exact MUA|]. split; [exact WMA|]. split; [exact MIA|]. split; [exact SA|]. rewrite <- EB. exact BA. }
zstep. if_cases G2; zify_cond G2.
+ zstep. zstep. if_cases G2'; zify_lts G2'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN2.
+ apply JOIN2. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN1.
+ apply JOIN1. }
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
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25924166697.7628559041944.7632883044276.7650550177429.7600000100500:00BSS2TLS3TLRS2TL3TLR".
replace ((0 <=? tl) && (tl <? 31)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [bind]. rewrite shl32_ok by lia. cbn [bind]. change (2^0) with 1.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). rewrite Z.mul_1_r.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). rewrite Z.add_0_l.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_main : write_ncount_generic buf0 nc msv tl safe = Ok (buf', n) -> 5 <= tl <= 12 ->
evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BUF) (Z_to_bv 64 bsz) (Z_to_bv 64 NC) (Z_to_bv 64 msv) (Z_to_bv 64 tl)
(Z_to_bv 64 (Z.b2z safe)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x816d4) fc None m (seg_rom asegs)).
Proof using All.
intros GOK TLR.
unfold write_ncount_generic in GOK. cbv zeta in GOK. rewrite (winit_ok buf0 TLR) in GOK. cbn [bind] in GOK.
apply bind_inv in GOK. destruct GOK as (sf & WL & WF). unfold FseNCount.Zlength in WL, WF.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof ST as (LO0 & _ & _).
pose proof (u8arr_bound _ _ _ _ BUF0) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NCB) as NB. rewrite u16s_length, length_map in NB.
pose proof (ablk_lin _ _ BLKB) as LBK. pose proof (ablk_lin _ _ BLKN) as LNK. unfold KHIGH, AIMG_HI in *.
assert (P2 : 32 <= 2^tl <= 4096).
{ Local Ltac2 Set LiaHints.tbl := fun () => "02B0?10371693015.97 10787530696.92 11046723646.96 11903774446.97 12101529815.95 13061480274.97 13115648110.97 13641502815.96 14344564414.98 15043033658.92 15649124780.98 17264948959.96 1733665630.105 1738456419.92  18434612386.97 18848698606.98 19152212908.95 19199919342.98 19611527606.91 2003044974.97  21659919916.97 22163107130.98 23144071639.96 2342125151.96  24096502638.97 24232518001.98 24278038227.92 24630998586.98 25181880364.97 2533208966.88  253673568.92   25711131602.98 2599566318.105 26035549399.98 26798724209.97 27687638188.98 27730847314.97 27911502958.97 28251215826.97 28290589618.92 28996933234.92 30180773870.98 30196181434.97 31192823468.98 31598888919.97 31731548819.97 3216443911.95  3216443911.96  3216443911.97  3216443911.98  32651489978.97 3276943591.91  33680001082.97 33700542764.97 34782976604.95 34803553003.92 35153358318.98 35212070535.10535276564801.92 36300595415.97 36485046743.97 36550167519.96 37218310956.97 38503264702.98 39302330479.86 39728246700.97 39879683282.98 39949608786.97 40069102958.97 40437312978.98 40818989526.92 41161757422.97 41422282358.86 42132587124.89 42547251749.10342560149147.90 42744733806.96 42764144210.96 42831019478.97 43872227806.97 44054420798.97 44956307390.95 45003960671.96 45042151022.97 45221239098.97 45450798590.86 45736959020.96 45833747070.10246232973498.97 4641771484.94  46564874353.96 46787521758.97 48394734674.97 48635769742.97 49741439345.97 49978085870.97 50554043535.92 51261860670.97 51508760695.89 51764527788.97 51781592415.96 52136437230.97 52715537106.95 53766521426.97 54068232031.96 54077074142.97 54256680510.97 5432979569.97  54729132247.98 55978215150.95 56023003502.97 563227834.96   5635726270.97  56813015230.98 56912526318.98 57745675194.97 57877014385.97 58821271538.92 59314873579.91 59849776017.10360156864707.91 61198613617.97 61896502994.97 62140770976.97 62382487927.92 62907701586.97 62947167693.97 62979965517.92 63430708081.98 64401800182.86 64798196951.98 6537483326.97  65805175866.95 65806924526.95 65888922839.97 65977411438.97 66840963185.97 66961164782.98 67003974766.96 6701218494.97  7237347185.95  7612119643.98  8514435441.98  8553591767.97  8583720762.98  9909228067.92  00000400800A00Z00^00g01@01G01P01T01[01b01j02202;02T02[03403<03U03\03d03h03o04H04L04T04\04c04g04k05405805<05@05G05`06906B06I06P06i07107807<07@07D07H07L07P07X07`07h07o08608:08S08T08[08_08c08j09109:09A09H09Q09j0:C0:L0:P0:i0:m0;O0;W0;_0<80<A0<I0<P0<Y0<b0<i0=B0=J0=R0=Y0=`0=h0=o0>30>:0>C0>L0>P0>i0?40?=0?E0?L0?S0?l0@50@>0@E0@L0@U0@Y0@]0A60AO0AW0A`0Ai0BB0BJ0BN0BR0B\0Bc0Bn0C20C;0CB0CF0CO0CS0C[0C_0Cg0Ck0D40D<0DU0DY0E20E60EO0Eh0F10F50F=0FA0FE0FM0FTS2NBS2NBS4SEPN2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS4SEPB2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2LO2NBS4SEPN2NBS2NBS2NB2HBS2LO2NBS3MSV2NBS3MSV2NBS4SEPN2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NB2HBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3TLR2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NB2HBS3RSP2NBS2NBS2LO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS3TLR2NBS3RSP2NBS2NB2HBS2NBS2NBS4SEPB2NBS2NBS2NBS2NBS2NB2HBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPB2NBS2NB2P2S2NB2P2S2TL5BUFNZ4NCNZ2LO3KLO2NBS3RSP2NBS2NB2HBS2NBS2NBS2NBS2NBS2NBS2NBS3RSP2NBS3MSV2NBS3RSP2NBS2NB2HBS2LO2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBFS2TL2NBS2NBS2NBS2LO2NBS2NB2HBS4SEPN2NBS2LO2NBS2NB2HBS4SEPB2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPB2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS2TL5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2NBS3MSV2NBS3MSV2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPB2NBS3RSP2NBS2LO2NBS4SEPN2NBS4SEPN2NBS2LO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3RSP2NBS3TLR2NBS2NB2HBS2NB2P2S3RSP2NBS2LO2NBS2NBS2LO2NBS4SEPB2NBS4SEPB2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL3TLR2NBS4SEPN2NBS3MSV2NBS2NB2HBS2LO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPB2NBS4SEPB2NBS2LO2NBS2LO2NBS4SEPN2NBS2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3RSP2NBS4SEPN2NBS4SEPN2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS3RSP2NBS2NBS2NBS3MSV2NB1KS2TL2NBS2TL3TLR2NBS2NBS4SEPB2NBS2NB2HBS2NBS4SEPB2NBS2NBS3TLR2NBS2NBS3TLR2NBS2NBS4SEPN2NBS3RSP2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS2TL5BUFNZ4NCNZ2LO3KLO2NBS4SEPN2NBS2NBS3MSV2NBS2NBS2NBS3RSP2NBS2TL2NB".
split; [change 32 with (2^5)| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia. }
carve_frame 96%nat ST.
apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
do 13 zstep.
zstep. sw32 (msv + 1). zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
do 12 zstep. rewrite sllw_pow2 by lia.
do 2 zstep. rewrite (Z.mod_small asz 4294967296) by lia.
zstep. rewrite lor_pow2_1 by lia.
do 6 zstep.
set (s0w := mkW buf0 0 (tl - 5) 4 0 (2^tl + 1) (2^tl) (tl + 1) false) in *.
replace (tl + -5) with (tl - 5) by lia.
eapply (evtF_eq asegs _ _ _ (AST 0x81768 m1 (Z_to_bv 64 (w_bitCount s0w)) (Z_to_bv 64 (BUF + w_out s0w)) (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 s0w))))
(Z_to_bv 64 (tl - 5)) (Z_to_bv 64 (w_nbBits s0w)) s3 (Z_to_bv 64 (w_threshold s0w)) (Z_to_bv 64 (w_remaining s0w))
(Z_to_bv 64 (w_symbol s0w)) s7 s8 s9 s10)).
{ cbn [s0w w_nbBits w_threshold w_out w_bitCount w_previousIs0 w_remaining w_symbol negb Z.b2z].
replace (BUF + 0) with BUF by lia. reflexivity. }
eapply (wr_loop _ s0w sf); [ | | | | | exact WL | ].
- unfold winv, s0w, FseNCount.Zlength. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
change (2^32) with 4294967296. replace (tl + 1 - 1) with tl by lia. repeat split; lia.
- cbn [s0w w_symbol w_remaining]. apply andb_true_iff. split; apply Z.ltb_lt; lia.
- change (2^64) with 18446744073709551616. lia.
- cbn [s0w w_bitStream]. apply Z.mod_small. change (2^32) with 4294967296. lia.
- cbn [s0w w_buf]. unfold AF_fse_write_A.MINV, AF_fse_write_A.FRAMEC.
split; [exact BUF0|]. split; [exact NCB|]. split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
- intros m2 X' y14 y18 y19 y20 y21 y22 y24 y25 y26 WIF MV2 RX2 EX2.
eapply (wr_finish sf); [exact WIF | exact MV2 | exact RX2 | exact EX2 | exact WF].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
Lemma lxor_b2z_1 : forall b : bool, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof using Type. intros [|]; reflexivity. Qed.
Lemma wr_body : evtF asegs RNG POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BUF) (Z_to_bv 64 bsz) (Z_to_bv 64 NC) (Z_to_bv 64 msv) (Z_to_bv 64 tl)
a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AFSE_WRITE) fc None m (seg_rom asegs)).
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
