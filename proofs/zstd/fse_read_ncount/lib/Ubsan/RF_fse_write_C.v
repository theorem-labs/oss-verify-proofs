(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseWriteModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_write_A RF_fse_write_B.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Section WR.
Variables (ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : fmem) (SP BUF NC : Z)
(buf0 buf' nc : list Z) (msv tl n lo : Z).
Hypothesis BUF0 : u8arr usegs m BUF (map (Z_to_bv 8) buf0).
Hypothesis BUFB : Forall (fun c => 0 <= c < 256) buf0.
Hypothesis NCB : bytes_at usegs m NC (u16s (map (Z_to_bv 64) nc)).
Hypothesis NCR : Forall (fun c => - 32768 <= c < 32768) nc.
Hypothesis WOK : write_ncount buf0 nc msv tl = Ok (buf', n).
Hypothesis MSV : 0 <= msv <= 255.
Hypothesis TL : 0 <= tl < 2^32.
Hypothesis BSZ : zlen buf0 <= 65536.
Hypothesis BUFNZ : 0 < BUF.
Hypothesis NCNZ : 0 < NC.
Hypothesis NCEV : NC mod 2 = 0.
Hypothesis BUFW : BUF + zlen buf0 < 2^64.
Hypothesis NCW : NC + 2 * zlen nc < 2^64.
Hypothesis ST : stk usegs m lo SP.
Hypothesis LO : lo <= SP - 128.
Hypothesis RSP : 0 <= SP < 2^64.
Hypothesis SEPB : BUF + zlen buf0 <= SP - 128 \/ SP <= BUF.
Hypothesis SEPN : NC + 2 * zlen nc <= SP - 128 \/ SP <= NC.
Hypothesis SEPBN : NC + 2 * zlen nc <= BUF \/ BUF + zlen buf0 <= NC.
Hypothesis MI : mem_inv usegs m.
Collection WRC := ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ BUFNZ NCNZ NCEV BUFW NCW LO RSP SEPB SEPN SEPBN.
Notation POST := (fse_write_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP BUF buf0 buf' n lo m).
Notation bsz := (zlen buf0).
Notation asz := (msv + 1).
Notation W := [(BUF, BUF + bsz); (SP - 128, SP)].
Notation FRAMEC := (RF_fse_write_A.FRAMEC ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 msv).
Notation MINV := (RF_fse_write_A.MINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP BUF NC buf0 nc msv lo).
Lemma wloop_bc16 : forall sf0 f s sf, wloop nc asz bsz sf0 f s = Ok sf -> winv asz bsz s -> w_bitCount s <= 16 -> w_bitCount sf <= 16.
Proof using NCR.
intros sf0. induction f as [|f IH]; intros s sf WL WI B16; [discriminate|].
rewrite wloop_S in WL. destruct ((w_symbol s <? asz) && (1 <? w_remaining s)) eqn:CND; [| injection WL as <-; exact B16].
apply andb_true_iff in CND. destruct CND as [CS CR]. apply Z.ltb_lt in CS.
apply bind_inv in WL. destruct WL as (fl & WB & WL). unfold wbody in WB.
apply bind_inv in WB. destruct WB as (fl0 & ZB & WB).
assert (CNT : forall sa, fl0 = Cont sa -> winv asz bsz sa -> w_symbol sa < asz -> w_bitCount sa <= 17 -> w_bitCount sf <= 16).
{ intros sa -> WIA SYA BA. apply bind_inv in WB. destruct WB as (sc & CB & WB). apply bind_inv in WB. destruct WB as (sd & FL & WB).
injection WB as <-. destruct (wcount_flush_facts nc asz bsz sf0 sa sc sd CB FL WIA SYA NCR) as (WID & _ & _).
eapply IH; [exact WL | exact WID |].
pose proof WIA as (_ & _ & _ & _ & _ & _ & NBI & _).
apply wcount_block_inv in CB. cbv zeta in CB. destruct CB as (thr' & nb' & _ & _ & _ & _ & ->).
apply wflush_if_inv in FL. destruct FL as [[G FL]|[G ->]].
- apply wflush_inv in FL. destruct FL as (_ & _ & _ & ->). cbn [w_bitCount] in G |- *.
match goal with |- context [if ?c then 1 else 0] => destruct c end; lia.
- cbn [w_bitCount] in G |- *. lia. }
destruct (w_previousIs0 s).
- pose proof (wzero_block_facts nc asz bsz sf0 s fl0 ZB WI CS) as ZF. destruct fl0 as [sa|sa].
+ destruct ZF as (WIA & _ & SYA & BCA). eapply CNT; [reflexivity | exact WIA | lia | exact BCA].
+ injection WB as <-. injection WL as <-. destruct ZF as (_ & _ & _ & _ & BCA & _). lia.
- injection ZB as <-. eapply CNT; [reflexivity | exact WI | exact CS | lia].
Qed.
Lemma wout_le : n <= bsz.
Proof using WOK NCR MSV TL.
pose proof WOK as G. unfold write_ncount, FSE_MAX_TABLELOG, FSE_MIN_TABLELOG in G.
destruct (Z.ltb_spec 12 tl) as [TL12|TL12]; [discriminate|].
destruct (Z.ltb_spec tl 5) as [TL5|TL5]; [discriminate|].
assert (GOK : exists sf0, write_ncount_generic buf0 nc msv tl sf0 = Ok (buf', n)).
{ destruct (FseNCount.Zlength buf0 <? write_bound msv tl); eexists; exact G. }
clear G. destruct GOK as (sf0 & GOK). unfold write_ncount_generic in GOK. cbv zeta in GOK.
apply bind_inv in GOK. destruct GOK as (w0 & WI0 & GOK). apply bind_inv in GOK. destruct GOK as (sf & WL & WF).
unfold winit, assert in WI0.
replace ((0 <=? tl) && (tl <? 31)) with true in WI0 by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [bind] in WI0. apply bind_inv in WI0. destruct WI0 as (v & _ & WI0). injection WI0 as E0.
assert (WINV0 : winv (msv + 1) (FseNCount.Zlength buf0) w0).
{ subst w0. assert (P2 : 32 <= 2^tl <= 4096).
{ split; [change 32 with (2^5)| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia. }
unfold winv. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0].
pose proof (u32_range (0 + v)). replace (tl + 1 - 1) with tl by lia.
assert (0 <= FseNCount.Zlength buf0) by (unfold FseNCount.Zlength; lia). repeat split; lia. }
assert (B0 : w_bitCount w0 <= 16) by (subst w0; cbn [w_bitCount]; lia).
pose proof (wloop_winv nc (msv + 1) (FseNCount.Zlength buf0) sf0 _ _ _ WL WINV0 NCR) as (LB & RO & RB & BC & _).
pose proof (wloop_bc16 sf0 _ _ _ WL WINV0 B0) as B16.
unfold wfinish in WF. destruct (negb (w_remaining sf =? 1)); [discriminate|].
destruct (negb sf0 && (FseNCount.Zlength buf0 - 2 <? w_out sf)); [discriminate|].
apply bind_inv in WF. destruct WF as (b1 & S1 & WF). apply bind_inv in WF. destruct WF as (b2 & S2 & WF).
apply store_inv in S1. destruct S1 as [O1 ->]. apply store_inv in S2. destruct S2 as [O2 _].
rewrite Zlength_Zupd in O2. injection WF as _ <-.
rewrite Z.quot_div_nonneg by lia.
assert ((w_bitCount sf + 7) / 8 < 3) by (apply Z.div_lt_upper_bound; lia).
unfold FseNCount.Zlength in *. lia.
Qed.
Section LOOP.
Variable safe : bool.
Notation A_ l := (l ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ BUFNZ NCNZ NCEV BUFW NCW LO RSP SEPB SEPN SEPBN safe).
Notation B_ l := (A_ l).
Notation UST pc mm x1 x5 x6 x9 x13 x14 x19 x22 x24 x25 x26 x28 x29 :=
(MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 (Z_to_bv 64 1) (Z_to_bv 64 1) x9
(Z_to_bv 64 BUF) (Z_to_bv 64 (BUF + bsz)) (Z_to_bv 64 NC) x13 x14 (Z_to_bv 64 (Z.b2z safe))
(Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 asz) (Z_to_bv 64 31) x19 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3)) x22
(Z_to_bv 64 3) x24 x25 x26 (Z_to_bv 64 1) x28 x29 (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551615 - NC)))
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
Lemma wr_loop : forall f s sf m1 X (x9 x19 x22 x25 x26 : word),
winv asz bsz s -> (w_symbol s <? asz) && (1 <? w_remaining s) = true -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
MINV m1 (w_buf s) ->
wloop nc asz bsz safe f s = Ok sf ->
(forall m2 X' (y1 y6 y9 y19 y22 y24 y25 y26 y28 : word), winv asz bsz sf -> MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evt usegs POST (UST 0x13c90 m2 y1 (Z_to_bv 64 (w_bitCount sf)) y6 y9 (Z_to_bv 64 X') (Z_to_bv 64 (BUF + w_out sf)) y19 y22
y24 y25 y26 y28 (Z_to_bv 64 (w_remaining sf)))) ->
evt usegs POST (UST 0x13a44 m1 (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 s))))
x9 (Z_to_bv 64 X) (Z_to_bv 64 (BUF + w_out s)) x19 x22 (Z_to_bv 64 (w_threshold s)) x25 x26
(Z_to_bv 64 (w_nbBits s)) (Z_to_bv 64 (w_remaining s))).
Proof using WRC.
induction f as [|f IH]; intros s sf m1 X x9 x19 x22 x25 x26 WI CND RX EX MV WL K; [cbn in WL; discriminate|].
rewrite wloop_S in WL. rewrite CND in WL. apply bind_inv in WL. destruct WL as (fl & WB & WL).
apply andb_true_iff in CND. destruct CND as [CS CR]. apply Z.ltb_lt in CS. apply Z.ltb_lt in CR.
unfold wbody in WB. apply bind_inv in WB. destruct WB as (fl0 & ZB & WB).
assert (CNT : forall sa m2 X2 (y1 y6 y9 y19 y25 y26 : word), fl0 = Cont sa -> winv asz bsz sa -> w_symbol sa < asz -> same_ctl s sa ->
MINV m2 (w_buf sa) -> 0 <= X2 < 2^64 -> X2 mod 2^32 = w_bitStream sa ->
evt usegs POST (UST 0x13b78 m2 y1 (Z_to_bv 64 (w_bitCount sa)) y6 y9 (Z_to_bv 64 X2) (Z_to_bv 64 (BUF + w_out sa)) y19
(Z_to_bv 64 (w_symbol sa)) (Z_to_bv 64 (w_threshold s)) y25 y26 (Z_to_bv 64 (w_nbBits s)) (Z_to_bv 64 (w_remaining s)))).
{ intros sa m2 X2 y1 y6 y9 y19 y25 y26 -> WIA SYA (C1 & C2 & C3 & C4) MV2 RX2 EX2.
apply bind_inv in WB. destruct WB as (sc & CB & WB). apply bind_inv in WB. destruct WB as (sd & FL & WB). injection WB as <-.
pose proof (wcount_flush_facts nc asz bsz safe sa sc sd CB FL WIA SYA NCR) as (WID & SYD & CTL).
rewrite <- C1, <- C2, <- C3.
eapply (B_ wr_count sa sc sd); [exact WIA | exact SYA | exact RX2 | exact EX2 | exact MV2 | exact CB | exact FL | | ].
- intros m3 X3 z9 z19 z22 z25 z26 CND3 MV3 RX3 EX3.
eapply (IH sd sf); [exact WID | exact CND3 | exact RX3 | exact EX3 | exact MV3 | exact WL | exact K].
- intros m3 X3 z1 z6 z9 z19 z22 z24 z25 z26 z28 CND3 MV3 RX3 EX3.
destruct f as [|f']; [cbn in WL; discriminate|]. rewrite wloop_S in WL. rewrite CND3 in WL. injection WL as <-.
apply K; assumption. }
destruct (w_previousIs0 s) eqn:P0; cbn [negb Z.b2z].
-
zstep. zstep. if_true.
pose proof (wzero_block_facts nc asz bsz safe s fl0 ZB WI CS) as ZF.
eapply (B_ wr_zero s fl0); [exact WI | exact CS | exact RX | exact EX | exact MV | exact ZB | | ].
+ intros sa m2 X' y1 y6 y9 y19 y25 y26 -> MV2 RX2 EX2. destruct ZF as (WIA & CTL & SYA & _).
eapply (CNT sa); [reflexivity | exact WIA | lia | exact CTL | exact MV2 | exact RX2 | exact EX2].
+ intros sa y1 y6 y9 y19 y22' y25 y26 ->. destruct ZF as (SYA & BUA & OUA & BSA & BCA & (C1 & C2 & C3 & C4)).
injection WB as <-. injection WL as <-.
rewrite <- OUA, <- BCA, <- C1.
apply K; [ | rewrite BUA; exact MV | exact RX | rewrite BSA; exact EX].
destruct WI as (LB & RO & RB & BC & SY & RM & NBI & TH).
unfold winv. rewrite BUA, OUA, BSA, BCA, SYA, C1, C2, C3. repeat split; try assumption; try lia.
-
injection ZB as <-.
zstep. zstep. if_false. zstep. zstep.
eapply (CNT s); [reflexivity | exact WI | exact CS | unfold same_ctl; repeat split | exact MV | exact RX | exact EX].
Qed.
Lemma wr_finish : forall sf m1 X (y1 y6 y9 y19 y22 y24 y25 y26 y28 : word),
winv asz bsz sf -> MINV m1 (w_buf sf) -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream sf ->
wfinish bsz safe sf = Ok (buf', n) ->
evt usegs POST (UST 0x13c90 m1 y1 (Z_to_bv 64 (w_bitCount sf)) y6 y9 (Z_to_bv 64 X) (Z_to_bv 64 (BUF + w_out sf)) y19 y22
y24 y25 y26 y28 (Z_to_bv 64 (w_remaining sf))).
Proof using WRC.
intros sf m1 X y1 y6 y9 y19 y22 y24 y25 y26 y28 WI MV RX EX WF.
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
assert (STORES : forall (z11 z12 z31 : word), evt usegs POST
(MS (mkR y1 (Z_to_bv 64 (SP + -128)) gp tp (Z_to_bv 64 (w_bitCount sf)) y6 (Z_to_bv 64 1) (Z_to_bv 64 1) y9
(Z_to_bv 64 BUF) z11 z12 (Z_to_bv 64 X) (Z_to_bv 64 (BUF + w_out sf)) (Z_to_bv 64 (Z.b2z safe))
(Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 asz) (Z_to_bv 64 31) y19 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3)) y22
(Z_to_bv 64 3) y24 y25 y26 (Z_to_bv 64 1) y28 (Z_to_bv 64 (w_remaining sf)) (Z_to_bv 64 0) z31)
F (Z_to_bv 64 0x13cf8) fc None m1 (seg_rom usegs))).
{ intros z11 z12 z31.
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep.
u8_sok BA (w_out sf). zstep.
u8_store BA (w_out sf) (to_byte (w_bitStream sf)). { unfold to_byte. rewrite <- EX. change (2^32) with 4294967296. lia. }
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. zstep. rewrite (swrap32_small (w_bitCount sf + 7)) by lia.
u8_sok BA (w_out sf + 1). zstep.
u8_store BA (w_out sf + 1) (to_byte (w_bitStream sf / 2^8)).
{ unfold to_byte. rewrite <- EX. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^8) with 256. lia. }
zstep. if_cases G3; unfold bv_lts in G3; rewrite !signed_lit in G3 by lia; zify_bool G3; [exfalso; lia|].
zstep. zstep.
assert (E61 : Z.shiftr (Z.shiftl (w_bitCount sf + 7) 1 mod 18446744073709551616) 61 = 0).
{ rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
rewrite Z.mod_small by lia. apply Z.div_small. change (2^61) with 2305843009213693952. lia. }
rewrite E61.
zstep. zstep.
rewrite (swrap32_small (w_bitCount sf + 7)) by lia. rewrite (Z.shiftr_div_pow2 (w_bitCount sf + 7) 3) by lia. change (2^3) with 8.
set (q := (w_bitCount sf + 7) / 8).
assert (RQ : 0 <= q < 5) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (swrap32_small q) by lia.
pose proof wout_le as NLE.
assert (QE : q = Z.quot (w_bitCount sf + 7) 8) by (subst q; rewrite Z.quot_div_nonneg by lia; reflexivity).
zstep.
zstep. if_cases G4; zify_cond G4; [exfalso; lia|].
zstep. zstep. zstep. zstep.
lazymatch goal with |- context [Z.lxor (w_bitCount sf + 7) ?k <? ?j] =>
replace (Z.lxor (w_bitCount sf + 7) k <? j) with false
by (symmetry; apply Z.ltb_ge; change k with (2^63); rewrite zb_lxor_pow2_small by lia; change (2^63) with k; lia) end.
rewrite ?(Z.mod_small (q + (BUF + w_out sf))) by lia.
replace (q + (BUF + w_out sf) <? q) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [Z.b2z]. change (Z.lxor (Z.lxor 0 0) 1) with 1.
zstep. if_cases G5; zify_cond G5; [exfalso; lia|].
zstep. zstep.
assert (EQ10 : q + (BUF + w_out sf) - BUF = w_out sf + Z.quot (w_bitCount sf + 7) 8) by lia.
rewrite EQ10, EN.
do 13 zstep. zstep.
release_frame FA SA SP.
zstep.
apply evt_done. unfold fse_write_post. do 14 eexists. eexists. split; [reflexivity|].
split; [exact MUA|]. split; [exact WMA|]. split; [exact MIA|]. split; [exact SA|]. rewrite <- EB. exact BA. }
zstep. zstep. if_cases J0; zify_cond J0; [exfalso; lia|].
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
- rewrite (ite_true _ safe _ _ SAFE). apply STORES.
- apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
rewrite SAFE in CK. cbn [negb andb] in CK. apply Z.ltb_ge in CK.
zstep. zstep. if_cases J1; zify_cond J1; [exfalso; lia|].
zstep. zstep. if_cases J2; zify_cond J2; [exfalso; lia|].
zstep. if_cases J3; zify_cond J3; [| exfalso; lia]. apply STORES.
Qed.
Lemma winit_ok : forall buf, 5 <= tl <= 12 ->
winit buf tl = Ok (mkW buf 0 (tl - 5) 4 0 (2^tl + 1) (2^tl) (tl + 1) false).
Proof using WRC.
intros buf TLR. unfold winit, assert, FSE_MIN_TABLELOG.
replace ((0 <=? tl) && (tl <? 31)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [bind]. rewrite shl32_ok by lia. cbn [bind]. change (2^0) with 1.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). rewrite Z.mul_1_r.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). rewrite Z.add_0_l.
rewrite (u32_id (tl - 5)) by (change (2^32) with 4294967296; lia). reflexivity.
Qed.
Lemma wr_main : write_ncount_generic buf0 nc msv tl safe = Ok (buf', n) -> 5 <= tl <= 12 ->
evt usegs POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BUF) (Z_to_bv 64 bsz) (Z_to_bv 64 NC) (Z_to_bv 64 msv) (Z_to_bv 64 tl)
(Z_to_bv 64 (Z.b2z safe)) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x13978) fc None m (seg_rom usegs)).
Proof using All.
intros GOK TLR.
pose proof (write_generic_bsz _ _ _ _ _ _ _ GOK TLR ltac:(lia) NCR) as B2. unfold FseNCount.Zlength in B2.
unfold write_ncount_generic in GOK. cbv zeta in GOK. rewrite (winit_ok buf0 TLR) in GOK. cbn [bind] in GOK.
apply bind_inv in GOK. destruct GOK as (sf & WL & WF). unfold FseNCount.Zlength in WL, WF.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl usegs m) as WM.
pose proof ST as (LO0 & _ & _).
pose proof (u8arr_bound _ _ _ _ BUF0) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NCB) as NB. rewrite u16s_length, length_map in NB.
assert (P2 : 32 <= 2^tl <= 4096).
{ split; [change 32 with (2^5)| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia. }
carve_frame 128%nat ST.
apply (rw_cells_split_CB _ _ _ [] _ _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
do 14 zstep.
zstep. zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. zstep. zstep.
replace (0 <? BUF) with true by (symmetry; apply Z.ltb_lt; lia).
replace (BUF + bsz <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
cbn [Z.b2z]. change (Z.lxor 1 0) with 1.
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. sw32 (msv + 1). zstep. if_cases K; zify_cond K; [exfalso; lia|].
do 17 zstep. rewrite sllw_pow2 by lia.
do 12 zstep.
replace (BUF + bsz <? 2) with false in * by (symmetry; apply Z.ltb_ge; lia).
replace (BUF + bsz + -2 <? 1) with false in * by (symmetry; apply Z.ltb_ge; lia).
replace (0 <? NC) with true in * by (symmetry; apply Z.ltb_lt; lia).
cbn [Z.b2z] in *. change (Z.lxor 1 0) with 1 in *.
lazymatch goal with |- context [Z.land (Z.lxor 0 ?k) 1] => change (Z.land (Z.lxor 0 k) 1) with 1 end.
replace (Z.land NC 1) with (NC mod 2) by (first [exact (land_ones_mod NC 1 ltac:(lia)) | exact (eq_sym (land_ones_mod NC 1 ltac:(lia)))]).
rewrite NCEV. rewrite (zb_lxor_ones NC) by lia. sw32 (tl + 1). rewrite lor_pow2_1 by lia.
rewrite (Z.mod_small asz 4294967296) in FR by lia.
set (s0w := mkW buf0 0 (tl - 5) 4 0 (2^tl + 1) (2^tl) (tl + 1) false) in *.
replace (tl + -5) with (tl - 5) by lia.
eapply (evt_eq usegs _ _ (UST 0x13a44 _ (Z_to_bv 64 (w_symbol s0w)) (Z_to_bv 64 (w_bitCount s0w)) (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 s0w))))
_ (Z_to_bv 64 (tl - 5)) (Z_to_bv 64 (BUF + w_out s0w)) _ _ (Z_to_bv 64 (w_threshold s0w)) _ _
(Z_to_bv 64 (w_nbBits s0w)) (Z_to_bv 64 (w_remaining s0w)))).
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
- intros m2 X' y1 y6 y9 y19 y22 y24 y25 y26 y28 WIF MV2 RX2 EX2.
eapply (wr_finish sf); [exact WIF | exact MV2 | exact RX2 | exact EX2 | exact WF].
Qed.
End LOOP.
Lemma lxor_b2z_1 : forall b : bool, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof using Type. intros [|]; reflexivity. Qed.
Lemma wr_body : evt usegs POST
(MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BUF) (Z_to_bv 64 bsz) (Z_to_bv 64 NC) (Z_to_bv 64 msv) (Z_to_bv 64 tl)
a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 PFSE_WRITE) fc None m (seg_rom usegs)).
Proof using All.
unfold PFSE_WRITE.
pose proof WOK as WOK'. unfold write_ncount, FSE_MAX_TABLELOG, FSE_MIN_TABLELOG in WOK'.
destruct (Z.ltb_spec 12 tl) as [TL12|TL12]; [discriminate|].
destruct (Z.ltb_spec tl 5) as [TL5|TL5]; [discriminate|].
assert (GOK : write_ncount_generic buf0 nc msv tl (negb (FseNCount.Zlength buf0 <? write_bound msv tl)) = Ok (buf', n)).
{ destruct (FseNCount.Zlength buf0 <? write_bound msv tl); exact WOK'. }
clear WOK'. unfold FseNCount.Zlength in GOK.
zstep. zstep.
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
Qed.
End WR.
Theorem fse_write_proof : fse_write_stmt.
Proof.
intros until lo. intros BUF0 BUFB NCB NCR WOK MSV TL BSZ BUFNZ NCNZ NCEV BUFW NCW ST LO RSP SEPB SEPN SEPBN MI -> -> -> -> ->.
unfold FSE_WRITE_STACK in *.
eapply wr_body; eassumption.
Qed.
