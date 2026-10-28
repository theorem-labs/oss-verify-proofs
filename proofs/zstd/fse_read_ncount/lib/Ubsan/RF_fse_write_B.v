(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseWriteModel FseWalkArith.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_write_A.
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
Ltac lts_lit K := unfold bv_lts in K; rewrite !signed_lit in K by lia; zify_bool K.
Notation FRAMEC := (RF_fse_write_A.FRAMEC ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 msv).
Notation MINV := (RF_fse_write_A.MINV ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SP BUF NC buf0 nc msv lo).
Ltac minv_close BA NA FA SA MUA WMA MIA :=
split; [exact BA|]; split; [exact NA|]; split; [exact FA|]; split; [exact SA|]; split; [exact MUA|]; split; [exact WMA| exact MIA].
Section LOOP.
Variable safe : bool.
Notation A_ l := (l ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ BUFNZ NCNZ NCEV BUFW NCW LO RSP SEPB SEPN SEPBN safe).
Notation UST pc mm x1 x5 x6 x9 x13 x14 x19 x22 x24 x25 x26 x28 x29 :=
(MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 (Z_to_bv 64 1) (Z_to_bv 64 1) x9
(Z_to_bv 64 BUF) (Z_to_bv 64 (BUF + bsz)) (Z_to_bv 64 NC) x13 x14 (Z_to_bv 64 (Z.b2z safe))
(Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 asz) (Z_to_bv 64 31) x19 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3)) x22
(Z_to_bv 64 3) x24 x25 x26 (Z_to_bv 64 1) x28 x29 (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551615 - NC)))
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
Ltac wrap13 := let v := reg_val 13%Z in
lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
Lemma wr_zero_tail : forall s start2 sf m1 X (x1 x9 x19 x24 x25 x26 x28 x29 : word),
0 <= start2 -> start2 <= w_symbol s < start2 + 3 -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> 0 <= w_out s <= bsz -> MINV m1 (w_buf s) ->
bind (shl32 (u32 (w_symbol s - start2)) (w_bitCount s)) (fun v =>
wflush_if bsz safe (mkW (w_buf s) (w_out s) (u32 (w_bitStream s + v)) (w_bitCount s + 2)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s))) = Ok sf ->
(forall m2 X' (y6 : word), MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evt usegs POST (UST 0x13b78 m2 x1 (Z_to_bv 64 (w_bitCount sf)) y6 x9 (Z_to_bv 64 X') (Z_to_bv 64 (BUF + w_out sf)) x19
(Z_to_bv 64 (w_symbol s)) x24 x25 x26 x28 x29)) ->
evt usegs POST (UST 0x13b28 m1 x1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 start2) x9 (Z_to_bv 64 X) (Z_to_bv 64 (BUF + w_out s)) x19
(Z_to_bv 64 (w_symbol s)) x24 x25 x26 x28 x29).
Proof using WRC.
intros s start2 sf m1 X x1 x9 x19 x24 x25 x26 x28 x29 S0 SR SY RX EX LB RO (BA & NA & FA & SA & MUA & WMA & MIA) H K.
apply bind_inv in H. destruct H as (v & SH & FL). apply shl32_inv in SH. destruct SH as [BC ->].
pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold RF_fse_write_A.FRAMEC in FA.
rewrite (u32_id (w_symbol s - start2)) in FL by (change (2^32) with 4294967296; lia).
zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
zstep. sw32 (w_symbol s - start2).
zstep. rewrite shiftl_mod32 by lia.
zstep.
assert (EX1 : ((bv_swrap 32 ((w_symbol s - start2) * 2 ^ w_bitCount s) + X) mod 2^64) mod 2^32
= u32 (w_bitStream s + u32 ((w_symbol s - start2) * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296. rewrite swrap32_eq. lia. }
assert (RX1 : 0 <= (bv_swrap 32 ((w_symbol s - start2) * 2 ^ w_bitCount s) + X) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap13. revert EX1 RX1. generalize ((bv_swrap 32 ((w_symbol s - start2) * 2 ^ w_bitCount s) + X) mod 2^64). intros X1 EX1 RX1.
set (bs1 := u32 (w_bitStream s + u32 ((w_symbol s - start2) * 2 ^ w_bitCount s))) in *.
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
zstep. zstep.
apply wflush_if_inv in FL. cbn [w_bitCount] in FL.
if_cases B; zify_cond B.
-
destruct FL as [[G _]|[_ ->]]; [exfalso; lia|].
zstep. sw32 (w_bitCount s + 2).
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact RX1 | cbn [w_bitStream]; exact EX1].
- destruct FL as [[_ FL]|[G _]]; [| exfalso; lia].
apply wflush_inv in FL. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL.
destruct FL as (OE & O0 & O1 & ->). unfold FseNCount.Zlength in O1.
assert (FLUSH : evt usegs POST (UST 0x13b4c m1 x1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 15) x9 (Z_to_bv 64 X1)
(Z_to_bv 64 (BUF + w_out s)) x19 (Z_to_bv 64 (w_symbol s)) x24 x25 x26 x28 x29)).
{ zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)).
{ unfold to_byte. rewrite ?Z.shiftr_div_pow2 by lia. rewrite <- EX1. change (2^8) with 256. change (2^32) with 4294967296. lia. }
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
zstep. zstep. sw32 (w_bitCount s + -14).
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep.
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
setreg 14%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
replace (w_bitCount s + -14) with (w_bitCount s + 2 - 16) by lia.
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA
| change (2^32) with 4294967296 in RB3; change (2^64) with 18446744073709551616; lia
| cbn [w_bitStream]; apply Z.mod_small; exact RB3]. }
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
+ rewrite (ite_true _ safe _ _ SAFE). apply FLUSH.
+ apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
destruct OE as [OE|OE]; [congruence|].
zstep. if_false. zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply FLUSH.
Qed.
Lemma wr_zero_mid : forall f s start1 s2' start2 sf m1 X (x9 x19 x24 x25 x26 x28 x29 : word),
0 <= start1 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
0 <= w_bitStream s < 2^32 -> 0 <= w_bitCount s ->
zlen (w_buf s) = bsz -> 0 <= w_out s <= bsz -> MINV m1 (w_buf s) ->
run3 (S f) s start1 = Ok (s2', start2) ->
bind (shl32 (u32 (w_symbol s2' - start2)) (w_bitCount s2')) (fun v =>
wflush_if bsz safe (mkW (w_buf s2') (w_out s2') (u32 (w_bitStream s2' + v)) (w_bitCount s2' + 2)
(w_symbol s2') (w_remaining s2') (w_threshold s2') (w_nbBits s2') (w_previousIs0 s2'))) = Ok sf ->
(forall m2 X' (y6 y19 y25 : word), MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evt usegs POST (UST 0x13b78 m2 (Z_to_bv 64 start1) (Z_to_bv 64 (w_bitCount sf)) y6 x9 (Z_to_bv 64 X') (Z_to_bv 64 (BUF + w_out sf)) y19
(Z_to_bv 64 (w_symbol s)) x24 y25 x26 x28 x29)) ->
evt usegs POST (UST 0x13b04 m1 (Z_to_bv 64 start1) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 start1) x9 (Z_to_bv 64 X)
(Z_to_bv 64 (BUF + w_out s)) x19 (Z_to_bv 64 (w_symbol s)) x24 x25 x26 x28 x29).
Proof using WRC.
intros f s start1 s2' start2 sf m1 X x9 x19 x24 x25 x26 x28 x29 S1 SY RX EX RB BC LB RO MV R3 TLH K.
pose proof (run3_facts _ _ _ _ _ R3 RB BC) as ((D1 & D2 & D3 & D4) & SY2 & B2 & O2 & RB2 & BC2 & ST2 & SR2).
specialize (SR2 ltac:(lia)).
zstep. sw32 (start1 + 3). zstep.
if_cases B; zify_cond B.
- rewrite run3_S in R3. replace (start1 + 3 <=? w_symbol s) with false in R3 by (symmetry; apply Z.leb_gt; lia).
injection R3 as <- <-.
eapply (wr_zero_tail s start1 sf); [lia | lia | lia | exact RX | exact EX | exact LB | exact RO | exact MV | exact TLH | ].
intros. apply K; assumption.
- eapply (A_ wr_run3 f s start1 s2' start2); [lia | lia | lia | exact RX | exact EX | exact R3 | ].
intros X' y19 y25 RX' EX'.
rewrite <- SY2, <- O2.
eapply (wr_zero_tail s2' start2 sf);
[ lia | lia | lia | exact RX' | exact EX' | rewrite B2; exact LB | lia | rewrite B2; exact MV | exact TLH | ].
intros. rewrite SY2. apply K; assumption.
Qed.
Lemma wr_zero : forall s fl m1 X (x9 x19 x22 x24 x25 x26 x28 x29 : word),
winv asz bsz s -> w_symbol s < asz -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s -> MINV m1 (w_buf s) ->
wzero_block nc asz bsz safe s = Ok fl ->
(forall sa m2 X' (y1 y6 y9 y19 y25 y26 : word), fl = Cont sa -> MINV m2 (w_buf sa) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sa ->
evt usegs POST (UST 0x13b78 m2 y1 (Z_to_bv 64 (w_bitCount sa)) y6 y9 (Z_to_bv 64 X') (Z_to_bv 64 (BUF + w_out sa)) y19
(Z_to_bv 64 (w_symbol sa)) x24 y25 y26 x28 x29)) ->
(forall sa (y1 y6 y9 y19 y22 y25 y26 : word), fl = Brk sa ->
evt usegs POST (UST 0x13c90 m1 y1 (Z_to_bv 64 (w_bitCount s)) y6 y9 (Z_to_bv 64 X) (Z_to_bv 64 (BUF + w_out s)) y19 y22
x24 y25 y26 x28 x29)) ->
evt usegs POST (UST 0x13a54 m1 (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 0) x9 (Z_to_bv 64 X)
(Z_to_bv 64 (BUF + w_out s)) x19 x22 x24 x25 x26 x28 x29).
Proof using WRC.
intros s fl m1 X x9 x19 x22 x24 x25 x26 x28 x29 WI SYA RX EX MV H KC KB.
pose proof WI as (LB & RO & RB & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & FA & SA & MUA & WMA & MIA). unfold RF_fse_write_A.FRAMEC in FA.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
unfold wzero_block in H. apply bind_inv in H. destruct H as (sym & SK & H).
pose proof (skip_zeros_range nc asz _ (w_symbol s) sym ltac:(lia) SK) as SR.
zstep. zstep. if_cases J0; zify_cond J0; [exfalso; lia|].
zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
do 7 zstep.
rewrite zext32_sh31 by lia. rewrite (Z.mod_small (w_symbol s) 4294967296) by lia.
eapply (A_ wr_skip _ (w_symbol s) sym); [lia | exact NA | exact SK | | ].
- intros y6 y19 y25 y26 SR'.
replace (sym =? asz) with false in H by (symmetry; apply Z.eqb_neq; lia).
apply bind_inv in H. destruct H as ([sa start1] & R24 & H).
apply bind_inv in H. destruct H as ([s2' start2] & R3 & H).
apply bind_inv in H. destruct H as (v & SH & H). apply bind_inv in H. destruct H as (sf & FL & H). injection H as <-.
set (s0' := mkW (w_buf s) (w_out s) (w_bitStream s) (w_bitCount s) sym (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s)) in *.
pose proof (run24_facts bsz safe _ _ _ _ _ R24 ltac:(exact LB) RB RO) as ((C1 & C2 & C3 & C4) & SY1 & BC1 & LB1 & RO1 & RB1 & ST1 & SR1).
cbn [s0' w_symbol w_bitCount] in SY1, BC1, SR1. specialize (SR1 ltac:(lia)). unfold FseNCount.Zlength in LB1.
pose proof (run3_facts _ _ _ _ _ R3 RB1 ltac:(lia)) as ((D1 & D2 & D3 & D4) & SY2 & B2 & O2 & RB2 & BC2 & ST2 & SR2).
assert (TLH : bind (shl32 (u32 (w_symbol s2' - start2)) (w_bitCount s2')) (fun v =>
wflush_if bsz safe (mkW (w_buf s2') (w_out s2') (u32 (w_bitStream s2' + v)) (w_bitCount s2' + 2)
(w_symbol s2') (w_remaining s2') (w_threshold s2') (w_nbBits s2') (w_previousIs0 s2'))) = Ok sf).
{ assert (ES : sym = w_symbol s2') by congruence. rewrite ES in SH. rewrite SH. cbn [bind]. exact FL. }
assert (MID : forall m2 X1 (z9 z19 z25 z26 : word), MINV m2 (w_buf sa) -> 0 <= X1 < 2^64 -> X1 mod 2^32 = w_bitStream sa ->
evt usegs POST (UST 0x13b04 m2 (Z_to_bv 64 start1) (Z_to_bv 64 (w_bitCount sa)) (Z_to_bv 64 start1) z9 (Z_to_bv 64 X1)
(Z_to_bv 64 (BUF + w_out sa)) z19 (Z_to_bv 64 (w_symbol sa)) x24 z25 z26 x28 x29)).
{ intros m2 X1 z9 z19 z25 z26 MV2 RX1 EX1.
eapply (wr_zero_mid _ sa start1 s2' start2 sf); [lia | lia | exact RX1 | exact EX1 | exact RB1 | lia | exact LB1 | exact RO1 | exact MV2 | exact R3 | exact TLH | ].
intros m3 X' w6 w19 w25 MV3 RX3 EX3.
assert (SYF : w_symbol sf = w_symbol sa).
{ apply bind_inv in TLH. destruct TLH as (v' & _ & FL'). apply wflush_if_inv in FL'. destruct FL' as [[_ FL']|[_ ->]].
- apply wflush_inv in FL'. destruct FL' as (_ & _ & _ & ->). cbn [w_symbol]. exact SY2.
- cbn [w_symbol]. exact SY2. }
rewrite <- SYF. apply (KC sf m3 X'); [reflexivity | exact MV3 | exact RX3 | exact EX3]. }
zstep. if_cases J1; zify_cond J1; [exfalso; lia|].
zstep. sw32 (w_symbol s + 24). zstep.
if_cases J2; zify_cond J2.
+ eapply (A_ wr_run24 _ s0' (w_symbol s) sa start1); [lia | cbn [s0' w_symbol]; lia | cbn [s0' w_symbol]; lia
| exact RX | exact EX | exact LB | exact MV | exact R24 | ].
intros m2 X' z19 z26 MV2 RX2 EX2. cbn [s0' w_symbol w_bitCount]. rewrite <- SY1. rewrite <- BC1.
apply MID; assumption.
+ rewrite run24_S in R24. cbn [s0' w_symbol] in R24.
replace (w_symbol s + 24 <=? sym) with false in R24 by (symmetry; apply Z.leb_gt; lia).
injection R24 as <- <-.
zstep. zstep.
apply (MID m1 X); [exact MV | exact RX | exact EX].
- intros y6 y19 y25 y26 ->.
replace (asz =? asz) with true in H by (symmetry; apply Z.eqb_refl). injection H as <-.
zstep.
eapply KB. reflexivity.
Qed.
Lemma wr_count : forall s sc sd m1 X (x1 x6 x9 x19 x25 x26 : word),
winv asz bsz s -> w_symbol s < asz -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s -> MINV m1 (w_buf s) ->
wcount_block nc s = Ok sc -> wflush_if bsz safe sc = Ok sd ->
(forall m2 X' (y9 y19 y22 y25 y26 : word), (w_symbol sd <? asz) && (1 <? w_remaining sd) = true ->
MINV m2 (w_buf sd) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sd ->
evt usegs POST (UST 0x13a44 m2 (Z_to_bv 64 (w_symbol sd)) (Z_to_bv 64 (w_bitCount sd))
(Z_to_bv 64 (Z.b2z (negb (w_previousIs0 sd)))) y9 (Z_to_bv 64 X') (Z_to_bv 64 (BUF + w_out sd)) y19 y22
(Z_to_bv 64 (w_threshold sd)) y25 y26 (Z_to_bv 64 (w_nbBits sd)) (Z_to_bv 64 (w_remaining sd)))) ->
(forall m2 X' (y1 y6 y9 y19 y22 y24 y25 y26 y28 : word), (w_symbol sd <? asz) && (1 <? w_remaining sd) = false ->
MINV m2 (w_buf sd) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sd ->
evt usegs POST (UST 0x13c90 m2 y1 (Z_to_bv 64 (w_bitCount sd)) y6 y9 (Z_to_bv 64 X') (Z_to_bv 64 (BUF + w_out sd)) y19 y22
y24 y25 y26 y28 (Z_to_bv 64 (w_remaining sd)))) ->
evt usegs POST (UST 0x13b78 m1 x1 (Z_to_bv 64 (w_bitCount s)) x6 x9 (Z_to_bv 64 X) (Z_to_bv 64 (BUF + w_out s)) x19
(Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_threshold s)) x25 x26 (Z_to_bv 64 (w_nbBits s)) (Z_to_bv 64 (w_remaining s))).
Proof using WRC.
intros s sc sd m1 X x1 x6 x9 x19 x25 x26 WI SYA RX EX MV CB FL KL KE.
pose proof WI as (LB & RO & RB & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & FA & SA & MUA & WMA & MIA).
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof (wcount_flush_facts nc asz bsz safe s sc sd CB FL WI SYA NCR) as (WID & SYD & CTL).
pose proof (wcount_block_inv nc s sc CB) as CI. cbv zeta in CI. destruct CI as (thr' & nb' & LR & BCR & R1 & SHR & ESC).
unfold FseNCount.Zlength in LR.
pose proof (Forall_Znth _ _ (w_symbol s) NCR LR) as CR. cbv beta in CR.
set (count := Znth (w_symbol s) nc) in *.
set (rem' := w_remaining s - (if count <? 0 then - count else count)) in *.
pose proof (shrink_facts _ _ _ _ _ _ SHR R1 ltac:(lia) TH) as (NB' & TH').
assert (THR : 1 <= w_threshold s <= 4096).
{ rewrite TH. pose proof (Z.pow_pos_nonneg 2 (w_nbBits s - 1) ltac:(lia) ltac:(lia)). split; [lia|]. change 4096 with (2^12). apply Z.pow_le_mono_r; lia. }
pose proof (u16_znth usegs m1 NC nc (w_symbol s) (Z_to_bv 64 (NC + 2 * w_symbol s)) NA LR ltac:(reflexivity)) as RD.
set (mx := 2 * w_threshold s - 1 - w_remaining s) in *.
set (count2 := if w_threshold s <=? count + 1 then count + 1 + mx else count + 1) in *.
set (bs1 := u32 (w_bitStream s + u32 (u32 count2 * 2 ^ w_bitCount s))) in *.
set (bc1 := w_bitCount s + w_nbBits s - (if count2 <? mx then 1 else 0)) in *.
assert (RMX : - 8192 <= mx <= 8192) by (subst mx; lia).
assert (RC2 : - 65536 <= count2 < 65536) by (subst count2; destruct (w_threshold s <=? count + 1); lia).
assert (RBC1 : 0 <= bc1 <= 44) by (subst bc1; destruct (count2 <? mx); lia).
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
destruct CTL as (CT1 & CT2 & CT3 & CT4). rewrite ESC in CT1, CT2, CT3, CT4.
cbn [w_remaining w_threshold w_nbBits w_previousIs0] in CT1, CT2, CT3, CT4.
assert (RR : 1 <= rem' <= 8192) by (rewrite <- CT1; destruct WID as (_ & _ & _ & _ & _ & RQ & _); exact RQ).
assert (TAIL : forall m2 X3 (y1 y6 y9 y19 y26 : word), MINV m2 (w_buf sd) -> 0 <= X3 < 2^64 -> X3 mod 2^32 = w_bitStream sd ->
evt usegs POST (UST 0x13c7c m2 y1 (Z_to_bv 64 (w_bitCount sd)) y6 y9 (Z_to_bv 64 X3) (Z_to_bv 64 (BUF + w_out sd)) y19
(Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 thr') (Z_to_bv 64 count2) y26 (Z_to_bv 64 nb') (Z_to_bv 64 rem'))).
{ intros m2 X3 y1 y6 y9 y19 y26 MV2 RX3 EX3.
zstep. sw32 (w_symbol s + 1). zstep.
if_cases J1; zify_cond J1.
- rewrite <- CT1. apply KE; [ | exact MV2 | exact RX3 | exact EX3].
rewrite SYD. replace (w_symbol s + 1 <? asz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- zstep. zstep.
lazymatch goal with |- context [Z.ltb 0 ?e] => replace (Z.ltb 0 e) with (negb (count2 =? 1)) end.
2:{ destruct (Z.eqb_spec count2 1) as [E1|N1]; cbn [negb]; symmetry; [apply Z.ltb_ge| apply Z.ltb_lt]; lia. }
zstep. if_cases J2; zify_cond J2.
+ rewrite <- CT1, <- CT2, <- CT3, <- CT4, <- SYD.
apply KL; [ | exact MV2 | exact RX3 | exact EX3].
rewrite SYD, CT1. replace (w_symbol s + 1 <? asz) with true by (symmetry; apply Z.ltb_lt; lia).
replace (1 <? rem') with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+ rewrite <- CT1. apply KE; [ | exact MV2 | exact RX3 | exact EX3].
rewrite CT1. replace (1 <? rem') with false by (symmetry; apply Z.ltb_ge; lia). apply andb_false_r. }
assert (P34 : forall (y9 y19 y26 : word), evt usegs POST
(UST 0x13c34 m1 (Z_to_bv 64 bc1) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 count2) y9 (Z_to_bv 64 X) (Z_to_bv 64 (BUF + w_out s)) y19
(Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 thr') (Z_to_bv 64 count2) y26 (Z_to_bv 64 nb') (Z_to_bv 64 rem'))).
{ intros y9 y19 y26.
zstep. zstep. wrap13.
let v := reg_val 13%Z in lazymatch v with Z_to_bv 64 ?e => remember e as X1 eqn:HX1 end.
assert (EX1 : X1 mod 2^32 = bs1) by (rewrite HX1; exact (container_add X (w_bitStream s) count2 (w_bitCount s) BCR EX)).
assert (RX1 : 0 <= X1 < 2^64) by (rewrite HX1; apply Z.mod_pos_bound; lia).
clear HX1.
zstep. zstep.
pose proof FL as FL'. rewrite ESC in FL'. apply wflush_if_inv in FL'. cbn [w_bitCount] in FL'.
if_cases J3; lts_lit J3.
- destruct FL' as [[G _]|[_ ESD]]; [exfalso; lia|]. subst sd.
zstep.
eapply TAIL; [cbn [w_buf]; exact MV | exact RX1 | cbn [w_bitStream]; exact EX1].
- destruct FL' as [[_ FLH]|[G _]]; [| exfalso; lia].
apply wflush_inv in FLH. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FLH.
destruct FLH as (OE & O0 & O1 & ESD). unfold FseNCount.Zlength in O1. subst sd.
pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof SA as (LO0 & _ & _). unfold RF_fse_write_A.FRAMEC in FA.
assert (FLUSH : evt usegs POST (UST 0x13c50 m1 (Z_to_bv 64 bc1) (Z_to_bv 64 17) (Z_to_bv 64 count2) y9 (Z_to_bv 64 X1)
(Z_to_bv 64 (BUF + w_out s)) y19 (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 thr') (Z_to_bv 64 count2) y26 (Z_to_bv 64 nb')
(Z_to_bv 64 rem'))).
{ zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)).
{ unfold to_byte. rewrite <- EX1. rewrite ?Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^8) with 256. lia. }
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
zstep. zstep. sw32 (bc1 - 16).
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep.
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
setreg 14%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
eapply TAIL; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA
| change (2^32) with 4294967296 in RB3; lia
| cbn [w_bitStream]; apply Z.mod_small; exact RB3 ]. }
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
+ rewrite (ite_true _ safe _ _ SAFE). apply FLUSH.
+ apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
destruct OE as [OE|OE]; [congruence|].
zstep. if_false. zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply FLUSH. }
assert (P1C : forall (y9 y19 y25 : word), evt usegs POST
(UST 0x13be0 m1 (Z_to_bv 64 mx) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 count2) y9 (Z_to_bv 64 X) (Z_to_bv 64 (BUF + w_out s)) y19
(Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_threshold s)) y25 (Z_to_bv 64 count) (Z_to_bv 64 (w_nbBits s)) (Z_to_bv 64 (w_remaining s)))).
{ intros y9 y19 y25.
zstep. if_cases H1; zify_cond H1; [exfalso; lia|].
zstep. zstep. sw32 (w_bitCount s + w_nbBits s).
zstep. if_cases H2; zify_cond H2; [exfalso; lia|].
zstep. sw32 (w_bitCount s + w_nbBits s). zstep. sw32 count2.
zstep. rewrite slt_lit_rr by lia.
zstep. rewrite (zb_b2z_if (count2 <? mx)). fold bc1. rewrite (swrap32_small bc1) by lia.
zstep. fold bc1.
zstep. if_cases H3; zify_cond H3; [exfalso; lia|].
zstep. rewrite sraiw31_sign by lia.
zstep. zstep. zstep. rewrite abs_via_sign by (fold rem'; lia). fold rem'.
zstep. if_cases J0; lts_lit J0; [exfalso; lia|].
zstep.
if_cases J1; lts_lit J1.
- rewrite shrink_S in SHR. replace (rem' <? w_threshold s) with false in SHR by (symmetry; apply Z.ltb_ge; lia).
injection SHR as <- <-. apply P34.
- eapply (A_ wr_shrink 63%nat rem' (w_threshold s) (w_nbBits s) thr' nb'); [lia | lia | lia | exact TH | exact SHR | ].
intros y9'. apply P34. }
zstep. zstep. rewrite zext32_sh31 by lia. zstep.
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. zstep.
replace (NC + 2 * w_symbol s <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. change (Z.lxor 1 0) with 1.
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
zstep. rewrite land_1_mod2.
assert (EV : (NC + 2 * w_symbol s) mod 2 = 0) by (Z.div_mod_to_equations; lia).
zstep. if_cases G4; zify_cond G4; [exfalso; apply G4; exact EV|].
zstep. zstep. sw32 (w_threshold s + 1073741824).
zstep. if_cases G5; lts_lit G5; [exfalso; lia|].
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2. sw32 (w_threshold s * 2).
zstep. sw32 (w_threshold s * 2 + -1).
zstep. if_cases G6; lts_lit G6; [exfalso; lia|].
zstep. sw32 mx. zstep. setreg 19%Z (Z_to_bv 64 mx) ltac:(f_equal; subst mx; lia).
zstep. if_cases G7; zify_cond G7; [exfalso; lia|].
zstep. fold count. rewrite sx16_short by exact CR.
zstep. zstep.
if_cases J1; lts_lit J1.
- assert (EC2 : count2 = count + 1) by (subst count2; replace (w_threshold s <=? count + 1) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
setreg 6%Z (Z_to_bv 64 count2) ltac:(f_equal; lia). apply P1C.
- assert (EC2 : count2 = count + 1 + mx) by (subst count2; replace (w_threshold s <=? count + 1) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
zstep. zstep. sw32 (count + 1 + mx).
zstep. if_cases G8; zify_cond G8; [exfalso; lia|].
zstep. setreg 6%Z (Z_to_bv 64 count2) ltac:(f_equal; lia). apply P1C.
Qed.
End LOOP.
End WR.
