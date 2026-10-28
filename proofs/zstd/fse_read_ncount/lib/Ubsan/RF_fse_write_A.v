(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseWriteModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface.
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
Definition FRAMEC : list cell :=
[C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 65535); C8 (Z_to_bv 64 asz);
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition MINV (m1 : fmem) (buf : list Z) : Prop :=
u8arr usegs m1 BUF (map (Z_to_bv 8) buf) /\ bytes_at usegs m1 NC (u16s (map (Z_to_bv 64) nc))
/\ rw_cells usegs m1 (SP + -128) FRAMEC /\ stk usegs m1 lo (SP + -128)
/\ munch W m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.
Ltac minv_close BA NA FA SA MUA WMA MIA :=
split; [exact BA|]; split; [exact NA|]; split; [exact FA|]; split; [exact SA|]; split; [exact MUA|]; split; [exact WMA| exact MIA].
Section LOOP.
Variable safe : bool.
Notation UST pc mm x1 x5 x6 x9 x13 x14 x19 x22 x24 x25 x26 x28 x29 :=
(MS (mkR x1 (Z_to_bv 64 (SP + -128)) gp tp x5 x6 (Z_to_bv 64 1) (Z_to_bv 64 1) x9
(Z_to_bv 64 BUF) (Z_to_bv 64 (BUF + bsz)) (Z_to_bv 64 NC) x13 x14 (Z_to_bv 64 (Z.b2z safe))
(Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 asz) (Z_to_bv 64 31) x19 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3)) x22
(Z_to_bv 64 3) x24 x25 x26 (Z_to_bv 64 1) x28 x29 (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551615 - NC)))
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
Ltac wrap13 := let v := reg_val 13%Z in
lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
Lemma wr_shrink : forall f rem thr nb thr' nb' m1 (x1 x5 x6 x9 x13 x14 x19 x22 x25 x26 : word),
rem < thr -> 1 <= rem -> 1 <= nb <= 13 -> thr = 2^(nb - 1) ->
shrink (S f) rem thr nb = Ok (thr', nb') ->
(forall (y9 : word), evt usegs POST (UST 0x13c34 m1 x1 x5 x6 y9 x13 x14 x19 x22 (Z_to_bv 64 thr') x25 x26
(Z_to_bv 64 nb') (Z_to_bv 64 rem))) ->
evt usegs POST (UST 0x13c20 m1 x1 x5 x6 x9 x13 x14 x19 x22 (Z_to_bv 64 thr) x25 x26 (Z_to_bv 64 nb) (Z_to_bv 64 rem)).
Proof using WRC.
induction f as [|f IH]; intros rem thr nb thr' nb' m1 x1 x5 x6 x9 x13 x14 x19 x22 x25 x26 LT R1 NB TH SH K.
- rewrite shrink_S in SH.
replace (rem <? thr) with true in SH by (symmetry; apply Z.ltb_lt; lia). cbn in SH. discriminate.
- rewrite shrink_S in SH. replace (rem <? thr) with true in SH by (symmetry; apply Z.ltb_lt; lia).
assert (NB2 : 2 <= nb). { destruct (Z.eq_dec nb 1) as [->|]; [|lia]. change (2^(1-1)) with 1 in TH. lia. }
assert (THB : 2 <= thr <= 4096).
{ rewrite TH. split; [change 2 with (2^1) at 1| change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia. }
assert (TH2 : thr / 2 = 2^(nb - 1 - 1)).
{ rewrite TH. replace (2 ^ (nb - 1)) with (2 ^ (nb - 1 - 1) * 2); [apply Z.div_mul; lia|].
rewrite Z.mul_comm, <- (Z.pow_succ_r 2 (nb - 1 - 1)) by lia. f_equal. lia. }
zstep. zstep. sw32 (nb + -1).
zstep. if_cases G; lts_lit G; [exfalso; lia|].
zstep. rewrite (swrap32_small thr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
rewrite swrap32_small by lia.
zstep.
if_cases B; lts_lit B.
+ replace (nb + -1) with (nb - 1) by lia.
eapply (IH rem (thr / 2) (nb - 1) thr' nb'); [lia| lia| lia| exact TH2| exact SH| exact K].
+ rewrite shrink_S in SH. replace (rem <? thr / 2) with false in SH by (symmetry; apply Z.ltb_ge; lia).
injection SH as <- <-. replace (nb - 1) with (nb + -1) in K by lia. apply K.
Qed.
Lemma wr_run3 : forall f s start s' start' m1 X (x1 x9 x14 x19 x24 x25 x26 x28 x29 : word),
0 <= start -> start + 3 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
run3 (S f) s start = Ok (s', start') ->
(forall X' (y19 y25 : word), 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evt usegs POST (UST 0x13b28 m1 x1 (Z_to_bv 64 (w_bitCount s')) (Z_to_bv 64 start') x9 (Z_to_bv 64 X') x14 y19
(Z_to_bv 64 (w_symbol s)) x24 y25 x26 x28 x29)) ->
evt usegs POST (UST 0x13b0c m1 x1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 start) x9 (Z_to_bv 64 X) x14 x19
(Z_to_bv 64 (w_symbol s)) x24 x25 x26 x28 x29).
Proof using WRC.
induction f as [|f IH]; intros s start s' start' m1 X x1 x9 x14 x19 x24 x25 x26 x28 x29 S0 S3 SY RX EX R3 K;
rewrite run3_S in R3; replace (start + 3 <=? w_symbol s) with true in R3 by (symmetry; apply Z.leb_le; lia);
apply bind_inv in R3; destruct R3 as (v & SH & R3); apply shl32_inv in SH; destruct SH as [BC ->].
- cbn in R3. discriminate.
- zstep. if_cases G; zify_cond G; [exfalso; lia|].
zstep. rewrite shiftl_mod32 by lia.
zstep. sw32 (w_bitCount s + 2). zstep. sw32 (start + 6). zstep. zstep.
assert (EX' : (bv_swrap 32 (3 * 2 ^ w_bitCount s) + X) mod 2^64 mod 2^32 = u32 (w_bitStream s + u32 (3 * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
rewrite swrap32_eq. Z.div_mod_to_equations. lia. }
zstep.
if_cases B; zify_cond B.
+ wrap13.
lazymatch type of R3 with run3 _ ?sn _ = _ =>
eapply (IH sn (start + 3) s' start'); [lia | cbn [w_symbol]; lia | cbn [w_symbol]; lia | apply Z.mod_pos_bound; lia
| cbn [w_bitStream]; exact EX' | exact R3 | ] end.
cbn [w_symbol w_bitCount]. exact K.
+ rewrite run3_S in R3. cbn [w_symbol] in R3.
replace (start + 3 + 3 <=? w_symbol s) with false in R3 by (symmetry; apply Z.leb_gt; lia).
injection R3 as <- <-. wrap13.
apply K; [apply Z.mod_pos_bound; lia | cbn [w_bitStream]; exact EX'].
Qed.
Lemma wr_skip : forall f sym sym' m1 (x1 x5 x9 x13 x14 x19 x24 x28 x29 : word),
0 <= sym < asz -> bytes_at usegs m1 NC (u16s (map (Z_to_bv 64) nc)) ->
skip_zeros nc asz (S f) sym = Ok sym' ->
(forall (y6 y19 y25 y26 : word), sym <= sym' < asz ->
evt usegs POST (UST 0x13aa4 m1 x1 x5 y6 x9 x13 x14 y19 (Z_to_bv 64 sym') x24 y25 y26 x28 x29)) ->
(forall (y6 y19 y25 y26 : word), sym' = asz ->
evt usegs POST (UST 0x13aa0 m1 x1 x5 y6 x9 x13 x14 y19 (Z_to_bv 64 sym') x24 y25 y26 x28 x29)) ->
evt usegs POST (UST 0x13a7c m1 x1 x5 (Z_to_bv 64 (2 * sym)) x9 x13 x14 x19 (Z_to_bv 64 sym) x24
(Z_to_bv 64 (NC + 2 * sym)) (Z_to_bv 64 (asz - sym)) x28 x29).
Proof using WRC.
induction f as [|f IH]; intros sym sym' m1 x1 x5 x9 x13 x14 x19 x24 x28 x29 SY NC1 SK KA KB;
rewrite skip_zeros_S in SK; replace (sym <? asz) with true in SK by (symmetry; apply Z.ltb_lt; lia);
apply bind_inv in SK; destruct SK as (c & LD & SK); apply load_inv in LD; destruct LD as [LR ->]; unfold FseNCount.Zlength in LR;
pose proof (Forall_Znth _ _ sym NCR LR) as CR; cbv beta in CR;
pose proof (bytes_at_bound _ _ _ _ NC1) as NB; rewrite u16s_length, length_map in NB;
pose proof (u16_znth usegs m1 NC nc sym (Z_to_bv 64 (NC + 2 * sym)) NC1 LR ltac:(reflexivity)) as RD;
(zstep; if_cases G1; zify_cond G1; [exfalso; lia|]);
(zstep; if_cases G2; zify_cond G2; [exfalso; lia|]).
- destruct (Z.eqb_spec (Znth sym nc) 0) as [E0|N0]; [cbn in SK; discriminate|]. injection SK as <-.
zstep. rewrite zx16_short by exact CR. zstep.
if_cases B; zify_cond B; [| exfalso; lia].
apply KA. lia.
- zstep. rewrite zx16_short by exact CR. zstep.
destruct (Z.eqb_spec (Znth sym nc) 0) as [E0|N0].
+ if_cases B; zify_cond B; [exfalso; lia|].
zstep. sw32 (sym + 1). zstep. zstep. zstep. zstep.
if_cases B2; zify_cond B2.
* replace (asz - sym + -1) with (asz - (sym + 1)) by lia. replace (NC + 2 * sym + 2) with (NC + 2 * (sym + 1)) by lia.
replace (2 * sym + 2) with (2 * (sym + 1)) by lia.
eapply (IH (sym + 1) sym'); [lia | exact NC1 | exact SK | | exact KB].
intros. apply KA. lia.
* assert (sym + 1 = asz) by lia.
destruct f as [|f]; [cbn in SK|rewrite skip_zeros_S in SK];
replace (sym + 1 <? asz) with false in SK by (symmetry; apply Z.ltb_ge; lia); injection SK as <-.
-- apply KB. lia.
-- apply KB. lia.
+ injection SK as <-. if_cases B; zify_cond B; [| exfalso; lia].
apply KA. lia.
Qed.
Lemma wr_run24_loop : forall f s start s' start' m1 X (x6 x9 x19 x24 x25 x28 x29 : word),
0 <= start -> start + 24 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> MINV m1 (w_buf s) ->
run24 bsz safe (S f) s start = Ok (s', start') ->
(forall m2 X' (y19 y26 : word), MINV m2 (w_buf s') -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evt usegs POST (UST 0x13b04 m2 (Z_to_bv 64 start') (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 start') x9 (Z_to_bv 64 X')
(Z_to_bv 64 (BUF + w_out s')) y19 (Z_to_bv 64 (w_symbol s)) x24 x25 y26 x28 x29)) ->
evt usegs POST (UST 0x13ac4 m1 (Z_to_bv 64 start) (Z_to_bv 64 (w_bitCount s)) x6 x9 (Z_to_bv 64 X)
(Z_to_bv 64 (BUF + w_out s)) x19 (Z_to_bv 64 (w_symbol s)) x24 x25 (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) x28 x29).
Proof using WRC.
induction f as [|f IH]; intros s start s' start' m1 X x6 x9 x19 x24 x25 x28 x29 S0 S24 SY RX EX LB (BA & NA & FA & SA & MUA & WMA & MIA) R24 K;
rewrite run24_S in R24; replace (start + 24 <=? w_symbol s) with true in R24 by (symmetry; apply Z.leb_le; lia);
apply bind_inv in R24; destruct R24 as (v & SH & R24); apply shl32_inv in SH; destruct SH as [BC ->];
apply bind_inv in R24; destruct R24 as (sfl & FL & R24); apply wflush_inv in FL; cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL;
destruct FL as (OE & O0 & O1 & ->); unfold FseNCount.Zlength in O1.
- cbn in R24. discriminate.
- pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold FRAMEC in FA.
zstep.
lazymatch goal with |- evt ?sg ?Q (MS ?R ?F (if _ then ?a else _) ?fc ?rv ?mm ?ro) =>
assert (STORES : evt sg Q (MS R F a fc rv mm ro)) end.
{ zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep.
assert (EX1 : ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64) mod 2^32 = u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296. rewrite swrap32_eq. lia. }
assert (RX1 : 0 <= (X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap13. revert EX1 RX1. generalize ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64). intros X1 EX1 RX1.
set (bs1 := u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))) in *.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. rewrite <- EX1. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^8) with 256. lia. }
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
zstep. zstep. zstep. sw32 (start + 48).
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep.
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
assert (RB2 : 0 <= bs1 / 2^16 < 2^64).
{ change (2^32) with 4294967296 in RB3. change (2^64) with 18446744073709551616. lia. }
setreg 14%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
assert (LB2 : zlen (Zupd (w_out s + 1) (to_byte (bs1 / 2 ^ 8)) (Zupd (w_out s) (to_byte bs1) (w_buf s))) = bsz)
by (rewrite !Zupd_length; exact LB).
zstep.
if_cases B; zify_cond B.
+ lazymatch type of R24 with run24 _ _ _ ?sn _ = _ =>
eapply (IH sn (start + 24) s' start'); [lia | cbn [w_symbol]; lia | cbn [w_symbol]; lia | exact RB2
| cbn [w_bitStream]; apply Z.mod_small; exact RB3 | cbn [w_buf]; exact LB2
| cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact R24 | ] end.
cbn [w_symbol w_bitCount]. exact K.
+ rewrite run24_S in R24. cbn [w_symbol] in R24.
replace (start + 24 + 24 <=? w_symbol s) with false in R24 by (symmetry; apply Z.leb_gt; lia).
injection R24 as <- <-.
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact RB2 | cbn [w_bitStream]; apply Z.mod_small; exact RB3]. }
rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
+ rewrite (ite_true _ safe _ _ SAFE). apply STORES.
+ apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
destruct OE as [OE|OE]; [congruence|].
zstep. if_false. zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply STORES.
Qed.
Lemma wr_run24 : forall f s start s' start' m1 X (x6 x9 x19 x24 x25 x26 x28 x29 : word),
0 <= start -> start + 24 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> MINV m1 (w_buf s) ->
run24 bsz safe (S f) s start = Ok (s', start') ->
(forall m2 X' (y19 y26 : word), MINV m2 (w_buf s') -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evt usegs POST (UST 0x13b04 m2 (Z_to_bv 64 start') (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 start') x9 (Z_to_bv 64 X')
(Z_to_bv 64 (BUF + w_out s')) y19 (Z_to_bv 64 (w_symbol s)) x24 x25 y26 x28 x29)) ->
evt usegs POST (UST 0x13ab8 m1 (Z_to_bv 64 start) (Z_to_bv 64 (w_bitCount s)) x6 x9 (Z_to_bv 64 X)
(Z_to_bv 64 (BUF + w_out s)) x19 (Z_to_bv 64 (w_symbol s)) x24 x25 x26 x28 x29).
Proof using WRC.
intros f s start s' start' m1 X x6 x9 x19 x24 x25 x26 x28 x29 S0 S24 SY RX EX LB MV R24 K.
assert (BC : 0 <= w_bitCount s < 32).
{ rewrite run24_S in R24. replace (start + 24 <=? w_symbol s) with true in R24 by (symmetry; apply Z.leb_le; lia).
apply bind_inv in R24. destruct R24 as (v & SH & _). apply shl32_inv in SH. lia. }
pose proof MV as (_ & _ & FA & _). unfold FRAMEC in FA.
zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
zstep. zstep. rewrite shiftl_mod32 by lia.
exact (wr_run24_loop f s start s' start' m1 X _ x9 _ x24 x25 x28 x29 S0 S24 SY RX EX LB MV R24 K).
Qed.
End LOOP.
End WR.
