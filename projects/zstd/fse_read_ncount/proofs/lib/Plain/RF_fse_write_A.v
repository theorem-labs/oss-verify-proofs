(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseWriteModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface.
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
Ltac lts_lit K := unfold bv_lts in K; rewrite !signed_lit in K by lia; zify_bool K.
Definition FRAMEC : list cell := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].
Definition MINV (m1 : fmem) (buf : list Z) : Prop :=
u8arr psegs m1 BUF (map (Z_to_bv 8) buf) /\ bytes_at psegs m1 NC (u16s (map (Z_to_bv 64) nc))
/\ rw_cells psegs m1 (SP + -80) FRAMEC /\ stk psegs m1 lo (SP + -80)
/\ munch W m m1 /\ wmono psegs m m1 /\ mem_inv psegs m1.
Section LOOP.
Variable safe : bool.
Notation WST pc mm x8 x9 x11 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 :=
(MS (mkR ra (Z_to_bv 64 (SP + -80)) gp tp (Z_to_bv 64 asz) (Z_to_bv 64 1) (Z_to_bv 64 17) x8 x9 (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 NC) x13
(Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 (Z.b2z safe)) (Z_to_bv 64 BUF) x17 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11
(Z_to_bv 64 15) (Z_to_bv 64 3) (Z_to_bv 64 asz) (Z_to_bv 64 65535))
F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
Lemma wr_shrink : forall f rem thr nb thr' nb' m1 (x8 x9 x11 x13 x17 x18 x19 x20 x24 x25 : word),
rem < thr -> 1 <= rem -> thr <= 8192 ->
shrink (S f) rem thr nb = Ok (thr', nb') ->
(evt psegs POST (WST 0x13b24 m1 x8 x9 x11 x13 x17 x18 x19 x20 (Z_to_bv 64 rem) (Z_to_bv 64 nb') (Z_to_bv 64 thr') x24 x25)) ->
evt psegs POST (WST 0x13b18 m1 x8 x9 x11 x13 x17 x18 x19 x20 (Z_to_bv 64 rem) (Z_to_bv 64 nb) (Z_to_bv 64 thr) x24 x25).
Proof using WRC.
induction f as [|f IH]; intros rem thr nb thr' nb' m1 x8 x9 x11 x13 x17 x18 x19 x20 x24 x25 LT R1 T8 SH K.
- rewrite shrink_S in SH. Local Ltac2 Set LiaHints.tbl := fun () => "00>0>10842114114.7519726814754.7821778203972.8629011846530.7834727867976.78362166662.87  38047386523.783971545388.78 40308748580.774410630228.75 4410630228.77 61588508711.9265664998174.786758062595.77 00000100;00J00T00W00`00d00g01101501901C01D01ESS2LT2R12T8S2LT2R12T81H2H0S2LT2R12T8S1BS2T81H2H0S2R1S1BS2LT2R12T8S2LTS2LTS2LT2R12T8SS".
replace (rem <? thr) with true in SH by (symmetry; apply Z.ltb_lt; lia). cbn in SH. discriminate.
- rewrite shrink_S in SH. replace (rem <? thr) with true in SH by (symmetry; apply Z.ltb_lt; lia).
zstep. rewrite (swrap32_small thr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
rewrite swrap32_small by (Z.div_mod_to_equations; lia).
zstep. zstep.
if_cases B; lts_lit B.
+ eapply (IH rem (thr / 2) (nb - 1) thr' nb'); [lia| lia| Z.div_mod_to_equations; lia| | exact K].
replace (nb + -1) with (nb - 1) by lia. exact SH.
+ rewrite shrink_S in SH. replace (rem <? thr / 2) with false in SH by (symmetry; apply Z.ltb_ge; lia).
injection SH as <- <-. replace (nb - 1) with (nb + -1) in K by lia. exact K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac wrap17 := let v := reg_val 17%Z in
lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
Lemma wr_run3 : forall f s start s' start' m1 X (x8 x9 x11 x19 x20 x21 x23 x24 x25 : word),
0 <= start -> start + 3 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
run3 (S f) s start = Ok (s', start') ->
(forall X' (x20' : word), 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evt psegs POST (WST 0x13aa8 m1 x8 x9 x11 (Z_to_bv 64 (w_bitCount s')) (Z_to_bv 64 X') (Z_to_bv 64 (w_symbol s)) x19 x20' x21
(Z_to_bv 64 start') x23 x24 x25)) ->
evt psegs POST (WST 0x13a90 m1 x8 x9 x11 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X) (Z_to_bv 64 (w_symbol s)) x19 x20 x21
(Z_to_bv 64 start) x23 x24 x25).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "00C0?107508260.79   11447729191.13015350524130.79 17316818851.94 17316818853.92 17328780436.81 20142628527.81 38954800347.78 38954800347.81 40053791375.81 42130673131.79 48953163024.79 55516386911.76 55516386911.78 56448729815.94 57295617883.81 6256592031.81  66149329544.95 7568103724.81  00000400b00f00j00n01801<01=01>01A01H01R01V01Z01d01g01k01l026S2BCS4SEPB4SEPN5SEPBN2BC1H2H02H42H52H93H143H193H24S2BCS2BCS2BCS2S02S32SYS2S0SSS1BS2RX2BCS2S02S32SYS2S3S2S3S2S02S32SYS1BS2SYFS2S02S32SY".
induction f as [|f IH]; intros s start s' start' m1 X x8 x9 x11 x19 x20 x21 x23 x24 x25 S0 S3 SY RX EX R3 K;
rewrite run3_S in R3; replace (start + 3 <=? w_symbol s) with true in R3 by (symmetry; apply Z.leb_le; lia);
apply bind_inv in R3; destruct R3 as (v & SH & R3); apply shl32_inv in SH; destruct SH as [BC ->].
- cbn in R3. discriminate.
- zstep. rewrite shiftl_mod32 by lia.
zstep. zstep. sw32 (start + 6). zstep. zstep. sw32 (w_bitCount s + 2). zstep.
assert (EX' : (bv_swrap 32 (3 * 2 ^ w_bitCount s) + X) mod 2^64 mod 2^32 = u32 (w_bitStream s + u32 (3 * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
rewrite swrap32_eq. Z.div_mod_to_equations. lia. }
if_cases B; zify_cond B.
+
wrap17.
lazymatch type of R3 with run3 _ ?s1 _ = _ =>
eapply (IH s1 (start + 3) s' start'); [lia | cbn [w_symbol]; lia | cbn [w_symbol]; lia | apply Z.mod_pos_bound; lia
| cbn [w_bitStream]; exact EX' | exact R3 | ] end.
cbn [w_symbol w_bitCount]. exact K.
+
rewrite run3_S in R3. cbn [w_symbol] in R3.
replace (start + 3 + 3 <=? w_symbol s) with false in R3 by (symmetry; apply Z.leb_gt; lia).
injection R3 as <- <-. wrap17.
apply K; [apply Z.mod_pos_bound; lia | cbn [w_bitStream]; exact EX'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_skip : forall f sym sym' m1 (x8 x9 x11 x13 x17 x19 x20 x23 x24 x25 : word),
0 <= sym < asz -> bytes_at psegs m1 NC (u16s (map (Z_to_bv 64) nc)) ->
skip_zeros nc asz (S f) sym = Ok sym' ->
(forall (x21' x22' x23' : word), sym <= sym' < asz ->
evt psegs POST (WST 0x13a14 m1 x8 x9 x11 x13 x17 (Z_to_bv 64 sym') x19 x20 x21' x22' x23' x24 x25)) ->
(forall (x21' x22' x23' : word), sym' = asz ->
evt psegs POST (WST 0x13a10 m1 x8 x9 x11 x13 x17 (Z_to_bv 64 sym') x19 x20 x21' x22' x23' x24 x25)) ->
evt psegs POST (WST 0x139f8 m1 x8 x9 x11 x13 x17 (Z_to_bv 64 sym) x19 x20 (Z_to_bv 64 (NC + 2 * sym)) (Z_to_bv 64 (asz - sym)) x23 x24 x25).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "00G0>11275272025.7911275272025.8011281384035.811289448109.85 38697646388.7238697646388.7442130557540.8048781072250.8151122350107.8152067329428.8153628768993.8153628768993.8259315036641.7659315036641.7859315036641.8059583424896.7659583424896.7859583424896.8060231311587.8061336826000.816607192544.88 66233976023.7666233976023.7800000:00D00N00T00X00\01901C01G01U01\01c02E02g03F03J03N03R03]03a03k042049S2SY2NB2B2S2SY2NB2B2S2SY2NB2B2S2NB1HS2SYS2SYS2TL4SEPB4SEPN5SEPBN2LR2NB2E0S2SY2NB2B2S2NBS3MSV2SY2LR2NBS2NB2B2S2NB2B2S2TL4SEPB4SEPN5SEPBN2LR2CR2NB2N01BS2TL4SEPB4SEPN5SEPBN2LR2CR2NB2N01BS2TL4SEPB4SEPN5SEPBN2LR2NB2E01BS2NBS2NBS2NBS3MSV2SY2NBS2NBS2SY2LR2NBS2SY2NBS2SY2NB".
induction f as [|f IH]; intros sym sym' m1 x8 x9 x11 x13 x17 x19 x20 x23 x24 x25 SY NC1 SK KA KB;
rewrite skip_zeros_S in SK; replace (sym <? asz) with true in SK by (symmetry; apply Z.ltb_lt; lia);
apply bind_inv in SK; destruct SK as (c & LD & SK); apply load_inv in LD; destruct LD as [LR ->]; unfold FseNCount.Zlength in LR;
pose proof (Forall_Znth _ _ sym NCR LR) as CR; cbv beta in CR;
pose proof (bytes_at_bound _ _ _ _ NC1) as NB; rewrite u16s_length, length_map in NB;
pose proof (u16_znth psegs m1 NC nc sym (Z_to_bv 64 (NC + 2 * sym)) NC1 LR ltac:(reflexivity)) as RD.
-
destruct (Z.eqb_spec (Znth sym nc) 0) as [E0|N0]; [cbn in SK; discriminate|]. injection SK as <-.
zstep. rewrite zx16_short by exact CR. zstep.
if_cases B; zify_cond B; [| exfalso; lia].
apply KA. lia.
- zstep. rewrite zx16_short by exact CR. zstep.
destruct (Z.eqb_spec (Znth sym nc) 0) as [E0|N0].
+ if_cases B; zify_cond B; [exfalso; lia|].
zstep. sw32 (sym + 1). zstep. zstep. zstep.
if_cases B2; zify_cond B2.
* replace (asz - sym + -1) with (asz - (sym + 1)) by lia. replace (NC + 2 * sym + 2) with (NC + 2 * (sym + 1)) by lia.
eapply (IH (sym + 1) sym'); [lia | exact NC1 | exact SK | | exact KB].
intros. apply KA. lia.
* assert (sym + 1 = asz) by lia.
destruct f as [|f]; [cbn in SK|rewrite skip_zeros_S in SK];
replace (sym + 1 <? asz) with false in SK by (symmetry; apply Z.ltb_ge; lia); injection SK as <-.
-- apply KB. lia.
-- apply KB. lia.
+ injection SK as <-. if_cases B; zify_cond B; [| exfalso; lia].
apply KA. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac minv_close BA NA FA SA MUA WMA MIA :=
split; [exact BA|]; split; [exact NA|]; split; [exact FA|]; split; [exact SA|]; split; [exact MUA|]; split; [exact WMA| exact MIA].
Lemma wr_run24s : forall f s start s' start' m1 X (x8 x9 x19 x22 x23 x24 x25 : word),
safe = true -> 0 <= start -> start + 24 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> MINV m1 (w_buf s) ->
run24 bsz safe (S f) s start = Ok (s', start') ->
(forall m2 X' (x20' x21' x23' : word), MINV m2 (w_buf s') -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evt psegs POST (WST 0x13a88 m2 x8 x9 (Z_to_bv 64 (BUF + w_out s')) (Z_to_bv 64 (w_bitCount s')) (Z_to_bv 64 X')
(Z_to_bv 64 (w_symbol s)) x19 x20' x21' (Z_to_bv 64 start') x23' x24 x25)) ->
evt psegs POST (WST 0x13a30 m1 x8 x9 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X)
(Z_to_bv 64 (w_symbol s)) x19 (Z_to_bv 64 start) (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) x22 x23 x24 x25).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "00S0?10083654594.98 11872430787.96 13070568592.96 13072942494.95 15641283330.95 15641300924.96 17328780436.10021281359300.97 22448268900.96 2707782907.100 31075518971.96 3214378781.96  36067184287.10037421852671.95 38950590954.92 40037303598.95 41477017263.10042134488917.95 46833963628.1004857125224.91  49170713844.96 49423367528.96 5152176687.83  5152176687.85  51818759664.96 52242146818.96 53722431576.95 54480128241.96 56448729813.1126256592031.100 63370508179.96 64799663456.96 64895803440.96 913132285.96   9581028844.96  00000400F00P00Z00d00n01<01D01N01T01f02302:02>02B02P02V03D03R04<04O04Y04^04c04m05[05_06M06[06b06f07907R07V07`S2NBS4SEPB2LB2O02O12NBS2O02O12NBS2O02O12NBS2O02O12NBS2O02O12NBS2S03S242SY2NBS2NB3RB3S2O02BB2NBS2NB1BS4SEPB2LB2O02O12NBS2LB2O02O12NBS2S02NBS2NBS2NBS2S03S242SY2NBS2NB1BS2TL4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3EX13RX1S2S03S242SY2NBS2TL3RSP4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NBS5SEPBN2LB2O02O12NBS2O12BB2NBS3S24S3S24S2O12BB2NBS2TL4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3EX13RX1S2NBS2TL4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3EX13RX1S2S03S242SY2NBS2SY2NBS2NBS5SEPBN2LB2O02O12NBS2TL2RX2BC2NB3EX13RX13RB1S2NBS2O02BB2NB".
induction f as [|f IH]; intros s start s' start' m1 X x8 x9 x19 x22 x23 x24 x25 SAFE S0 S24 SY RX EX LB (BA & NA & FA & SA & MUA & WMA & MIA) R24 K;
rewrite run24_S in R24; replace (start + 24 <=? w_symbol s) with true in R24 by (symmetry; apply Z.leb_le; lia);
apply bind_inv in R24; destruct R24 as (v & SH & R24); apply shl32_inv in SH; destruct SH as [BC ->];
apply bind_inv in R24; destruct R24 as (sfl & FL & R24); apply wflush_inv in FL; cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL;
destruct FL as (_ & O0 & O1 & ->); unfold FseNCount.Zlength in O1.
- cbn in R24. discriminate.
- pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold FRAMEC in FA.
zstep.
assert (EX1 : ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64) mod 2^32 = u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296. rewrite swrap32_eq. lia. }
assert (RX1 : 0 <= (X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap17. revert EX1 RX1. generalize ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64). intros X1 EX1 RX1.
set (bs1 := u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))) in *.
zstep. zstep. sw32 (start + 48). zstep.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. rewrite <- EX1. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^8) with 256. lia. }
zstep. zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep. zstep.
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
assert (RB3 : 0 <= bs1 / 2^16 < 2^32).
{ change (2^16) with 65536. change (2^32) with 4294967296 in *. lia. }
assert (RB2 : 0 <= bs1 / 2^16 < 2^64).
{ change (2^32) with 4294967296 in RB3. change (2^64) with 18446744073709551616. lia. }
setreg 11%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
assert (LB2 : zlen (Zupd (w_out s + 1) (to_byte (bs1 / 2 ^ 8)) (Zupd (w_out s) (to_byte bs1) (w_buf s))) = bsz)
by (rewrite !Zupd_length; exact LB).
if_cases B; zify_cond B.
+
lazymatch type of R24 with run24 _ _ _ ?sn _ = _ =>
eapply (IH sn (start + 24) s' start'); [exact SAFE | lia | cbn [w_symbol]; lia | cbn [w_symbol]; lia | exact RB2
| cbn [w_bitStream]; apply Z.mod_small; exact RB3 | cbn [w_buf]; exact LB2
| cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact R24 | ] end.
cbn [w_symbol w_bitCount]. exact K.
+
rewrite run24_S in R24. cbn [w_symbol] in R24.
replace (start + 24 + 24 <=? w_symbol s) with false in R24 by (symmetry; apply Z.leb_gt; lia).
injection R24 as <- <-.
zstep.
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact RB2 | cbn [w_bitStream]; apply Z.mod_small; exact RB3].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_run24c : forall f s start s' start' m1 X (x8 x9 x19 x22 x23 x24 x25 : word),
safe = false -> 0 <= start -> start + 24 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> MINV m1 (w_buf s) ->
run24 bsz safe (S f) s start = Ok (s', start') ->
(forall m2 X' (x20' x21' x23' : word), MINV m2 (w_buf s') -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evt psegs POST (WST 0x13a88 m2 x8 x9 (Z_to_bv 64 (BUF + w_out s')) (Z_to_bv 64 (w_bitCount s')) (Z_to_bv 64 X')
(Z_to_bv 64 (w_symbol s)) x19 x20' x21' (Z_to_bv 64 start') x23' x24 x25)) ->
evt psegs POST (WST 0x13a5c m1 x8 x9 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X)
(Z_to_bv 64 (w_symbol s)) x19 (Z_to_bv 64 start) (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) x22 x23 x24 x25).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "00V0?10083654594.10011872430787.98 13070568592.98 13072942494.97 15641283330.97 15641300924.98 17328780436.10221281359300.99 22448268900.98 2707782907.102 31075518971.98 3214378781.98  36067184287.10237421852671.97 38950590954.94 40037303598.97 41477017263.10242134488917.97 45589988655.93 46833963628.1024859255113.93  49170713844.98 492328663.93   49423367528.98 5152176687.83  5152176687.85  51818759664.98 52242146818.98 53722431576.97 54480128241.98 56448729813.11459308746866.93 6256592031.102 63370508179.98 64799663456.98 64895803440.98 913132285.98   9581028844.98  00000400C00M00W00a00k01901A01K01Q01`01j02102502902G02M03803E03S04604F04V04c04h04m05:05e05i06T06b06l07307707G07`07d07nS2NBS4SEPB2O02NB2BOS2O02O12NBS2O02O12NBS2O02O12NBS2O02O12NBS2S03S242SY2NBS2NB3RB3S2O02BB2NBS2NB1BS4SEPB2O02NB2BOS2OE2O02NBS2S02NBS2NBS2NBS2S03S242SY2NBS2NB1BS2TL4SEPB4SEPN5SEPBN2RX2BC2O02NB2BO3EX13RX1S2O02O12BB2NBS2S03S242SY2NBS2TL4SEPB4SEPN5SEPBN2RX2BC2O02NB2BOS5SEPBN2O02NB2BOS2LB2O02O12BB2NBS2LB2BB2NB2BOS3S24S3S24S2LB2BB2NB2BOS2TL4SEPB4SEPN5SEPBN2RX2BC2O02NB2BO3EX13RX1S2NBS2TL4SEPB4SEPN5SEPBN2RX2BC2O02NB2BO3EX13RX1S2S03S242SY2NBS2OE2NB2BOS2SY2NBS2NBS5SEPBN2O02NB2BOS2TL2RX2BC2NB3EX13RX13RB1S2NBS2O02BB2NB".
induction f as [|f IH]; intros s start s' start' m1 X x8 x9 x19 x22 x23 x24 x25 SAFE S0 S24 SY RX EX LB (BA & NA & FA & SA & MUA & WMA & MIA) R24 K;
rewrite run24_S in R24; replace (start + 24 <=? w_symbol s) with true in R24 by (symmetry; apply Z.leb_le; lia);
apply bind_inv in R24; destruct R24 as (v & SH & R24); apply shl32_inv in SH; destruct SH as [BC ->];
apply bind_inv in R24; destruct R24 as (sfl & FL & R24); apply wflush_inv in FL; cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL;
destruct FL as (OE & O0 & O1 & ->); unfold FseNCount.Zlength in O1; (destruct OE as [OE|OE]; [congruence|]).
- cbn in R24. discriminate.
- pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold FRAMEC in FA.
zstep. if_cases BO; zify_cond BO; [exfalso; lia|].
zstep.
assert (EX1 : ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64) mod 2^32 = u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296. rewrite swrap32_eq. lia. }
assert (RX1 : 0 <= (X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap17. revert EX1 RX1. generalize ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64). intros X1 EX1 RX1.
set (bs1 := u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))) in *.
zstep. zstep. sw32 (start + 48). zstep.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. rewrite <- EX1. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^8) with 256. lia. }
zstep. zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep. zstep.
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
assert (RB3 : 0 <= bs1 / 2^16 < 2^32).
{ change (2^16) with 65536. change (2^32) with 4294967296 in *. lia. }
assert (RB2 : 0 <= bs1 / 2^16 < 2^64).
{ change (2^32) with 4294967296 in RB3. change (2^64) with 18446744073709551616. lia. }
setreg 11%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
assert (LB2 : zlen (Zupd (w_out s + 1) (to_byte (bs1 / 2 ^ 8)) (Zupd (w_out s) (to_byte bs1) (w_buf s))) = bsz)
by (rewrite !Zupd_length; exact LB).
if_cases B; zify_cond B.
+
lazymatch type of R24 with run24 _ _ _ ?sn _ = _ =>
eapply (IH sn (start + 24) s' start'); [exact SAFE | lia | cbn [w_symbol]; lia | cbn [w_symbol]; lia | exact RB2
| cbn [w_bitStream]; apply Z.mod_small; exact RB3 | cbn [w_buf]; exact LB2
| cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact R24 | ] end.
cbn [w_symbol w_bitCount]. exact K.
+
rewrite run24_S in R24. cbn [w_symbol] in R24.
replace (start + 24 + 24 <=? w_symbol s) with false in R24 by (symmetry; apply Z.leb_gt; lia).
injection R24 as <- <-.
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact RB2 | cbn [w_bitStream]; apply Z.mod_small; exact RB3].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
End WR.
