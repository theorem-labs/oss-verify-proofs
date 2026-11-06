(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseWriteModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_write_A.
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
Ltac lts_lit K := unfold bv_lts in K; rewrite !signed_lit in K by lia; zify_bool K.
Notation FRAMEC := (RF_fse_write_A.FRAMEC s0 s1 s2 s3 s4 s5 s6 s7 s8 s9).
Notation MINV := (RF_fse_write_A.MINV s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m SP BUF NC buf0 nc lo).
Section LOOP.
Variable safe : bool.
Notation A_ l := (l ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SP BUF NC buf0 buf' nc msv tl n lo
BUFB NCR WOK MSV TL BSZ LO RSP SEPB SEPN SEPBN safe).
Notation WST pc mm x8 x9 x11 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 :=
(MS (mkR ra (Z_to_bv 64 (SP + -80)) gp tp (Z_to_bv 64 asz) (Z_to_bv 64 1) (Z_to_bv 64 17) x8 x9 (Z_to_bv 64 (-1)) x11 (Z_to_bv 64 NC) x13
(Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 (Z.b2z safe)) (Z_to_bv 64 BUF) x17 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11
(Z_to_bv 64 15) (Z_to_bv 64 3) (Z_to_bv 64 asz) (Z_to_bv 64 65535))
F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
Ltac wrap17 := let v := reg_val 17%Z in
lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
Ltac minv_close BA NA FA SA MUA WMA MIA :=
split; [exact BA|]; split; [exact NA|]; split; [exact FA|]; split; [exact SA|]; split; [exact MUA|]; split; [exact WMA| exact MIA].
Lemma wr_zero_tail : forall s start2 sf m1 X (x8 x9 x19 x20 x21 x23 x24 x25 : word),
0 <= start2 -> start2 <= w_symbol s < start2 + 3 -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> 0 <= w_out s <= bsz -> MINV m1 (w_buf s) ->
bind (shl32 (u32 (w_symbol s - start2)) (w_bitCount s)) (fun v =>
wflush_if bsz safe (mkW (w_buf s) (w_out s) (u32 (w_bitStream s + v)) (w_bitCount s + 2)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s))) = Ok sf ->
(forall m2 X' (x20' : word), MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evt psegs POST (WST 0x13ae0 m2 x8 x9 (Z_to_bv 64 (BUF + w_out sf)) (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 X')
(Z_to_bv 64 (w_symbol s)) x19 x20' x21 (Z_to_bv 64 start2) x23 x24 x25)) ->
evt psegs POST (WST 0x13aa8 m1 x8 x9 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X)
(Z_to_bv 64 (w_symbol s)) x19 x20 x21 (Z_to_bv 64 start2) x23 x24 x25).
Proof using WRC.
intros s start2 sf m1 X x8 x9 x19 x20 x21 x23 x24 x25 S0 SR SY RX EX LB RO (BA & NA & FA & SA & MUA & WMA & MIA) H K.
apply bind_inv in H. destruct H as (v & SH & FL). apply shl32_inv in SH. destruct SH as [BC ->].
pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold FRAMEC in FA.
Local Ltac2 Set LiaHints.tbl := fun () => "00V0?10083654597.96 11872430787.96 13070568592.96 13072942494.95 1345910911.96  15331224399.87 15346411231.87 15640690177.95 15641300924.96 17316818850.10317316818851.10222448268900.96 25206072947.10231075518971.96 3214378781.96  3599829581.87  37421852671.95 37497644658.93 38765519574.93 38950590954.88 42134848470.87 45589988655.97 4857125224.87  49170713844.96 492328663.97   49423367528.96 51818759664.96 52242146818.96 5254976934.103 53722431576.95 54480128241.96 59308746866.97 59315036641.93 63370508179.96 64799663456.96 64895803446.96 913132285.96   9581028844.96  00000400F00P00Z00^00e00l01601@01M01T01^01e02702D02K02O02V02Z02^03E03R04904L04\04f05005Z05g05k06U06_06g06k07>07W07[07eS2NBS4SEPB2LB2O02O12NBS2RO2O12NBS2RO2O12NBS2NBS2SR2NBS2BC2NBS2RO2O12NBS2RO2O12NBS2S02SR2SY2NBS2BC2NBS2O02BB2NBS2SR2NBS4SEPB2LB2O02O12NBS2LB2RO2O12NBS2SR2NBS2NBS2BC2NBS2NBS2NBS2TL3RSP4SEPB4SEPN5SEPBN2RX2LB2RO2BC2NBS2O02O12BB2NBS2TL3RSP4SEPB4SEPN5SEPBN2RX2LB2RO2BC2NBS5SEPBN2LB2O02O12NBS2LB2O02O12BB2NBS2O12BB2NBS2O12BB2NBS2TL4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S2S02SR2SY2NBS2NBS2TL4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S2OE2NB2BOS1G2NB1BS2NBS5SEPBN2LB2O02O12NBS2TL2RX2BC2NB3EX13RX13RB1S2NBS2O02BB2NB".
rewrite (u32_id (w_symbol s - start2)) in FL by (change (2^32) with 4294967296; lia).
zstep. sw32 (w_symbol s - start2).
zstep. rewrite shiftl_mod32 by lia.
zstep.
assert (EX1 : ((bv_swrap 32 ((w_symbol s - start2) * 2 ^ w_bitCount s) + X) mod 2^64) mod 2^32
= u32 (w_bitStream s + u32 ((w_symbol s - start2) * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296. rewrite swrap32_eq. lia. }
assert (RX1 : 0 <= (bv_swrap 32 ((w_symbol s - start2) * 2 ^ w_bitCount s) + X) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap17. revert EX1 RX1. generalize ((bv_swrap 32 ((w_symbol s - start2) * 2 ^ w_bitCount s) + X) mod 2^64). intros X1 EX1 RX1.
set (bs1 := u32 (w_bitStream s + u32 ((w_symbol s - start2) * 2 ^ w_bitCount s))) in *.
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
zstep.
apply wflush_if_inv in FL. cbn [w_bitCount] in FL.
if_cases B; lts_lit B.
-
destruct FL as [[G _]|[_ ->]]; [exfalso; lia|].
zstep.
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact RX1 | cbn [w_bitStream]; exact EX1].
- destruct FL as [[_ FL]|[G _]]; [| exfalso; lia].
apply wflush_inv in FL. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL.
destruct FL as (OE & O0 & O1 & ->). unfold FseNCount.Zlength in O1.
assert (FLUSH : forall (y20 : word), evt psegs POST
(WST 0x13ac0 m1 x8 x9 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X1)
(Z_to_bv 64 (w_symbol s)) x19 y20 x21 (Z_to_bv 64 start2) x23 x24 x25)).
{ intros y20.
zstep. u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. rewrite <- EX1. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^8) with 256. lia. }
zstep. zstep. zstep.
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
setreg 11%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
setreg 13%Z (Z_to_bv 64 (w_bitCount s + 2 - 16)) ltac:(f_equal; lia).
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA
| change (2^32) with 4294967296 in RB3; change (2^64) with 18446744073709551616; lia
| cbn [w_bitStream]; apply Z.mod_small; exact RB3]. }
zstep. destruct safe eqn:SAFE.
+ if_true. apply FLUSH.
+ if_false. destruct OE as [OE|OE]; [discriminate|].
zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply FLUSH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 tl BUFB NCR WOK MSV TL BSZ LO RSP SEPB SEPN SEPBN"] Lemma wr_zero_mid : forall f s start1 s2' start2 sf m1 X (x8 x9 x19 x20 x21 x23 x24 x25 : word),
0 <= start1 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
0 <= w_bitStream s < 2^32 -> 0 <= w_bitCount s ->
zlen (w_buf s) = bsz -> 0 <= w_out s <= bsz -> MINV m1 (w_buf s) ->
run3 (S f) s start1 = Ok (s2', start2) ->
bind (shl32 (u32 (w_symbol s2' - start2)) (w_bitCount s2')) (fun v =>
wflush_if bsz safe (mkW (w_buf s2') (w_out s2') (u32 (w_bitStream s2' + v)) (w_bitCount s2' + 2)
(w_symbol s2') (w_remaining s2') (w_threshold s2') (w_nbBits s2') (w_previousIs0 s2'))) = Ok sf ->
(forall m2 X' (x20' x21' x22' : word), MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evt psegs POST (WST 0x13ae0 m2 x8 x9 (Z_to_bv 64 (BUF + w_out sf)) (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 X')
(Z_to_bv 64 (w_symbol s)) x19 x20' x21' x22' x23 x24 x25)) ->
evt psegs POST (WST 0x13a88 m1 x8 x9 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X)
(Z_to_bv 64 (w_symbol s)) x19 x20 x21 (Z_to_bv 64 start1) x23 x24 x25).
Proof.
intros f s start1 s2' start2 sf m1 X x8 x9 x19 x20 x21 x23 x24 x25 S1 SY RX EX RB BC LB RO MV R3 TLH K.
pose proof (run3_facts _ _ _ _ _ R3 RB BC) as ((D1 & D2 & D3 & D4) & SY2 & B2 & O2 & RB2 & BC2 & ST2 & SR2).
Local Ltac2 Set LiaHints.tbl := fun () => "00?0?17328780436.94 19617478418.91 19617478418.94 26604383400.94 42134471252.93 46515793883.91 46515793883.94 49597639079.98 50104863001.11051020183212.93 58270426683.93 58364785427.94 6321005544.98  6562756080.98  8592517893.98  00000?00@00A00H00b00f00j01301:01>01E01H01P01W01aS2S12SY3ST23SR2FFS2S12SYS2TL4SEPB4SEPN5SEPBN2RX2LBS2S1S2S1S3SY23SR2S2S12SYS2S1S2S12SYS1BS2SY3SY2S2RO2O2S2S13SR21B".
specialize (SR2 ltac:(lia)).
zstep. sw32 (start1 + 3). zstep.
if_cases B; zify_cond B.
-
rewrite run3_S in R3. replace (start1 + 3 <=? w_symbol s) with false in R3 by (symmetry; apply Z.leb_gt; lia).
injection R3 as <- <-.
eapply (wr_zero_tail s start1 sf); try eassumption; try lia.
intros. apply K; assumption.
- eapply (A_ wr_run3 f s start1 s2' start2); try eassumption; try lia.
intros X' x20' RX' EX'.
rewrite <- SY2, <- O2.
eapply (wr_zero_tail s2' start2 sf);
[ lia | lia | lia | exact RX' | exact EX' | rewrite B2; exact LB | lia | rewrite B2; exact MV | exact TLH | ].
intros. rewrite SY2. apply K; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 tl BUFB NCR WOK MSV TL BSZ LO RSP SEPB SEPN SEPBN"] Lemma wr_zero : forall s fl m1 X (x8 x9 x18 x19 x21 x22 x23 x24 x25 : word),
winv asz bsz s -> w_symbol s < asz -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s -> MINV m1 (w_buf s) ->
wzero_block nc asz bsz safe s = Ok fl ->
(forall sa m2 X' (y20 y21 y22 y23 : word), fl = Cont sa -> MINV m2 (w_buf sa) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sa ->
evt psegs POST (WST 0x13ae0 m2 x8 x9 (Z_to_bv 64 (BUF + w_out sa)) (Z_to_bv 64 (w_bitCount sa)) (Z_to_bv 64 X')
(Z_to_bv 64 (w_symbol sa)) x19 y20 y21 y22 y23 x24 x25)) ->
(forall sa (y18 y20 y22 y23 : word), fl = Brk sa ->
evt psegs POST (WST 0x13ba4 m1 x8 x9 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X)
y18 x19 y20 x19 y22 y23 x24 x25)) ->
evt psegs POST (WST 0x139d8 m1 x8 x9 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X)
x18 x19 (Z_to_bv 64 (w_symbol s)) x21 x22 x23 x24 x25).
Proof.
intros s fl m1 X x8 x9 x18 x19 x21 x22 x23 x24 x25 WI SYA RX EX MV H KC KB.
pose proof WI as (LB & RO & RB & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & FA & SA & MUA & WMA & MIA).
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
unfold wzero_block in H. apply bind_inv in H. destruct H as (sym & SK & H).
Local Ltac2 Set LiaHints.tbl := fun () => "00R0?15339623494.13615534271600.13515534282078.13716346644575.95 17314721709.10617316818851.14817316818851.15117322479014.95 2597469152.106 27809844849.1343122459008.134 32080162237.1193304526956.139 34119377926.10634122874170.13735212070535.11035214167689.1064013517358.93  4013576988.95  42132796117.13342547251749.10842558040485.13342558171174.95 46093983509.99 59308611920.13359308742867.95 59588178609.10860348271652.1376599369317.133 6599369444.134 67547235139.13968185370196.11968185729876.1397704535130.133 00000900@00G00U00c01101:01I01M01T01b01i02902@02G02H02I02T02_03G03O03W03_03g04204=04A04M04\04k05>05I05T05bS4BC242NBS2NB2J2S2NB2J2S3MSV2SY2NB2B0S3MSV2SY2NB2B0S3MSV2SY2NB2B0S4BC242NBS3MSV3SYA2SY2NBS2NBS2NB2J2S3MSV2SY2NB2B0S2NB2SRS3MSV2NB3SR'3SY1S2SY2NBS2SY2NBFFS3SYA2SY2NBS3SYA2SY2NBS2TL4SEPB4SEPN5SEPBN2RX3NBI2NB2SR3RO12J1S3MSV2NBS3MSV2NBS3MSV2NBS2NB3SR'S2NB3SR'2J1S3SYA2NB2B0S2NBS3MSV2NB3SR'S3MSV2SY2NB3SR'S3MSV2SY2NB3SR'S2SY2NB3SY13ST13SR1S2BC2NB3BC1S2BC2NB3BC1S3MSV2SY2NB2B0".
pose proof (skip_zeros_range nc asz _ (w_symbol s) sym ltac:(lia) SK) as SR.
zstep. zstep. if_cases B0; zify_cond B0; [exfalso; lia|].
do 6 zstep.
rewrite zext32_sh31 by lia. rewrite (Z.mod_small (w_symbol s) 4294967296) by lia.
eapply (A_ wr_skip _ (w_symbol s) sym); [lia | exact NA | exact SK | | ].
-
intros x21' x22' x23' SR'.
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
assert (MID : forall m2 X1 (y20 y21 y23 : word), MINV m2 (w_buf sa) -> 0 <= X1 < 2^64 -> X1 mod 2^32 = w_bitStream sa ->
evt psegs POST (WST 0x13a88 m2 x8 x9 (Z_to_bv 64 (BUF + w_out sa)) (Z_to_bv 64 (w_bitCount sa)) (Z_to_bv 64 X1)
(Z_to_bv 64 (w_symbol sa)) x19 y20 y21 (Z_to_bv 64 start1) y23 x24 x25)).
{ intros m2 X1 y20 y21 y23 MV2 RX1 EX1.
eapply (wr_zero_mid _ sa start1 s2' start2 sf); [lia | lia | exact RX1 | exact EX1 | exact RB1 | lia | exact LB1 | exact RO1 | exact MV2 | exact R3 | exact TLH | ].
intros m3 X' z20 z21 z22 MV3 RX3 EX3.
pose proof (wzero_block_facts nc asz bsz safe s (Cont sf)) as WF. cbv beta iota in WF.
assert (SYF : w_symbol sf = w_symbol sa).
{ apply bind_inv in TLH. destruct TLH as (v' & _ & FL'). apply wflush_if_inv in FL'. destruct FL' as [[_ FL']|[_ ->]].
- apply wflush_inv in FL'. destruct FL' as (_ & _ & _ & ->). cbn [w_symbol]. exact SY2.
- cbn [w_symbol]. exact SY2. }
rewrite <- SYF. apply (KC sf m3 X'); [reflexivity | exact MV3 | exact RX3 | exact EX3]. }
zstep. if_cases J1; zify_cond J1; [exfalso; lia|].
zstep. sw32 (w_symbol s + 24). zstep.
if_cases J2; zify_cond J2.
+
assert (R24' : run24 bsz safe (S (Z.to_nat asz)) s0' (w_symbol s) = Ok (sa, start1)) by exact R24.
rewrite run24_S in R24. cbn [s0' w_symbol] in R24.
replace (w_symbol s + 24 <=? sym) with true in R24 by (symmetry; apply Z.leb_le; lia).
apply bind_inv in R24. destruct R24 as (v24 & SH24 & _). apply shl32_inv in SH24. cbn [s0' w_bitCount] in SH24. destruct SH24 as [BC24 _].
zstep. rewrite shiftl_mod32 by lia.
zstep. rewrite b2z_word_eqz. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
* rewrite (ite_negb_true _ safe _ _ SAFE).
eapply (A_ wr_run24s _ s0' (w_symbol s) sa start1); [exact SAFE | lia | cbn [s0' w_symbol]; lia | cbn [s0' w_symbol]; lia
| exact RX | exact EX | exact LB | exact MV | exact R24' | ].
intros m2 X' z20 z21 z23 MV2 RX2 EX2. cbn [s0' w_symbol]. rewrite <- SY1. apply MID; assumption.
* apply Bool.not_true_is_false in SAFE. rewrite (ite_negb_false _ safe _ _ SAFE).
eapply (A_ wr_run24c _ s0' (w_symbol s) sa start1); [exact SAFE | lia | cbn [s0' w_symbol]; lia | cbn [s0' w_symbol]; lia
| exact RX | exact EX | exact LB | exact MV | exact R24' | ].
intros m2 X' z20 z21 z23 MV2 RX2 EX2. cbn [s0' w_symbol]. rewrite <- SY1. apply MID; assumption.
+
rewrite run24_S in R24. cbn [s0' w_symbol] in R24.
replace (w_symbol s + 24 <=? sym) with false in R24 by (symmetry; apply Z.leb_gt; lia).
injection R24 as <- <-.
zstep. zstep.
apply (MID m1 X); [exact MV | exact RX | exact EX].
-
intros x21' x22' x23' ->.
replace (asz =? asz) with true in H by (symmetry; apply Z.eqb_refl). injection H as <-.
zstep. zstep.
eapply KB. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SP BUF NC buf0 nc tl TL RSP SEPB SEPN SEPBN"] Lemma sraiw31_sign : forall c, - 2147483648 <= c < 2147483648 ->
bv_swrap 32 (Z.shiftr (bv_swrap 32 (c mod 18446744073709551616)) 31) = (if c <? 0 then -1 else 0).
Proof.
intros c Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0060>1641691110.57 21918288674.562807064488.57 61933545449.5764097424.56   7224928843.56 00000600:00@00F00J00KS2Hc1HS2HcS2Hc1HS2Hc1HS2HcS".
rewrite (swrap32_eqm (c mod 18446744073709551616) c) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2^31) with 2147483648.
destruct (Z.ltb_spec c 0); rewrite swrap32_small; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SP BUF NC buf0 nc tl TL RSP SEPB SEPN SEPBN"] Lemma lxor_sign_mod : forall a, - 9223372036854775808 <= a < 9223372036854775808 ->
Z.lxor (a mod 18446744073709551616) 9223372036854775808 = a + 9223372036854775808.
Proof.
intros a Ha. change 9223372036854775808 with (2^63) at 2. Local Ltac2 Set LiaHints.tbl := fun () => "0020>12840669021.5638948406330.56000004005S2HaS".
rewrite zb_lxor_sign by (apply Z.mod_pos_bound; lia).
change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SP BUF NC buf0 nc tl TL RSP SEPB SEPN SEPBN"] Lemma slt_lit_rr : forall a b, - 9223372036854775808 <= a < 9223372036854775808 -> - 9223372036854775808 <= b < 9223372036854775808 ->
(Z.lxor (a mod 18446744073709551616) 9223372036854775808 <? Z.lxor (b mod 18446744073709551616) 9223372036854775808) = (a <? b).
Proof.
intros a b Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0040>21270332905.5922124252747.5829306103519.5851894210119.5900000300700;00>S1HS2HbS2HaS1H".
rewrite !lxor_sign_mod by lia.
destruct (Z.ltb_spec a b); [apply Z.ltb_lt| apply Z.ltb_ge]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SP BUF NC buf0 nc tl TL RSP SEPB SEPN SEPBN"] Lemma slt_lit_mr : forall a b, - 9223372036854775808 <= a < 9223372036854775808 -> 0 <= b < 9223372036854775808 ->
(Z.lxor (a mod 18446744073709551616) 9223372036854775808 <? Z.lxor b 9223372036854775808) = (a <? b).
Proof.
intros a b Ha Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0030>22124252747.5829306103519.5850363210057.5800000400800<S2HbS2HaS2Hb".
rewrite <- (Z.mod_small b 18446744073709551616) at 1 by lia. apply slt_lit_rr; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SP buf0 nc tl TL RSP"] Lemma mask_sel : forall (b : bool) y,
Z.land ((Z.b2z b + -1) mod 18446744073709551616) (y mod 18446744073709551616) = (if b then 0 else y mod 18446744073709551616).
Proof.
intros [|] y; cbn [Z.b2z].
- reflexivity.
- change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "0020>18932239167.5535496346213.55000001002SS".
rewrite Z.land_comm, Z.land_ones by lia.
change (2^64) with 18446744073709551616. apply Z.mod_mod. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SP buf0 nc tl TL RSP"] Lemma container_add : forall X bs c2 bc, 0 <= bc < 32 -> X mod 2^32 = bs ->
((bv_swrap 32 (Z.shiftl (c2 mod 18446744073709551616) (bc mod 32)) + X) mod 2^64) mod 2^32 = u32 (bs + u32 (u32 c2 * 2 ^ bc)).
Proof.
intros X bs c2 bc Hbc <-. Local Ltac2 Set LiaHints.tbl := fun () => "0020>18928846753.5840136305770.58000001006SS3Hbc".
rewrite shiftl_mod32 by lia. unfold u32.
change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
rewrite mod64_mod32. rewrite Z.add_mod by lia. rewrite swrap32_mod32.
rewrite (Z.mul_mod (c2 mod 18446744073709551616)) by lia. rewrite mod64_mod32.
rewrite <- (Z.mul_mod c2) by lia. rewrite (Z.add_mod (X mod 4294967296)) by lia.
rewrite (Z.mul_mod (c2 mod 4294967296)) by lia. rewrite !Z.mod_mod by lia.
rewrite <- (Z.mul_mod c2) by lia. rewrite (Z.add_comm (X mod 4294967296)). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 tl BUFB NCR WOK MSV TL BSZ LO RSP SEPB SEPN SEPBN"] Lemma wr_count : forall s sc sd m1 X (x20 x21 x22 x23 x24 x25 : word),
winv asz bsz s -> w_symbol s < asz -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s -> MINV m1 (w_buf s) ->
wcount_block nc s = Ok sc -> wflush_if bsz safe sc = Ok sd ->
(forall m2 X' (y21 y22 y23 y24 y25 : word), (w_symbol sd <? asz) && (1 <? w_remaining sd) = true ->
MINV m2 (w_buf sd) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sd ->
evt psegs POST (WST 0x139c8 m2 (Z_to_bv 64 (w_nbBits sd)) (Z_to_bv 64 (w_threshold sd)) (Z_to_bv 64 (BUF + w_out sd))
(Z_to_bv 64 (w_bitCount sd)) (Z_to_bv 64 X') (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 sd))))
(Z_to_bv 64 (w_remaining sd)) (Z_to_bv 64 (w_symbol sd)) y21 y22 y23 y24 y25)) ->
(forall m2 X' (y8 y9 y18 y19 y20 y22 y23 y24 y25 : word), (w_symbol sd <? asz) && (1 <? w_remaining sd) = false ->
MINV m2 (w_buf sd) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sd ->
evt psegs POST (WST 0x13ba4 m2 y8 y9 (Z_to_bv 64 (BUF + w_out sd)) (Z_to_bv 64 (w_bitCount sd)) (Z_to_bv 64 X')
y18 y19 y20 (Z_to_bv 64 (w_remaining sd)) y22 y23 y24 y25)) ->
evt psegs POST (WST 0x13ae0 m1 (Z_to_bv 64 (w_nbBits s)) (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (BUF + w_out s))
(Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X) (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_remaining s))
x20 x21 x22 x23 x24 x25).
Proof.
intros s sc sd m1 X x20 x21 x22 x23 x24 x25 WI SYA RX EX MV CB FL KL KE.
pose proof WI as (LB & RO & RB & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & FA & SA & MUA & WMA & MIA).
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof (wcount_flush_facts nc asz bsz safe s sc sd CB FL WI SYA NCR) as (WID & SYD & CTL).
pose proof (wcount_block_inv nc s sc CB) as CI. cbv zeta in CI. destruct CI as (thr' & nb' & LR & BCR & R1 & SHR & ESC).
unfold FseNCount.Zlength in LR.
pose proof (Forall_Znth _ _ (w_symbol s) NCR LR) as CR. cbv beta in CR.
set (count := Znth (w_symbol s) nc) in *.
set (rem' := w_remaining s - (if count <? 0 then - count else count)) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "01a0?10083654597.13011156006425.13011603572554.10611872430787.13012330428065.11913070568592.13013072942494.12914216876961.1251496497254.136 15585600701.10515641300924.13015642786442.12916009427861.13016218154386.10616346397291.10716350690787.11917316818850.13517316818850.13617316818853.14217316818854.13117316818862.14817316818863.12617318653978.11919628467489.12921448881065.11122131842618.11922448268900.13023362391946.12923740125337.1202693046722.119 31075518971.13031141918491.1203214378781.130 33928627217.11933938916757.11934499072371.12335212070535.12236141251023.12036200736884.12237421852671.12937504065219.12338950590954.12138954701265.12039124915372.13039727528474.12941417891415.10541422282358.10641968874928.13341968874932.13842130722670.11942130722670.12042132654821.12942134701907.12842558040485.12942637760174.11943462678665.1204401355653.130 44480718584.12244480718715.12344927972772.13844927972774.13645589988655.13147171887389.14247428594748.13447815654693.11947830579739.12048613897338.13548613897342.13149170713844.130492328663.131  49423367528.13050993072687.12351818759664.13051851082428.13352074235540.13352242146818.13053508216722.13153510313882.13953722431576.12954290872331.10354309134372.13854309134374.1365434985518.123 54480128241.13055590205916.12855935222436.13655935222438.13857850263189.10958063764493.12559308611795.12259308612182.12559308746866.13159588178608.13459588178610.13160245107412.13860245107414.13663370508179.13063980631420.12363980631549.13064799663456.13064821634240.13364895803446.13066636823158.1396751262978.119 67940486329.1117644692889.109 8399199891.130 8437231849.120 8935173664.133 8935173665.133 8935173668.138 913132285.130  9581028844.130 00000400800>00P00`00j01401801901A01K01U02H02P02_02g02o03603>03E03O03Y03`03j04604<04F04O04Y05D05V05^05k06206906@06A06J06N06R06Z06^06b06l07307707;07<07=08408d09^0:J0:R0:X0:_0:f0;00;:0;;0;<0;I0;R0;S0;^0;i0;j0;k0<>0<N0<X0<_0<i0=00=10=n0>20>60>70>?0>@0>A0>I0?B0?Q0?R0?S0?a0?j0@40@=0@G0@K0@O0@P0@Q0@U0@\0@f0A90AA0Ab0Ac0Ag0B30B:0BA0BK0BL0BX0BY0B]0BgS2NBS2E1S2NB1HS4SEPB2LB2NB2O02O1S2RM2NB2CR3THR1HS2RO2NB2O1S2RO2NB2O1S2NBFS3NBI2NBS2RO2NB2O1S2RO2NB2O1S2TL4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB3NB'3RC23RX32N1S3NBI2NBS3MSV3SYA2SY2NBS2NB3THRS2NB3THRS2BC2NBS2NB3THRS2RM2NBS2SY2NB2LRS2SY2NB2LRS2RM2NBS2SY2NB2LRS3NBI2NB3BCRS2NB1HS2NB2O02BBS2NB4RBC1S2NB2R12RRS2TL4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'S4SEPB2LB2NB2O02O1S2NB3RC2S2LB2RO2NB2O1S2NB2CRS2NB2CRS2NB2J1FS2NB4RBC1S2NBS2NBS2NB3THRS2NBS2NBS2NB2R12RRS2NB2J1S2NBS2NBFFS2TL4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB3NB'3THR1H2RM2TH2CRS2TL4SEPB4SEPN5SEPBN2RX2LB2BC2RM3NBI2NB2LR3NB'1HS2TL3RSP4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB3NB'3RB13RX12O02O1S2TL4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB3NB'3RX3S3MSV2NBS2NB1HS2NB2CRS2NB2J1S2NB2R12RRS2NB2R12RRFFS2NB2O02O12BBS2NB4RBC1FS2RM2NB3THRS2RM2NB3THRFFS5SEPBN2LB2NB2O02O1S2LB2NB2O02O12BBS2NB2O12BBS2NB2J1S2NB2O12BBS2RM2NBFS2TL4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13EX13RX12O02O1S2NBS2NBSS3NBI2NBFFS2NB3THRS2TL4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S3MSV3SYA2SY2NBFFS2RM2NB2CR3THRS2NB4RBC1S2NB2R12J0S2NB1G2J3S2NB2OE2BOS2NBS2NBFFS2NBS2NB2R1S2NB2R12J2S5SEPBN2LB2NB2O02O1S2NB3THRS2TL2RX2BC3NBI2NB3NB'3RB13EX13RX1FS2NBS3NBI2NB3BCRS2NB2CRS2NB2J2S2NB2R12RRFS3NBI2NB3BCRFS2NBS2NB2O02BB".
pose proof (shrink_facts _ _ _ _ _ _ SHR R1 ltac:(lia) TH) as (NB' & TH').
assert (THR : 1 <= w_threshold s <= 4096).
{ rewrite TH. pose proof (Z.pow_pos_nonneg 2 (w_nbBits s - 1) ltac:(lia) ltac:(lia)). split; [lia|]. change 4096 with (2^12). apply Z.pow_le_mono_r; lia. }
pose proof (u16_znth psegs m1 NC nc (w_symbol s) (Z_to_bv 64 (NC + 2 * w_symbol s)) NA LR ltac:(reflexivity)) as RD.
zstep. zstep. rewrite zext32_sh31 by lia. zstep.
zstep. fold count. rewrite sx16_short by exact CR.
set (mx := 2 * w_threshold s - 1 - w_remaining s) in *.
set (count2 := if w_threshold s <=? count + 1 then count + 1 + mx else count + 1) in *.
set (bs1 := u32 (w_bitStream s + u32 (u32 count2 * 2 ^ w_bitCount s))) in *.
set (bc1 := w_bitCount s + w_nbBits s - (if count2 <? mx then 1 else 0)) in *.
assert (RC2 : - 50000 <= count2 < 50000) by (subst count2 mx; destruct (w_threshold s <=? count + 1); lia).
assert (RBC1 : 0 <= bc1 <= 44) by (subst bc1; destruct (count2 <? mx); lia).
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
destruct CTL as (CT1 & CT2 & CT3 & CT4). rewrite ESC in CT1, CT2, CT3, CT4.
cbn [w_remaining w_threshold w_nbBits w_previousIs0] in CT1, CT2, CT3, CT4.
assert (RR : 1 <= rem' <= 8192) by (rewrite <- CT1; destruct WID as (_ & _ & _ & _ & _ & RQ & _); exact RQ).
assert (TAIL : forall m2 X3 (y9 y19 y20 y24 y25 : word), MINV m2 (w_buf sd) -> 0 <= X3 < 2^64 -> X3 mod 2^32 = w_bitStream sd ->
evt psegs POST (WST 0x13b7c m2 (Z_to_bv 64 count2) y9 (Z_to_bv 64 (BUF + w_out sd)) (Z_to_bv 64 (w_bitCount sd)) (Z_to_bv 64 X3)
(Z_to_bv 64 (w_symbol s)) y19 y20 (Z_to_bv 64 rem') (Z_to_bv 64 nb') (Z_to_bv 64 thr') y24 y25)).
{ intros m2 X3 y9 y19 y20 y24 y25 MV2 RX3 EX3.
zstep. sw32 (w_symbol s + 1). zstep.
if_cases J1; zify_cond J1.
-
rewrite <- CT1.
apply KE; [ | exact MV2 | exact RX3 | exact EX3].
rewrite SYD. replace (w_symbol s + 1 <? asz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
- zstep. zstep.
replace (0 <? (count2 + -1) mod 18446744073709551616) with (negb (count2 =? 1)).
2:{ destruct (Z.eqb_spec count2 1) as [E1|N1]; cbn [negb]; symmetry; [apply Z.ltb_ge| apply Z.ltb_lt]; lia. }
zstep. zstep. zstep. zstep.
if_cases J2; zify_cond J2.
+ rewrite <- CT1, <- CT2, <- CT3, <- CT4, <- SYD.
apply KL; [ | exact MV2 | exact RX3 | exact EX3].
rewrite SYD, CT1. replace (w_symbol s + 1 <? asz) with true by (symmetry; apply Z.ltb_lt; lia).
replace (1 <? rem') with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
+ zstep. rewrite <- CT1.
apply KE; [ | exact MV2 | exact RX3 | exact EX3].
rewrite CT1. replace (1 <? rem') with false by (symmetry; apply Z.ltb_ge; lia). apply andb_false_r. }
assert (P60 : forall (y22' y23' : word), evt psegs POST
(WST 0x13b24 m1 (Z_to_bv 64 (w_nbBits s)) (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (BUF + w_out s))
(Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 X) (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_remaining s))
(Z_to_bv 64 count) (Z_to_bv 64 rem') (Z_to_bv 64 nb') (Z_to_bv 64 thr') x24 x25)).
{ intros _ _.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
zstep. rewrite zb_lxor_ones by lia.
zstep. zstep.
zstep. sw32 mx.
zstep. rewrite slt_lit_mr by lia.
zstep. zstep. rewrite mask_sel. zstep.
assert (EC2 : bv_swrap 32 ((if count + 1 <? w_threshold s then 0 else mx mod 18446744073709551616) + (count + 1) mod 18446744073709551616) = count2).
{ subst count2. destruct (Z.ltb_spec (count + 1) (w_threshold s)).
- replace (w_threshold s <=? count + 1) with false by (symmetry; apply Z.leb_gt; lia). apply swrap32_eqm; lia.
- replace (w_threshold s <=? count + 1) with true by (symmetry; apply Z.leb_le; lia). apply swrap32_eqm; lia. }
rewrite EC2.
zstep. zstep. rewrite slt_lit_rr by lia. zstep. rewrite (zb_b2z_if (count2 <? mx)). fold bc1. rewrite (swrap32_small bc1) by lia.
zstep.
pose proof (container_add X (w_bitStream s) count2 (w_bitCount s) BCR EX) as EX1. fold bs1 in EX1.
assert (RX1 : 0 <= (bv_swrap 32 (Z.shiftl (count2 mod 18446744073709551616) (w_bitCount s mod 32)) + X) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap17. revert EX1 RX1. generalize ((bv_swrap 32 (Z.shiftl (count2 mod 18446744073709551616) (w_bitCount s mod 32)) + X) mod 2^64). intros X1 EX1 RX1.
zstep.
pose proof FL as FL'. rewrite ESC in FL'. apply wflush_if_inv in FL'. cbn [w_bitCount] in FL'.
if_cases J3; lts_lit J3.
-
destruct FL' as [[G _]|[_ ESD]]; [exfalso; lia|]. subst sd.
eapply TAIL; [cbn [w_buf]; exact MV | exact RX1 | cbn [w_bitStream]; exact EX1].
- destruct FL' as [[_ FLH]|[G _]]; [| exfalso; lia].
apply wflush_inv in FLH. cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FLH.
destruct FLH as (OE & O0 & O1 & ESD). unfold FseNCount.Zlength in O1. subst sd.
pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof SA as (LO0 & _ & _). unfold FRAMEC in FA.
assert (FLUSH : forall (y9 : word), evt psegs POST
(WST 0x13b64 m1 (Z_to_bv 64 count2) y9 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 bc1) (Z_to_bv 64 X1)
(Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 mx) (Z_to_bv 64 (count + 1)) (Z_to_bv 64 rem') (Z_to_bv 64 nb') (Z_to_bv 64 thr')
(Z_to_bv 64 (w_threshold s * 2)) (Z_to_bv 64 (w_bitCount s + w_nbBits s)))).
{ intros y9.
zstep. u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. rewrite <- EX1. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^8) with 256. lia. }
zstep. zstep. sw32 (bc1 - 16).
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
setreg 11%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
eapply TAIL; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA
| change (2^32) with 4294967296 in RB3; change (2^64) with 18446744073709551616; lia
| cbn [w_bitStream]; apply Z.mod_small; exact RB3 ]. }
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
+ rewrite (ite_true _ safe _ _ SAFE). apply FLUSH.
+ apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
destruct OE as [OE|OE]; [congruence|].
zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply FLUSH. }
zstep. rewrite sraiw31_sign by lia.
zstep. zstep. zstep.
assert (E21 : bv_swrap 32 ((w_remaining s + (if count <? 0 then -1 else 0)) mod 18446744073709551616
- Z.lxor (count mod 18446744073709551616) ((if count <? 0 then -1 else 0) mod 18446744073709551616)) = rem').
{ subst rem'. destruct (Z.ltb_spec count 0).
- change ((-1) mod 18446744073709551616) with 18446744073709551615.
rewrite zb_lxor_ones by (apply Z.mod_pos_bound; lia). apply swrap32_eqm; lia.
- change (0 mod 18446744073709551616) with 0. rewrite Z.lxor_0_r. apply swrap32_eqm; lia. }
rewrite E21.
zstep. if_cases J0; lts_lit J0; [exfalso; lia|].
zstep. zstep. zstep.
if_cases J1; lts_lit J1.
-
rewrite shrink_S in SHR. replace (rem' <? w_threshold s) with false in SHR by (symmetry; apply Z.ltb_ge; lia).
injection SHR as <- <-. apply (P60 x22 x23).
- zstep. zstep.
eapply (A_ wr_shrink 63%nat rem' (w_threshold s) (w_nbBits s) thr' nb'); [lia | lia | lia | exact SHR | apply (P60 x22 x23)].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
End WR.
