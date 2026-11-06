(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWriteModel FseWalkArith.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AF_fse_iface AF_fse_write_A.
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
Ltac lts_lit K := unfold bv_lts in K; rewrite !signed_lit in K by lia; zify_bool K.
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
Notation AS_ l := (A_ l safe).
Ltac wrap16 := let v := reg_val 16%Z in
lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
Ltac minv_close BA NA FA SA MUA WMA MIA :=
split; [exact BA|]; split; [exact NA|]; split; [exact FA|]; split; [exact SA|]; split; [exact MUA|]; split; [exact WMA| exact MIA].
Lemma wr_zero_tail : forall s start2 sf m1 X (x14 x18 x20 x21 x22 x23 x25 x26 : word),
0 <= start2 -> start2 <= w_symbol s < start2 + 3 -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> 0 <= w_out s <= bsz -> MINV m1 (w_buf s) ->
bind (shl32 (u32 (w_symbol s - start2)) (w_bitCount s)) (fun v =>
wflush_if bsz safe (mkW (w_buf s) (w_out s) (u32 (w_bitStream s + v)) (w_bitCount s + 2)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s))) = Ok sf ->
(forall m2 X' (y14 y22 y23 : word), MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evtF asegs RNG POST (AST 0x818e0 m2 (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 (BUF + w_out sf)) y14 (Z_to_bv 64 X') x18
(Z_to_bv 64 (w_symbol s)) x20 x21 y22 y23 (Z_to_bv 64 start2) x25 x26)) ->
evtF asegs RNG POST (AST 0x8180c m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) x14 (Z_to_bv 64 X) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 x22 x23 (Z_to_bv 64 start2) x25 x26).
Proof using WRC.
intros s start2 sf m1 X x14 x18 x20 x21 x22 x23 x25 x26 S0 SR SY RX EX LB RO (BA & NA & FA & SA & MUA & WMA & MIA) H K.
apply bind_inv in H. destruct H as (v & SH & FL). apply shl32_inv in SH. destruct SH as [BC ->].
pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold AF_fse_write_A.FRAMEC in FA.
pose proof (ablk_lin _ _ BLKB) as LBK. unfold KHIGH, AIMG_HI in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0130?10088275704.12613070568592.12413071039784.1231350466882.126 14362626257.18515326963703.10915350540903.10915640641027.11915641300924.12017316818849.12517316818854.12019489965866.12719618399905.13819618399911.14222448268900.12025206072950.12027517043963.12029782367974.13529782367974.13931183134347.1183214378781.120 3214378781.124 32313870464.1183405217491.124 35206187911.1253599827952.108 36441195085.13436441195085.13837424291657.12337497742200.11538765357020.11538954701265.11039572309083.18142134850155.10845589988655.11845596907400.13945596907404.13747788875075.1224861253072.109 48725325126.14049170713844.124492328663.118  49423367528.12051818759664.1245222230152.122 5254976933.125 53728626131.12454475752564.12156736913457.13759310676568.18159310676568.18559314873579.11559314873579.11964407683368.13464407683368.13864794109999.12364799663456.12064899638539.12668017740603.13468017740603.13868189636808.13468189636808.1388316058051.124 913132285.124  9448783535.181 9448783535.185 9581028844.124 00000400>00H00L00T00[00b00l01601g01n02l03V04@04g04n05`05d05h06Z07O08D08K08O09E09L09M09N09R09Y09]09a09i0:Q0;;0;e0<O0=A0=i0>^0?P0@:0@]0A@0AG0Ae0Ai0B[0CP0D90Dd0Dl0E60F80G:0H80Hj0IK0IL0IM0IN0IO0JA0JE0JR0J`0KGS2NBS2RO2O12NBS2RO2O12NBS2NBS2NB3SR2S2SR2NBS2BC2NBS2RO2O12NBS2RO2O12NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S02SR2SY2RX2LB2BC2NBS2BC2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2O02O12NB3LBK3RX13CK2S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX1S2SR2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC2O02O12NB3RX1S2RO2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S2SR2NBFFS2NBS2BC2NBS2NBS2NBS2NB3SR1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2NBS5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX1S5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX1S2RO2NBS5BUFNZ4NCNZ2S02SR2SY2RX2BC2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC2O02O12NB3RX1S4SEPB4SEPN5SEPBN2LB2BC2O02O12NB3CK11G2G'S4SEPB4SEPN5SEPBN2LB2BC2O02O12NB3CK22G23G2'S1G2NB1BS2OE2NB2BOS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2O02O12NB3LBK3RX13CK1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ2RX2BC2NB3EX13RX13RB1FFFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S2NBS2NB3CK11G2H0S2NB3CK22G22H0S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX1".
rewrite (u32_id (w_symbol s - start2)) in FL by (change (2^32) with 4294967296; lia).
zstep. sw32 (w_symbol s - start2).
zstep. rewrite shiftl_mod32 by lia.
zstep.
assert (EX1 : ((bv_swrap 32 ((w_symbol s - start2) * 2 ^ w_bitCount s) + X) mod 2^64) mod 2^32
= u32 (w_bitStream s + u32 ((w_symbol s - start2) * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296. rewrite swrap32_eq. lia. }
assert (RX1 : 0 <= (bv_swrap 32 ((w_symbol s - start2) * 2 ^ w_bitCount s) + X) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap16. revert EX1 RX1. generalize ((bv_swrap 32 ((w_symbol s - start2) * 2 ^ w_bitCount s) + X) mod 2^64). intros X1 EX1 RX1.
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
assert (FLUSH : forall (y14 : word), evtF asegs RNG POST
(AST 0x81824 m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) y14 (Z_to_bv 64 X1) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 x22 x23 (Z_to_bv 64 start2) x25 x26)).
{ intros y14.
destruct (A_ inv_shadow _ MUA) as [UB1 _].
destruct (A_ chk_out m1 (BUF + w_out s) UB1 ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN1 : forall (z14 z22 : word), evtF asegs RNG POST
(AST 0x81834 m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) z14 (Z_to_bv 64 X1) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 z22 x23 (Z_to_bv 64 start2) x25 x26)).
{ intros z14 z22. clear RDB1 CK1 SR1 b1.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep.
destruct (A_ inv_shadow _ MUA) as [UB2 _].
lazymatch type of UB2 with unpoisoned ?mm _ _ =>
destruct (A_ chk_out mm (BUF + w_out s + 1) UB2 ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2) end.
zstep. zstep. zstep. rewrite sxb_sval.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JOIN2 : forall (w22 w23 : word), evtF asegs RNG POST
(AST 0x8184c mm (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s + 1)) (Z_to_bv 64 X1) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 w22 w23 (Z_to_bv 64 start2) x25 x26)) end.
{ intros w22 w23. clear RDB2 CK2 SR2 b2.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. change (2^8) with 256. lia. }
zstep. zstep. zstep.
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
setreg 13%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
setreg 5%Z (Z_to_bv 64 (w_bitCount s + 2 - 16)) ltac:(f_equal; lia).
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA
| change (2^32) with 4294967296 in RB3; change (2^64) with 18446744073709551616; lia
| cbn [w_bitStream]; apply Z.mod_small; exact RB3]. }
zstep. if_cases G2; zify_cond G2.
+ zstep. zstep. if_cases G2'; zify_lts G2'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN2.
+ apply JOIN2. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN1.
+ apply JOIN1. }
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
+ rewrite (ite_true _ safe _ _ SAFE). apply FLUSH.
+ apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
destruct OE as [OE|OE]; [congruence|].
zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply FLUSH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_zero_mid : forall f s start1 s2' start2 sf m1 X (x14 x18 x20 x21 x22 x23 x25 x26 : word),
0 <= start1 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
0 <= w_bitStream s < 2^32 -> 0 <= w_bitCount s ->
zlen (w_buf s) = bsz -> 0 <= w_out s <= bsz -> MINV m1 (w_buf s) ->
run3 (S f) s start1 = Ok (s2', start2) ->
bind (shl32 (u32 (w_symbol s2' - start2)) (w_bitCount s2')) (fun v =>
wflush_if bsz safe (mkW (w_buf s2') (w_out s2') (u32 (w_bitStream s2' + v)) (w_bitCount s2' + 2)
(w_symbol s2') (w_remaining s2') (w_threshold s2') (w_nbBits s2') (w_previousIs0 s2'))) = Ok sf ->
(forall m2 X' (y14 y22 y23 y24 : word), MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evtF asegs RNG POST (AST 0x818e0 m2 (Z_to_bv 64 (w_bitCount sf)) (Z_to_bv 64 (BUF + w_out sf)) y14 (Z_to_bv 64 X') x18
(Z_to_bv 64 (w_symbol s)) x20 x21 y22 y23 y24 x25 x26)) ->
evtF asegs RNG POST (AST 0x817ec m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) x14 (Z_to_bv 64 X) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 x22 x23 (Z_to_bv 64 start1) x25 x26).
Proof using WRC.
intros f s start1 s2' start2 sf m1 X x14 x18 x20 x21 x22 x23 x25 x26 S1 SY RX EX RB0 BC LB RO MV R3 TLH K.
pose proof (run3_facts _ _ _ _ _ R3 RB0 BC) as ((D1 & D2 & D3 & D4) & SY2 & B2 & O2 & RB2 & BC2 & ST2 & SR2).
Local Ltac2 Set LiaHints.tbl := fun () => "00?0?17328780436.11419617478418.11119617478418.11426604383400.11442134471252.11346515793883.11146515793883.11449597639079.11850104863000.13151020183212.11358270426683.11358364785427.1146321005544.118 6562756080.118 8592517893.118 00000`00a00b01701\01`01d02R02g02k03@03C04004\05KS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S12SY2RX2LB3ST23SR2FFS5BUFNZ4NCNZ2S12SY2RXS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2ROS2S1S2S1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB3SY23SR23RX'S5BUFNZ4NCNZ2S12SY2RXS2S1S5BUFNZ4NCNZ2S12SY2RXS1BS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2SY2RX2LB3SY23RX'S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2O23RX'S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S12RX2LB3SR21B3RX'".
specialize (SR2 ltac:(lia)).
zstep. sw32 (start1 + 3). zstep.
if_cases B; zify_cond B.
-
rewrite run3_S in R3. replace (start1 + 3 <=? w_symbol s) with false in R3 by (symmetry; apply Z.leb_gt; lia).
injection R3 as <- <-.
eapply (wr_zero_tail s start1 sf); try eassumption; try lia.
intros. apply K; assumption.
- eapply (AS_ wr_run3 f s start1 s2' start2); try eassumption; try lia.
intros X' y14 RX' EX'.
rewrite <- SY2, <- O2.
eapply (wr_zero_tail s2' start2 sf);
[ lia | lia | lia | exact RX' | exact EX' | rewrite B2; exact LB | lia | rewrite B2; exact MV | exact TLH | ].
intros. rewrite SY2. apply K; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_zero : forall s fl m1 X (x14 x18 x19 x20 x21 x23 x24 x25 x26 : word),
winv asz bsz s -> w_symbol s < asz -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s -> MINV m1 (w_buf s) ->
wzero_block nc asz bsz safe s = Ok fl ->
(forall sa m2 X' (y14 y22 y23 y24 y25 y26 : word), fl = Cont sa -> MINV m2 (w_buf sa) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sa ->
evtF asegs RNG POST (AST 0x818e0 m2 (Z_to_bv 64 (w_bitCount sa)) (Z_to_bv 64 (BUF + w_out sa)) y14 (Z_to_bv 64 X') x18
(Z_to_bv 64 (w_symbol sa)) x20 x21 y22 y23 y24 y25 y26)) ->
(forall sa (y14 y19 y24 y25 y26 : word), fl = Brk sa ->
evtF asegs RNG POST (AST 0x81a8c m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) y14 (Z_to_bv 64 X) x18
y19 x20 x21 (Z_to_bv 64 (w_symbol s)) x21 y24 y25 y26)) ->
evtF asegs RNG POST (AST 0x81778 m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) x14 (Z_to_bv 64 X) x18
x19 x20 x21 (Z_to_bv 64 (w_symbol s)) x23 x24 x25 x26).
Proof using WRC.
intros s fl m1 X x14 x18 x19 x20 x21 x23 x24 x25 x26 WI SYA RX EX MV H KC KB.
pose proof WI as (LB & RO & RB0 & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & FA & SA & MUA & WMA & MIA).
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
destruct (A_ inv_shadow _ MUA) as [_ UN1].
unfold wzero_block in H. apply bind_inv in H. destruct H as (sym & SK & H).
Local Ltac2 Set LiaHints.tbl := fun () => "00R0?15339623494.15915534271600.15815534282078.16016346644575.11617314721696.16717316818851.13117316818854.16817322479014.1162599566317.134 27809844849.1573122459008.157 32080162237.1423304526956.164 34117280779.13434122874170.16035212070532.13435212070534.1324011830303.114 4013576988.116 42132796117.15642547251744.13442558040485.15642558171174.11646093983509.12259308611920.15659308742867.11659588178612.13460348271652.1606599369317.156 6599369444.157 67547235139.16468185370196.14268185729876.1647704535130.156 00000900@00G00g01001P02002Q02U02\03<03C04=04D04K04L04M04X04c05M05U05]05e06R07G07R07V08H09I0:J0;K0<@0=90=YS4BC242NBS2NB2J2S2NB2J2S3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2B0S4BC242NBS3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2B0S3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2B0S3MSV5BUFNZ4NCNZ3SYA2RX2SY3NBI2NBS2NBS2NB2J2S3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2B0S2NB2SRS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX3NBI2NB3SR'3SY13RO13RX1S2SY2NBS2SY2NBFFS3SYA2SY2NBS3SYA2SY2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX3NBI2NB3RO1S3MSV2NBS3MSV2NBS3MSV2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB3NBI2NB3SR'S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX3NBI2NB3SR'3LB13RO12J1S3SYA2NB2B0S2NBS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX3NBI2NB3SR'3RO1S3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2SY3NBI2NB3SR'3LB13RO13ST13SR1S3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2SY3NBI2NB3SR'3LB13RO13ST13SR1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2SY3NBI2NB3SY13LB13RO13ST13SR13RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC3NBI2NB3BC13LB13RO1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC3NBI2NB3BC13LB13RO13RX1S3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2B0".
pose proof (skip_zeros_range nc asz _ (w_symbol s) sym ltac:(lia) SK) as SR.
zstep. zstep. if_cases B0; zify_cond B0; [exfalso; lia|].
do 7 zstep.
rewrite zext32_sh31 by lia. rewrite (Z.mod_small (w_symbol s) 4294967296) by lia.
eapply (AS_ wr_skip _ (w_symbol s) sym); [lia | exact NA | exact UN1 | exact SK | | ].
-
intros y14 y23 y24 y25 y26 SR'.
replace (sym =? asz) with false in H by (symmetry; apply Z.eqb_neq; lia).
apply bind_inv in H. destruct H as ([sa start1] & R24 & H).
apply bind_inv in H. destruct H as ([s2' start2] & R3 & H).
apply bind_inv in H. destruct H as (v & SH & H). apply bind_inv in H. destruct H as (sf & FL & H). injection H as <-.
set (s0' := mkW (w_buf s) (w_out s) (w_bitStream s) (w_bitCount s) sym (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s)) in *.
pose proof (run24_facts bsz safe _ _ _ _ _ R24 ltac:(exact LB) RB0 RO) as ((C1 & C2 & C3 & C4) & SY1 & BC1 & LB1 & RO1 & RB1 & ST1 & SR1).
cbn [s0' w_symbol w_bitCount] in SY1, BC1, SR1. specialize (SR1 ltac:(lia)). unfold FseNCount.Zlength in LB1.
pose proof (run3_facts _ _ _ _ _ R3 RB1 ltac:(lia)) as ((D1 & D2 & D3 & D4) & SY2 & B2 & O2 & RB2 & BC2 & ST2 & SR2).
assert (TLH : bind (shl32 (u32 (w_symbol s2' - start2)) (w_bitCount s2')) (fun v =>
wflush_if bsz safe (mkW (w_buf s2') (w_out s2') (u32 (w_bitStream s2' + v)) (w_bitCount s2' + 2)
(w_symbol s2') (w_remaining s2') (w_threshold s2') (w_nbBits s2') (w_previousIs0 s2'))) = Ok sf).
{ assert (ES : sym = w_symbol s2') by congruence. rewrite ES in SH. rewrite SH. cbn [bind]. exact FL. }
assert (MID : forall m2 X1 (z14 z22 z23 z25 z26 : word), MINV m2 (w_buf sa) -> 0 <= X1 < 2^64 -> X1 mod 2^32 = w_bitStream sa ->
evtF asegs RNG POST (AST 0x817ec m2 (Z_to_bv 64 (w_bitCount sa)) (Z_to_bv 64 (BUF + w_out sa)) z14 (Z_to_bv 64 X1) x18
(Z_to_bv 64 (w_symbol sa)) x20 x21 z22 z23 (Z_to_bv 64 start1) z25 z26)).
{ intros m2 X1 z14 z22 z23 z25 z26 MV2 RX1 EX1.
eapply (wr_zero_mid _ sa start1 s2' start2 sf); [lia | lia | exact RX1 | exact EX1 | exact RB1 | lia | exact LB1 | exact RO1 | exact MV2 | exact R3 | exact TLH | ].
intros m3 X' w14 w22 w23 w24 MV3 RX3 EX3.
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
zstep.
zstep. rewrite b2z_word_eqz. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
* rewrite (ite_negb_true _ safe _ _ SAFE).
eapply (AS_ wr_run24s _ s0' (w_symbol s) sa start1); [exact SAFE | lia | cbn [s0' w_symbol]; lia | cbn [s0' w_symbol]; lia
| exact RX | exact EX | exact LB | exact MV | exact R24' | ].
intros m2 X' z14 z22 z25 z26 MV2 RX2 EX2. cbn [s0' w_symbol w_bitCount]. rewrite <- SY1. rewrite <- BC1 at 1. apply MID; assumption.
* apply Bool.not_true_is_false in SAFE. rewrite (ite_negb_false _ safe _ _ SAFE).
eapply (AS_ wr_run24c _ s0' (w_symbol s) sa start1); [exact SAFE | lia | cbn [s0' w_symbol]; lia | cbn [s0' w_symbol]; lia
| exact RX | exact EX | exact LB | exact MV | exact R24' | ].
intros m2 X' z14 z22 z25 z26 MV2 RX2 EX2. cbn [s0' w_symbol w_bitCount]. rewrite <- SY1. rewrite <- BC1 at 1. apply MID; assumption.
+
rewrite run24_S in R24. cbn [s0' w_symbol] in R24.
replace (w_symbol s + 24 <=? sym) with false in R24 by (symmetry; apply Z.leb_gt; lia).
injection R24 as <- <-.
zstep.
apply (MID m1 X); [exact MV | exact RX | exact EX].
-
intros y14 y23 y24 y25 y26 ->.
replace (asz =? asz) with true in H by (symmetry; apply Z.eqb_refl). injection H as <-.
zstep. zstep.
eapply KB. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_count : forall s sc sd m1 X (x14 x22 x23 x24 x25 x26 : word),
winv asz bsz s -> w_symbol s < asz -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s -> MINV m1 (w_buf s) ->
wcount_block nc s = Ok sc -> wflush_if bsz safe sc = Ok sd ->
(forall m2 X' (y19 y23 y24 y25 y26 : word), (w_symbol sd <? asz) && (1 <? w_remaining sd) = true ->
MINV m2 (w_buf sd) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sd ->
evtF asegs RNG POST (AST 0x81768 m2 (Z_to_bv 64 (w_bitCount sd)) (Z_to_bv 64 (BUF + w_out sd)) (Z_to_bv 64 (Z.b2z (negb (w_previousIs0 sd))))
(Z_to_bv 64 X') (Z_to_bv 64 (w_nbBits sd)) y19 (Z_to_bv 64 (w_threshold sd)) (Z_to_bv 64 (w_remaining sd))
(Z_to_bv 64 (w_symbol sd)) y23 y24 y25 y26)) ->
(forall m2 X' (y14 y18 y19 y20 y21 y22 y24 y25 y26 : word), (w_symbol sd <? asz) && (1 <? w_remaining sd) = false ->
MINV m2 (w_buf sd) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sd ->
evtF asegs RNG POST (AST 0x81a8c m2 (Z_to_bv 64 (w_bitCount sd)) (Z_to_bv 64 (BUF + w_out sd)) y14 (Z_to_bv 64 X') y18 y19 y20 y21 y22
(Z_to_bv 64 (w_remaining sd)) y24 y25 y26)) ->
evtF asegs RNG POST (AST 0x818e0 m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) x14 (Z_to_bv 64 X) (Z_to_bv 64 (w_nbBits s))
(Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (w_remaining s)) x22 x23 x24 x25 x26).
Proof using WRC.
intros s sc sd m1 X x14 x22 x23 x24 x25 x26 WI SYA RX EX MV CB FL KL KE.
pose proof WI as (LB & RO & RB0 & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & FA & SA & MUA & WMA & MIA).
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof (wcount_flush_facts nc asz bsz safe s sc sd CB FL WI SYA NCR) as (WID & SYD & CTL).
pose proof (wcount_block_inv nc s sc CB) as CI. cbv zeta in CI. destruct CI as (thr' & nb' & LR & BCR & R1 & SHR & ESC).
unfold FseNCount.Zlength in LR.
pose proof (Forall_Znth _ _ (w_symbol s) NCR LR) as CR. cbv beta in CR.
set (count := Znth (w_symbol s) nc) in *.
set (rem' := w_remaining s - (if count <? 0 then - count else count)) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "02L0?10088275704.16111149532066.15411603572554.12612324133529.14413070568592.15913071039790.15814210624796.15014362626129.2341496497248.160 15585600701.12515640641025.15515641300924.15616011609646.15416218154386.12616344464487.14416344464487.14716344464487.14917314721711.15217316818850.15917316818852.16717316818853.15717316818861.17217316818862.16817328943518.14419118483249.13119489965866.16219618399904.17619618399910.17619628467489.15221448881065.13222133940738.14422448268900.15623362391946.15923746254485.1302691685756.143 27517043963.15628707550844.16729646625993.18029782367974.16229782367974.17129782367974.17331145898401.14531183134347.1543214378781.156 3214378781.159 32313870464.15433932638637.14433938916757.1443405217491.159 34497014984.14935206187911.16035212070534.16436145266549.14536202861644.14836441195085.17036441195086.17237424291663.15837497742200.14938954701265.14639124915372.15339159981841.15039572309211.23139721191329.15340244715328.14540829096510.18741417891415.12541422282358.12641730628386.14841968874928.15741968874928.15842132654821.15942132829014.14442134701907.15142558040485.15242631473814.14443467007921.1474399294143.154 44478585536.14844478585536.14944927972768.15844927972769.15745589988655.15545596907403.18245596907405.17247169790233.16647428594747.16147788875075.15747826599073.14547829975451.14348613897338.15948613897340.15748725325126.17549170713844.159492328663.155  49423367528.15650986760084.14951818759664.15951851082428.15752074235540.1575222230152.157 53508216720.15753508216720.16653728626131.1595428736405.149 54290872331.12354309134368.15854309134369.15754475752564.15755590205916.15155894028037.14755935222434.16055935222437.16156736913461.17956862664148.18758061619888.15059310676439.18759310676696.23159310676696.23459314873579.14859314873579.15059314873579.15659437227811.16159437227813.16559588178608.15759588178615.16160245107408.16060245107415.16161814822930.14563986878663.14963986878663.15464407683368.16164407683368.17064407683371.17264794109999.15964799663456.15664821634240.15764899638539.16166638920316.1666758013062.144 67940486329.13268017740600.17268017740603.17068189636808.16168189636808.17068189636811.1727642596357.131 8316058051.159 8401265577.154 8935173664.157 8935173664.158 8935173665.157 913132285.159  9448783407.231 9448783407.234 9544766530.145 9581028844.159 00000400n01401]01g02102502=02>02F02P02Z03X03`03h03o04m05405<05D05K06J07E07L08009=0:30:i0;h0<_0<e0=X0=a0>[0?N0@O0AB0B90B=0BA0BE0BM0CN0DO0ES0EZ0Ea0Eh0El0F30G40G50G>0GB0GC0GD0GH0GP0GT0G^0He0Hm0I40Ig0Io0J30J70J;0J<0J=0K>0L@0M70M?0ME0ML0MS0M]0Mg0Mh0Mi0N_0OU0PK0PT0PU0QV0Q^0Qf0Qg0Qh0Rl0Sj0Tc0UR0UY0VH0VO0VP0VW0V[0V_0Vc0Vk0W30W40W50X60Y80YB0YC0YD0ZH0ZT0Z]0[J0\>0]40]>0]G0]Q0^E0_90_=0_A0_B0_C0`60`=0`G0aM0b^0co0e<0f:0g10gZ0g[0g_0hV0hW0hX0hY0hZ0h[0hb0ic0ij0ik0il0j`0jd0k10k?0kC0l6S2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RX32E1S2NB1HS5BUFNZ4NCNZ2RX2BC2RM3NBI2NB2CR3NB'3RMX1HS2RO2NB2O1S2RO2NB2O1S2NBS2NB3SR2FS3NBI2NBS2RO2NB2O1S2RO2NB2O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RC23RX32N1S3NBI2NBS2NB3THRS2RM2NBS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN3SYA2RX2LB2BC2SY3NBI2NB2LR3NB'S2RM2NBS2NB3THRS2NB3THRS2BC2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2SY3NBI2NB2LR3NB'3LBK3LNK3RX3S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2SY3NBI2NB2LR3NB'3LBK3LNKS2RM2NBS5BUFNZ4NCNZ2RX2BC3NBI2NB2CR3NB'3RMXS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2NB2LR3NB'3RB13LBK3RX12O02O13CK2S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3NB'3RB13LBK3RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3NB'3RB13LBK3RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2SY3NBI2NB2LR3NB'3LBK3LNK3RX3S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3BCR3NB'S2NB1HS5BUFNZ4NCNZ2LO3KLO2RX2BC3NBI2NB3NB'3RB13LBK3RX12O0S2NB4RBC1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2RM3NBI2TH2NB3NB'3THRS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'S4NCEV4SEPB4SEPN5SEPBN2LB2BC3NBI2NB3SYD2LR3NB'1H2H03H19S2NBS2NBS2NBS2NB3RC2S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC3NBI2NB3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC3NBI2NB2LR3NB'3RB13RX12O02O1S2RO2NBS2NB2CRS2NB2CRS2NBS2NB2J1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1FS2NB4RBC1S2NBFFS2NBS2NB3THRS2NBS2NB2R12RRS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2NB3SYD2LR3NB'3LNK2CKS2NB3SR1S2NB2J1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'S2NB3SRBS2NBS2NBS2NBFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2RM3NBI2NB2LR3NB'3RMX1H2TH2CRS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RX3S3MSV2NBS2NB1HS2NB2CRS2NB2J1S2NB2R12RRS2NB2R12RRFFS5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3NB'3RB13LBK3RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3NB'3RB13LBK3RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB3NB'3RB13LBK3RX12O02O1S2NB4RBC1FS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S2NB3RMXS2NB3RMXFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC3NBI2NB2LR3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB3NB'3RB13RX12O02O1S5BUFNZ4NCNZ2LO3KLO2RX2LB3NBI2NB2LR3NB'3RB13LBK3RX12O02O1S5BUFNZ4NCNZ2RX2LB2BC3NBI2NB3NB'3RB13LBK3RX12O1S2NB2J1S5BUFNZ4NCNZ2RX2LB2BC3NBI2NB3NB'3RB13LBK3RX12O1S2RM2NBFS2RO2NBS2NBS2NBS2NBS2NB3THRS3NBI2NBFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN3SYA2RX2LB2BC2SY3NBI2NB2LR3NB'3RX3S2NB2R12RRFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC3NBI2NB2LR3NB'3RB13RX12O02O1S2NB2CK1G2H0S2NB4RBC1S4SEPB4SEPN5SEPBN2LB2BC3NBI2NB2LR3NB'2CK1G2G'S4SEPB4SEPN5SEPBN2LB2BC3NBI2NB2LR3NB'2O02O13CK11G2G'S4SEPB4SEPN5SEPBN2LB2BC3NBI2NB2LR3NB'2O02O13CK22G23G2'S2NB2R12J0S2NB1G2J3S2NB2OE2BOS5BUFNZ4NCNZ2LO4SEPN3KLO2RX2LB3NBI2NB2LR3NB'3LBK3LNKS5BUFNZ4NCNZ2LO4SEPN3KLO2RX2LB3NBI2NB2LR3NB'3LBK3LNKS2NBS2NBFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'S2NB2R1S2NB2R12J2S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3NC83KLO2RX2RO2BC3NBI2NB3SYD2LR3NB'3LNKS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC3NBI2NB2LR3NB'3RB13LBK3RX12O02O1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC3NBI2NB2LR3NB'3RB13LBK3RX12O02O1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB3NBI2NB2LR3NB'3RB13LBK3RX12O02O13CK1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB3NB'3RB13RX12O02O1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB3NBI2TH2NB2LR3NB'3THRS5BUFNZ4NCNZ2RX2BC3NBI2NB3NB'3RB13EX13RX1FS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3BCR3NB'FFFFFS2NB2CRS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC3NBI2NB2LR3NB'3RB13RX12O02O1S2NB2J2FFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB3NBI2NB2LR3BCR3NB'S2NBS2NB3CK11G2H0S2NB3CK22G22H0S2NBS5BUFNZ4NCNZ2LO3KLO2RX2BC3NBI2NB3NB'3RB13LBK3RX12O0".
pose proof (shrink_facts _ _ _ _ _ _ SHR R1 ltac:(lia) TH) as (NB' & TH').
assert (THR : 1 <= w_threshold s <= 4096).
{ rewrite TH. pose proof (Z.pow_pos_nonneg 2 (w_nbBits s - 1) ltac:(lia) ltac:(lia)). split; [lia|]. change 4096 with (2^12). apply Z.pow_le_mono_r; lia. }
pose proof (u16_znth asegs m1 NC nc (w_symbol s) (Z_to_bv 64 (NC + 2 * w_symbol s)) NA LR ltac:(reflexivity)) as RD.
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
pose proof (ablk_lin _ _ BLKB) as LBK. pose proof (ablk_lin _ _ BLKN) as LNK. unfold KHIGH, AIMG_HI in *.
assert (TAIL : forall m2 X3 (y14 y20 y21 y22 y26 : word), MINV m2 (w_buf sd) -> 0 <= X3 < 2^64 -> X3 mod 2^32 = w_bitStream sd ->
evtF asegs RNG POST (AST 0x819b0 m2 (Z_to_bv 64 (w_bitCount sd)) (Z_to_bv 64 (BUF + w_out sd)) y14 (Z_to_bv 64 X3) (Z_to_bv 64 count2)
(Z_to_bv 64 (w_symbol s)) y20 y21 y22 (Z_to_bv 64 rem') (Z_to_bv 64 nb') (Z_to_bv 64 thr') y26)).
{ intros m2 X3 y14 y20 y21 y22 y26 MV2 RX3 EX3.
zstep. sw32 (w_symbol s + 1). zstep.
if_cases J1; zify_cond J1.
- rewrite <- CT1.
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
assert (P78 : forall (y22 : word), evtF asegs RNG POST
(AST 0x81934 m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 count) (Z_to_bv 64 X) (Z_to_bv 64 (w_nbBits s))
(Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (w_remaining s)) y22
(Z_to_bv 64 rem') (Z_to_bv 64 nb') (Z_to_bv 64 thr') x26)).
{ intros y22.
zstep. rewrite (Z.shiftl_mul_pow2 (w_threshold s) 1) by lia. change (2^1) with 2.
zstep. rewrite (zb_lxor_ones (w_remaining s)) by lia.
zstep. zstep.
zstep. sw32 mx.
zstep. rewrite slt_lit_mr by lia.
zstep. zstep. rewrite mask_sel. zstep.
assert (EC2 : bv_swrap 32 ((if count + 1 <? w_threshold s then 0 else mx mod 18446744073709551616) + (count + 1) mod 18446744073709551616) = count2).
{ subst count2. destruct (Z.ltb_spec (count + 1) (w_threshold s)).
- replace (w_threshold s <=? count + 1) with false by (symmetry; apply Z.leb_gt; lia). apply swrap32_eqm; lia.
- replace (w_threshold s <=? count + 1) with true by (symmetry; apply Z.leb_le; lia). apply swrap32_eqm; lia. }
rewrite EC2.
zstep. zstep. rewrite slt_lit_rr by lia. zstep. rewrite (zb_b2z_if (count2 <? mx)). fold bc1. rewrite (FseWalkKit.swrap32_small bc1) by lia.
zstep.
pose proof (container_add X (w_bitStream s) count2 (w_bitCount s) BCR EX) as EX1. fold bs1 in EX1.
assert (RX1 : 0 <= (bv_swrap 32 (Z.shiftl (count2 mod 18446744073709551616) (w_bitCount s mod 32)) + X) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap16. revert EX1 RX1. generalize ((bv_swrap 32 (Z.shiftl (count2 mod 18446744073709551616) (w_bitCount s mod 32)) + X) mod 2^64). intros X1 EX1 RX1.
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
pose proof SA as (LO0 & _ & _). unfold AF_fse_write_A.FRAMEC in FA.
assert (FLUSH : evtF asegs RNG POST
(AST 0x81974 m1 (Z_to_bv 64 bc1) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (count2 mod 18446744073709551616) (w_bitCount s mod 32))))
(Z_to_bv 64 X1) (Z_to_bv 64 count2) (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 mx) (Z_to_bv 64 (w_threshold s * 2))
(Z_to_bv 64 rem') (Z_to_bv 64 nb') (Z_to_bv 64 thr') (Z_to_bv 64 (w_bitCount s + w_nbBits s)))).
{ destruct (A_ inv_shadow _ MUA) as [UB1 _].
destruct (A_ chk_out m1 (BUF + w_out s) UB1 ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN1 : forall (z14 z20 : word), evtF asegs RNG POST
(AST 0x81984 m1 (Z_to_bv 64 bc1) (Z_to_bv 64 (BUF + w_out s)) z14 (Z_to_bv 64 X1) (Z_to_bv 64 count2) (Z_to_bv 64 (w_symbol s))
z20 (Z_to_bv 64 mx) (Z_to_bv 64 (w_threshold s * 2))
(Z_to_bv 64 rem') (Z_to_bv 64 nb') (Z_to_bv 64 thr') (Z_to_bv 64 (w_bitCount s + w_nbBits s)))).
{ intros z14 z20. clear RDB1 CK1 SR1 b1.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep.
destruct (A_ inv_shadow _ MUA) as [UB2 _].
lazymatch type of UB2 with unpoisoned ?mm _ _ =>
destruct (A_ chk_out mm (BUF + w_out s + 1) UB2 ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2) end.
zstep. zstep. zstep. rewrite sxb_sval.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JOIN2 : forall (w20 w21 : word), evtF asegs RNG POST
(AST 0x8199c mm (Z_to_bv 64 bc1) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s + 1)) (Z_to_bv 64 X1) (Z_to_bv 64 count2)
(Z_to_bv 64 (w_symbol s)) w20 w21 (Z_to_bv 64 (w_threshold s * 2))
(Z_to_bv 64 rem') (Z_to_bv 64 nb') (Z_to_bv 64 thr') (Z_to_bv 64 (w_bitCount s + w_nbBits s)))) end.
{ intros w20 w21. clear RDB2 CK2 SR2 b2.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. change (2^8) with 256. lia. }
zstep. zstep. sw32 (bc1 - 16).
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
setreg 13%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
eapply TAIL; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA
| change (2^32) with 4294967296 in RB3; change (2^64) with 18446744073709551616; lia
| cbn [w_bitStream]; apply Z.mod_small; exact RB3 ]. }
zstep. if_cases G2; zify_cond G2.
+ zstep. zstep. if_cases G2'; zify_lts G2'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN2.
+ apply JOIN2. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN1.
+ apply JOIN1. }
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
+ rewrite (ite_true _ safe _ _ SAFE). apply FLUSH.
+ apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
destruct OE as [OE|OE]; [congruence|].
zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply FLUSH. }
destruct (A_ inv_shadow _ MUA) as [_ UN1].
destruct (unpoisoned_check_rd asegs m1 NC (NC + 2 * zlen nc) (NC + 2 * w_symbol s) 2 UN1 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK).
unfold shad, ASHOFF in RDB. replace (2147450880 + Z.shiftr (NC + 2 * w_symbol s) 3) with (Z.shiftr (NC + 2 * w_symbol s) 3 + 2147450880) in RDB by lia.
pose proof (sval_range b) as SRB.
zstep. zstep. rewrite zext32_sh31 by lia. zstep.
zstep. zstep. zstep. rewrite sxb_sval.
assert (LOADED : forall (z22 z23 : word), evtF asegs RNG POST
(AST 0x818fc m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (NC + 2 * w_symbol s)) (Z_to_bv 64 X) (Z_to_bv 64 (w_nbBits s))
(Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 (w_threshold s)) (Z_to_bv 64 (w_remaining s)) z22 z23 x24 x25 x26)).
{ intros z22 z23. clear RDB CK SRB b.
zstep. fold count. rewrite sx16_short by exact CR.
zstep. rewrite sraiw31_sign by lia.
zstep. zstep. zstep. rewrite abs_via_sign by (fold rem'; lia). fold rem'.
zstep. if_cases J0; lts_lit J0; [exfalso; lia|].
zstep. zstep. zstep.
if_cases J1; lts_lit J1.
-
rewrite shrink_S in SHR. replace (rem' <? w_threshold s) with false in SHR by (symmetry; apply Z.ltb_ge; lia).
injection SHR as <- <-. apply P78.
- zstep. zstep.
eapply (AS_ wr_shrink 63%nat rem' (w_threshold s) (w_nbBits s) thr' nb'); [lia | lia | lia | exact SHR | apply P78]. }
zstep. if_cases G; zify_cond G.
- zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply LOADED.
- apply LOADED.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
End WR.
End CANSEC1.
