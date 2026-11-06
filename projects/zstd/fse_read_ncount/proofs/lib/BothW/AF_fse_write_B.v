(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
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
Lemma wr_zero_tail : forall s start2 sf m1 X (x8 x10 x13 x20 x22 x26 x28 x30 x31 : word),
0 <= start2 -> start2 <= w_symbol s < start2 + 3 -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> 0 <= w_out s <= bsz -> MINV m1 (w_buf s) ->
bind (shl32 (u32 (w_symbol s - start2)) (w_bitCount s)) (fun v =>
wflush_if bsz safe (mkW (w_buf s) (w_out s) (u32 (w_bitStream s + v)) (w_bitCount s + 2)
(w_symbol s) (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s))) = Ok sf ->
(forall m2 X' (y10 y13 y14 y30 : word), MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evtF bsegs RNG POST (BST 0x81890 m2 x8 y10 (Z_to_bv 64 (BUF + w_out sf)) y13 y14 (Z_to_bv 64 X') x20 x22 x26 (Z_to_bv 64 (w_symbol s)) x28
(Z_to_bv 64 (w_bitCount sf)) y30 x31)) ->
evtF bsegs RNG POST (BST 0x81788 m1 x8 x10 (Z_to_bv 64 (BUF + w_out s)) x13 (Z_to_bv 64 start2) (Z_to_bv 64 X) x20 x22 x26 (Z_to_bv 64 (w_symbol s)) x28
(Z_to_bv 64 (w_bitCount s)) x30 x31).
Proof using WRC.
intros s start2 sf m1 X x8 x10 x13 x20 x22 x26 x28 x30 x31 S0 SR SY RX EX LB RO (BA & NA & [junk8 FA] & SA & MUA & WMA & MIA) H K.
apply bind_inv in H. destruct H as (v & SH & FL). apply shl32_inv in SH. destruct SH as [BC ->].
pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold AF_fse_write_A.FRAMEC in FA.
pose proof (ablk_lin _ _ BLKB) as LBK. unfold KHIGH, AIMG_HI in *.
Local Ltac2 Set LiaHints.tbl := fun () => "01?0?10088275704.131107623851.115  13070568592.12813071252905.1271350466882.131 14362626257.18915326963703.11115350540903.11215640690308.12215641300924.12316845815291.12317316818850.12717316818852.14317316818853.12817322560934.11117328780436.11719489965100.13119618399909.14619618399909.14822448268900.12325206072946.12729782367974.14229782367974.14530047557315.12831183134347.1213214378781.123 3214378781.128 32313870464.1213405217491.128 35206187911.1293602119373.111 36441195081.14136441195083.14437424340936.12738954701265.11339572309083.18442130557540.11542132582867.12942132583254.11145589988655.12145590082573.11945590082700.12445590083339.12945596907403.13945596907403.14147788875075.1264861253072.112 48725325127.14349170713844.128492328663.121  49423367528.12351818759664.1285222230152.126 5254976934.127 53728626131.13054475752564.12456736913457.14059310676568.18459310676568.18959314873579.11259314873579.11859314873579.12059314873579.12259314873579.12559314873579.13062207021416.12964407683372.14164407683374.14464794109999.12664799663456.12364899638539.13168017740605.14468017740607.14168189636812.14168189636814.144913132285.128  9448783535.184 9448783535.189 9581028844.128 00000400;00E00O00S00[00b00i01301=01o02`02g02n03503<04@04j05T06;06B06F06J07<07n08c09X09_09c0:Y0:`0:a0:b0:f0:j0;20;^0<P0=80=b0>L0?60?`0@J0A40Af0BN0CC0D50D_0EB0Ee0El0FJ0FN0G@0H50Hl0Il0J60J>0Jh0K20KZ0LB0LI0MK0NM0ON0P@0Pa0Pb0Pc0Pd0Pe0Pi0Q60QJ0R1S2NBS2BC2NBS2RO2O12NBS2RO2O12NBS2NBS2NB3SR2S2SR2NBS2BC2NBS2RO2O12NBS2RO2O12NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S02SR2SY2RX2LB2BC2NBS2BC2NBS2BC2NBS2BC2NBS2BC2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2O02O12NB3LBK3RX12G12G23CK2S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX1S2SR2NBS2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC2O02O12NB3RX1S2RO2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S2SR2NBFFS2NBS2NBS2NB3SR1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2NBS5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX1S5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX1S2RO2NBS5BUFNZ4NCNZ2S02SR2SY2RX2BC2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2BC2O02O12NB3RX1S2LO4SEPB4SEPN5SEPBN3KLO2LB2BC2O02O12NB3LBK2G13CK11G2G'S2LO4SEPB4SEPN5SEPBN3KLO2LB2BC2O02O12NB3LBK2G12G23CK22G43G4'3H39S2BC2NB2G0S1G2NB1BS5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX12G1S2OE2NB2BOS5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX12G21HS5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX12G31HS2BC2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2O02O12NB3LBK3RX12G13CK1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ2RX2BC2NB3EX13RX13RB1FFFFS2NBS2NB3CK11G2H0S2NB2G12G23CK22G42H0S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX1".
rewrite (u32_id (w_symbol s - start2)) in FL by (change (2^32) with 4294967296; lia).
zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
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
assert (FLUSH : evtF bsegs RNG POST
(BST 0x817ac m1 x8 (Z_to_bv 64 15) (Z_to_bv 64 (BUF + w_out s)) x13 (Z_to_bv 64 start2) (Z_to_bv 64 X1) x20 x22 x26
(Z_to_bv 64 (w_symbol s)) x28 (Z_to_bv 64 (w_bitCount s)) x30 x31)).
{ zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
destruct (A0_ inv_shadow _ MUA) as [UB1 _].
destruct (A0_ chk_out m1 (BUF + w_out s) UB1 ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN1 : forall (y10 y13 : word), evtF bsegs RNG POST
(BST 0x817c0 m1 x8 y10 (Z_to_bv 64 (BUF + w_out s)) y13 (Z_to_bv 64 start2) (Z_to_bv 64 X1) x20 x22 x26
(Z_to_bv 64 (w_symbol s)) x28 (Z_to_bv 64 (w_bitCount s)) x30 x31)).
{ intros y10 y13. clear RDB1 CK1 SR1 b1.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep.
destruct (A0_ inv_shadow _ MUA) as [UB2 _].
lazymatch type of UB2 with unpoisoned ?mm _ _ =>
destruct (A0_ chk_out mm (BUF + w_out s + 1) UB2 ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2) end.
zstep. zstep. zstep. rewrite sxb_sval.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JOIN2 : forall (z10 z14 : word), evtF bsegs RNG POST
(BST 0x817dc mm x8 z10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s + 1)) z14 (Z_to_bv 64 X1) x20 x22 x26
(Z_to_bv 64 (w_symbol s)) x28 (Z_to_bv 64 (w_bitCount s)) x30 x31)) end.
{ intros z10 z14. clear RDB2 CK2 SR2 b2.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. change (2^8) with 256. lia. }
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
zstep. zstep. sw32 (w_bitCount s + -14).
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep.
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
setreg 11%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
replace (w_bitCount s + -14) with (w_bitCount s + 2 - 16) by lia.
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA
| change (2^32) with 4294967296 in RB3; change (2^64) with 18446744073709551616; lia
| cbn [w_bitStream]; apply Z.mod_small; exact RB3]. }
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
zstep. if_false. zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply FLUSH.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_zero_mid : forall f s start1 s2' start2 sf m1 X (x8 x10 x13 x20 x22 x26 x28 x30 x31 : word),
0 <= start1 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
0 <= w_bitStream s < 2^32 -> 0 <= w_bitCount s ->
zlen (w_buf s) = bsz -> 0 <= w_out s <= bsz -> MINV m1 (w_buf s) ->
run3 (S f) s start1 = Ok (s2', start2) ->
bind (shl32 (u32 (w_symbol s2' - start2)) (w_bitCount s2')) (fun v =>
wflush_if bsz safe (mkW (w_buf s2') (w_out s2') (u32 (w_bitStream s2' + v)) (w_bitCount s2' + 2)
(w_symbol s2') (w_remaining s2') (w_threshold s2') (w_nbBits s2') (w_previousIs0 s2'))) = Ok sf ->
(forall m2 X' (y10 y13 y14 y30 : word), MINV m2 (w_buf sf) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sf ->
evtF bsegs RNG POST (BST 0x81890 m2 x8 y10 (Z_to_bv 64 (BUF + w_out sf)) y13 y14 (Z_to_bv 64 X') x20 x22 x26 (Z_to_bv 64 (w_symbol s)) x28
(Z_to_bv 64 (w_bitCount sf)) y30 x31)) ->
evtF bsegs RNG POST (BST 0x81764 m1 x8 x10 (Z_to_bv 64 (BUF + w_out s)) x13 (Z_to_bv 64 start1) (Z_to_bv 64 X) x20 x22 x26 (Z_to_bv 64 (w_symbol s)) x28
(Z_to_bv 64 (w_bitCount s)) x30 x31).
Proof using WRC.
intros f s start1 s2' start2 sf m1 X x8 x10 x13 x20 x22 x26 x28 x30 x31 S1 SY RX EX RBt BC LB RO MV R3 TLH K.
pose proof (run3_facts _ _ _ _ _ R3 RBt BC) as ((D1 & D2 & D3 & D4) & SY2 & B2 & O2 & RB2 & BC2 & ST2 & SR2).
Local Ltac2 Set LiaHints.tbl := fun () => "00A0?17328780436.11526604383400.11542134471252.1144640157628.112 46515793883.11246515793883.11549597639079.12050104863000.13251020183212.11458270426683.11458364785427.1156256592031.112 6256592031.115 6321005544.120 63431091439.1156562756080.120 8592517893.120 00000`01501Z01b01f01j02X02m03103F03I03M03Q04>04A04m05\S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S12SY2RX2LB3ST23SR2S5BUFNZ4NCNZ2S12SY2RXS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2ROS2S13SR2S2S1S2S1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB3SY23SR23RX'S5BUFNZ4NCNZ2S12SY2RXS2S1S5BUFNZ4NCNZ2S12SY2RXS1BS2SYS2SYS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2SY2RX2LB3SY23RX'S1BS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2RO2O23RX'S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S12RX2LB3SR21B3RX'".
specialize (SR2 ltac:(lia)).
zstep. sw32 (start1 + 3). zstep.
if_cases B; zify_cond B.
- rewrite run3_S in R3. replace (start1 + 3 <=? w_symbol s) with false in R3 by (symmetry; apply Z.leb_gt; lia).
injection R3 as <- <-.
eapply (wr_zero_tail s start1 sf); [lia | lia | lia | exact RX | exact EX | exact LB | exact RO | exact MV | exact TLH | ].
intros. apply K; assumption.
- eapply (A_ wr_run3 f s start1 s2' start2); [lia | lia | lia | exact RX | exact EX | exact R3 | ].
intros X' y10 y13 RX' EX'.
rewrite <- SY2, <- O2.
eapply (wr_zero_tail s2' start2 sf);
[ lia | lia | lia | exact RX' | exact EX' | rewrite B2; exact LB | lia | rewrite B2; exact MV | exact TLH | ].
intros. rewrite SY2. apply K; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_zero : forall s fl m1 X (x8 x10 x13 x14 x20 x22 x26 x27 x30 x31 : word),
winv asz bsz s -> w_symbol s < asz -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s -> MINV m1 (w_buf s) ->
wzero_block nc asz bsz safe s = Ok fl ->
(forall sa m2 X' (y10 y13 y14 y20 y22 y28 y30 : word), fl = Cont sa -> MINV m2 (w_buf sa) -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream sa ->
evtF bsegs RNG POST (BST 0x81890 m2 x8 y10 (Z_to_bv 64 (BUF + w_out sa)) y13 y14 (Z_to_bv 64 X') y20 y22 x26 (Z_to_bv 64 (w_symbol sa)) y28
(Z_to_bv 64 (w_bitCount sa)) y30 x31)) ->
(forall sa (y10 y13 y14 y20 y22 y27 y28 y30 : word), fl = Brk sa ->
evtF bsegs RNG POST (BST 0x81a2c m1 x8 y10 (Z_to_bv 64 (BUF + w_out s)) y13 y14 (Z_to_bv 64 X) y20 y22 x26 y27 y28
(Z_to_bv 64 (w_bitCount s)) y30 x31)) ->
evtF bsegs RNG POST (BST 0x816dc m1 x8 x10 (Z_to_bv 64 (BUF + w_out s)) x13 x14 (Z_to_bv 64 X) x20 x22 x26 x27 (Z_to_bv 64 (w_symbol s))
(Z_to_bv 64 (w_bitCount s)) x30 x31).
Proof using WRC.
intros s fl m1 X x8 x10 x13 x14 x20 x22 x26 x27 x30 x31 WI SYA RX EX MV H KC KB.
pose proof WI as (LB & RO & RBt & BC & SY & RM & NBI & TH). unfold FseNCount.Zlength in LB.
pose proof MV as (BA & NA & [junk8 FA] & SA & MUA & WMA & MIA). unfold AF_fse_write_A.FRAMEC in FA.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
destruct (A0_ inv_shadow _ MUA) as [_ UN1].
pose proof (ablk_lin _ _ BLKN) as LN. pose proof (ablk_lin _ _ BLKB) as LBK. unfold KHIGH, AIMG_HI in *.
unfold wzero_block in H. apply bind_inv in H. destruct H as (sym & SK & H).
Local Ltac2 Set LiaHints.tbl := fun () => "00Z0?1388995953.135 15350540903.16715523942993.16515523942993.16716346546271.12217316818850.18217316818851.13617316818851.17717322560549.16617322610086.12019553650907.1342599566316.138 27816112971.1643122459008.163 32084762758.1493300154455.172 34112764469.16734117280778.13835212070528.13535212070533.1384013478684.119 4013478684.122 42132796117.16242547251744.13942558040102.12042558040485.16246092037644.12952131809393.18059308579027.12159308579027.12259314873579.16359314873579.16759588178612.13960359133995.1676168199686.121 6599369317.162 6599369444.163 67551513464.17268189741935.14968189741935.1727704535130.162 8657468251.179 00000400=00D00K00k01401T02402=02^02e02i03003P03W04Q04X04_04`04a04l05705e05m06506=06j06n07907E08608B08F09809X0:M0;B0<?0=00=e0>E0>LS2NBS4BC242NBS2NB2J2S2NB2J2S3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2J0S4BC242NBS3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2J0S3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2J0S4BC242NBS3MSV5BUFNZ4NCNZ3SYA2RX2SY3NBI2NBS2LO2NBS2NBS2NB2J2S3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2J0S2NB2SRS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX3NBI2NB3SR'3SY13LB13RX1S2SY2NBS2SY2NBFFS3SYA2SY2NBS3SYA2SY2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX3NBI2NB3LB13RO1S3MSV2NBS3MSV2NBS3MSV2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB3NBI2NB3SR'S2NBS3SYA2NB2J0S4NCNZ2NB2G0S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX3NBI2NB3SR'3LB12J1S4BC242NB2G1S2NBS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX3NBI2NB3SR'3LB1S5BUFNZ4NCNZ2RX2LB3NBI2NB2LN3LBKS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2SY3NBI2NB3SR'3LB1S3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2SY3NBI2NB3SR'3LB1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2SY3NBI2NB3SY13LB13ST13SR13RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC3NBI2NB3BC13LB1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC3NBI2NB3BC13LB13RX1S3MSV5BUFNZ4NCNZ2RX2SY3NBI2NB2J0S2LO2NB".
pose proof (skip_zeros_range nc asz _ (w_symbol s) sym ltac:(lia) SK) as SR.
zstep. zstep. if_cases J0; zify_cond J0; [exfalso; lia|].
zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
do 8 zstep.
rewrite zext32_sh31 by lia. rewrite ?(Z.mod_small (w_symbol s) 4294967296) by lia.
eapply (A_ wr_skip _ (w_symbol s) sym); [lia | exact NA | exact UN1 | exact SK | | ].
- intros y10 y13 y14 y20 y22 y30 SR'.
replace (sym =? asz) with false in H by (symmetry; apply Z.eqb_neq; lia).
apply bind_inv in H. destruct H as ([sa start1] & R24 & H).
apply bind_inv in H. destruct H as ([s2' start2] & R3 & H).
apply bind_inv in H. destruct H as (v & SH & H). apply bind_inv in H. destruct H as (sf & FL & H). injection H as <-.
set (s0' := mkW (w_buf s) (w_out s) (w_bitStream s) (w_bitCount s) sym (w_remaining s) (w_threshold s) (w_nbBits s) (w_previousIs0 s)) in *.
pose proof (run24_facts bsz safe _ _ _ _ _ R24 ltac:(exact LB) RBt RO) as ((C1 & C2 & C3 & C4) & SY1 & BC1 & LB1 & RO1 & RB1 & ST1 & SR1).
cbn [s0' w_symbol w_bitCount] in SY1, BC1, SR1. specialize (SR1 ltac:(lia)). unfold FseNCount.Zlength in LB1.
pose proof (run3_facts _ _ _ _ _ R3 RB1 ltac:(lia)) as ((D1 & D2 & D3 & D4) & SY2 & B2 & O2 & RB2 & BC2 & ST2 & SR2).
assert (TLH : bind (shl32 (u32 (w_symbol s2' - start2)) (w_bitCount s2')) (fun v =>
wflush_if bsz safe (mkW (w_buf s2') (w_out s2') (u32 (w_bitStream s2' + v)) (w_bitCount s2' + 2)
(w_symbol s2') (w_remaining s2') (w_threshold s2') (w_nbBits s2') (w_previousIs0 s2'))) = Ok sf).
{ assert (ES : sym = w_symbol s2') by congruence. rewrite ES in SH. rewrite SH. cbn [bind]. exact FL. }
assert (MID : forall m2 X1 (z10 z13 z20 z22 z28 z30 : word), MINV m2 (w_buf sa) -> 0 <= X1 < 2^64 -> X1 mod 2^32 = w_bitStream sa ->
evtF bsegs RNG POST (BST 0x81764 m2 x8 z10 (Z_to_bv 64 (BUF + w_out sa)) z13 (Z_to_bv 64 start1) (Z_to_bv 64 X1) z20 z22 x26
(Z_to_bv 64 (w_symbol sa)) z28 (Z_to_bv 64 (w_bitCount sa)) z30 x31)).
{ intros m2 X1 z10 z13 z20 z22 z28 z30 MV2 RX1 EX1.
eapply (wr_zero_mid _ sa start1 s2' start2 sf); [lia | lia | exact RX1 | exact EX1 | exact RB1 | lia | exact LB1 | exact RO1 | exact MV2 | exact R3 | exact TLH | ].
intros m3 X' w10 w13 w14 w30 MV3 RX3 EX3.
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
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. zstep. rewrite shiftl_mod32 by lia. zstep.
eapply (A_ wr_run24 _ s0' (w_symbol s) sa start1); [lia | cbn [s0' w_symbol]; lia | cbn [s0' w_symbol]; lia
| exact RX | exact EX | exact LB | exact MV | exact R24' | ].
intros m2 X' z10 z13 z30 MV2 RX2 EX2. cbn [s0' w_symbol w_bitCount]. rewrite <- SY1. rewrite <- BC1.
zstep. apply MID; assumption.
+
rewrite run24_S in R24. cbn [s0' w_symbol] in R24.
replace (w_symbol s + 24 <=? sym) with false in R24 by (symmetry; apply Z.leb_gt; lia).
injection R24 as <- <-.
zstep.
apply (MID m1 X); [exact MV | exact RX | exact EX].
-
intros y10 y13 y14 y20 y22 y30 ->.
replace (asz =? asz) with true in H by (symmetry; apply Z.eqb_refl). injection H as <-.
zstep.
eapply KB. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
End WR.
End CANSEC1.
