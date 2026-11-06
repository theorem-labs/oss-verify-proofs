(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWriteModel FseWalkArith.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AF_fse_iface.
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
Ltac lts_lit K := unfold bv_lts in K; rewrite !signed_lit in K by lia; zify_bool K.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
Lemma inv_shadow : forall m1, munch W m m1 -> unpoisoned m1 BUF (BUF + bsz) /\ unpoisoned m1 NC (NC + 2 * zlen nc).
Proof using WRC.
intros m1 MU. pose proof (ablk_lin _ _ BLKB) as LB. pose proof (ablk_lin _ _ BLKN) as LN.
pose proof (ablk_disj_band _ _ BLKB) as DBB. unfold KHIGH, KLS, AIMG_HI in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0020?44095615338.10766163708546.10700000_01RS4NCEV2LO4SEPB3NC83KLO2LB2H42H52H93H143H192LN1HS3BSZ2LO4BUF83KLO3DBB1H2H42H54SEPN5SEPBN3NC82LN3H19".
split; (eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition FRAMEC : list cell := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition MINV (m1 : amem) (buf : list Z) : Prop :=
u8arr asegs m1 BUF (map (Z_to_bv 8) buf) /\ bytes_at asegs m1 NC (u16s (map (Z_to_bv 64) nc))
/\ rw_cells asegs m1 (SP + -96) FRAMEC /\ stk asegs m1 lo (SP + -96)
/\ munch W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1.
Section LOOP.
Variable safe : bool.
Notation AST pc mm x5 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 :=
(MS (mkR ra (Z_to_bv 64 (SP + -96)) gp tp x5 (Z_to_bv 64 2147450880) (Z_to_bv 64 asz) (Z_to_bv 64 3) (Z_to_bv 64 65535)
(Z_to_bv 64 BUF) (Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 NC) x13 x14 (Z_to_bv 64 (Z.b2z safe)) x16 (Z_to_bv 64 (-1))
x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 (Z_to_bv 64 1) (Z_to_bv 64 17) (Z_to_bv 64 15) (Z_to_bv 64 asz))
F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
Lemma wr_shrink : forall f rem thr nb thr' nb' m1 (x5 x13 x14 x16 x18 x19 x20 x21 x22 x26 : word),
rem < thr -> 1 <= rem -> thr <= 8192 ->
shrink (S f) rem thr nb = Ok (thr', nb') ->
(evtF asegs RNG POST (AST 0x81934 m1 x5 x13 x14 x16 x18 x19 x20 x21 x22 (Z_to_bv 64 rem) (Z_to_bv 64 nb') (Z_to_bv 64 thr') x26)) ->
evtF asegs RNG POST (AST 0x81928 m1 x5 x13 x14 x16 x18 x19 x20 x21 x22 (Z_to_bv 64 rem) (Z_to_bv 64 nb) (Z_to_bv 64 thr) x26).
Proof using WRC.
induction f as [|f IH]; intros rem thr nb thr' nb' m1 x5 x13 x14 x16 x18 x19 x20 x21 x22 x26 LT R1 T8 SH K.
- rewrite shrink_S in SH. Local Ltac2 Set LiaHints.tbl := fun () => "00>0?10842114114.95 19726814754.98 21780299845.12529011846530.98 34727867976.98 364264583.126  38047386523.98 3971545388.98  40308748580.97 4410630228.95  4410630228.97  61588508710.11365664998174.98 6758062595.97  00000100F00U00j00m01601:01=01R01V01Z02?02@02ASS5BUFNZ4NCNZ2LT2R12T8S2LT2R12T81H2H0S5BUFNZ4NCNZ2LT2R12T8S1BS2T81H2H0S2R1S1BS5BUFNZ4NCNZ2LT2R12T8S2LTS2LTS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LT2R12T8SS".
replace (rem <? thr) with true in SH by (symmetry; apply Z.ltb_lt; lia). cbn in SH. discriminate.
- rewrite shrink_S in SH. replace (rem <? thr) with true in SH by (symmetry; apply Z.ltb_lt; lia).
zstep. rewrite (FseWalkKit.swrap32_small thr) by lia. rewrite (Z.shiftr_div_pow2 thr 1) by lia. change (2^1) with 2.
rewrite FseWalkKit.swrap32_small by (Z.div_mod_to_equations; lia).
zstep. zstep.
if_cases B; lts_lit B.
+ eapply (IH rem (thr / 2) (nb - 1) thr' nb'); [lia| lia| Z.div_mod_to_equations; lia| | exact K].
replace (nb + -1) with (nb - 1) by lia. exact SH.
+ rewrite shrink_S in SH. replace (rem <? thr / 2) with false in SH by (symmetry; apply Z.ltb_ge; lia).
injection SH as <- <-. replace (nb - 1) with (nb + -1) in K by lia. exact K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac wrap16 := let v := reg_val 16%Z in
lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
Lemma wr_run3 : forall f s start s' start' m1 X (x13 x14 x18 x20 x21 x22 x23 x25 x26 : word),
0 <= start -> start + 3 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
run3 (S f) s start = Ok (s', start') ->
(forall X' (y14 : word), 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evtF asegs RNG POST (AST 0x8180c m1 (Z_to_bv 64 (w_bitCount s')) x13 y14 (Z_to_bv 64 X') x18 (Z_to_bv 64 (w_symbol s)) x20 x21 x22 x23
(Z_to_bv 64 start') x25 x26)) ->
evtF asegs RNG POST (AST 0x817f4 m1 (Z_to_bv 64 (w_bitCount s)) x13 x14 (Z_to_bv 64 X) x18 (Z_to_bv 64 (w_symbol s)) x20 x21 x22 x23
(Z_to_bv 64 start) x25 x26).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "00C0?107508260.99   11447729318.16915350524130.99 17314721709.11017316818850.11517328780436.10120142628527.10138954800347.10138954800347.98 40053791375.10142130673131.99 48953163024.99 55516386911.96 55516386911.98 56448729808.11357295617883.1016256592031.101 66149329423.1347568103724.101 00000400b00f00j00n01Y01]01^01_01b02D02_02c02g03B03E03I03J03eS2BCS4SEPB4SEPN5SEPBN2BC1H2H02H42H52H93H143H193H24S2BCS2BCS2BCS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S02S32SY2RX2BCS2S0SSS1BS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BCS5BUFNZ4NCNZ2S02S32SY2RX2BCS2S3S2S3S5BUFNZ4NCNZ2S02S32SY2RX2BCS1BS2SYFS5BUFNZ4NCNZ2S02S32SY2RX2BC".
induction f as [|f IH]; intros s start s' start' m1 X x13 x14 x18 x20 x21 x22 x23 x25 x26 S0 S3 SY RX EX R3 K;
rewrite run3_S in R3; replace (start + 3 <=? w_symbol s) with true in R3 by (symmetry; apply Z.leb_le; lia);
apply bind_inv in R3; destruct R3 as (v & SH & R3); apply shl32_inv in SH; destruct SH as [BC ->].
- cbn in R3. discriminate.
- zstep. rewrite shiftl_mod32 by lia.
zstep. zstep. sw32 (start + 6). zstep. zstep. sw32 (w_bitCount s + 2). zstep.
assert (EX' : (bv_swrap 32 (3 * 2 ^ w_bitCount s) + X) mod 2^64 mod 2^32 = u32 (w_bitStream s + u32 (3 * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
rewrite swrap32_eq. Z.div_mod_to_equations. lia. }
if_cases B; zify_cond B.
+ wrap16.
lazymatch type of R3 with run3 _ ?s1 _ = _ =>
eapply (IH s1 (start + 3) s' start'); [lia | cbn [w_symbol]; lia | cbn [w_symbol]; lia | apply Z.mod_pos_bound; lia
| cbn [w_bitStream]; exact EX' | exact R3 | ] end.
cbn [w_symbol w_bitCount]. exact K.
+ rewrite run3_S in R3. cbn [w_symbol] in R3.
replace (start + 3 + 3 <=? w_symbol s) with false in R3 by (symmetry; apply Z.leb_gt; lia).
injection R3 as <- <-. wrap16.
apply K; [apply Z.mod_pos_bound; lia | cbn [w_bitStream]; exact EX'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_skip : forall f sym sym' m1 (x5 x13 x16 x18 x20 x21 x22 x25 x26 : word),
0 <= sym < asz -> bytes_at asegs m1 NC (u16s (map (Z_to_bv 64) nc)) -> unpoisoned m1 NC (NC + 2 * zlen nc) ->
skip_zeros nc asz (S f) sym = Ok sym' ->
(forall (y14 y23 y24 y25 y26 : word), sym <= sym' < asz ->
evtF asegs RNG POST (AST 0x817dc m1 x5 x13 y14 x16 x18 (Z_to_bv 64 sym') x20 x21 x22 y23 y24 y25 y26)) ->
(forall (y14 y23 y24 y25 y26 : word), sym' = asz ->
evtF asegs RNG POST (AST 0x817c8 m1 x5 x13 y14 x16 x18 (Z_to_bv 64 sym') x20 x21 x22 y23 y24 y25 y26)) ->
evtF asegs RNG POST (AST 0x8179c m1 x5 x13 (Z_to_bv 64 (NC + 2 * sym)) x16 x18 (Z_to_bv 64 sym) x20 x21 x22
(Z_to_bv 64 (NC + 2 * sym)) (Z_to_bv 64 (asz - sym)) x25 x26).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "00e0?11275272025.10911281548129.10711281548129.1081287345813.115 28707550832.11928707550832.12229646625862.12629646625862.12829782367974.10829782367974.11038697646388.92 38697646388.94 39159981841.10239159981841.10540244715328.10040244715328.98 40829096625.13240829096625.13541730628386.10141730628386.10342130557540.10748787532352.10951124606241.10952067329428.10853635067609.10953635067609.11056862664027.13256862664027.13559310676312.13259310676312.13559314873579.10459314873579.10659314873579.10859437227811.11559437227811.11859437227815.11859437227815.12059583424896.10359583424896.10559583424896.10760231311587.10761330623914.10964405586223.10764405586223.1096607192559.116 66233876957.10466233876957.10668187539663.10768187539663.1097351371905.100 7351371905.98  9544766530.100 9544766530.98  00000:00D00N00T01601X02=02b02f02j02n03203f04Z05<05^05e05l06006406Y06c06g07@07G07N07Z07f08E08d09]0:V0;L0;h0<D0<`0=<0=@0=D0=H0>10>50>e0?U0@=0@D0@K0@L0@M0@o0AQ0AU0AYS2SY2NB2B2S2SY2NB2B2S2SY2NB2B2S2NB1HS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS4NCEV4SEPB4SEPN5SEPBN2LR2NB1H2H03H14S4NCEV4SEPB4SEPN5SEPBN2LR2NB1H2H03H14S2NBS2NBS2SYS2SYS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2NB2LN2CKS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2NB2LN2CKS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS2NB2SRS2NB2SRS2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NB2E0S2SY2NB2B2S2NBS3MSV5BUFNZ4NCNZ2SY2LR2NBS2NB2B2S2NB2B2S2NB2CK1G2H0S2NB2CK1G2H0S4SEPB4SEPN5SEPBN2LR2NB2CK1G2G'S4SEPB4SEPN5SEPBN2LR2NB2CK1G2G'S5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2CR2NB2LN2N01BS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2CR2NB2LN2N01BS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2NB2LN2E01BS5BUFNZ4NCNZ2LO3KLO2LR2NB2LNS5BUFNZ4NCNZ2LO3KLO2LR2NB2LNS5BUFNZ4NCNZ2LO3KLO2LR2NB2LNS5BUFNZ4NCNZ2LO3KLO2LR2NB2LNS2NBS2NBS2NBS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2SY2LR2NBS2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3NC83KLO2LR2NB2LNS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3NC83KLO2LR2NB2LNS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2SY2LR2NB2LNS2SY2NBS2SY2NBFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS2NBS2NB".
induction f as [|f IH]; intros sym sym' m1 x5 x13 x16 x18 x20 x21 x22 x25 x26 SY NC1 UN1 SK KA KB;
rewrite skip_zeros_S in SK; replace (sym <? asz) with true in SK by (symmetry; apply Z.ltb_lt; lia);
apply bind_inv in SK; destruct SK as (c & LD & SK); apply load_inv in LD; destruct LD as [LR ->]; unfold FseNCount.Zlength in LR;
pose proof (Forall_Znth _ _ sym NCR LR) as CR; cbv beta in CR;
pose proof (bytes_at_bound _ _ _ _ NC1) as NB; rewrite u16s_length, length_map in NB;
pose proof (u16_znth asegs m1 NC nc sym (Z_to_bv 64 (NC + 2 * sym)) NC1 LR ltac:(reflexivity)) as RD;
pose proof (ablk_lin _ _ BLKN) as LN; unfold KHIGH, AIMG_HI in *;
destruct (unpoisoned_check_rd asegs m1 NC (NC + 2 * zlen nc) (NC + 2 * sym) 2 UN1 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK);
unfold shad, ASHOFF in RDB; replace (2147450880 + Z.shiftr (NC + 2 * sym) 3) with (Z.shiftr (NC + 2 * sym) 3 + 2147450880) in RDB by lia;
pose proof (sval_range b) as SR;
(zstep; zstep; zstep; rewrite sxb_sval).
-
destruct (Z.eqb_spec (Znth sym nc) 0) as [E0|N0]; [cbn in SK; discriminate|]. injection SK as <-.
assert (LOADED : forall (y25 y26 : word), evtF asegs RNG POST
(AST 0x817ac m1 x5 x13 (Z_to_bv 64 (NC + 2 * sym)) x16 x18 (Z_to_bv 64 sym) x20 x21 x22
(Z_to_bv 64 (NC + 2 * sym)) (Z_to_bv 64 (asz - sym)) y25 y26)).
{ intros y25 y26. zstep. rewrite zx16_short by exact CR. zstep.
if_cases B; zify_cond B; [| exfalso; lia].
apply KA. lia. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply LOADED.
+ apply LOADED.
- assert (LOADED : forall (y25 y26 : word), evtF asegs RNG POST
(AST 0x817ac m1 x5 x13 (Z_to_bv 64 (NC + 2 * sym)) x16 x18 (Z_to_bv 64 sym) x20 x21 x22
(Z_to_bv 64 (NC + 2 * sym)) (Z_to_bv 64 (asz - sym)) y25 y26)).
{ intros y25 y26. zstep. rewrite zx16_short by exact CR. zstep.
destruct (Z.eqb_spec (Znth sym nc) 0) as [E0|N0].
+ if_cases B; zify_cond B; [exfalso; lia|].
zstep. sw32 (sym + 1). zstep. zstep. zstep. zstep.
if_cases B2; zify_cond B2.
* replace (asz - sym + -1) with (asz - (sym + 1)) by lia. replace (NC + 2 * sym + 2) with (NC + 2 * (sym + 1)) by lia.
eapply (IH (sym + 1) sym'); [lia | exact NC1 | exact UN1 | exact SK | | exact KB].
intros. apply KA. lia.
* assert (sym + 1 = asz) by lia.
destruct f as [|f]; [cbn in SK|rewrite skip_zeros_S in SK];
replace (sym + 1 <? asz) with false in SK by (symmetry; apply Z.ltb_ge; lia); injection SK as <-.
-- apply KB. lia.
-- apply KB. lia.
+ injection SK as <-. if_cases B; zify_cond B; [| exfalso; lia].
apply KA. lia. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply LOADED.
+ apply LOADED.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac minv_close BA NA FA SA MUA WMA MIA :=
split; [exact BA|]; split; [exact NA|]; split; [exact FA|]; split; [exact SA|]; split; [exact MUA|]; split; [exact WMA| exact MIA].
Lemma chk_out : forall m1 a, unpoisoned m1 BUF (BUF + bsz) -> BUF <= a -> a + 1 <= BUF + bsz ->
exists b, ov_read_bytes asegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
/\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)) /\ -128 <= sval b <= 127.
Proof using WRC.
intros m1 a UB1 A0 A1.
Local Ltac2 Set LiaHints.tbl := fun () => "0060?15389206805.10743608222505.79 53039786928.79 53960035342.79 57212711813.82 8454139159.82  00000400500900=00A00BS2H0SS2A0S2A1S2CKS".
destruct (unpoisoned_check_rd asegs m1 BUF (BUF + bsz) a 1 UB1 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK).
exists b. unfold shad, ASHOFF in RDB. replace (2147450880 + Z.shiftr a 3) with (Z.shiftr a 3 + 2147450880) in RDB by lia.
split; [exact RDB|]. split; [| apply sval_range].
destruct CK as [CK|CK]; [left; exact CK| right; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_run24s : forall f s start s' start' m1 X (x18 x20 x21 x24 x25 x26 : word),
safe = true -> 0 <= start -> start + 24 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> MINV m1 (w_buf s) ->
run24 bsz safe (S f) s start = Ok (s', start') ->
(forall m2 X' (y14 y22 y25 y26 : word), MINV m2 (w_buf s') -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evtF asegs RNG POST (AST 0x817ec m2 (Z_to_bv 64 (w_bitCount s')) (Z_to_bv 64 (BUF + w_out s')) y14 (Z_to_bv 64 X') x18
(Z_to_bv 64 (w_symbol s)) x20 x21 y22 (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s)))
(Z_to_bv 64 start') y25 y26)) ->
evtF asegs RNG POST (AST 0x81870 m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 X) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 (Z_to_bv 64 start) (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s)))
x24 x25 x26).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "0100?10088275704.12713070568592.12613071252779.12514362626257.18715641283330.11815641300924.11917328780436.12819489965866.12919618399905.13719618399909.14621276737785.12722448268900.1192707945969.129 27517043963.11929782367974.13129782367974.13431183134347.1133214378781.119 3214378781.126 32313870464.1133405217491.126 35206187911.12736067281813.12936441195084.13036443292231.13337424340810.12538954701265.11639572309076.16940036921387.12541477180325.12942134106704.12545596907399.13545596907404.13246833963628.12847788875075.1214861253072.115 48727422282.13649170713844.12649423367528.1195152176687.102 5152176687.104 51818759664.1265222230152.121 53728626131.12654475752564.12056448729814.14156736913459.13459310676567.16959310676568.1876256755093.129 64405586210.13364407683369.13064794109999.11864799663456.11966149329282.18168015643441.13368017740602.13068187539650.13368189636809.1308316058051.126 913132285.126  9448783520.169 9448783535.187 9581028844.126 00000400>00H00P00Z00d01a02c03M04;04C04j05005b05f05j06X07J08@08G08K09A09H09I09J09N09R09Z0:A0:G0;=0;f0<O0=30=e0>S0?I0@?0@b0@g0@l0AS0AZ0A^0BT0C80Cj0DS0E>0EE0FK0GI0HF0I80I90I:0I;0I<0I=0J30J70JD0JR0K=S2NBS2O02O12NBS2O02O12NBS2NB3SR2S2O02O12NBS2O02O12NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S03S242SY2RX2LB2O02O12NB3RX13RB1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2O02O12NB3LBK3RX13CK23RB1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX13RB1S2NB3RB3S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX1S2NB1BS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S2O02NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S2S02NBFFS2NBS2NBS2NB3SR1S5BUFNZ4NCNZ2S03S242SY2RX2BC2NB3RX13RB1S2NB1BS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2S03S242SY2RX2NB3RX13RB1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX1S3S24S3S24S5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX13RB1S2O02NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3EX13RX1S5BUFNZ4NCNZ2S03S242SY2RX2NB3RX13RB1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S4SEPB4SEPN5SEPBN2LB2BC2O02O12NB3CK11G2G'S4SEPB4SEPN5SEPBN2LB2BC2O02O12NB3CK22G23G2'S2SY2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02O12NB3LBK3EX13RX1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2BC2O02O12NB3LBK3CK1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1FFFFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S2NBS2NB3CK11G2H0S2NB3CK22G22H0S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX13RB1".
induction f as [|f IH]; intros s start s' start' m1 X x18 x20 x21 x24 x25 x26 SAFE S0 S24 SY RX EX LB (BA & NA & FA & SA & MUA & WMA & MIA) R24 K;
rewrite run24_S in R24; replace (start + 24 <=? w_symbol s) with true in R24 by (symmetry; apply Z.leb_le; lia);
apply bind_inv in R24; destruct R24 as (v & SH & R24); apply shl32_inv in SH; destruct SH as [BC ->];
apply bind_inv in R24; destruct R24 as (sfl & FL & R24); apply wflush_inv in FL; cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL;
destruct FL as (_ & O0 & O1 & ->); unfold FseNCount.Zlength in O1.
- cbn in R24. discriminate.
- pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold FRAMEC in FA.
pose proof (ablk_lin _ _ BLKB) as LBK. unfold KHIGH, AIMG_HI in *.
destruct (inv_shadow _ MUA) as [UB1 _].
destruct (chk_out m1 (BUF + w_out s) UB1 ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN1 : forall (y24 y25 : word), evtF asegs RNG POST
(AST 0x81880 m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 X) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 (Z_to_bv 64 start) (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) y24 y25 x26)).
{ intros y24 y25. clear RDB1 CK1 SR1 b1.
zstep.
assert (EX1 : ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64) mod 2^32 = u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296. rewrite swrap32_eq. lia. }
assert (RX1 : 0 <= (X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
let v := reg_val 24%Z in lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
revert EX1 RX1. generalize ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64). intros X1 EX1 RX1.
set (bs1 := u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))) in *.
zstep.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
destruct (inv_shadow _ MUA) as [UB2 _].
lazymatch type of UB2 with unpoisoned ?mm _ _ =>
destruct (chk_out mm (BUF + w_out s + 1) UB2 ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2) end.
zstep. zstep. zstep. rewrite sxb_sval.
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
assert (RB2 : 0 <= bs1 / 2^16 < 2^64).
{ change (2^32) with 4294967296 in RB3. change (2^64) with 18446744073709551616. lia. }
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JOIN2 : forall (z25 z26 : word), evtF asegs RNG POST
(AST 0x8189c mm (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s + 1)) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 (Z_to_bv 64 start) (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) (Z_to_bv 64 X1) z25 z26)) end.
{ intros z25 z26. clear RDB2 CK2 SR2 b2.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep. zstep. sw32 (start + 48).
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. change (2^8) with 256. lia. }
zstep. zstep. zstep.
setreg 13%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
assert (LB2 : zlen (Zupd (w_out s + 1) (to_byte (bs1 / 2 ^ 8)) (Zupd (w_out s) (to_byte bs1) (w_buf s))) = bsz)
by (rewrite !Zupd_length; exact LB).
zstep.
if_cases B; zify_cond B.
+ lazymatch type of R24 with run24 _ _ _ ?sn _ = _ =>
eapply (IH sn (start + 24) s' start'); [exact SAFE | lia | cbn [w_symbol]; lia | cbn [w_symbol]; lia | exact RB2
| cbn [w_bitStream]; apply Z.mod_small; exact RB3 | cbn [w_buf]; exact LB2
| cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact R24 | ] end.
cbn [w_symbol w_bitCount]. exact K.
+ rewrite run24_S in R24. cbn [w_symbol] in R24.
replace (start + 24 + 24 <=? w_symbol s) with false in R24 by (symmetry; apply Z.leb_gt; lia).
injection R24 as <- <-.
zstep.
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact RB2 | cbn [w_bitStream]; apply Z.mod_small; exact RB3]. }
zstep. if_cases G2; zify_cond G2.
+ zstep. zstep. if_cases G2'; zify_lts G2'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN2.
+ apply JOIN2. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN1.
+ apply JOIN1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_run24c : forall f s start s' start' m1 X (x18 x20 x21 x24 x25 x26 : word),
safe = false -> 0 <= start -> start + 24 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> MINV m1 (w_buf s) ->
run24 bsz safe (S f) s start = Ok (s', start') ->
(forall m2 X' (y14 y22 y25 y26 : word), MINV m2 (w_buf s') -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evtF asegs RNG POST (AST 0x817ec m2 (Z_to_bv 64 (w_bitCount s')) (Z_to_bv 64 (BUF + w_out s')) y14 (Z_to_bv 64 X') x18
(Z_to_bv 64 (w_symbol s)) x20 x21 y22 (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s)))
(Z_to_bv 64 start') y25 y26)) ->
evtF asegs RNG POST (AST 0x819ec m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 X) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 (Z_to_bv 64 start) (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s)))
x24 x25 x26).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "0130?10088275704.12913070568592.12813071252779.12714362626257.18915641283330.12015641300924.12117328780436.13019489965866.13119618399905.13919618399909.14821276737785.12922448268900.1212707945969.131 27517043963.12129782367974.13329782367974.13631183134347.1143214378781.121 3214378781.128 32313870464.1143405217491.128 35206187911.12936067281813.13136441195084.13236443292231.13537424340810.12738954701265.11839572309076.17140036921387.12741477180325.13142134106704.12745589988655.11845596907401.13545596907404.13446833963628.13047788875075.1234861253072.117 48727422282.13849170713844.128492328663.118  49423367528.1215152176687.102 5152176687.104 51818759664.1285222230152.123 53728626131.12854475752564.12256448729814.14356736913459.13659310676567.17159310676568.18959314873579.1196256755093.131 64405586210.13564407683369.13264794109999.12064799663456.12166149329282.18368015643441.13568017740602.13268187539650.13568189636809.1328316058051.128 913132285.128  9448783520.171 9448783535.189 9581028844.128 00000400>00H00P00Z00d01^02]03D03o04704^04d05S05W05[05b05l06606=06A07407;07<07=07A07E07M08408:08m09V0:<0:b0;F0;M0<80<B0=80=a0>A0>F0>K0>o0?60?:0?m0@Q0@[0AA0Ai0B30B:0C@0D>0E;0Ej0Ek0El0Em0En0Eo0Fb0Ff0G30GA0GlS2NBS2O02O12NBS2O02O12NBS2NB3SR2S2O02O12NBS2O02O12NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S03S242SY2RX2O02NB2BO3RX13RB1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2O02NB3LBK2BO3RX13CK23RB1S5BUFNZ4NCNZ2LO3KLO2RX2O02NB3LBK2BO3RX1S5BUFNZ4NCNZ2LO3KLO2RX2O02NB3LBK2BO3RX13RB1S2NB3RB3S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX1S2NB1BS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC2O02NB2BO3RX1S2NBS2NBS2OE2NBS2OE2O02NBS2OE2O02NBS2O02NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC2O02NB2BO3RX13RB1S2S02NBFFS2NBS2NBS2NB3SR1S5BUFNZ4NCNZ2S03S242SY2RX2BC2NB3RX13RB1S2NB1BS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC2O02NB2BO3RX13RB1S5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK2BOS5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK2BOS5BUFNZ4NCNZ2S03S242SY2RX2NB3RX13RB1S2OE2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC2O02NB2BOS2OE2O02NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02NB2BO3RX13RB1S5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2RX2BC2NB3LBK2BO3RX1S3S24S3S24S5BUFNZ4NCNZ2RX2BC2NB3LBK2BO3RX13RB1S2O02NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC2O02NB2BO3EX13RX1S5BUFNZ4NCNZ2S03S242SY2RX2NB3RX13RB1S2OE2O02NBS4SEPB4SEPN5SEPBN2BC2O02NB3CK12BO1G2G'S4SEPB4SEPN5SEPBN2BC2O02NB2BO3CK22G23G2'S2OE2NB2BOS2SY2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02NB3LBK2BO3EX13RX1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02NB3LBK2BOS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2BC2O02NB3LBK3CK12BOS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC2O02NB2BO3RX1FFFFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BC2O02NB2BO3RX13RB1S2NBS2NB3CK11G2H0S2NB3CK22G22H0S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX13RB1".
induction f as [|f IH]; intros s start s' start' m1 X x18 x20 x21 x24 x25 x26 SAFE S0 S24 SY RX EX LB (BA & NA & FA & SA & MUA & WMA & MIA) R24 K;
rewrite run24_S in R24; replace (start + 24 <=? w_symbol s) with true in R24 by (symmetry; apply Z.leb_le; lia);
apply bind_inv in R24; destruct R24 as (v & SH & R24); apply shl32_inv in SH; destruct SH as [BC ->];
apply bind_inv in R24; destruct R24 as (sfl & FL & R24); apply wflush_inv in FL; cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL;
destruct FL as (OE & O0 & O1 & ->); unfold FseNCount.Zlength in O1; (destruct OE as [OE|OE]; [congruence|]).
- cbn in R24. discriminate.
- pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold FRAMEC in FA.
pose proof (ablk_lin _ _ BLKB) as LBK. unfold KHIGH, AIMG_HI in *.
destruct (inv_shadow _ MUA) as [UB1 _].
destruct (chk_out m1 (BUF + w_out s) UB1 ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
zstep. if_cases BO; zify_cond BO; [exfalso; lia|].
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN1 : forall (y24 y25 : word), evtF asegs RNG POST
(AST 0x81a00 m1 (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 X) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 (Z_to_bv 64 start) (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) y24 y25 x26)).
{ intros y24 y25. clear RDB1 CK1 SR1 b1.
zstep.
assert (EX1 : ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64) mod 2^32 = u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296. rewrite swrap32_eq. lia. }
assert (RX1 : 0 <= (X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
let v := reg_val 24%Z in lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
revert EX1 RX1. generalize ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64). intros X1 EX1 RX1.
set (bs1 := u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))) in *.
zstep.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
destruct (inv_shadow _ MUA) as [UB2 _].
lazymatch type of UB2 with unpoisoned ?mm _ _ =>
destruct (chk_out mm (BUF + w_out s + 1) UB2 ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2) end.
zstep. zstep. zstep. rewrite sxb_sval.
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
assert (RB2 : 0 <= bs1 / 2^16 < 2^64).
{ change (2^32) with 4294967296 in RB3. change (2^64) with 18446744073709551616. lia. }
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JOIN2 : forall (z25 z26 : word), evtF asegs RNG POST
(AST 0x81a1c mm (Z_to_bv 64 (w_bitCount s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s + 1)) x18
(Z_to_bv 64 (w_symbol s)) x20 x21 (Z_to_bv 64 start) (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) (Z_to_bv 64 X1) z25 z26)) end.
{ intros z25 z26. clear RDB2 CK2 SR2 b2.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep. zstep. sw32 (start + 48).
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. change (2^8) with 256. lia. }
zstep. zstep. zstep.
setreg 13%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
assert (LB2 : zlen (Zupd (w_out s + 1) (to_byte (bs1 / 2 ^ 8)) (Zupd (w_out s) (to_byte bs1) (w_buf s))) = bsz)
by (rewrite !Zupd_length; exact LB).
zstep.
if_cases B; zify_cond B.
+ lazymatch type of R24 with run24 _ _ _ ?sn _ = _ =>
eapply (IH sn (start + 24) s' start'); [exact SAFE | lia | cbn [w_symbol]; lia | cbn [w_symbol]; lia | exact RB2
| cbn [w_bitStream]; apply Z.mod_small; exact RB3 | cbn [w_buf]; exact LB2
| cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact R24 | ] end.
cbn [w_symbol w_bitCount]. exact K.
+ rewrite run24_S in R24. cbn [w_symbol] in R24.
replace (start + 24 + 24 <=? w_symbol s) with false in R24 by (symmetry; apply Z.leb_gt; lia).
injection R24 as <- <-.
zstep.
apply K; [cbn [w_buf]; minv_close BA NA FA SA MUA WMA MIA | exact RB2 | cbn [w_bitStream]; apply Z.mod_small; exact RB3]. }
zstep. if_cases G2; zify_cond G2.
+ zstep. zstep. if_cases G2'; zify_lts G2'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN2.
+ apply JOIN2. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN1.
+ apply JOIN1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
End WR.
End CANSEC1.
