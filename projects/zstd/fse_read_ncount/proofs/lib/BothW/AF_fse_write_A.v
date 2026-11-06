(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWriteModel FseWalkArith.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AF_fse_iface.
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
Lemma inv_shadow : forall m1, munch W m m1 -> unpoisoned m1 BUF (BUF + bsz) /\ unpoisoned m1 NC (NC + 2 * zlen nc).
Proof using WRC.
intros m1 MU. pose proof (ablk_lin _ _ BLKB) as LB. pose proof (ablk_lin _ _ BLKN) as LN.
pose proof (ablk_disj_band _ _ BLKB) as DBB. unfold KHIGH, KLS, AIMG_HI in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0020?15865719914.10766163708546.10700000_01RS4NCEV2LO4SEPB3NC83KLO2LB2H42H52H93H143H192LN1HS3BSZ2LO4BUF83KLO3DBB1H2H42H54SEPN5SEPBN3NC82LN3H19".
split; (eapply unpoisoned_munch; [eassumption| exact MU|]); rewrite !shad_div; unfold ASHOFF; cbn [disjoint_from];
(split; [Z.div_mod_to_equations; lia|]; split; [Z.div_mod_to_equations; lia| exact I]).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition FRAMEC (junk8 : list byte) : list cell :=
[CB 8 junk8; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 65535); C8 (Z_to_bv 64 asz); C8 (Z_to_bv 64 1);
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition MINV (m1 : amem) (buf : list Z) : Prop :=
u8arr bsegs m1 BUF (map (Z_to_bv 8) buf) /\ bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) nc))
/\ (exists junk8, rw_cells bsegs m1 (SP + -144) (FRAMEC junk8)) /\ stk bsegs m1 lo (SP + -144)
/\ munch W m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1.
Ltac minv_close BA NA FA SA MUA WMA MIA :=
split; [exact BA|]; split; [exact NA|]; split; [eexists; exact FA|]; split; [exact SA|]; split; [exact MUA|]; split; [exact WMA| exact MIA].
Lemma chk_out : forall m1 a, unpoisoned m1 BUF (BUF + bsz) -> BUF <= a -> a + 1 <= BUF + bsz ->
exists b, ov_read_bytes bsegs m1 (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) 1 = Some [b]
/\ (sval b = 0 \/ (0 < sval b <= 7 /\ a mod 8 < sval b)) /\ -128 <= sval b <= 127.
Proof using WRC.
intros m1 a UB1 A0 A1.
pose proof (ablk_lin _ _ BLKB) as LBK. unfold KHIGH, AIMG_HI in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0060?15389206806.10843606267538.80 53033342475.80 53958062517.80 57214923008.83 8447668114.83  00000400500900=00A00BS2H0SS2A0S2A1S2CKS".
destruct (unpoisoned_check_rd bsegs m1 BUF (BUF + bsz) a 1 UB1 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK).
exists b. unfold shad, ASHOFF in RDB. replace (2147450880 + Z.shiftr a 3) with (Z.shiftr a 3 + 2147450880) in RDB by lia.
split; [exact RDB|]. split; [| apply sval_range].
destruct CK as [CK|CK]; [left; exact CK| right; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section LOOP.
Variable safe : bool.
Notation BST pc mm x8 x10 x11 x13 x14 x17 x20 x22 x26 x27 x28 x29 x30 x31 :=
(MS (mkR (Z_to_bv 64 1) (Z_to_bv 64 (SP + -144)) gp tp (Z_to_bv 64 (BUF + bsz + -2)) (Z_to_bv 64 2147450880) (Z_to_bv 64 asz)
x8 (Z_to_bv 64 0) x10 x11 (Z_to_bv 64 NC) x13 x14 (Z_to_bv 64 (Z.b2z safe)) (Z_to_bv 64 BUF) x17
(Z_to_bv 64 (18446744073709551615 - NC)) (Z_to_bv 64 (BUF + bsz)) x20 (Z_to_bv 64 31) x22 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-3))
(Z_to_bv 64 3) x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
Lemma wr_shrink : forall f rem thr nb thr' nb' m1 (x10 x11 x13 x14 x17 x20 x22 x27 x28 x29 x30 : word),
rem < thr -> 1 <= rem -> 1 <= nb <= 13 -> thr = 2^(nb - 1) ->
shrink (S f) rem thr nb = Ok (thr', nb') ->
(forall (y10 : word), evtF bsegs RNG POST (BST 0x81960 m1 (Z_to_bv 64 rem) y10 x11 x13 x14 x17 x20 x22 (Z_to_bv 64 thr') x27 x28 x29 x30 (Z_to_bv 64 nb'))) ->
evtF bsegs RNG POST (BST 0x8194c m1 (Z_to_bv 64 rem) x10 x11 x13 x14 x17 x20 x22 (Z_to_bv 64 thr) x27 x28 x29 x30 (Z_to_bv 64 nb)).
Proof using WRC.
induction f as [|f IH]; intros rem thr nb thr' nb' m1 x10 x11 x13 x14 x17 x20 x22 x27 x28 x29 x30 LT R1 NB TH SH K.
- rewrite shrink_S in SH. Local Ltac2 Set LiaHints.tbl := fun () => "00L0?10842114114.10114584537807.10017290158429.10318143769900.10319726814754.10420299290625.10029011846530.10434727867976.10437933076457.10438047386523.10439543018726.1013971545388.104 40308683552.10341417988940.10042134458196.1024410630228.97  4410630228.99  51405031183.10255462416432.10156203923314.10157311939879.98 57967260369.10358814736386.11459314988138.10361588508704.11764691467168.10065664998174.1046757865479.103 00000100500900P00m01201I01L01T01X01Y01\01a01b02I02M02Q02U02V02[03@03D03H03K03P03W03X03YSS2NBS2NBS5BUFNZ4NCNZ2NB3NB23THBS5BUFNZ4NCNZ2LT2R12NB3NB23THBS3NB2S5BUFNZ4NCNZ2NB3NB23THBS1BS2NB3NB2S2R1SS1BS3THBSS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2NB3NB23THBS2LTS2LTS2NBSS3NB2S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LT2R12THS2NBS2NBS1GS3THBS2NB2n0SS".
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
zstep. rewrite (FseWalkKit.swrap32_small thr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
rewrite FseWalkKit.swrap32_small by lia.
zstep.
if_cases B; lts_lit B.
+ replace (nb + -1) with (nb - 1) by lia.
eapply (IH rem (thr / 2) (nb - 1) thr' nb'); [lia| lia| lia| exact TH2| exact SH| exact K].
+ rewrite shrink_S in SH. replace (rem <? thr / 2) with false in SH by (symmetry; apply Z.ltb_ge; lia).
injection SH as <- <-. replace (nb - 1) with (nb + -1) in K by lia. apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac wrap17 := let v := reg_val 17%Z in
lazymatch v with Z_to_bv 64 ?e => rewrite <- (Z_to_bv_mod64 e) end.
Lemma wr_run3 : forall f s start s' start' m1 X (x8 x10 x11 x13 x20 x22 x26 x28 x30 x31 : word),
0 <= start -> start + 3 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
run3 (S f) s start = Ok (s', start') ->
(forall X' (y10 y13 : word), 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evtF bsegs RNG POST (BST 0x81788 m1 x8 y10 x11 y13 (Z_to_bv 64 start') (Z_to_bv 64 X') x20 x22 x26 (Z_to_bv 64 (w_symbol s)) x28
(Z_to_bv 64 (w_bitCount s')) x30 x31)) ->
evtF bsegs RNG POST (BST 0x8176c m1 x8 x10 x11 x13 (Z_to_bv 64 start) (Z_to_bv 64 X) x20 x22 x26 (Z_to_bv 64 (w_symbol s)) x28
(Z_to_bv 64 (w_bitCount s)) x30 x31).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "00D0?107704352.101  11447729318.17115350459110.10117316818849.11817316818850.11717328780436.10317328861471.10120142628527.10338954800347.10038954800347.10340053791375.10342130477039.10148953229076.10155516386911.97 55516386911.99 56448729812.11957295617883.10359314988138.1016256592031.103 7568103724.103 00000400b00f00j00n01Y01]01a01b01c01f02H02c02g02k03F03I03O03S03nS2BCS4SEPB4SEPN5SEPBN2BC1H2H02H42H52H93H143H193H24S2BCS2BCS2BCS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S02S32SY2RX2BCS2BCS2S0SSS1BS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2BCS5BUFNZ4NCNZ2S02S32SY2RX2BCS2S3S2S3S5BUFNZ4NCNZ2S02S32SY2RX2BCS1BS2BC1GS2SYS5BUFNZ4NCNZ2S02S32SY2RX2BC".
induction f as [|f IH]; intros s start s' start' m1 X x8 x10 x11 x13 x20 x22 x26 x28 x30 x31 S0 S3 SY RX EX R3 K;
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
+ wrap17.
lazymatch type of R3 with run3 _ ?sn _ = _ =>
eapply (IH sn (start + 3) s' start'); [lia | cbn [w_symbol]; lia | cbn [w_symbol]; lia | apply Z.mod_pos_bound; lia
| cbn [w_bitStream]; exact EX' | exact R3 | ] end.
cbn [w_symbol w_bitCount]. exact K.
+ rewrite run3_S in R3. cbn [w_symbol] in R3.
replace (start + 3 + 3 <=? w_symbol s) with false in R3 by (symmetry; apply Z.leb_gt; lia).
injection R3 as <- <-. wrap17.
apply K; [apply Z.mod_pos_bound; lia | cbn [w_bitStream]; exact EX'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma wr_skip : forall f sym sym' m1 (x8 x11 x13 x17 x26 x28 x29 x30 x31 : word),
0 <= sym < asz -> bytes_at bsegs m1 NC (u16s (map (Z_to_bv 64) nc)) -> unpoisoned m1 NC (NC + 2 * zlen nc) ->
skip_zeros nc asz (S f) sym = Ok sym' ->
(forall (y10 y13 y14 y20 y22 y30 : word), sym <= sym' < asz ->
evtF bsegs RNG POST (BST 0x81754 m1 x8 y10 x11 y13 y14 x17 y20 y22 x26 (Z_to_bv 64 sym') x28 x29 y30 x31)) ->
(forall (y10 y13 y14 y20 y22 y30 : word), sym' = asz ->
evtF bsegs RNG POST (BST 0x81740 m1 x8 y10 x11 y13 y14 x17 y20 y22 x26 (Z_to_bv 64 sym') x28 x29 y30 x31)) ->
evtF bsegs RNG POST (BST 0x81708 m1 x8 (Z_to_bv 64 (NC + 2 * sym)) x11 x13 (Z_to_bv 64 (2 * sym)) x17 (Z_to_bv 64 (asz - sym))
(Z_to_bv 64 (NC + 2 * sym)) x26 (Z_to_bv 64 sym) x28 x29 x30 x31).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "00m0?11275272025.11111281548129.10911281548129.1101287345813.118 28707550833.12228707550833.12529646625862.12629646625862.12829782367974.11829782367974.12034104303248.11138697646388.92 38697646388.94 39159981841.10439159981841.10740244715328.10040244715328.98 40829096625.13440829096625.13741730628386.10141730628386.10342130557540.10948787532352.11149355232569.10249355232569.10451124606241.11152067329428.11053635067609.11153635067609.11256862664027.13456862664027.13759310676312.13459310676312.13759314873579.10359314873579.10459314873579.10559314873579.10659314873579.10859314873579.11059437227813.11859437227813.12059437227815.12159437227815.12459583424896.10559583424896.10759583424896.10960231311587.10961330623914.11161514227145.10261514227145.10464407683369.11764407683369.1196607192557.120 66233876957.10666233876957.10868189636809.11768189636809.1197351371905.100 7351371905.98  9544766530.100 9544766530.98  00000:00D00N00T01601X02=02b02f02j02n03203603j04^05@05b05i06006406806]06g07L08108508N08U08\08h09409S0:20:L0:S0:m0;i0<b0=X0>70>V0?50?T0?X0?\0?`0@I0@M0@b0A70Ag0BW0Bo0C60C=0C>0C?0Ca0DC0DG0DKS2SY2NB2B2S2SY2NB2B2S2SY2NB2B2S2NB1HS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS4NCEV4SEPB4SEPN5SEPBN2LR2NB1H2H03H14S4NCEV4SEPB4SEPN5SEPBN2LR2NB1H2H03H14S2NBS2NBS2NBS2SYS2SYS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2NB2LN2CKS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2NB2LN2CKS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS2NB2SRS2NB2SRS2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NB2E0S2SY2NB2B2S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NB2LNS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NB2LNS2NBS3MSV5BUFNZ4NCNZ2SY2LR2NBS2NB2B2S2NB2B2S2NB2CK1G2H0S2NB2CK1G2H0S4SEPB4SEPN5SEPBN2LR2NB2CK1G2G'S4SEPB4SEPN5SEPBN2LR2NB2CK1G2G'S5BUFNZ4NCNZ2LR2NB2LN2G11HS2NB2G2S5BUFNZ4NCNZ2LR2NB2LN2G11HS2NB2G25BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2CR2LN2N01BS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2CR2NB2LN2N01BS5BUFNZ4NCNZ4NCEV2LO4SEPB4SEPN5SEPBN3KLO2LR2NB2LN2E01BS5BUFNZ4NCNZ2LO3KLO2LR2NB2LN2G1S5BUFNZ4NCNZ2LO3KLO2LR2NB2LN2G1S5BUFNZ4NCNZ2LO3KLO2LR2NB2LN2G1S5BUFNZ4NCNZ2LO3KLO2LR2NB2LN2G1S2NBS2NBS2NBS3MSV5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2SY2LR2NBS2NBS5BUFNZ4NCNZ2LR2NB2LNS5BUFNZ4NCNZ2LR2NB2LNS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3NC83KLO2LR2NB2LNS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3NC83KLO2LR2NB2LNS5BUFNZ4NCNZ2SY2NB2LN2G1S2SY2NBS2SY2NBFFS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2LR2NBS2NBS2NB".
induction f as [|f IH]; intros sym sym' m1 x8 x11 x13 x17 x26 x28 x29 x30 x31 SY NC1 UN1 SK KA KB;
rewrite skip_zeros_S in SK; replace (sym <? asz) with true in SK by (symmetry; apply Z.ltb_lt; lia);
apply bind_inv in SK; destruct SK as (c & LD & SK); apply load_inv in LD; destruct LD as [LR ->]; unfold FseNCount.Zlength in LR;
pose proof (Forall_Znth _ _ sym NCR LR) as CR; cbv beta in CR;
pose proof (bytes_at_bound _ _ _ _ NC1) as NB; rewrite u16s_length, length_map in NB;
pose proof (u16_znth bsegs m1 NC nc sym (Z_to_bv 64 (NC + 2 * sym)) NC1 LR ltac:(reflexivity)) as RD;
pose proof (ablk_lin _ _ BLKN) as LN; unfold KHIGH, AIMG_HI in *;
destruct (unpoisoned_check_rd bsegs m1 NC (NC + 2 * zlen nc) (NC + 2 * sym) 2 UN1 ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK);
unfold shad, ASHOFF in RDB; replace (2147450880 + Z.shiftr (NC + 2 * sym) 3) with (Z.shiftr (NC + 2 * sym) 3 + 2147450880) in RDB by lia;
pose proof (sval_range b) as SR;
(zstep; if_cases G1; zify_cond G1; [exfalso; lia|]);
(zstep; if_cases G2; zify_cond G2; [exfalso; lia|]);
(zstep; zstep; zstep; rewrite sxb_sval).
-
destruct (Z.eqb_spec (Znth sym nc) 0) as [E0|N0]; [cbn in SK; discriminate|]. injection SK as <-.
assert (LOADED : forall (y13 y30 : word), evtF bsegs RNG POST
(BST 0x81720 m1 x8 (Z_to_bv 64 (NC + 2 * sym)) x11 y13 (Z_to_bv 64 (2 * sym)) x17 (Z_to_bv 64 (asz - sym))
(Z_to_bv 64 (NC + 2 * sym)) x26 (Z_to_bv 64 sym) x28 x29 y30 x31)).
{ intros y13 y30. zstep. rewrite zx16_short by exact CR. zstep.
if_cases B; zify_cond B; [| exfalso; lia].
apply KA. lia. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply LOADED.
+ apply LOADED.
- assert (LOADED : forall (y13 y30 : word), evtF bsegs RNG POST
(BST 0x81720 m1 x8 (Z_to_bv 64 (NC + 2 * sym)) x11 y13 (Z_to_bv 64 (2 * sym)) x17 (Z_to_bv 64 (asz - sym))
(Z_to_bv 64 (NC + 2 * sym)) x26 (Z_to_bv 64 sym) x28 x29 y30 x31)).
{ intros y13 y30. zstep. rewrite zx16_short by exact CR. zstep.
destruct (Z.eqb_spec (Znth sym nc) 0) as [E0|N0].
+ if_cases B; zify_cond B; [exfalso; lia|].
zstep. sw32 (sym + 1). zstep. zstep. zstep. zstep. zstep.
if_cases B2; zify_cond B2.
* replace (asz - sym + -1) with (asz - (sym + 1)) by lia. replace (NC + 2 * sym + 2) with (NC + 2 * (sym + 1)) by lia.
replace (2 * sym + 2) with (2 * (sym + 1)) by lia.
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
Lemma wr_run24 : forall f s start s' start' m1 X (x8 x10 x14 x20 x26 x30 x31 : word),
0 <= start -> start + 24 <= w_symbol s -> w_symbol s <= 256 -> 0 <= X < 2^64 -> X mod 2^32 = w_bitStream s ->
zlen (w_buf s) = bsz -> MINV m1 (w_buf s) ->
run24 bsz safe (S f) s start = Ok (s', start') ->
(forall m2 X' (y10 y13 y30 : word), MINV m2 (w_buf s') -> 0 <= X' < 2^64 -> X' mod 2^32 = w_bitStream s' ->
evtF bsegs RNG POST (BST 0x81870 m2 x8 y10 (Z_to_bv 64 (BUF + w_out s')) y13 (Z_to_bv 64 start') (Z_to_bv 64 X') x20
(Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) x26 (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 start')
(Z_to_bv 64 (w_bitCount s)) y30 x31)) ->
evtF bsegs RNG POST (BST 0x81808 m1 x8 x10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) x14 (Z_to_bv 64 X) x20
(Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) x26 (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 start)
(Z_to_bv 64 (w_bitCount s)) x30 x31).
Proof using WRC.
Local Ltac2 Set LiaHints.tbl := fun () => "0180?10088275704.13213070568592.13013071253165.12914362626257.19115641283330.12115641300924.12216845815291.12217328780436.13319489965100.13319618399904.14219618399904.14721276737785.13122448268900.1222707945969.134 29782367974.13429782367974.14330047557315.13031183134347.1163214378781.122 3214378781.130 32313870464.1163405217491.130 35206187911.13136067281813.13436441195084.13336441195084.14237424340172.12938954701265.11939572309076.17240035529640.13141477180325.13442132582867.13145589988655.11645590082573.11445590082700.12345590083339.13145596907400.13945596907401.13646833963628.13347788875075.1254861253072.118 48725325126.14649170713844.130492328663.116  49423367528.1225152176687.103 5152176687.105 51818759664.1305222230152.125 53728626131.13254475752564.12356448729814.14756736913457.13959310676567.17259310676568.19159314873579.11559314873579.11759314873579.12459314873579.1326256755093.134 64407683369.13364407683369.14264794109999.12164799663456.12268017740602.13368017740602.14268189636809.13368189636809.142913132285.130  9448783520.172 9448783535.191 9581028844.130 00000400>00H00P00Z00d01V02S03[04E05305;05b05h05l06006f07T08F09<09C09G0:=0:D0:E0:F0:J0:N0:V0;=0;C0<90<b0=K0>50>c0?L0@50@Y0AK0B90Bo0Ce0DN0E10E60E;0Eb0Ei0Em0Fc0GG0H90I00J00JV0J`0KH0L40L;0M90N?0O?0P10P20P30P40P50P90PF0PZ0QES2NBS2O02O12NBS2O02O12NBS2NB3SR2S2O02O12NBS2O02O12NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2S03S242SY2RX2LB2O02O12NB3RX13RB1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2O02O12NB3LBK2G13RX12G23CK23RB1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX13RB1S2NB3RB3S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX1S2NB1BS2NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S2O02NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S2S02NBFFS2NBS2NBS2NB3SR1S5BUFNZ4NCNZ2S03S242SY2RX2BC2NB3RX13RB1S2NB1BS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX1S5BUFNZ4NCNZ2LO3KLO2RX2LB2O02O12NB3LBK3RX13RB1S5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2S03S242SY2RX2NB3RX13RB1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX13RB1S5BUFNZ4NCNZ2LO3KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX1S3S24S3S24S5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX13RB1S2O02NBS2NBS5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3EX13RX1S5BUFNZ4NCNZ2S03S242SY2RX2NB3RX13RB1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1S2LO4SEPB4SEPN5SEPBN3KLO2LB2BC2O02O12NB3LBK2G13CK11G2G'S2LO4SEPB4SEPN5SEPBN3KLO2LB2BC2O02O12NB3LBK2G12G23CK22G43G4'3H39S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK2G1S2OE2NB2BOS5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX12G21HS5BUFNZ4NCNZ2RX2LB2BC2O12NB3LBK3RX13RB12G31HS2SY2NBS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02O12NB3LBKS5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN4BUF83KLO2RX2LB2BC2O02O12NB3LBK3EX13RX1S5BUFNZ4NCNZ2LO4SEPB4SEPN5SEPBN3KLO2RX2LB2BC2O02O12NB3LBK2G13CK1S5BUFNZ4NCNZ4SEPB4SEPN5SEPBN2RX2LB2BC2O02O12NB3RX1FFFFS2NBS2NB3CK11G2H0S2NB2G12G23CK22G42H0S5BUFNZ4NCNZ2LO3KLO2RX2BC2O02NB3LBK3RX13RB1".
induction f as [|f IH]; intros s start s' start' m1 X x8 x10 x14 x20 x26 x30 x31 S0 S24 SY RX EX LB (BA & NA & [junk8 FA] & SA & MUA & WMA & MIA) R24 K;
rewrite run24_S in R24; replace (start + 24 <=? w_symbol s) with true in R24 by (symmetry; apply Z.leb_le; lia);
apply bind_inv in R24; destruct R24 as (v & SH & R24); apply shl32_inv in SH; destruct SH as [BC ->];
apply bind_inv in R24; destruct R24 as (sfl & FL & R24); apply wflush_inv in FL; cbn [w_buf w_out w_bitStream w_bitCount w_symbol w_remaining w_threshold w_nbBits w_previousIs0] in FL;
destruct FL as (OE & O0 & O1 & ->); unfold FseNCount.Zlength in O1.
- cbn in R24. discriminate.
- pose proof (u8arr_bound _ _ _ _ BA) as BB. rewrite length_map in BB.
pose proof (bytes_at_bound _ _ _ _ NA) as NB. rewrite u16s_length, length_map in NB.
pose proof SA as (LO0 & _ & _). unfold FRAMEC in FA.
pose proof (ablk_lin _ _ BLKB) as LBK. unfold KHIGH, AIMG_HI in *.
assert (STORES : evtF bsegs RNG POST
(BST 0x81814 m1 x8 x10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) x14 (Z_to_bv 64 X) x20
(Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) x26 (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 start)
(Z_to_bv 64 (w_bitCount s)) x30 x31)).
{ zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
destruct (inv_shadow _ MUA) as [UB1 _].
destruct (chk_out m1 (BUF + w_out s) UB1 ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN1 : forall (y10 y14 : word), evtF bsegs RNG POST
(BST 0x81828 m1 x8 y10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) y14 (Z_to_bv 64 X) x20
(Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) x26 (Z_to_bv 64 (w_symbol s)) (Z_to_bv 64 start)
(Z_to_bv 64 (w_bitCount s)) x30 x31)).
{ intros y10 y14. clear RDB1 CK1 SR1 b1.
zstep.
assert (EX1 : ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64) mod 2^32 = u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))).
{ unfold u32. rewrite <- EX. change (2^64) with 18446744073709551616. change (2^32) with 4294967296. rewrite swrap32_eq. lia. }
assert (RX1 : 0 <= (X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64 < 2^64) by (apply Z.mod_pos_bound; lia).
wrap17. revert EX1 RX1. generalize ((X + bv_swrap 32 (65535 * 2 ^ w_bitCount s)) mod 2^64). intros X1 EX1 RX1.
set (bs1 := u32 (w_bitStream s + u32 (65535 * 2 ^ w_bitCount s))) in *.
u8_sok BA (w_out s). zstep.
u8_store BA (w_out s) (to_byte bs1). { unfold to_byte. rewrite <- EX1. change (2^32) with 4294967296. lia. }
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep.
destruct (inv_shadow _ MUA) as [UB2 _].
lazymatch type of UB2 with unpoisoned ?mm _ _ =>
destruct (chk_out mm (BUF + w_out s + 1) UB2 ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2) end.
zstep. zstep. zstep. rewrite sxb_sval.
assert (RB1 : 0 <= bs1 < 2^32) by (subst bs1; apply u32_range).
assert (RB3 : 0 <= bs1 / 2^16 < 2^32) by (apply div16_range; exact RB1).
assert (RB2 : 0 <= bs1 / 2^16 < 2^64).
{ change (2^32) with 4294967296 in RB3. change (2^64) with 18446744073709551616. lia. }
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JOIN2 : forall (z10 z30 : word), evtF bsegs RNG POST
(BST 0x81848 mm x8 z10 (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s)) (Z_to_bv 64 (BUF + w_out s + 1))
(Z_to_bv 64 X1) x20 (Z_to_bv 64 (bv_swrap 32 (65535 * 2 ^ w_bitCount s))) x26 (Z_to_bv 64 (w_symbol s))
(Z_to_bv 64 start) (Z_to_bv 64 (w_bitCount s)) z30 x31)) end.
{ intros z10 z30. clear RDB2 CK2 SR2 b2.
zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
u8_sok BA (w_out s + 1). zstep.
u8_store BA (w_out s + 1) (to_byte (bs1 / 2^8)). { unfold to_byte. change (2^8) with 256. lia. }
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
zstep. zstep. rewrite srliw_val by lia. change 4294967296 with (2^32). rewrite EX1.
zstep. zstep. sw32 (start + 48). zstep. zstep.
setreg 11%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
setreg 13%Z (Z_to_bv 64 (BUF + (w_out s + 2))) ltac:(f_equal; lia).
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
zstep. if_cases G4; zify_cond G4.
+ zstep. zstep. if_cases G4'; zify_lts G4'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN2.
+ apply JOIN2. }
zstep. if_cases G; zify_cond G.
+ zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply JOIN1.
+ apply JOIN1. }
zstep. rewrite b2z_word_nez. destruct (Bool.bool_dec safe true) as [SAFE|SAFE].
+ rewrite (ite_true _ safe _ _ SAFE). apply STORES.
+ apply Bool.not_true_is_false in SAFE. rewrite (ite_false _ safe _ _ SAFE).
destruct OE as [OE|OE]; [congruence|].
zstep. if_false. zstep. if_cases BO; zify_cond BO; [exfalso; lia|]. apply STORES.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End LOOP.
End WR.
End CANSEC1.
