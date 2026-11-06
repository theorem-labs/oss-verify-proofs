(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseRdKit FseRdKit2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_count AF_fse_rd_loop.
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
Local Ltac acc_hint ::= rdA_acc_hint.
Section CANSEC1. Context {rc : runConstT}.
Section Hdr.
Variable C : rdctxA.
Variable RNG : footprint.
Hypothesis OK : rd_okA C.
Hypothesis SH : rd_shA C.
Hypothesis RNGS : rd_rngA C RNG.
Notation buf := (a_buf C).
Notation msv1 := (a_msv0 C + 1).
Notation BUF := (a_BUF C).
Notation NC := (a_NC C).
Notation MSVP := (a_MSVP C).
Notation TLP := (a_TLP C).
Notation SPA := (a_SPA C).
Notation FF := (a_FF C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
Definition FRA_pro (j0 j8 j16 j32 j40 j48 j64 : list byte) : list cell :=
[CB 8 j0; CB 8 j8; CB 8 j16; C8 (Z_to_bv 64 FF); CB 8 j32; CB 8 j40; CB 8 j48; C8 (Z_to_bv 64 MSVP); CB 16 j64; C8 (Z_to_bv 64 FF)].
Definition FRA_mid (j0 j8 j32 j40 j48 j64 : list byte) : list cell :=
[CB 8 j0; CB 8 j8; C8 (Z_to_bv 64 (Z.shiftr MSVP 3 + ASHB)); C8 (Z_to_bv 64 FF); CB 8 j32; CB 8 j40; CB 8 j48; C8 (Z_to_bv 64 MSVP);
CB 16 j64; C8 (Z_to_bv 64 FF)].
#[using="rc OK SH RNGS"] Lemma loop_runA' : forall tl (Htl : 5 <= tl <= 15) f s sF m1 msvw pc (x1 x6 x7 x10 x11 x12 x13 x16 x18 x20 x22 x29 : word),
rloop buf msv1 f s = Ok sF ->
rd_invA C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
pc = (if r_previous0 s then 0x82050 else 0x82034) ->
x1 = Z_to_bv 64 (r_nbBits s) -> x6 = Z_to_bv 64 (bv_swrap 32 (r_bitStream s)) -> x10 = Z_to_bv 64 (BUF + r_ip s) ->
x11 = Z_to_bv 64 (r_remaining s) -> x13 = Z_to_bv 64 (r_charnum s) -> x16 = Z_to_bv 64 (r_bitCount s) ->
x18 = Z_to_bv 64 (r_threshold s) ->
evtF bsegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) tl (r_ip sF + (r_bitCount sF + 7) / 8))
(rd_lstA C pc m1 x1 x6 x7 x10 x11 x12 x13 x16 x18 x20 x22 x29).
Proof.
intros tl Htl f s sF m1 msvw pc x1 x6 x7 x10 x11 x12 x13 x16 x18 x20 x22 x29 RL INV HC HP HB F1 F2 F3 -> -> -> -> -> -> -> ->.
exact (loop_runA C RNG OK SH RNGS tl Htl f s sF m1 msvw x7 x12 x20 x22 x29 RL INV HC HP HB F1 F2 F3).
Qed.
#[using="rc OK SH RNGS"] Lemma hd_tailA : forall m1 tl0 sF j0 j8 j32 j40 j48 j64 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_mid j0 j8 j32 j40 j48 j64) ->
stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
Z.land (le32 buf 0) 15 <= 10 ->
rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) = Ok sF ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
evtF bsegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81fb0) (a_fc C) None m1 (seg_rom bsegs)).
Proof.
intros m1 tl0 sF j0 j8 j32 j40 j48 j64 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX RL F1 F2 F3.
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNT & _ & SMT & _ & STB & _).
pose proof (okA_lin C OK) as (HH' & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
unfold FRA_mid, ASHB in FRM. unfold rd_WA, RDA_CALLEE in MU.
Local Ltac2 Set LiaHints.tbl := fun () => "00b0?10433625893.10512596293755.10914281265119.11017713987757.10518750122335.11019491437791.11020908760156.11122605103099.96 25703506617.10529134622547.10429315478722.94 3223250298.96  32651489978.11132947271516.11133376210745.11135091177529.11137187770245.96 37211491939.10537504048583.10438960293340.11140825345228.96 41415729742.92 42831019478.10543290223857.94 43327240343.1054339286231.94  43774890704.10544511195010.94 45221239098.10547101426873.11148625107299.95 48771018667.84 50553141824.10251813165669.92 52567164907.10552567164907.11153510313876.10255590255846.94 55754453387.96 56091574818.94 5750404528.108 57745675194.11158705023297.96 58756150127.92 59128021829.96 60154389715.97 63035102172.10564391634778.94 65502002695.89 8583720762.111 00000800@00N01[01i02702?02D03D03R03W03_03g03o04o05o06406906>06F06K06L06T06\06a06l07507>07F08F08Q08Z09S09W09\09a09f09n0:30:;0:F0:N0:V0:Z0:[0:b0:j0:o0;00;8S2RW3LWSS2P53LWSS2LO5SPA123LWSS3STB3LWS2LO3LOA5SPA123NC03MS03TL03TL13BF03FF03ATR2X03SMT3SNT4SP164SPA32N82T4S2LO5SPA123LWSS2LO5SPA123LWSS3LWS2HBS3LWSS2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR2X03LWS2HB3TL13MS13NC1S2LO5SPA123LWSS3LWSS2RW3LWSS3LWS2HBS3LWS2HBS2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR2X03LWS2HB3TL13MS13NC1S2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR2X03LWS2HB3TL13MS13NC1S3LWSS3LWSS3LWSS3LWS2HBS3LWSSS3LWS2HBS2P53LWSS3LWSS2HX2X03LWSS3TL03LWSS3NC03LWSS3LWS2HBS2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR2X03LWS2HB3TL13MS13NC1S2HX2X03LWSS3HM03HM1S3HM03HM12LO3LOA5SPA123NC03NC13MS03TL03BF03FF03ATR2X03LWSS2X0S3LWSS3LWSS3LWSS2P53LWSS3LWSS2X03LWSS2HX2X03LWSS3LWS2HBS2RW3LWSS2HXFS3LWS1HS3LWS2HBS3LWSSS3LWS2HB".
destruct (rd_s0_inv buf msv1 (a_rt0 C) (buf_all_bytesA C OK) (proj1 HH) ltac:(lia) HX) as (HC0 & HP0 & HB0').
pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
set (W := le32 buf 0) in *.
remember (Z.land W 15) as x eqn:Ex.
assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
assert (P5 : 32 <= 2 ^ (x + 5) <= 32768).
{ split; [change 32 with (2^5)| change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. }
assert (LWS : length (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))) = length (a_rt0 C))
by (rewrite length_map; apply zero_prefix_length).
zstep. zstep. zstep. zstep. zstep.
zstep. zstep. zstep.
zstep.
zstep. replace (0 <? NC) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
do 7 zstep.
zstep.
zstep.
zstep. rewrite ?(Z.mod_small x 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
replace (32 * 2 ^ x) with (2 ^ (x + 5)) by (rewrite Z.pow_add_r by lia; change (2^5) with 32; lia).
rewrite (FseWalkKit.swrap32_small (2 ^ (x + 5))) by lia.
zstep. zstep.
zstep. zstep. zstep. zstep. zstep.
zstep.
zstep. rewrite (FseWalkKit.swrap32_small (2 ^ (x + 5) + 1)) by lia.
zstep. zstep. zstep. zstep. if_false.
replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 18446744071562067968) by (apply bv_eq; reflexivity).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (INV0 : rd_invA C mm (r_nc (rd_s0 buf msv1 (a_rt0 C))) (Z_to_bv 64 (a_msv0 C)) (Z_to_bv 64 (x + 5))) end.
{ unfold rd_s0. cbv zeta. cbnR. unfold rd_invA.
split; [eassumption|]. split; [apply zero_prefix_length|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [do 2 eexists; unfold FRA_main, ASHB; eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption. }
pose proof (loop_runA' (x + 5) ltac:(lia) (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) sF m (Z_to_bv 64 (a_msv0 C)) 0x82034) as LR.
unfold rd_lstA in LR.
eapply LR; try eassumption; try reflexivity.
all: unfold rd_s0; cbv zeta; cbnR; fold W; rewrite <- ?Ex.
all: try (f_equal; lia).
all: try reflexivity.
rewrite ?(Z.shiftr_div_pow2 W 4) by lia. f_equal. symmetry. apply FseWalkKit.swrap32_small.
assert (0 <= W / 2^4 < 2^28) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma hd_tlpA : forall m1 tl0 sF j0 j8 j16 j32 j40 j48 j64 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_pro j0 j8 j16 j32 j40 j48 j64) ->
stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
Z.land (le32 buf 0) 15 <= 10 ->
rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) = Ok sF ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
evtF bsegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f90) (a_fc C) None m1 (seg_rom bsegs)).
Proof.
intros m1 tl0 sF j0 j8 j16 j32 j40 j48 j64 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX RL F1 F2 F3.
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
unfold FRA_pro, ASHB in FRM. unfold rd_WA, RDA_CALLEE in MU.
assert (LWS : length (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))) = length (a_rt0 C))
by (rewrite length_map; apply zero_prefix_length).
assert (LBS : length (map (Z_to_bv 8) buf) = length buf) by apply length_map.
pose proof (hd_tailA) as TAIL.
Local Ltac2 Set LiaHints.tbl := fun () => "00E0?22736838437.14424666713560.97 33816247282.10141404702245.95 41416008653.93 44987877980.98 50553141837.10450553141838.10550553141839.10250562030021.93 52567164907.98 53538128661.159563227834.98   59308693840.93 59310676694.15959655640147.15962179823348.88 65979776700.88 66149329282.14966664437305.98 8943524158.88  00000E00W01V02U02^02j03\04N05@06206;06T06`07007I07V07_07h08409509>S2T43LWS3LBS1H2H03H14S2LO5SPA123LWS3LBSS4SP162LO3LOA5SPA124SPA33NC03MS03TL03TL12T43BF03FF03ATR3LWS3LBSS4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3LWS3LBS3CKT2G1S3LWS3LBSS3LWS3LBS2HBS2LO3LOA5SPA123NC03MS03TL03TL13BF03FF03ATR3LWS3LBSS2LO3LOA5SPA123NC03MS03TL03TL13BF03FF03ATR3LWS3LBSS2LO3LOA5SPA123NC03MS03TL03TL13BF03FF03ATR3LWS3LBSS2LO3LOA5SPA123NC03MS03TL03TL13BF03FF03ATR3LWS3LBSS3LWS3LBSS3TL03LWS3LBS3CKT2G11G2H0S3LWS3LBS2HBS3TL03LWS3LBS2G1S3TL03LWS3LBS3CKT2G11G2G'S3LWS3LBS3SRTS3LWS3LBSS3LWS3LBSS2T43LWS3LBSS2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR3LWS3LBS2HB3TL13MS13NC1S3LWS3LBS".
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => remember mm as m2 eqn:Hm2 end.
assert (MU2 : munch (rd_WA C) (a_m C) m2) by (unfold rd_WA, RDA_CALLEE; assumption).
destruct (inv_shadowA C m2 OK SH MU2) as (_ & _ & UT & _).
destruct (chk1A m2 TLP (TLP + 4) TLP 4 UT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (bt & RDBT & CKT & SRT).
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. replace (Z.land TLP 3) with 0
by (change 3 with (2^2 - 1); rewrite land_ones_mod by lia; change (2^2) with 4; symmetry; Z.div_mod_to_equations; lia).
zstep. if_false.
zstep. zstep. zstep. rewrite sxb_sval.
assert (J3 : forall (y12 y13 : word),
evtF bsegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) y12 y13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81fb0) (a_fc C) None m2 (seg_rom bsegs))).
{ intros y12 y13. clear RDBT CKT SRT. eapply TAIL; try eassumption; unfold FRA_mid, ASHB; eassumption. }
zstep. if_cases G; zify_cond G.
- zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply J3.
- apply J3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma hd_chkA : forall m1 tl0 sF j0 j8 j16 j32 j40 j48 j64 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word),
u8arr bsegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells bsegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells bsegs m1 TLP [C4 tl0] ->
bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells bsegs m1 SPA (FRA_pro j0 j8 j16 j32 j40 j48 j64) ->
stk bsegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono bsegs (a_m C) m1 -> mem_inv bsegs m1 ->
Z.land (le32 buf 0) 15 <= 10 ->
rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) = Ok sF ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
evtF bsegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 NC) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f2c) (a_fc C) None m1 (seg_rom bsegs)).
Proof.
intros m1 tl0 sF j0 j8 j16 j32 j40 j48 j64 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX RL F1 F2 F3.
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & UT & UB).
Local Ltac2 Set LiaHints.tbl := fun () => "0170?10644829208.92 11447729318.17911447729318.18111447729451.18511447729451.18812374825302.11114202106942.96 15534906503.11321922089021.94 24362092084.10824362092084.11125261073778.10825261073778.11128022624402.1113132576391.113 32845107955.16733536214416.84 33550629318.11133816247282.11033816247283.10735129193542.11035129193543.10735322926884.88 35943704740.10835943704740.11136401657513.11136401657514.11137694598650.11138361712443.10943929283719.11345230898969.10845657192820.10948729316279.11448973659295.10150553141826.10950553141838.11250562029638.10251069061334.11152946877380.10955020753293.88 55036003867.11055702594692.10855702594692.11156117678754.10856117678754.11156662150274.10856662150274.11157020354443.10957309684293.16558067894962.11158805924857.11259308692554.10259308692554.10459308693715.10259314923118.10059328944939.10959588178615.11360700203023.10060856834888.10860856834888.11161015399828.10961448213823.98 62976236565.10862976236565.11163872857899.11065979774378.84 66721607490.11167048124130.11167485074685.1039448783393.165 9448783393.167 00000400500600700800900=00>00B00C00D00E00F00G00H00M00Q00R01?01l02@02T02X02Y02Z03G04404504604704;04<04@05405a06N07;07<07=07>07B07C07D07E07F07G07H07I07N07O07S08L09H09P09V09W09X09Y09Z09[09\09`09a09b09f09g09h09i0:`0:j0:nS2HHFFFFFS2HHFS2HHFFFFFFS3SR0S2HHFS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS3MS03TL03BF02B83FF0S3MS03TL03BF02B83FF0S2HHFFS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRFFFS2HHFS2RWS4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3CK3S2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRFFSS2HHFFFFFFFS3SR3FS2HHS4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3CK31G2G'S4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3CK02G01G2G'S3BF02G0S2HX1KFSSFFFS2HHFFS2HHSFFS4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3CK02G0S3CK31G2H0S2B8".
destruct (chkB m1 BUF (BUF + zlen buf) BUF UB ltac:(lia) ltac:(lia)) as (b0 & RDB0 & CK0 & SR0).
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + 3) UB ltac:(lia) ltac:(lia)) as (b3 & RDB3 & CK3 & SR3).
destruct (buf_rdA C OK m1 0 HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rdA C OK m1 1 HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rdA C OK m1 2 HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rdA C OK m1 3 HBUF ltac:(lia)) as [RD3 R3].
rewrite Z.add_0_r in RD0.
pose proof (hd_tlpA m1 tl0 sF j0 j8 j16 j32 j40 j48 j64) as TLPK.
assert (J2 : forall (y12 y13 y14 y15 : word),
evtF bsegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) y12 y13 y14 y15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f90) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y12 y13 y14 y15. eapply TLPK; eassumption. }
clear TLPK.
assert (J1 : forall (y10 y11 y12 : word),
evtF bsegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
y10 y11 y12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f54) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y10 y11 y12. clear RDB0 CK0 SR0 RDB3 CK3 SR3.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lbu_raw by assumption.
change (Znth 0 buf + 2 ^ 8 * Znth 1 buf + 2 ^ 16 * Znth 2 buf + 2 ^ 24 * Znth 3 buf) with (le32 buf 0).
pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
zstep. zstep. zstep.
if_cases K; zify_cond K; rewrite ?(Z.mod_small (le32 buf 0) 18446744073709551616) in * by lia; [| exfalso; lia].
apply J2. }
clear J2.
assert (J0 : forall (y10 y11 : word),
evtF bsegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
y10 y11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 msv1)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f40) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y10 y11. clear RDB0 CK0 SR0.
zstep. zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J1.
- apply J1. }
clear J1.
zstep. if_cases G0; zify_cond G0; [exfalso; lia|].
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J0.
- apply J0.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Theorem rd_mainA : forall rt msv tlr n (tl0 : word) (j0 j8 j16 j32 j40 j48 j64 : list byte) (RLO RHI : Z)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31 : word),
u8arr bsegs (a_m C) NC (u16s (map (Z_to_bv 64) (a_rt0 C))) ->
rw_cells bsegs (a_m C) MSVP [C4 (Z_to_bv 64 (a_msv0 C))] ->
rw_cells bsegs (a_m C) TLP [C4 tl0] ->
bytes_at bsegs (a_m C) BUF (map (Z_to_bv 8) buf) ->
rw_cells bsegs (a_m C) SPA (FRA_pro j0 j8 j16 j32 j40 j48 j64) ->
stk bsegs (a_m C) (a_lo C) SPA -> mem_inv bsegs (a_m C) ->
rt_got (a_m C) -> rt_got_ric (a_m C) -> rt_shbase (a_m C) -> rt_inited (a_m C) -> rt_layout (a_m C) -> rt_real_mem (a_m C) ->
(RLO <= NC /\ NC + 2 * zlen (a_rt0 C) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND) ->
wr_at bsegs (a_m C) (shad RLO) (shad RHI - shad RLO) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
read_ncount_body8 buf msv1 (a_rt0 C) = Ok (rt, msv, tlr, n) ->
evtF bsegs RNG (rd_mainA_post C rt msv tlr n)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) (Z_to_bv 64 (BUF + zlen buf)) x20 (Z_to_bv 64 NC) (Z_to_bv 64 TLP) x23
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 BUF) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f0c) (a_fc C) None (a_m C) (seg_rom bsegs)).
Proof.
intros rt msv tlr n tl0 j0 j8 j16 j32 j40 j48 j64 RLO RHI x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x23 x28 x29 x30 x31
ARR HMSV HTL HBUF FRA0 ST MI GOT RIC SHB INI LAY REAL HULL WRH RSH RB.
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB' & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
destruct (read_body8_inv buf msv1 (a_rt0 C) rt msv tlr n (proj1 HH) RB) as (HL & HX & -> & sF & RL & F1 & F2 & F3 & -> & -> & ->).
pose proof (munch_refl (rd_WA C) (a_m C)) as MU. pose proof (wmono_refl bsegs (a_m C)) as WM. unfold rd_WA, RDA_CALLEE in MU.
pose proof SH as (UN & UM & UT & UB).
assert (LWS : length (map (Z_to_bv 64) (a_rt0 C)) = length (a_rt0 C)) by apply length_map.
unfold FRA_pro in FRA0.
remember (a_m C) as m eqn:Em.
Local Ltac2 Set LiaHints.tbl := fun () => "00V0?13543389264.11413827271458.11819620497065.11421181963197.10821182078378.11825076071819.13625076071819.13725792348067.13628371444497.13430665193763.13632174006523.11833051759717.13633051759717.1373370534861.118 34064013718.13335214167690.11337211491939.11437504048583.11340507981603.13645243883939.13645382455823.11848725681100.11850553141826.10950560132980.11850881776563.103545472525.118  55590091132.10356563527971.13657018342201.11857498902798.11857622410744.13761942807650.1356234796707.136 63331384996.10665833869487.13465977643946.11865977791933.10866504755511.10300000>01701@02903504c06O07@08<08m09^09_0:[0;W0;c0;d0;i0;n0<_0=P0=_0>[0>d0?Y0?b0@b0@k0A\0Ah0C40D[0Dg0EX0FQ0GJ0GV0G^0GgS2LO5SPA123LWSS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HM03LWSS4HULL3HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HU23HU52LO3LOA5SPA123NC03NC13MS03TL03BF03FF03ATR2HL3LWS2LA3HU42HH3HM04SP164SPA32N83MS13TL12T43BF13SNT2M43SNMS3HU23HU43HU53HM04SP162LO3LOA5SPA124SPA33NC03NC12N83MS03MS13TL03TL13BF03BF12B83FF03ATR2HL3LWS2LA3LBS3SNT3SNBS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAFS3HU23HU52LO3LOA5SPA123NC03NC13MS03TL03BF03FF03ATR2HL3LWS2LAS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HU53LWS2LAFS3LWSS3LWSS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU52LO3LWS2LAS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HM03LWSS3HU53SPK2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HM03LWSS3HU23HU53HM02LO3LOA5SPA123NC03NC13MS03TL03BF03FF03ATR2HL3LWS2LAS3HM03LWSS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU53LWS2LAS3HU13HU23HU33HU43HU53HU63HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HU23HU43HU52HH3HM04SP162LO3LOA5SPA124SPA33NC03NC13MS03MS13TL03TL13BF03BF13FF03ATR2HL3LWS2LA3SNM3SNT1HS3HU53LWS2LAS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS4HULL3HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU53LWS2LAS3LWS2LAS3HM03LWS".
zstep.
zstep. rewrite (sx32_small (a_msv0 C)) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small msv1) by lia.
zstep. zstep. rewrite (shl32_shr31 msv1) by lia.
zstep. zstep. zstep.
set (bsA := u16s (map (Z_to_bv 64) (a_rt0 C))) in *.
assert (LA : length bsA = (2 * length (a_rt0 C))%nat) by (subst bsA; rewrite u16s_length, LWS; reflexivity).
set (n1 := Z.to_nat (2 * msv1)).
pose proof (rw_cells_of_u8arr _ _ _ _ ARR) as RA. clear ARR.
pose proof (rw_cells_split_CB bsegs _ NC [] _ bsA [] [n1; (length bsA - n1)%nat] RA ltac:(cbn [sum_nat]; lia)) as RS.
cbn [app mk_CB_cells] in RS. clear RA.
change [CB n1 (firstn n1 bsA); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]
with ([CB n1 (firstn n1 bsA)] ++ [CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) in RS.
apply rd_rw_cells_appA in RS. destruct RS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
assert (LBS : Z.of_nat (length (map (Z_to_bv 8) buf)) = zlen buf) by (rewrite length_map; reflexivity).
assert (UN1 : unpoisoned m NC (NC + 2 * msv1)) by (eapply unpoisoned_sub; [exact UN| lia| lia]).
pose proof OK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BN & _ & _ & _ & _ & _ & _ & _ & _ & SNM & SNT & SNB & _).
destruct HULL as (HU1 & HU2 & HU3 & HU4 & HU5 & HU6).
call (amemset_specZ NC (2 * msv1) 0 SPA).
all: first [ lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- mem_inv _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ NC _ => exact R1
| |- rw_cells _ _ _ _ => assumption
| |- app_blk _ _ => apply ablk_app_blk; [eapply ablk_sub; [exact BN| lia| lia]| lia]
| |- unpoisoned _ _ _ => exact UN1
| |- wr_at _ _ _ _ => eassumption
| |- rng _ _ _ => eapply rng_sub'; [exact RSTK| lia]
| |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
| |- _ => unfold KHIGH, KEND in *; lia
end | lazymatch goal with |- ?G => idtac "FAILED:" G end ].
lazymatch goal with
| P : rw_cells bsegs ?mm NC [CB (Z.to_nat (2 * msv1)) (repeat (Z_to_bv 8 0) (Z.to_nat (2 * msv1)))] |- _ =>
rename mm into m2; rename P into P0
end.
assert (ARR : u8arr bsegs m2 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))))).
{ pose proof (proj2 (rd_rw_cells_appA bsegs m2 NC [CB n1 (repeat (Z_to_bv 8 0) n1)]
[CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) (conj P0 R2)) as RJ.
pose proof (rw_cells_merge bsegs m2 NC [] [CB n1 (repeat (Z_to_bv 8 0) n1); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))] [] RJ) as RMg.
cbn [app] in RMg.
apply u8arr_of_rw_cells in RMg. cbn [cells_bytes cbytes app] in RMg. rewrite app_nil_r in RMg.
rewrite firstn_all2 in RMg by (rewrite length_skipn; lia).
replace n1 with (2 * Z.to_nat msv1)%nat in RMg by (subst n1; lia).
subst bsA. rewrite u16s_zero_prefix in RMg by lia. exact RMg. }
clear R2 P0.
eapply (hd_chkA m2 tl0 sF j0 j8 j16 j32 j40 j48 j64); try eassumption.
- unfold rd_WA, RDA_CALLEE. rewrite <- Em. eassumption.
- rewrite <- Em. eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Hdr.
End CANSEC1.
