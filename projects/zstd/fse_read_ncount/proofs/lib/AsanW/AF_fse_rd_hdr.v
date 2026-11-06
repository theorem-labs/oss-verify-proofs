(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseRdKit FseRdKit2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_loop.
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
Definition FRA_mid (j0 j24 : list byte) : list cell :=
[CB 8 j0; C8 (Z_to_bv 64 (Z.shiftr MSVP 3 + ASHB)); C8 (Z_to_bv 64 MSVP); CB 24 j24; C8 (Z_to_bv 64 FF)].
#[using="rc OK SH RNGS"] Lemma hd_tailA : forall m1 tl0 sF j0 j24 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
u8arr asegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells asegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells asegs m1 TLP [C4 tl0] ->
bytes_at asegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells asegs m1 SPA (FRA_mid j0 j24) ->
stk asegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono asegs (a_m C) m1 -> mem_inv asegs m1 ->
Z.land (le32 buf 0) 15 <= 10 ->
rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) = Ok sF ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
evtF asegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81fac) (a_fc C) None m1 (seg_rom asegs)).
Proof.
intros m1 tl0 sF j0 j24 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX RL F1 F2 F3.
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNT & _ & SMT & _ & STB & _).
pose proof (okA_lin C OK) as (HH' & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
unfold FRA_mid, ASHB in FRM. unfold rd_WA, RDA_CALLEE in MU.
Local Ltac2 Set LiaHints.tbl := fun () => "00Z0?10433625894.10011670174649.10312596293758.10217713987757.10117713987757.10222605103099.92 23926578779.10227637725770.10129315478722.90 3223250298.92  33680001082.10337187770245.92 37211491939.10137211491939.10237504048583.10040825345228.92 41415729742.88 42831019478.10142831019478.10243290223857.90 43327240343.10143327240343.1024339286231.90  43774890704.10143774890704.10248625107299.91 48771018667.80 50996590812.10351813165669.88 52567164907.10152567164907.10252567164907.10355590255846.90 55754453387.92 56091574818.90 5750404530.102 58705023297.92 58756150127.88 59128021829.92 60154389715.93 64391634778.90 65502002695.85 00000801801@02M03M03R03`03n04304;04C04H04M04R04W04\04]04e04m05505:05?05J05S05[05f05o06706;06@06E06J06R06W06_06j07207607707>07C07DS2RW3LWSS2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR2X03LWS2HB3TL13MS13NC1S2P53LWSS3STB3LWS2LO3LOA5SPA123NC03MS03TL03TL13BF03FF03ATR2X03SMT3SNT4SP164SPA32N82T4S2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR2X03LWS2HB3TL13MS13NC1S3LWSS2LO5SPA123LWSS2LO5SPA123LWSS3LWSS2RW3LWSS3LWS2HBS3LWSS3LWSS3LWSS3LWSS3LWSSS3LWS2HBS3LWS2HBS2P53LWSS3LWSS3LWSS2HX2X03LWSS3TL03LWSS3LWS2HBS2HX2X03LWSS3HM03HM1S3LWS2HBS2X0S3LWSS3LWSS3LWSS2P53LWSS3LWSS2X03LWSS2HX2X03LWSS2RW3LWSS2HXFS3LWS1HS3LWSS".
destruct (rd_s0_inv buf msv1 (a_rt0 C) (buf_all_bytesA C OK) (proj1 HH) ltac:(lia) HX) as (HC0 & HP0 & HB0').
pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
set (W := le32 buf 0) in *.
remember (Z.land W 15) as x eqn:Ex.
assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
assert (P5 : 32 <= 2 ^ (x + 5) <= 32768).
{ split; [change 32 with (2^5)| change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. }
assert (LWS : length (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))) = length (a_rt0 C))
by (rewrite length_map; apply zero_prefix_length).
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
do 7 zstep.
zstep.
zstep. rewrite ?(Z.mod_small x 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
replace (32 * 2 ^ x) with (2 ^ (x + 5)) by (rewrite Z.pow_add_r by lia; change (2^5) with 32; lia).
rewrite (FseWalkKit.swrap32_small (2 ^ (x + 5))) by lia.
zstep. zstep. zstep.
zstep. zstep.
do 4 zstep.
zstep. rewrite (FseWalkKit.swrap32_small (2 ^ (x + 5) + 1)) by lia.
zstep. zstep. zstep. zstep. if_true.
replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 18446744071562067968) by (apply bv_eq; reflexivity).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (INV0 : rd_invA C mm (r_nc (rd_s0 buf msv1 (a_rt0 C))) (Z_to_bv 64 (a_msv0 C)) (Z_to_bv 64 (x + 5))) end.
{ unfold rd_s0. cbv zeta. cbnR. unfold rd_invA.
split; [eassumption|]. split; [apply zero_prefix_length|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
split; [eexists; unfold FRA_main, ASHB; eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption. }
pose proof (loop_runA' C RNG OK SH RNGS (x + 5) ltac:(lia) (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) sF m (Z_to_bv 64 (a_msv0 C)) 0x821a0) as LR.
unfold rd_lstA in LR.
eapply LR; try eassumption; try reflexivity.
all: unfold rd_s0; cbv zeta; cbnR; fold W; rewrite <- ?Ex.
all: try (f_equal; lia).
all: try reflexivity.
rewrite ?Z.shiftr_div_pow2 by lia. f_equal. symmetry. apply FseWalkKit.swrap32_small.
assert (0 <= W / 2^4 < 2^28) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma hd_chkA : forall m1 tl0 sF j0 j24 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
u8arr asegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C)))) ->
rw_cells asegs m1 MSVP [C4 (Z_to_bv 64 (a_msv0 C))] -> rw_cells asegs m1 TLP [C4 tl0] ->
bytes_at asegs m1 BUF (map (Z_to_bv 8) buf) -> rw_cells asegs m1 SPA (FRA_mid j0 j24) ->
stk asegs m1 (a_lo C) SPA -> munch (rd_WA C) (a_m C) m1 -> wmono asegs (a_m C) m1 -> mem_inv asegs m1 ->
Z.land (le32 buf 0) 15 <= 10 ->
rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (a_rt0 C)) = Ok sF ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
evtF asegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 NC) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f3c) (a_fc C) None m1 (seg_rom asegs)).
Proof.
intros m1 tl0 sF j0 j24 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 ARR HMSV HTL HBUF FRM ST MU WM MI HX RL F1 F2 F3.
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & UT & UB).
Local Ltac2 Set LiaHints.tbl := fun () => "01J0?10644829241.91 11447729446.19111447729446.19311447729451.18211447729451.18712374825302.11014202106942.95 15534906503.11221922089021.93 22736838568.15024362092084.10524362092084.10724362092084.10925261073778.10525261073778.10725261073778.10928022624402.10728022624402.1093132576391.112 32845107966.17233536214416.79 33550629318.11033816247282.10433816247282.10833816247283.10635129193542.10835129193543.10635322926884.83 35943704740.10535943704740.10735943704740.10936401657513.11036401657514.11037694598650.10737694598650.10938361712443.11041404702245.97 43929283719.11245228801809.10945657192820.11048729316279.11348973659295.10050551044676.11050551044678.11250553141838.10750553141838.11151069061334.11052946877380.11053538128661.16155020753293.83 55036003867.10955702594692.10555702594692.10755702594692.10956117678754.10556117678754.10756117678754.10956662150274.10556662150274.10756662150274.10957020354443.11057309684296.17158067894962.11058805924857.11159308692554.10159308692554.10259310676694.16159314923118.99 59328944939.11059588178615.11259655640147.16160700203023.99 60856834888.10560856834888.10760856834888.10961015399828.11061448213823.97 62177758677.87 62976236565.10562976236565.10762976236565.10963872857899.10965977646493.87 65979774378.79 66721607490.11067048124130.11067485074685.1018945588767.87  9448783404.171 9448783404.172 00000400500600700800900=00>00B00O00P00Q00R00S00T00U00V00W00X00]00a00b01Y02F03303G03[03_03`03a03b04O05<05=05>05?06306406806906=07107[08H09209_09`09a09k09l0:00:10:20:30:40:50:60:70:80:90::0:?0:@0:D0;=0<60<@0<F0<G0<H0<M0<N0<O0<P0<Q0<R0<V0<W0<X0<Y0<Z0<^0<_0<`0<a0<b0=V0=W0=a0=eS2HHFFFFFS2HHFS2HHS2T41H2H03H19FFFFFFFFFS3SR0S2HHFS4SP162LO3LOA5SPA124SPA33NC03MS03TL03TL12T43BF03FF03ATRS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS3MS03TL03BF02B83FF0S3MS03TL03BF02B83FF0S2HHFFFS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRFFFS4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3CKTFS2HHFS2RWS4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3CK3S2LO3LOA5SPA123NC03MS03TL03TL13BF03FF03ATRS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRS2LO3LOA5SPA123NC03MS03TL03TL13BF03FF03ATRS2HH2LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATRFFS3CKT1G2H0SS2HHFFFFFFFFFFS3SR3FS2HHS4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3CK31G2G'S4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3CK01G2G'S3CKT1G2G'S2HX1KFSS3SRTSFFFFS2HHSFFFS2HHSSFFS4SP162LO3LOA5SPA124SPA33NC03MS03TL03BF03FF03ATR3CK0SS3CK31G2H0S2B8".
destruct (chkB m1 BUF (BUF + zlen buf) BUF UB ltac:(lia) ltac:(lia)) as (b0 & RDB0 & CK0 & SR0).
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + 3) UB ltac:(lia) ltac:(lia)) as (b3 & RDB3 & CK3 & SR3).
destruct (chk1A m1 TLP (TLP + 4) TLP 4 UT ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (bt & RDBT & CKT & SRT).
destruct (buf_rdA C OK m1 0 HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rdA C OK m1 1 HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rdA C OK m1 2 HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rdA C OK m1 3 HBUF ltac:(lia)) as [RD3 R3].
rewrite Z.add_0_r in RD0.
pose proof (hd_tailA m1 tl0 sF j0 j24) as TAIL. unfold rd_lstA in TAIL.
assert (J3 : forall (y12 y13 : word),
evtF asegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
(Z_to_bv 64 (Z.land (le32 buf 0) 15)) (Z_to_bv 64 (le32 buf 0)) y12 y13 x14 x15 x16 x17
(Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81fac) (a_fc C) None m1 (seg_rom asegs))).
{ intros y12 y13. eapply TAIL; eassumption. }
clear TAIL.
assert (J2 : forall (y10 y11 y12 y13 : word), y10 = Z_to_bv 64 (Z.land (le32 buf 0) 15) -> y11 = Z_to_bv 64 (le32 buf 0) ->
evtF asegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
y10 y11 y12 y13 x14 x15 x16 x17
(Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f9c) (a_fc C) None m1 (seg_rom asegs))).
{ intros y10 y11 y12 y13 -> ->. clear RDB0 CK0 SR0 RDB3 CK3 SR3.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; Z.div_mod_to_equations; lia]. apply J3.
- apply J3. }
clear J3.
assert (J1 : forall (y10 y11 y12 : word),
evtF asegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
y10 y11 y12 x13 x14 x15 x16 x17
(Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f60) (a_fc C) None m1 (seg_rom asegs))).
{ intros y10 y11 y12. clear RDB0 CK0 SR0 RDB3 CK3 SR3.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lbu_raw by assumption.
change (Znth 0 buf + 2 ^ 8 * Znth 1 buf + 2 ^ 16 * Znth 2 buf + 2 ^ 24 * Znth 3 buf) with (le32 buf 0).
pose proof (le32_range buf 0 (buf_all_bytesA C OK)) as RW.
zstep. zstep. zstep.
if_cases K; zify_cond K; rewrite ?(Z.mod_small (le32 buf 0) 18446744073709551616) in * by lia; [| exfalso; lia].
eapply J2; reflexivity. }
clear J2.
assert (J0 : forall (y10 y11 : word),
evtF asegs RNG (rd_mainA_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
y10 y11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 FF) x19 (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 msv1) x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f4c) (a_fc C) None m1 (seg_rom asegs))).
{ intros y10 y11. clear RDB0 CK0 SR0.
zstep. zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J1.
- apply J1. }
clear J1.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply J0.
- apply J0.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Theorem rd_mainA : forall rt msv tlr n (tl0 : word) (j48 : list byte) (RLO RHI : Z)
(x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word),
u8arr asegs (a_m C) NC (u16s (map (Z_to_bv 64) (a_rt0 C))) ->
rw_cells asegs (a_m C) MSVP [C4 (Z_to_bv 64 (a_msv0 C))] ->
rw_cells asegs (a_m C) TLP [C4 tl0] ->
bytes_at asegs (a_m C) BUF (map (Z_to_bv 8) buf) ->
rw_cells asegs (a_m C) SPA [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
stk asegs (a_m C) (a_lo C) SPA -> mem_inv asegs (a_m C) ->
rt_got (a_m C) -> rt_got_ric (a_m C) -> rt_shbase (a_m C) -> rt_inited (a_m C) -> rt_layout (a_m C) -> rt_real_mem (a_m C) ->
(RLO <= NC /\ NC + 2 * zlen (a_rt0 C) <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND) ->
wr_at asegs (a_m C) (shad RLO) (shad RHI - shad RLO) -> rng RNG (shad RLO) (shad RHI - shad RLO) ->
read_ncount_body8 buf msv1 (a_rt0 C) = Ok (rt, msv, tlr, n) ->
evtF asegs RNG (rd_mainA_post C rt msv tlr n)
(MS (mkR x1 (Z_to_bv 64 SPA) (a_gp C) (a_tp C) x5 x6 x7 (Z_to_bv 64 (a_SP C)) (Z_to_bv 64 SPA)
x10 x11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) x13 x14 x15 x16 x17
(Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 (zlen buf))
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
(a_F C) (Z_to_bv 64 0x81f18) (a_fc C) None (a_m C) (seg_rom asegs)).
Proof.
intros rt msv tlr n tl0 j48 RLO RHI x1 x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31
ARR HMSV HTL HBUF FRA0 ST MI GOT RIC SHB INI LAY REAL HULL WRH RSH RB.
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA12 & SPA3 & NC0 & NC1 & N8 & MS0 & MS1 & M4
& TL0 & TL1 & T4 & BF0 & BF1 & B8 & FF0 & FF1 & F64).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB' & RBS).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
destruct (read_body8_inv buf msv1 (a_rt0 C) rt msv tlr n (proj1 HH) RB) as (HL & HX & -> & sF & RL & F1 & F2 & F3 & -> & -> & ->).
pose proof (munch_refl (rd_WA C) (a_m C)) as MU. pose proof (wmono_refl asegs (a_m C)) as WM. unfold rd_WA, RDA_CALLEE in MU.
pose proof SH as (UN & UM & UT & UB).
assert (LWS : length (map (Z_to_bv 64) (a_rt0 C)) = length (a_rt0 C)) by apply length_map.
remember (a_m C) as m eqn:Em.
Local Ltac2 Set LiaHints.tbl := fun () => "00k0?12675873390.10513827271458.11117292095523.12919620497065.10721182078378.11121182111184.10223039802350.10824668810717.10425076071819.12925076071819.13025703506617.10825814844398.10828371444497.12729136719707.10729514832494.10532174006523.11132377744366.10833051759717.12933051759717.1303370534861.111 34029725987.12935214167690.10635561507310.10837211491939.10237504048586.10138606657699.12942744733806.1054473558819.129 44987877980.10545221239098.10845382455823.11148725681100.11149978085870.10850553141826.10250560132980.11150871191190.96 52111889006.10552136437230.10852567164907.10552567164907.10853401708950.126545472525.111  55592350809.96 563227834.105  57018342201.11157498902798.11157622410744.13058477402019.12961560206755.12961942807650.12863035102172.10863331384996.99 65833869487.12765977643946.11165977676752.10266489975826.96 66664437305.10567003974766.1058805124206.105 00000_01X02I02R03N04G05605D07208^09g0:V0;R0;`0<O0=@0=o0>00>l0?h0@Y0@Z0AI0AN0AS0BD0C30Cd0Cl0D40DC0E?0En0F70Fl0G50Gd0HS0HX0H]0Hi0Ii0J20J:0JF0KR0M90Mj0N[0Ng0No0Oh0Pa0Pm0Q50Q>0RG0S60SeS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HM03LWSS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS4HULL3HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS2LO5SPA123LWSS3HU23HU52LO3LOA5SPA123NC03NC13MS03TL03BF03FF03ATR2HL3LWS2LA3HU42HH3HM04SP164SPA32N83MS13TL12T43BF13SNT2M43SNMS3HU23HU43HU53HM04SP162LO3LOA5SPA124SPA33NC03NC12N83MS03MS13TL03TL13BF03BF12B83FF03ATR2HL3LWS2LA3LBS3SNT3SNBS4HULL3HM02LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR2HL3LWS2HB3TL13MS13NC1S4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS2LO5SPA123LWSS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSFS3HU23HU52LO3LOA5SPA123NC03NC13MS03TL03BF03FF03ATR2HL3LWS2LAS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAFS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS3LWSS3LWSS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3LWS2HBS3LWS2HBS3HU52LO3LWS2LAS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS3HM03LWSS3HU53SPK2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HM03LWSS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS3LWSS3LWSS3HU53LWS2LAS3HU23HU53HM02LO3LOA5SPA123NC03NC13MS03TL03BF03FF03ATR2HL3LWS2LAS3HM03LWSS3LWS2HBS3HU53LWS2LAS3HU13HU23HU33HU43HU53HU63HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HU23HU43HU52HH3HM04SP162LO3LOA5SPA124SPA33NC03NC13MS03MS13TL03TL13BF03BF13FF03ATR2HL3LWS2LA3SNM3SNT1HS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU52LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU53LWS2LAS3LWS2HBS4HULL3HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR2HL3LWS2LAS3HU23HU53HM02LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS2LAS3HU53LWS2LAS3LWS2LAS3HM03LWSS4HULL3HM02LO3LOA5SPA123NC03MS03TL03BF03BF13FF03ATR2HL3LWS2HB3TL13MS13NC1S4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWSS4HULL2LO3LOA5SPA123NC03MS03TL03BF03FF03ATR3LWS".
zstep. zstep.
zstep. rewrite (sx32_small (a_msv0 C)) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small msv1) by lia.
zstep. zstep. rewrite (shl32_shr31 msv1) by lia.
zstep. zstep. zstep.
set (bsA := u16s (map (Z_to_bv 64) (a_rt0 C))) in *.
assert (LA : length bsA = (2 * length (a_rt0 C))%nat) by (subst bsA; rewrite u16s_length, LWS; reflexivity).
set (n1 := Z.to_nat (2 * msv1)).
pose proof (rw_cells_of_u8arr _ _ _ _ ARR) as RA. clear ARR.
pose proof (rw_cells_split_CB asegs _ NC [] _ bsA [] [n1; (length bsA - n1)%nat] RA ltac:(cbn [sum_nat]; lia)) as RS.
cbn [app mk_CB_cells] in RS. clear RA.
change [CB n1 (firstn n1 bsA); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]
with ([CB n1 (firstn n1 bsA)] ++ [CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) in RS.
apply rd_rw_cells_appA in RS. destruct RS as [R1 R2]. cbn [cells_size csize Nat.add] in R2.
assert (LBS : Z.of_nat (length (map (Z_to_bv 8) buf)) = zlen buf) by (rewrite length_map; reflexivity).
assert (UN1 : unpoisoned m1 NC (NC + 2 * msv1)).
{ assert (UNx : unpoisoned m1 NC (NC + 2 * zlen (a_rt0 C))) by (apply (inv_shadowA C m1 OK SH); unfold rd_WA, RDA_CALLEE; rewrite <- Em; exact MU).
eapply unpoisoned_sub; [exact UNx| lia| lia]. }
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
| P : rw_cells asegs ?mm NC [CB (Z.to_nat (2 * msv1)) (repeat (Z_to_bv 8 0) (Z.to_nat (2 * msv1)))] |- _ =>
rename mm into m2; rename P into P0
end.
assert (ARR : u8arr asegs m2 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (a_rt0 C))))).
{ pose proof (proj2 (rd_rw_cells_appA asegs m2 NC [CB n1 (repeat (Z_to_bv 8 0) n1)]
[CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))]) (conj P0 R2)) as RJ.
pose proof (rw_cells_merge asegs m2 NC [] [CB n1 (repeat (Z_to_bv 8 0) n1); CB (length bsA - n1) (firstn (length bsA - n1) (skipn n1 bsA))] [] RJ) as RMg.
cbn [app] in RMg.
apply u8arr_of_rw_cells in RMg. cbn [cells_bytes cbytes app] in RMg. rewrite app_nil_r in RMg.
rewrite firstn_all2 in RMg by (rewrite length_skipn; lia).
replace n1 with (2 * Z.to_nat msv1)%nat in RMg by (subst n1; lia).
subst bsA. rewrite u16s_zero_prefix in RMg by lia. exact RMg. }
clear R2 P0.
eapply (hd_chkA m2 tl0 sF); try eassumption.
- unfold rd_WA, RDA_CALLEE. rewrite <- Em. eassumption.
- rewrite <- Em. eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Hdr.
End CANSEC1.
