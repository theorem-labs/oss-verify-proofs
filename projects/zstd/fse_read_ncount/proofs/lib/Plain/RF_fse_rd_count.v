(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_rd_base RF_fse_rd_cnt1.
Import ListNotations.
Open Scope Z_scope.
Section Count.
Variable C : rdctx.
Hypothesis OK : rd_ok C.
Variable tl : Z.
Hypothesis Htl : 5 <= tl <= 15.
Variable POST : machine_state -> Prop.
Notation buf := (c_buf C).
Notation msv1 := (c_msv0 C + 1).
Notation BUF := (c_BUF C).
Notation NC := (c_NC C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
Ltac zify_lts H :=
unfold bv_lts in H; rewrite !signed_lit in H by lia;
first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H
| apply negb_true_iff in H; apply Z.ltb_ge in H | apply negb_false_iff in H; apply Z.ltb_lt in H ].
Let cnt_hb := cnt_hb C POST.
Let cnt_fin := cnt_fin C OK POST.
#[using="OK Htl cnt_hb cnt_fin"] Lemma cnt_tail : forall s m1 msvw tlw count0 addb fl (x1 x26 x27 : word),
rd_inv C m1 (r_nc s) msvw tlw -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
0 <= count0 <= r_remaining s -> 1 <= addb <= 16 ->
x26 = Z_to_bv 64 (if 0 <? count0 then 1 - count0 else -1) ->
rcount_rest buf msv1 s count0 (r_bitCount s + addb) = Ok fl ->
(forall s' m2 y1 y20 y23 y24 y26 y27 y30, fl = Brk s' -> rd_inv C m2 (r_nc s') msvw tlw -> rd_brk_ok C s' ->
evt psegs POST (rd_exit C s' m2 y1 y20 y23 y24 y26 y27 y30)) ->
(forall s' m2 y1 y25 y26 y27, fl = Cont s' -> rd_inv C m2 (r_nc s') msvw tlw ->
evt psegs POST (rd_head C s' m2 y1 y25 y26 y27)) ->
evt psegs POST (rd_lst C 0x140f4 m1 x1 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (r_threshold s))
(Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 addb) (Z_to_bv 64 (count0 + -1)) (Z_to_bv 64 (r_charnum s))
x26 x27 (Z_to_bv 64 (r_nbBits s))).
Proof.
intros s m1 msvw tlw count0 addb fl x1 x26 x27 INV HC HP HB32 Hc0 Haddb -> RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB).
unfold RD_STACK in *.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
set (DR := if 0 <? count0 then 1 - count0 else -1) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00f0>11747506463.8311757697184.8411758203192.8312209125738.8112218182491.7712220109797.8014294930078.7818287563419.8018289660562.8318360335846.832020125420.71 21129812315.7721129812442.7821731088147.7721733093293.8025164521219.7825200224666.7825995870147.9627977500628.7727979056266.7028312483310.8128571733958.7828574102758.7129043664697.8431340850685.7732842119390.8033015794425.7837410785143.7140003757761.7741051074026.7042170389469.8447144848255.7149700823848.8451200243584.7152579781329.8455502415983.7158090943158.8161506009662.8161556408220.7761558654754.8061897962919.7762477875340.8463436329801.7763438531575.8063940082953.7864141326532.7964185675951.7764187598865.8064909366221.8465607626313.8467202285866.796756767702.79 67637843975.968538909140.71 00000E00Z00o01001;01F01J01_02402A02F02Q02^02_02`02d02h03603j04;04P04U04^05305705C05L05Y05]05l06M06V06o07<07Q07e07f07g08708G08M08U08`08m09609:09K09\09f0:B0:F0:G0:R0:gS3LNC3Rcn3Lnc3HM13LWSS3LNC3Rcn3Lnc3HM13LWSS3LNC3Rcn3Lnc3HM13LWSFS3Hc05Rrem2S3Hc05Rrem2S2B2S3Rcn3Lnc3HM13HN03HN1S3Rcn3Lnc3HM13HN03HN1S3LNC3Lnc3LWSS3LncS5Rrem23RDRS4Rthr3RDR2B1SSS2B2S2B2S4HB323Lnc3RbcS3LNC4HB325Haddb3Rcn3Lnc3Rip4Rip43Rbc3HM03RDR3LWS2B2S3Hc05Rrem23Lnc1HS4Rthr4Rrem5Rrem23LncS3RDRS3Lnc3RDRS3LNC3Rcn3Lnc3HN03LWSS2B1S4Rthr2B12B2S4Rthr2B1S3Rcn3Lnc3HM0S2B1S4Rthr4Rrem3LncS3LNC3Rcn3Lnc3HM13SNB3LWS3SNT3SNMS3Lnc3RDRS3LNC3Rcn3Lnc3HM13HN13LWSS3Rcn3Lnc3HM0S3LNC3Rcn3Lnc3HM13LWSS4HB325Haddb3Lnc3RbcFFS4HB325Haddb3RbcS4HB325Haddb3RbcS4RthrS3RDR2H0S5Rrem23RDRS4Rthr3RDR2B1S4Rthr2B1S2L2S3LNC3Rcn3Lnc3LWSS3LNC3Rcn3Lnc3LWSS1H2H03Hc0S3LNC3Rcn3Lnc3HM12LO3SNS3LWSS2L2SS5Haddb3LncS4Rthr4Rrem5Rrem23Lnc".
assert (RDR : - 2^31 <= DR <= 0 /\ 1 <= rem + DR) by (subst DR; destruct (Z.ltb_spec 0 count0); lia).
unfold rd_lst.
zstep. rewrite (swrap32_small (addb + bc)) by lia. replace (addb + bc) with (bc + addb) by lia.
zstep. rewrite (addw_neg DR rem) by lia.
zstep. rewrite (swrap32_small (cn + 1)) by lia.
zstep. zstep. rewrite (shl32_shr31 cn) by lia.
zstep.
destruct INV as (ARR & LNC & HBUF & HMSV & HTL & (junk8 & FR) & ST & MU & WM & MI). unfold rd_W, RD_STACK in MU.
assert (LWS : length (map (Z_to_bv 64) nc) = length (c_rt0 C)) by (rewrite length_map; exact LNC).
assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
pose proof (u16arr_store_ok psegs _ NC _ cn (wa (NC + 2 * cn)) ARR ltac:(rewrite LWS; lia) eq_refl) as SOK.
zstep.
pose proof (u16arr_write psegs _ NC _ cn (Z_to_bv 64 (count0 + -1)) ARR ltac:(rewrite LWS; lia)) as ARR2.
clear ARR. store_done.
rewrite u16s_upd_short in ARR2.
unfold rcount_rest in RR. cbnR.
replace (count0 - 1) with (count0 + -1) in RR by lia.
rewrite (zstore_ok nc cn) in RR by (unfold FseNCount.Zlength; lia). cbn [bind] in RR.
replace (if 0 <=? count0 + -1 then rem - (count0 + -1) else rem + (count0 + -1)) with (rem + DR) in RR
by (subst DR; destruct (Z.ltb_spec 0 count0); destruct (Z.leb_spec 0 (count0 + -1)); lia).
set (nc' := Zupd cn (to_short (count0 + -1)) nc) in *.
assert (INV2 : rd_inv C m (nc') msvw tlw).
{ unfold rd_inv, rd_W, RD_STACK. split; [exact ARR2|]. split; [subst nc'; rewrite Zupd_length; exact LNC|].
split; [exact HBUF|]. split; [exact HMSV|]. split; [exact HTL|]. split; [exists junk8; exact FR|].
split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
clear ARR2 HBUF HMSV HTL FR ST MU WM MI.
zstep.
if_cases B1; zify_cond B1; rewrite !signed_lit in B1 by lia.
-
replace (rem + DR <? thr) with false in RR by (symmetry; apply Z.ltb_ge; lia). cbn [bind] in RR.
eapply (cnt_fin (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) thr nb (count0 + -1 =? 0)) m msvw tlw (count0 + -1) fl);
cbnR; try eassumption; try lia; try reflexivity.
- replace (rem + DR <? thr) with true in RR by (symmetry; apply Z.ltb_lt; lia).
zstep.
if_cases B2; zify_cond B2; rewrite ?signed_lit in B2 by lia.
+
replace (rem + DR <=? 1) with true in RR by (symmetry; apply Z.leb_le; lia). cbn [bind] in RR. injection RR as <-.
pose proof (KB (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) thr nb (count0 + -1 =? 0)) m) as KB'.
unfold rd_exit, rd_lst in KB'. cbnR.
zstep.
eapply KB'; [reflexivity| exact INV2|]. unfold rd_brk_ok. cbnR. change (2^31) with 2147483648. lia.
+ replace (rem + DR <=? 1) with false in RR by (symmetry; apply Z.leb_gt; lia).
unfold highbit32, assert in RR.
replace ((0 <? rem + DR) && (rem + DR <? 2 ^ 32)) with true in RR
by (symmetry; apply andb_true_iff; split; [apply Z.ltb_lt| apply Z.ltb_lt]; lia).
cbn [bind] in RR.
assert (L2 : 1 <= Z.log2 (rem + DR) < 15).
{ split; [apply Z.log2_le_pow2; lia| apply Z.log2_lt_pow2; lia]. }
replace (Z.log2 (rem + DR) + 1 - 1) with (Z.log2 (rem + DR)) in RR by lia.
replace ((0 <=? Z.log2 (rem + DR)) && (Z.log2 (rem + DR) <? 31)) with true in RR
by (symmetry; apply andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
cbn [bind] in RR.
pose proof (cnt_hb (rem + DR) m) as HBK. unfold rd_lst in HBK.
eapply HBK; [lia|]. intros y20 y30 -> ->.
eapply (cnt_fin (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) (2 ^ Z.log2 (rem + DR)) (Z.log2 (rem + DR) + 1) (count0 + -1 =? 0)) m msvw tlw (count0 + -1) fl);
cbnR; try eassumption; try lia; try reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK Htl cnt_hb cnt_fin"] Lemma count_run : forall s m1 msvw tlw fl (x1 x23 x26 x27 : word),
rd_inv C m1 (r_nc s) msvw tlw -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
rcount_block buf msv1 s = Ok fl ->
(forall s' m2 y1 y20 y23 y24 y26 y27 y30, fl = Brk s' -> rd_inv C m2 (r_nc s') msvw tlw -> rd_brk_ok C s' ->
evt psegs POST (rd_exit C s' m2 y1 y20 y23 y24 y26 y27 y30)) ->
(forall s' m2 y1 y25 y26 y27, fl = Cont s' -> rd_inv C m2 (r_nc s') msvw tlw ->
evt psegs POST (rd_head C s' m2 y1 y25 y26 y27)) ->
evt psegs POST (rd_cnt C s m1 x1 x23 x26 x27).
Proof.
intros s m1 msvw tlw fl x1 x23 x26 x27 INV HC HP HB32 RR KB KC.
rewrite rcount_block_split in RR.
pose proof (fun c0 ab => cnt_tail s m1 msvw tlw c0 ab fl) as TAIL.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
unfold rcount_decode in RR. unfold rd_cnt.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lst in TAIL |- *.
assert (RL : 0 <= Z.land bs (thr + -1) < thr).
{ rewrite Ethr. Local Ltac2 Set LiaHints.tbl := fun () => "01A0>1212270779.47 1219105805.57 1219105806.57 15766988587.4915824933547.4718010178223.491840970443.46 19682267231.4320318315843.4721793381037.4624319112985.432593365704.48 2597706485.52 26385907789.4527519251445.5827521348605.5928314580454.5828901832869.4728901832869.4830293992676.4830298595545.5231447655985.493289909708.51 33109390094.4536200720758.4936200720758.5336723521362.5039174078260.4939184184805.4641491202999.5141661078222.4641968874928.6641968874930.6142603369121.5042603369121.5443779307660.5043779307660.544635094036.49 4635094036.53 49435495706.4649439485690.4349441585539.4450933882444.5052074235542.5852074235542.6152076332701.5852076332702.5752457313216.5153508216720.6655336861646.5955338958788.6655670328202.5055670328202.5459175994411.4761586411562.5961588508705.6961812925946.5861812925946.6261815023088.6261815023090.6161815023090.6461815023090.6562003498707.5162042720127.5062042720127.546298778229.53 63863550174.4963863550174.536387321166.45 6755556875.46 68121059962.45826222779.46  8324888243.46 8327131835.47 8944026749.59 8946123893.57 8955943107.47 9706241318.49 9706241318.53 9874335286.46 9880216126.47 00000900B00K00X00_00i01301B01I01X01]02102@02R02S02T02i03803G03[03j04304804@04E04J04Y04h04m05205A05U05i06406@06J06T06U06V06`06i07207A07B07C07M07W07a07f08308@08E08J08T08^08h09<09K09_0:30:B0:Q0:[0:e0:o0;80;90;:0;C0;H0;M0;R0;[0;d0;n0<80<B0<V0<e0=20=?S3Lnc3RbsS3Lnc3RbsS3Lnc3RbsS4Rthr3Lnc2RCS3Lnc1KS4Rthr3LncS4Rthr3LncS4Ethr4Rthr3LncS3Lnc1KS4Rthr4Rrem3LncS3LncS4Rthr4Rrem3Lnc2RL1KS5Rrem23Lnc3RC0S4Ethr4Rthr3Lnc2P2FFS4Rthr4Rrem5Rrem23LncS4Rthr4Rrem3LncS4Rthr4Rrem3LncS4Rthr4Rrem3Lnc2RL1KS5Rrem23Lnc3RC0S3Rnb3LncS3LncS3Lnc2P2S3LncS3LncS4Rrem3Lnc2RC1HS4Rrem3Lnc2RL1KS3LncS3LncS4Rthr4Rrem3LncS4Rthr4Rrem3Lnc2RL1KS4Rthr4Rrem3Lnc2RL1KS3Lnc2RL2K2S3Lnc3RC02K2S3Lnc2K21HS3Lnc2K21HFFS4Rthr3LncS3Rnb3LncS3Rnb3LncS3Lnc2RL2RC1K1HFFS4Rthr3LncS4Rthr3LncS3Lnc1H2H0S3LncS4Rthr3Lnc2RCS4Rthr3Lnc2RCS3LncS3LncS4Rthr3LncS4Rthr3LncS4Rthr3LncS4Rthr4Rrem3Lnc2RL1KS5Rrem23Lnc3RC0S4Rthr4Rrem3Lnc2RL1KS4Rthr4Rrem3Lnc2RL1KS5Rrem23Lnc3RC0S5Rrem23Lnc3RC0S3Lnc1H2H0S3Lnc2K21HS3Lnc2K21HS3Rnb3LncFFS3Rnb3LncS3LncS3LncS3LncS3Lnc3RbsS3Lnc3RbsS4Rthr3LncS4Rthr3LncS4Rthr3LncS4Rthr4Rrem3Lnc2RL1KS5Rrem23Lnc3RC0S4Rthr3Lnc2RLS4Rthr3Lnc2RC".
replace (2 ^ (nb - 1) + -1) with (2 ^ (nb - 1) - 1) by lia. rewrite land_ones_mod by lia. apply Z.mod_pos_bound. lia. }
assert (P2 : 2 ^ (nb - 1 + 1) = 2 * 2 ^ (nb - 1)) by (apply pow2_S; lia). replace (nb - 1 + 1) with nb in P2 by lia.
assert (RC : 0 <= Z.land bs (thr * 2 + -1) < 2 * thr).
{ rewrite Ethr. replace (2 ^ (nb - 1) * 2 + -1) with (2 ^ nb - 1) by lia.
rewrite land_ones_mod by lia. rewrite <- P2. apply Z.mod_pos_bound. lia. }
replace (thr - 1) with (thr + -1) in RR by lia. replace (2 * thr - 1) with (thr * 2 + -1) in RR by lia.
rewrite (u32_id (thr * 2 + -1 - rem)) in RR by lia.
zstep. zstep. zstep. zstep.
rewrite (land_swrap32 bs (thr + -1)) by lia.
zstep.
rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
rewrite (Z.mod_small (thr * 2 + -1)) by lia. rewrite (swrap32_small (thr * 2 + -1 - rem)) by lia.
zstep.
rewrite Z.add_0_r. rewrite (swrap32_small (Z.land bs (thr + -1))) by lia.
zstep.
if_cases K; zify_cond K.
-
replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with false in RR by (symmetry; apply Z.ltb_ge; lia).
cbn [fst snd] in RR.
zstep. rewrite (land_swrap32 bs (thr * 2 + -1)) by lia.
zstep. rewrite Z.add_0_r. rewrite (swrap32_small (Z.land bs (thr * 2 + -1))) by lia.
set (c := Z.land bs (thr * 2 + -1)) in *. set (mx := thr * 2 + -1 - rem) in *.
zstep. rewrite (slt_small c thr) by lia.
zstep. zstep. rewrite (mask_sel (c <? thr) mx) by (subst mx; lia).
set (count0 := if thr <=? c then c - mx else c) in *.
assert (EC0 : c - (if c <? thr then 0 else mx) = count0).
{ subst count0. destruct (Z.ltb_spec c thr); destruct (Z.leb_spec thr c); lia. }
assert (RC0 : 0 <= count0 <= rem) by (subst count0 mx; destruct (Z.leb_spec thr c); lia).
zstep. rewrite EC0. rewrite (swrap32_small count0) by lia.
zstep. zstep. rewrite Z.add_0_r. rewrite (swrap32_small count0) by lia.
zstep. rewrite (swrap32_small (count0 + -1)) by lia.
zstep.
if_cases K2; zify_lts K2.
+
zstep. zstep.
eapply (TAIL count0 nb); try eassumption; try lia.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
+ zstep.
eapply (TAIL count0 nb); try eassumption; try lia.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
-
replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with true in RR by (symmetry; apply Z.ltb_lt; lia).
cbn [fst snd] in RR.
set (count0 := Z.land bs (thr + -1)) in *.
zstep. zstep. rewrite Z.add_0_r. rewrite (swrap32_small count0) by lia.
zstep. rewrite (swrap32_small (count0 + -1)) by lia.
zstep.
if_cases K2; zify_lts K2.
+ zstep.
eapply (TAIL count0 (nb + -1)); try eassumption; try lia.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
+ zstep. zstep.
eapply (TAIL count0 (nb + -1)); try eassumption; try lia.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Count.
