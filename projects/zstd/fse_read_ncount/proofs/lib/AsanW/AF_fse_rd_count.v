(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseRdKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AF_fse_rd_base AF_fse_rd_cnt1.
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
Section Count.
Variable C : rdctxA.
Variable RNG : footprint.
Hypothesis OK : rd_okA C.
Hypothesis SH : rd_shA C.
Hypothesis RNGS : rd_rngA C RNG.
Variable tl : Z.
Hypothesis Htl : 5 <= tl <= 15.
Variable POST : machine_state -> Prop.
Notation buf := (a_buf C).
Notation msv1 := (a_msv0 C + 1).
Notation BUF := (a_BUF C).
Notation NC := (a_NC C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
Let cnt_hbA := cnt_hbA C RNG OK RNGS POST.
Let cnt_finA := cnt_finA C RNG OK SH RNGS POST.
#[using="rc OK SH RNGS Htl cnt_hbA cnt_finA"] Lemma cnt_tailA : forall s m1 msvw tlw count0 addb fl (x11 x14 x15 x30 : word),
rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
0 <= count0 <= r_remaining s -> 1 <= addb <= 16 ->
x14 = Z_to_bv 64 (if 0 <? count0 then 1 - count0 else -1) ->
rcount_rest buf msv1 s count0 (r_bitCount s + addb) = Ok fl ->
(forall s' m2 y6 y11 y14 y15 y17 y19 y23 y30, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
evtF asegs RNG POST (rd_exitA C s' m2 y6 y11 y14 y15 y17 y19 y23 y30)) ->
(forall s' m2 y12 y14 y15 y19 y30, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
evtF asegs RNG POST (rd_headA C s' m2 y12 y14 y15 y19 y30)) ->
evtF asegs RNG POST (rd_lstA C 0x82204 m1 (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (BUF + r_ip s)) x11 (Z_to_bv 64 addb)
(Z_to_bv 64 (r_charnum s)) x14 x15
(Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (r_threshold s)) (Z_to_bv 64 (count0 + -1))
(Z_to_bv 64 (r_nbBits s)) x30).
Proof.
intros s m1 msvw tlw count0 addb fl x11 x14 x15 x30 INV HC HP HB32 Hc0 Haddb -> RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA1 & SPA2 & NC1 & NC2 & N8 & _).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
set (DR := if 0 <? count0 then 1 - count0 else -1) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00m0?11747638047.80 11758373533.79 12209125738.89 12218182491.82 12223015233.88 14294930078.83 18287563412.87 18289660567.10518360467430.80 2019709518.79  21129812315.82 21129812442.83 21731088147.82 21735462153.88 25164521219.83 25200224666.83 25995870147.10427977500628.82 27979056266.74 28312483310.89 28571733958.83 28574534724.79 29646625861.10531340850685.82 32842119390.85 33015794425.83 33816247282.88 35129193542.88 37410160597.79 39159981841.82 40003757761.82 40829096626.11141051074026.74 47144481757.79 51202358400.80 52344180348.77 55502786765.79 56862664024.11158090943158.89 59190898149.86 59308692554.83 61506009648.88 61556408220.82 61568384390.88 61897962919.82 62477875340.81 63436329801.82 63448764755.88 63940082953.83 64141326532.84 64173732533.88 64185675951.82 64909366221.81 67202285866.84 6756767702.84  67637843975.10468217125103.77 8539574646.79  8935173666.94  8937270827.89  9540508895.77  00000Y01B01C01n02Y02e03R04?04H04Q04l05I05j06K06W06c07508=08f09W09d0:10:I0:U0;A0;j0<W0<k0=T0>I0>U0>a0?H0?U0@>0@g0AW0Ah0Ai0BR0CL0CM0D=0Dm0E;0EK0F60Fc0GL0GX0Ge0H20HD0HP0HY0Hh0IM0J>0Jk0KX0KaS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13ATR3LWSFS3Hc03Rnb5Rrem23Lnc2LO3LOA4SPA13NC13ATR3LWSS3Hc03Rnb5Rrem23Lnc2LO3LOA4SPA13NC13ATR3LWSS3Lnc3LWS2B2S3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWSS3Lnc3LWSS3Lnc3LWSS3Rnb5Rrem23Lnc3NC13RDR3LWSS3Rnb4Rthr3Lnc3NC13RDR3LWS2B1S3Rnb3Lnc2LO3LOA4SPA13NC13ATR3LWSS3Rnb3Lnc2LO3LOA4SPA13NC13ATR3LWSS3Lnc3LWS2B2S3Lnc3LWS2B2S4HB323Lnc3Rbc3LWSS4HB325Haddb3Rnb3Rcn3Lnc3Rip4Rip43Rbc3HM02LO3LOA4SPA13NC13ATR3RDR3LWS2B2S3Hc03Rnb5Rrem23Lnc2LO3LOA4SPA13NC13ATR1HS3Rnb4Rthr4Rrem5Rrem23Lnc2LO3LOA4SPA13NC13ATR3LWSS3Lnc3RDR3LWSS3Lnc3RDR3LWSS3Rnb3Lnc2N83LWS1H2H02H4S3Lnc3LWS2B1S3Rnb4Rthr3Lnc2LO3LOA4SPA13NC13ATR3LWS2B12B2S3Rnb4Rthr3Lnc2LO3LOA4SPA13NC13ATR3LWS2B1S3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWSS3Rnb3Lnc3NC12N83LWSS3Rnb3Rcn3Lnc3HM02LO3LOA4SPA13NC13ATR3LWSS3Rnb3Rcn3Lnc4SP162LO3LOA4SPA14SPA23NC12N83ATR3LWS2CKS3Lnc3LWS2B1S3Lnc3LWS2SRS3Rnb4Rthr4Rrem3Lnc2LO3LOA4SPA13NC13ATRS3Lnc3RDR3LWSS3Rnb3Rcn3Lnc3HM02LO3LOA4SPA13NC13ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13ATR3LWSS4HB325Haddb3Rnb3Lnc3Rbc2LO3LOA4SPA13NC13ATR3LWSS3Lnc3LWS2CK1G2H0FS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13ATR3LWSS3Rnb3Rcn3Lnc4SP162LO3LOA4SPA14SPA23NC12N83ATR3LWS2CK1G2G'FS4HB325Haddb3Rnb3Lnc3Rbc2LO3LOA4SPA13NC13ATR3LWSS4HB325Haddb3Rnb3Lnc3Rbc2LO3LOA4SPA13NC13ATR3LWSS4Rthr3Lnc3LWSS3Lnc3LWS3RDR2H0S3Rnb5Rrem23Lnc2LO3LOA4SPA13NC13ATR3RDR3LWSS3Rnb4Rthr3Lnc2LO3LOA4SPA13NC13ATR3RDR3LWS2B1S3Rnb4Rthr3Lnc2LO3LOA4SPA13NC13ATR3LWS2B1S3Lnc3LWS2L2S3Rcn3Lnc3LWSS3Rcn3Lnc3LWSS3Lnc3LWS1H2H03Hc0S3Lnc3LWS2L2S3Lnc3LWSS5Haddb3Lnc3LWSS3Rnb3Rcn3Lnc2LO3LOA4SPA13NC13ATR3LWSS3Rnb4Rthr4Rrem5Rrem23Lnc2LO3LOA4SPA13NC13ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWSS3Lnc3LWS".
assert (RDR : - 2^31 <= DR <= 0 /\ 1 <= rem + DR) by (subst DR; destruct (Z.ltb_spec 0 count0); lia).
assert (UN : unpoisoned m1 NC (NC + 2 * zlen (a_rt0 C))) by (destruct INV as (_ & _ & _ & _ & _ & _ & _ & MU & _); apply (inv_shadowA C m1 OK SH MU)).
assert (LWS : length (map (Z_to_bv 64) nc) = length (a_rt0 C)) by (rewrite length_map; destruct INV as (_ & LNC & _); exact LNC).
destruct (chk1A m1 NC (NC + 2 * zlen (a_rt0 C)) (NC + 2 * cn) 2 UN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia))
as (b & RDB & CK & SR).
clear UN.
unfold rd_lstA.
zstep. zstep. rewrite (shl32_shr31 cn) by lia.
zstep.
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN : forall (y15 y30 : word),
evtF asegs RNG POST
(MS (mkR (Z_to_bv 64 16843009) (Z_to_bv 64 (a_SPA C)) (a_gp C) (a_tp C) (Z_to_bv 64 18446744071562067968) (Z_to_bv 64 bc) (Z_to_bv 64 23)
(Z_to_bv 64 (a_SP C)) (Z_to_bv 64 (a_SPA C)) (Z_to_bv 64 (BUF + ip)) (Z_to_bv 64 (NC + 2 * cn)) (Z_to_bv 64 addb) (Z_to_bv 64 cn)
(Z_to_bv 64 DR) y15 (Z_to_bv 64 rem) (Z_to_bv 64 thr)
(Z_to_bv 64 (a_FF C)) (Z_to_bv 64 (count0 + -1)) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 252645135) (Z_to_bv 64 nb)
(Z_to_bv 64 2147450880) (Z_to_bv 64 (a_FF C)) (Z_to_bv 64 (Z.shiftr (a_FF C) 3 + 2147450880)) (Z_to_bv 64 (a_msv0 C + 1))
(Z_to_bv 64 (BUF + zlen buf + -7)) (Z_to_bv 64 125613361) y30 (Z_to_bv 64 858993459))
(a_F C) (Z_to_bv 64 0x82220) (a_fc C) None m1 (seg_rom asegs))).
{ intros y15 y30. clear RDB CK SR.
zstep. rewrite (FseWalkKit.swrap32_small (addb + bc)) by lia. replace (addb + bc) with (bc + addb) by lia.
zstep. rewrite (addw_neg DR rem) by lia.
zstep. rewrite (FseWalkKit.swrap32_small (cn + 1)) by lia.
pose proof (u16arr_store_ok asegs _ NC _ cn (wa (NC + 2 * cn)) (proj1 INV) ltac:(rewrite LWS; lia) eq_refl) as SOK.
zstep. clear SOK.
pose proof (rd_invA_store2 C m1 nc msvw tlw cn (count0 + -1) OK INV ltac:(lia)) as INV2.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
change mm with (write_to_mem m1 (wa (NC + 2 * cn)) (le2 (Z_to_bv 64 (count0 + -1)))) end.
remember (write_to_mem m1 (wa (NC + 2 * cn)) (le2 (Z_to_bv 64 (count0 + -1)))) as m eqn:Hm. clear Hm INV.
unfold rcount_rest in RR. cbnR.
replace (count0 - 1) with (count0 + -1) in RR by lia.
rewrite (zstore_ok nc cn) in RR by (unfold FseNCount.Zlength; lia). cbn [bind] in RR.
replace (if 0 <=? count0 + -1 then rem - (count0 + -1) else rem + (count0 + -1)) with (rem + DR) in RR
by (subst DR; destruct (Z.ltb_spec 0 count0); destruct (Z.leb_spec 0 (count0 + -1)); lia).
set (nc' := Zupd cn (to_short (count0 + -1)) nc) in *.
zstep.
if_cases B1; zify_cond B1; rewrite !signed_lit in B1 by lia.
-
replace (rem + DR <? thr) with false in RR by (symmetry; apply Z.ltb_ge; lia). cbn [bind] in RR.
eapply (cnt_finA (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) thr nb (count0 + -1 =? 0)) m msvw tlw (count0 + -1) fl);
cbnR; try eassumption; try lia; try reflexivity.
- replace (rem + DR <? thr) with true in RR by (symmetry; apply Z.ltb_lt; lia).
zstep. zstep.
if_cases B2; zify_cond B2; rewrite ?signed_lit in B2 by lia.
+
replace (rem + DR <=? 1) with true in RR by (symmetry; apply Z.leb_le; lia). cbn [bind] in RR. injection RR as <-.
pose proof (KB (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) thr nb (count0 + -1 =? 0)) m) as KB'.
unfold rd_exitA, rd_lstA in KB'. cbnR.
eapply KB'; [reflexivity| exact INV2|]. unfold rd_brk_okA. cbnR. change (2^31) with 2147483648. lia.
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
pose proof (cnt_hbA (rem + DR) m nc' msvw tlw) as HBK. unfold rd_lstA in HBK.
eapply HBK; [exact INV2| lia|]. intros y11 y14 y15' y17 y23 -> ->.
eapply (cnt_finA (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) (2 ^ Z.log2 (rem + DR)) (Z.log2 (rem + DR) + 1) (count0 + -1 =? 0))
m msvw tlw (count0 + -1) fl);
cbnR; try eassumption; try lia; try reflexivity. }
zstep. if_cases G; zify_cond G.
- zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply JOIN.
- apply JOIN.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS Htl cnt_hbA cnt_finA"] Lemma count_runA : forall s m1 msvw tlw fl (x12 x14 x15 x19 x30 : word),
rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
rcount_block buf msv1 s = Ok fl ->
(forall s' m2 y6 y11 y14 y15 y17 y19 y23 y30, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
evtF asegs RNG POST (rd_exitA C s' m2 y6 y11 y14 y15 y17 y19 y23 y30)) ->
(forall s' m2 y12 y14 y15 y19 y30, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
evtF asegs RNG POST (rd_headA C s' m2 y12 y14 y15 y19 y30)) ->
evtF asegs RNG POST (rd_cntA C s m1 x12 x14 x15 x19 x30).
Proof.
intros s m1 msvw tlw fl x12 x14 x15 x19 x30 INV HC HP HB32 RR KB KC.
rewrite rcount_block_split in RR.
pose proof (fun c0 ab => cnt_tailA s m1 msvw tlw c0 ab fl) as TAIL.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
unfold rcount_decode in RR. unfold rd_cntA.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lstA in TAIL |- *.
assert (RL : 0 <= Z.land bs (thr + -1) < thr).
{ rewrite Ethr. Local Ltac2 Set LiaHints.tbl := fun () => "01>0>1212270779.52 1217008644.65 1217008646.64 15766988587.5415824933547.5218010178223.541840970443.51 19682267231.4820318315843.5221793381037.5124319112985.482593365704.53 2597706485.57 26385907789.5027519251450.5827521348606.6328312483309.6228901832869.5228901832869.5330293992676.5330298595545.5731447655985.543289909708.56 33109390094.5036200720758.5436200720758.5836723521362.5539174078260.5439184184805.5141491202999.5641661078222.5141968874928.7141970972090.6442603369121.5542603369121.5943779307660.5543779307660.594635094036.54 4635094036.58 49439485690.4849441585539.4950933882444.5552074235542.6452076332690.5852076332701.6252076332702.6452457313216.5653508216720.7155338958788.7155338958789.6755670328202.5555670328202.5959175994411.5261588508705.6761588508713.7261815023090.6561815023090.6661815023090.6961815023090.7062003498707.5662042720127.5562042720127.596298778229.58 63863550174.5463863550174.586387321166.50 6755556875.51 68121059962.50826222779.51  8324888243.51 8327131835.52 8944026748.65 8944026750.63 8955943107.52 9706241318.54 9706241318.58 9874335286.51 9880216126.52 00000900B00K00\00c00m01701@01G01Z01_02702J02S02T02U02n03A03T03l04?04H04M04Y04^04c05605N05S05X05k06C06[06f07207<07F07G07H07Q07Z07m08;08I08W08X08b08g09809I09N09S09a09k0:50:M0:e0;80;K0;U0;_0;i0<20<30<40<=0<B0<G0<L0<U0<^0<h0=20=<0=T0=g0>80>IS3Lnc3RbsS3Lnc3RbsS3Lnc3RbsS3Rnb4Rthr3Lnc2RCS3Lnc1KS4Rthr3LncS4Rthr3LncS3Rnb3LncS3Lnc1KS3Rnb4Rthr4Rrem3LncS3LncS3Rnb4Rthr4Rrem3Lnc2RL1KS3Rnb5Rrem23Lnc3RC0S3Rnb3LncFFS3Rnb4Rthr4Rrem5Rrem23LncS3Rnb4Rthr4Rrem3LncS3Rnb4Rthr4Rrem3LncS3Rnb4Rthr4Rrem3Lnc2RL1KS3Rnb5Rrem23Lnc3RC0S3Rnb3LncS3LncS3Rnb3Lnc2P2S3LncS3LncS3Rnb4Rrem3Lnc2RC1HS3Rnb4Ethr4Rrem3Lnc2RL1KS3LncS3LncS3Rnb4Rthr4Rrem3LncS3Rnb4Rthr4Rrem3Lnc2RL1KS3Rnb4Rthr4Rrem3Lnc2RL1KS3Lnc2RL2K2S3Lnc3RC02K2S3Lnc2K21HS3Lnc2K21HFFS3Rnb3LncS3Rnb3LncS3Rnb4Rrem3Lnc2RC1HS3Rnb4Rthr3LncS3Rnb4Rthr3LncS3Rnb4Rthr3LncFS3Lnc1H2H0S3LncS3Rnb4Rthr3Lnc2RCS3Rnb4Rthr3Lnc2RCS3LncS3LncS3Rnb4Rthr3LncS4Rthr3LncS4Rthr3LncS3Rnb4Rthr4Rrem3Lnc2RL1KS3Rnb4Rthr4Rrem3Lnc2RL1KS3Rnb5Rrem23Lnc3RC0S3Rnb5Rrem23Lnc3RC0S3Lnc1H2H0S3Lnc2K21HS3Lnc2K21HS3Rnb3LncFFS3Rnb3LncS3LncS3LncS3LncS3Lnc3RbsS3Lnc3RbsS4Rthr3LncS4Rthr3LncS4Rthr3LncS3Rnb4Rthr4Rrem3Lnc2RL1KS3Rnb5Rrem23Lnc3RC0S3Rnb4Rthr3Lnc2RLS3Rnb4Rthr3Lnc2RC".
replace (2 ^ (nb - 1) + -1) with (2 ^ (nb - 1) - 1) by lia. rewrite land_ones_mod by lia. apply Z.mod_pos_bound. lia. }
assert (P2 : 2 ^ (nb - 1 + 1) = 2 * 2 ^ (nb - 1)) by (apply pow2_S; lia). replace (nb - 1 + 1) with nb in P2 by lia.
assert (RC : 0 <= Z.land bs (thr * 2 + -1) < 2 * thr).
{ rewrite Ethr. replace (2 ^ (nb - 1) * 2 + -1) with (2 ^ nb - 1) by lia.
rewrite land_ones_mod by lia. rewrite <- P2. apply Z.mod_pos_bound. lia. }
replace (thr - 1) with (thr + -1) in RR by lia. replace (2 * thr - 1) with (thr * 2 + -1) in RR by lia.
rewrite (u32_id (thr * 2 + -1 - rem)) in RR by lia.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
zstep. zstep.
zstep. rewrite ?(land_swrap32 bs (thr + -1)) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small (thr * 2 + -1 - rem)) by lia.
zstep. rewrite ?Z.add_0_r. rewrite ?(FseWalkKit.swrap32_small (Z.land bs (thr + -1))) by lia.
zstep.
if_cases K; zify_cond K.
-
replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with false in RR by (symmetry; apply Z.ltb_ge; lia).
cbn [fst snd] in RR.
zstep. rewrite ?(land_swrap32 bs (thr * 2 + -1)) by lia.
zstep. rewrite ?Z.add_0_r. rewrite ?(FseWalkKit.swrap32_small (Z.land bs (thr * 2 + -1))) by lia.
set (c := Z.land bs (thr * 2 + -1)) in *. set (mx := thr * 2 + -1 - rem) in *.
zstep. rewrite (slt_small c thr) by lia.
zstep. zstep. rewrite (mask_sel (c <? thr) mx) by (subst mx; lia).
set (count0 := if thr <=? c then c - mx else c) in *.
assert (EC0 : c - (if c <? thr then 0 else mx) = count0).
{ subst count0. destruct (Z.ltb_spec c thr); destruct (Z.leb_spec thr c); lia. }
assert (RC0 : 0 <= count0 <= rem) by (subst count0 mx; destruct (Z.leb_spec thr c); lia).
zstep. rewrite EC0. rewrite ?(FseWalkKit.swrap32_small count0) by lia.
zstep.
zstep. rewrite ?Z.add_0_r. rewrite ?(FseWalkKit.swrap32_small count0) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small (count0 + -1)) by lia.
zstep.
if_cases K2; zify_lts K2.
+
zstep. zstep. zstep.
eapply (TAIL count0 nb); try eassumption; try lia.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
+ zstep.
eapply (TAIL count0 nb); try eassumption; try lia.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
-
replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with true in RR by (symmetry; apply Z.ltb_lt; lia).
cbn [fst snd] in RR.
set (count0 := Z.land bs (thr + -1)) in *.
zstep.
zstep. rewrite ?Z.add_0_r. rewrite ?(FseWalkKit.swrap32_small count0) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small (count0 + -1)) by lia.
zstep.
if_cases K2; zify_lts K2.
+ zstep.
eapply (TAIL count0 (nb + -1)); try eassumption; try lia.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
+ zstep. zstep. zstep.
eapply (TAIL count0 (nb + -1)); try eassumption; try lia.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Count.
End CANSEC1.
