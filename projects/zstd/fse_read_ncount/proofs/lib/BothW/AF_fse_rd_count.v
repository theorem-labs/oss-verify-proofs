(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseRdKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells AF_fse_rd_base AF_fse_rd_cnt1.
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
#[using="rc OK SH RNGS Htl cnt_hbA cnt_finA"] Lemma cnt_storeA : forall s m1 msvw tlw count0 addb fl (x7 x10 x11 x20 : word),
rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
0 <= count0 <= r_remaining s -> 1 <= addb <= 16 ->
rcount_rest buf msv1 s count0 (r_bitCount s + addb) = Ok fl ->
(forall s' m2 y1 y6 y7 y12 y18 y20 y22 y29, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
evtF bsegs RNG POST (rd_exitA C s' m2 y1 y6 y7 y12 y18 y20 y22 y29)) ->
(forall s' m2 y7 y12 y20 y22 y29, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
evtF bsegs RNG POST (rd_headA C s' m2 y7 y12 y20 y22 y29)) ->
evtF bsegs RNG POST (rd_lstA C 0x82294 m1 (Z_to_bv 64 (r_nbBits s)) (Z_to_bv 64 addb) x7 x10 x11 (Z_to_bv 64 (BUF + r_ip s))
(Z_to_bv 64 (r_charnum s)) (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_threshold s)) x20
(Z_to_bv 64 (count0 + -1)) (Z_to_bv 64 (r_remaining s + (if 0 <? count0 then 1 - count0 else -1)))).
Proof.
intros s m1 msvw tlw count0 addb fl x7 x10 x11 x20 INV HC HP HB32 Hc0 Haddb RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof RNGS as RNGS'. destruct RNGS' as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof (okA_lin C OK) as (HH & HM0 & HM1 & HRT & SP16 & SPK & LO & LOA & SPA1 & SPA2 & NC1 & NC2 & N8 & _).
pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
set (DR := if 0 <? count0 then 1 - count0 else -1) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0110?11747638047.83 11758373149.82 12218182491.85 12220918616.91 14294930078.86 18287563412.90 18289660560.10518360467430.83 21129812315.85 21129812442.86 21731088147.85 21733365520.91 22885170516.82 25164521219.86 25200224666.86 25995870148.10627977500628.85 27979056266.75 28571733958.86 29646625861.10631340850685.85 32842119390.88 33015794425.86 33816247283.90 35129193543.90 36533956797.82 37410159701.82 39159981841.85 40003757761.85 40829096626.11441051074026.75 49431378694.92 50562029892.83 50562030021.82 51202358400.81 52344180348.78 5631513093.82  56862664024.11459190898152.92 59308692554.86 59308693840.82 59308693969.83 61508106806.93 61556408220.85 61557899167.91 61897962919.85 62477875340.84 63436329801.85 63438279498.91 63940082953.86 64141326532.87 64185675951.85 64188412076.91 64909366221.84 66149329423.11867202285866.87 6755771836.83  6756767702.87  67637843968.10668217125103.78 8929349025.82  8935173666.94  8935173666.95  8937270826.95  9540508895.78  00000Y01B01m02X02d03Q04>04G04b05?05`06A06e07107=07O08W09@09M09e0:10:]0;F0<60<F0=10=Z0>Q0>]0>i0?P0?k0@[0AL0B50B^0CN0Cf0DR0EN0F60FF0FG0G70Gg0H50HE0I00I]0JF0JR0J_0Jl0K>0K]0Ki0L20L;0LJ0Lo0M\0NL0O<0Ol0P5S3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13ATR3LWSS3Hc03Rnb5Rrem23Lnc2LO3LOA4SPA13NC13ATR3LWSS3Hc03Rnb5Rrem23Lnc2LO3LOA4SPA13NC13ATR3LWSS3Lnc3LWS2B2S3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWSS3Lnc3LWSS3Rnb5Rrem23Lnc3NC13RDR3LWSS3Rnb4Rthr3Lnc3NC13RDR3LWS2B1S3Rnb3Lnc2LO3LOA4SPA13NC13ATR3LWSS3Rnb3Lnc2LO3LOA4SPA13NC13ATR3LWSS3Rnb3Lnc2LO3LOA4SPA13NC13ATR3LWS2G1S3Lnc3LWS2B2S3Lnc3LWS2B2S4HB323Lnc3Rbc3LWSS4HB325Haddb3Rnb3Rcn3Lnc3Rip4Rip43Rbc3HM02LO3LOA4SPA13NC13ATR3RDR3LWS2B2S3Hc03Rnb5Rrem23Lnc2LO3LOA4SPA13NC13ATR1HS3Lnc3RDR3LWSS3Rnb3Lnc2N83LWS1H2H02H4S3Lnc3LWS2B1S3Rnb4Rthr3Lnc2LO3LOA4SPA13NC13ATR3LWS2B12B2S3Rnb4Rthr3Lnc2LO3LOA4SPA13NC13ATR3LWS2B1S3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWS2G1S3Lnc3NC12N83LWSS3Rnb5Rrem23Lnc2LO3LOA4SPA13NC13ATR3RDR3LWSS3Rnb3Rcn3Lnc3HM02LO3LOA4SPA13NC13ATR3LWSS3Rnb3Lnc4SP162LO3LOA4SPA14SPA23NC12N83ATR3LWS2CK2G12G2S3Lnc3LWS2B1S3Lnc3LWS2SRS3Rnb4Rthr4Rrem3Lnc2LO3LOA4SPA13NC13ATRS3Rnb5Rrem23Lnc3NC13RDR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWS2G1S3Rnb3Rcn3Lnc3HM03HM12LO3LOA4SPA13NC13NC23ATR3LWSS3Rnb3Rcn3Lnc3HM02LO3LOA4SPA13NC13ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13ATR3LWSS4HB325Haddb3Rnb3Lnc3Rbc2LO3LOA4SPA13NC13ATR3LWSS3Lnc3NC13LWS2CK2G21G2H0S3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13ATR3LWS2G1S3Rnb3Lnc4SP162LO3LOA4SPA14SPA23NC12N83ATR3LWS2CK2G12G21G2G'S3Rnb3Rcn3Lnc2LO3LOA4SPA13NC13ATR3LWS2G1S3Lnc3NC13LWS2G2FS4HB325Haddb3Rnb3Lnc3Rbc2LO3LOA4SPA13NC13ATR3LWSS4HB325Haddb3Rnb3Lnc3Rbc2LO3LOA4SPA13NC13ATR3LWSS4Rthr3Lnc3LWSS3Lnc3LWS3RDR2H0S3Rnb5Rrem23Lnc2LO3LOA4SPA13NC13ATR3RDR3LWSS3Rnb4Rthr3Lnc2LO3LOA4SPA13NC13ATR3RDR3LWS2B1S3Rnb4Rthr3Lnc2LO3LOA4SPA13NC13ATR3LWS2B1S3Lnc3LWS2L2S3Rcn3Lnc3LWSS3Rcn3Lnc3LWSS3Lnc3LWS1H2H03Hc0S3Rnb3Lnc3NC12N83LWS2G21H2H02H9S3Lnc3LWS2L2S3Lnc3LWSS3Lnc3LWSS5Haddb3Lnc3LWSS3Rnb3Rcn3Lnc2LO3LOA4SPA13NC13ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWSS3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWS2G1S3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWS2G1S3Rnb3Rcn3Lnc3HM12LO3LOA4SPA13NC13NC23ATR3LWS2G1S3Lnc3LWS".
assert (RDR : - 2^31 <= DR <= 0 /\ 1 <= rem + DR) by (subst DR; destruct (Z.ltb_spec 0 count0); lia).
assert (UN : unpoisoned m1 NC (NC + 2 * zlen (a_rt0 C))) by (destruct INV as (_ & _ & _ & _ & _ & _ & _ & MU & _); apply (inv_shadowA C m1 OK SH MU)).
assert (LWS : length (map (Z_to_bv 64) nc) = length (a_rt0 C)) by (rewrite length_map; destruct INV as (_ & LNC & _); exact LNC).
destruct (chk1A m1 NC (NC + 2 * zlen (a_rt0 C)) (NC + 2 * cn) 2 UN ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia))
as (b & RDB & CK & SR).
clear UN.
unfold rd_lstA.
zstep. zstep. rewrite (shl32_shr31 cn) by lia.
zstep.
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. replace (NC + 2 * cn <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
zstep. change (Z.lxor 1 0) with 1.
zstep. if_false.
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. replace (Z.land (NC + 2 * cn) 1) with 0
by (change 1 with (2^1 - 1); rewrite land_ones_mod by lia; change (2^1) with 2; symmetry; Z.div_mod_to_equations; lia).
zstep. if_false.
zstep. zstep. zstep. rewrite sxb_sval.
assert (JOIN : forall (y11 y20 : word),
evtF bsegs RNG POST
(MS (mkR (Z_to_bv 64 nb) (Z_to_bv 64 (a_SPA C)) (a_gp C) (a_tp C) (Z_to_bv 64 1) (Z_to_bv 64 addb) x7
(Z_to_bv 64 (a_SP C)) (Z_to_bv 64 (a_SPA C)) (Z_to_bv 64 (NC + 2 * cn)) y11 (Z_to_bv 64 (BUF + ip)) (Z_to_bv 64 cn)
(Z_to_bv 64 (BUF + zlen buf + -7)) (Z_to_bv 64 858993459) (Z_to_bv 64 bc) (Z_to_bv 64 4)
(Z_to_bv 64 thr) (Z_to_bv 64 (BUF + zlen buf)) y20 (Z_to_bv 64 NC) (Z_to_bv 64 (count0 + -1)) (Z_to_bv 64 (a_msv0 C + 1))
(Z_to_bv 64 2147450880) (Z_to_bv 64 (a_FF C)) (Z_to_bv 64 (Z.shiftr (a_FF C) 3 + 2147450880)) (Z_to_bv 64 BUF)
(Z_to_bv 64 18446744071562067968) (Z_to_bv 64 (rem + DR)) (Z_to_bv 64 23) (Z_to_bv 64 125613361))
(a_F C) (Z_to_bv 64 0x822cc) (a_fc C) None m1 (seg_rom bsegs))).
{ intros y11 y20. clear RDB CK SR.
zstep. rewrite (FseWalkKit.swrap32_small (bc + addb)) by lia.
zstep. rewrite ?Z.add_0_r. rewrite (FseWalkKit.swrap32_small (rem + DR)) by lia.
zstep. rewrite (FseWalkKit.swrap32_small (cn + 1)) by lia.
pose proof (u16arr_store_ok bsegs _ NC _ cn (wa (NC + 2 * cn)) (proj1 INV) ltac:(rewrite LWS; lia) eq_refl) as SOK.
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
zstep.
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
eapply HBK; [exact INV2| lia|]. intros y1 y6 y7 y10 y18 -> ->.
eapply (cnt_finA (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) (2 ^ Z.log2 (rem + DR)) (Z.log2 (rem + DR) + 1) (count0 + -1 =? 0))
m msvw tlw (count0 + -1) fl);
cbnR; try eassumption; try lia; try reflexivity. }
zstep. if_cases G; zify_cond G.
- zstep. zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply JOIN.
- apply JOIN.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS Htl cnt_hbA cnt_finA"] Lemma cnt_tailA : forall s m1 msvw tlw count0 addb fl (x7 x20 x22 x29 : word),
rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
0 <= count0 <= r_remaining s -> 1 <= addb <= 16 ->
rcount_rest buf msv1 s count0 (r_bitCount s + addb) = Ok fl ->
(forall s' m2 y1 y6 y7 y12 y18 y20 y22 y29, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
evtF bsegs RNG POST (rd_exitA C s' m2 y1 y6 y7 y12 y18 y20 y22 y29)) ->
(forall s' m2 y7 y12 y20 y22 y29, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
evtF bsegs RNG POST (rd_headA C s' m2 y7 y12 y20 y22 y29)) ->
evtF bsegs RNG POST (rd_lstA C 0x82268 m1 (Z_to_bv 64 (r_nbBits s)) (Z_to_bv 64 addb) x7 (Z_to_bv 64 count0) (Z_to_bv 64 (r_remaining s))
(Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (r_charnum s)) (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_threshold s))
x20 x22 x29).
Proof.
intros s m1 msvw tlw count0 addb fl x7 x20 x22 x29 INV HC HP HB32 Hc0 Haddb RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
pose proof (cnt_storeA (FseNCount.mkR nc ip bs bc cn rem thr nb p0) m1 msvw tlw count0 addb fl) as STO.
unfold rd_lstA in STO |- *. cbnR.
Local Ltac2 Set LiaHints.tbl := fun () => "00F0>10762611738.532597687892.51 28314580451.6828314580453.6528314580453.6630298581112.5136202697030.5338659313020.5242134471031.5243062538659.5243067013808.5348189701725.5356650282082.5356656645331.5258509267827.6858509267829.6659308693840.5261812925940.5961815023088.7562471570612.5464903081973.549706306983.52 00000;00N00g01601O01b01g02602?02D02I02^03103D03Y03n04604I04\04a04j05=S3Hc03Lnc1BS3Hc03Rnb5Rrem23LncS3Rnb4Rthr4Rrem5Rrem23LncS3Hc05Rrem23LncS3Rnb4Rthr4Rrem5Rrem23LncS3Hc03Rnb5Rrem23LncS3LncS3Hc05Rrem23LncS3Rnb3LncS3LncS3LncS3Hc03Rnb5Rrem23Lnc1BS3Hc03Rnb5Rrem23LncS3Hc03Rnb5Rrem23LncS3Hc03Rnb5Rrem23Lnc1BS3Hc03Rnb5Rrem23Lnc1BS3Lnc2G1S3Hc03Rnb5Rrem23LncS3Hc03Rnb5Rrem23LncS3LncS3Lnc1B1HS3Hc03Rnb5Rrem23Lnc".
zstep. rewrite (FseWalkKit.swrap32_small (count0 + -1)) by lia.
zstep. rewrite ?Z.add_0_r. rewrite (FseWalkKit.swrap32_small count0) by lia.
zstep. if_cases G1; zify_lts G1; [exfalso; lia|].
zstep. if_cases B; zify_lts B.
-
assert (count0 = 0) by lia. subst count0. change (0 <? 0) with false in STO. cbv iota in STO.
zstep. zstep. sw32 (rem + -1). zstep. if_false.
eapply STO; try eassumption; try lia.
-
zstep. zstep. rewrite (FseWalkKit.swrap32_small (rem - (count0 + -1))) by lia. zstep. if_true.
replace (rem - (count0 + -1)) with (rem + (if 0 <? count0 then 1 - count0 else -1)) by (destruct (Z.ltb_spec 0 count0); lia).
eapply STO; try eassumption; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS Htl cnt_hbA cnt_finA"] Lemma count_runA : forall s m1 msvw tlw fl (x7 x10 x22 : word),
rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
rcount_block buf msv1 s = Ok fl ->
(forall s' m2 y1 y6 y7 y12 y18 y20 y22 y29, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
evtF bsegs RNG POST (rd_exitA C s' m2 y1 y6 y7 y12 y18 y20 y22 y29)) ->
(forall s' m2 y7 y12 y20 y22 y29, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
evtF bsegs RNG POST (rd_headA C s' m2 y7 y12 y20 y22 y29)) ->
evtF bsegs RNG POST (rd_cntA C s m1 x7 x10 x22).
Proof.
intros s m1 msvw tlw fl x7 x10 x22 INV HC HP HB32 RR KB KC.
rewrite rcount_block_split in RR.
pose proof (fun c0 ab => cnt_tailA s m1 msvw tlw c0 ab fl) as TAIL.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
unfold rcount_decode in RR. unfold rd_cntA.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lstA in TAIL |- *.
assert (RL : 0 <= Z.land bs (thr + -1) < thr).
{ rewrite Ethr. Local Ltac2 Set LiaHints.tbl := fun () => "00_0>1212270779.50 1219105792.57 1219105793.57 15824933547.501840970443.49 19682267231.4620318315843.5021793381037.4924319112985.4626385907789.4827519251449.5627521348606.6228894897182.5728901832869.5031244427940.5331441361294.5033109390094.4836717234792.5339184184805.4941053369843.5341661078222.4941968874928.6741970972091.6243060560512.5349439485690.4649441585539.4752074235542.6252076332689.5755336861647.6255338958788.6757611664097.5259175994411.5061070459625.5061897815334.536298778229.53 6387321166.48 67992638357.5368121059962.487645152770.53 826222779.49  8324888243.49 8327131835.50 8946123896.57 8946123897.56 8955943107.50 9874335286.49 9880216126.50 00000900B00K00R00\00e00l01?01D01M01N01O01b02502I02R02^03203703?03R03j04B04G04P04Y04g05505F05W06106?06R06\06e06n07607;07L07Q07Z07c07m08708A08R08cS3Lnc3RbsS3Lnc3RbsS3Lnc3RbsS3Lnc1KS4Rthr3LncS3Rnb3LncS3Lnc1KS3Rnb4Rthr4Rrem3LncS3LncS3Rnb3LncFFS3Rnb4Rthr4Rrem3LncS3Rnb4Rthr4Rrem3LncS3Rnb3Lnc2RL2RC1K2K2S3Rnb3LncS3Rnb3Lnc2P2S3Rnb3Lnc2RL2RC1K2K2S3LncS3Lnc2K2S3Rnb4Rthr4Rrem3LncS3Rnb4Rthr4Rrem3Lnc2RL1KS3Rnb4Rthr4Rrem3Lnc2RL1KS3LncS3Rnb3LncS3Rnb3LncS3Rnb4Rthr3LncS3Rnb4Rthr3LncS3Rnb4Rthr3Lnc2RCS3Rnb4Rthr3Lnc2RCS3Rnb4Rrem5Rrem23Lnc2RC2K2S3Rnb4Rthr3LncS3Rnb4Rrem3Lnc2RL1KS4Rthr3LncS3Rnb3LncS3Rnb3LncS3Lnc2K2S3LncS3Rnb4Rthr3Lnc2RCS3LncS3Lnc3RbsS3Lnc3RbsS4Rthr3LncS4Rthr3LncS4Rthr3LncS3Rnb4Rthr3Lnc2RLS3Rnb4Rthr3Lnc2RC".
replace (2 ^ (nb - 1) + -1) with (2 ^ (nb - 1) - 1) by lia. rewrite land_ones_mod by lia. apply Z.mod_pos_bound. lia. }
assert (P2 : 2 ^ (nb - 1 + 1) = 2 * 2 ^ (nb - 1)) by (apply pow2_S; lia). replace (nb - 1 + 1) with nb in P2 by lia.
assert (RC : 0 <= Z.land bs (thr * 2 + -1) < 2 * thr).
{ rewrite Ethr. replace (2 ^ (nb - 1) * 2 + -1) with (2 ^ nb - 1) by lia.
rewrite land_ones_mod by lia. rewrite <- P2. apply Z.mod_pos_bound. lia. }
replace (thr - 1) with (thr + -1) in RR by lia. replace (2 * thr - 1) with (thr * 2 + -1) in RR by lia.
rewrite (u32_id (thr * 2 + -1 - rem)) in RR by lia.
zstep.
zstep. rewrite (land_swrap32 bs (thr + -1)) by lia.
zstep. rewrite ?Z.add_0_r. rewrite (FseWalkKit.swrap32_small (Z.land bs (thr + -1))) by lia.
zstep. rewrite ?Z.add_0_r. rewrite (FseWalkKit.swrap32_small (thr * 2 + -1 - rem)) by lia.
zstep.
if_cases K; zify_cond K.
-
replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with false in RR by (symmetry; apply Z.ltb_ge; lia).
cbn [fst snd] in RR.
zstep. rewrite (land_swrap32 bs (thr * 2 + -1)) by lia.
zstep. rewrite ?Z.add_0_r. rewrite (FseWalkKit.swrap32_small (Z.land bs (thr * 2 + -1))) by lia.
set (c := Z.land bs (thr * 2 + -1)) in *. set (mx := thr * 2 + -1 - rem) in *.
zstep. if_cases K2; zify_cond K2; rewrite !signed_lit in K2 by lia.
+
replace (thr <=? c) with true in RR by (symmetry; apply Z.leb_le; lia).
zstep. zstep. rewrite (FseWalkKit.swrap32_small (c - mx)) by (subst mx; lia).
zstep. if_false.
zstep. zstep.
eapply (TAIL (c - mx) nb); try eassumption; try lia.
+ replace (thr <=? c) with false in RR by (symmetry; apply Z.leb_gt; lia).
zstep. zstep.
eapply (TAIL c nb); try eassumption; try lia.
-
replace (Z.land bs (thr + -1) <? thr * 2 + -1 - rem) with true in RR by (symmetry; apply Z.ltb_lt; lia).
cbn [fst snd] in RR.
zstep. zstep.
eapply (TAIL (Z.land bs (thr + -1)) (nb + -1)); try eassumption; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Htl"] Lemma cnt_entryA : forall s m1 (x7 x12 x20 x22 x29 : word),
CTL msv1 (a_rt0 C) tl s -> POS buf s ->
(forall y7 y10 y22, evtF bsegs RNG POST (rd_cntA C s m1 y7 y10 y22)) ->
evtF bsegs RNG POST (rd_lstA C 0x82034 m1 (Z_to_bv 64 (r_nbBits s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x7
(Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (r_remaining s)) x12 (Z_to_bv 64 (r_charnum s))
(Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_threshold s)) x20 x22 x29).
Proof.
intros s m1 x7 x12 x20 x22 x29 HC HP K.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_cntA, rd_lstA in *. cbnR.
zstep.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>28314580451.5528314580452.5441658976574.4043062553287.4052074235539.5552074235540.5461167956136.4061586411561.516753455611.40 8946823517.51 00000I00b01501:01H01V01d01n02302AS3Rnb4Rthr4Rrem5Rrem23LncS3Rnb4Rthr4Rrem5Rrem23LncS3Rnb4Rthr4Rrem3LncS3LncS3Rnb4Rthr3LncS3Rnb4Rthr3LncS3Rnb4Rthr3LncS4Rthr3LncS3LncS3Rnb4Rthr3Lnc".
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
zstep. rewrite (FseWalkKit.swrap32_small (thr * 2 + -1)) by lia.
zstep. zstep. rewrite (FseWalkKit.swrap32_small (thr * 2 + -1 - rem)) by lia.
zstep. if_true.
apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Count.
End CANSEC1.
