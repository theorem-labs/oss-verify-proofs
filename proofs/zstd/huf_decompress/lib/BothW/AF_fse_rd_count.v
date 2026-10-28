(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AF_fse_rd_base AF_fse_rd_cnt1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
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
evtF bsegs RNG POST (rd_lstA C 0x96f3c m1 (Z_to_bv 64 (r_nbBits s)) (Z_to_bv 64 addb) x7 x10 x11 (Z_to_bv 64 (BUF + r_ip s))
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
(a_F C) (Z_to_bv 64 0x96f74) (a_fc C) None m1 (seg_rom bsegs))).
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
Qed.
#[using="rc OK SH RNGS Htl cnt_hbA cnt_finA"] Lemma cnt_tailA : forall s m1 msvw tlw count0 addb fl (x7 x20 x22 x29 : word),
rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
0 <= count0 <= r_remaining s -> 1 <= addb <= 16 ->
rcount_rest buf msv1 s count0 (r_bitCount s + addb) = Ok fl ->
(forall s' m2 y1 y6 y7 y12 y18 y20 y22 y29, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
evtF bsegs RNG POST (rd_exitA C s' m2 y1 y6 y7 y12 y18 y20 y22 y29)) ->
(forall s' m2 y7 y12 y20 y22 y29, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
evtF bsegs RNG POST (rd_headA C s' m2 y7 y12 y20 y22 y29)) ->
evtF bsegs RNG POST (rd_lstA C 0x96f10 m1 (Z_to_bv 64 (r_nbBits s)) (Z_to_bv 64 addb) x7 (Z_to_bv 64 count0) (Z_to_bv 64 (r_remaining s))
(Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (r_charnum s)) (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_threshold s))
x20 x22 x29).
Proof.
intros s m1 msvw tlw count0 addb fl x7 x20 x22 x29 INV HC HP HB32 Hc0 Haddb RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
pose proof (cnt_storeA (FseNCount.mkR nc ip bs bc cn rem thr nb p0) m1 msvw tlw count0 addb fl) as STO.
unfold rd_lstA in STO |- *. cbnR.
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
Qed.
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
{ rewrite Ethr.
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
Qed.
#[using="Htl"] Lemma cnt_entryA : forall s m1 (x7 x12 x20 x22 x29 : word),
CTL msv1 (a_rt0 C) tl s -> POS buf s ->
(forall y7 y10 y22, evtF bsegs RNG POST (rd_cntA C s m1 y7 y10 y22)) ->
evtF bsegs RNG POST (rd_lstA C 0x96cdc m1 (Z_to_bv 64 (r_nbBits s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x7
(Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (r_remaining s)) x12 (Z_to_bv 64 (r_charnum s))
(Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_threshold s)) x20 x22 x29).
Proof.
intros s m1 x7 x12 x20 x22 x29 HC HP K.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_cntA, rd_lstA in *. cbnR.
zstep.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
zstep. rewrite (FseWalkKit.swrap32_small (thr * 2 + -1)) by lia.
zstep. zstep. rewrite (FseWalkKit.swrap32_small (thr * 2 + -1 - rem)) by lia.
zstep. if_true.
apply K.
Qed.
End Count.
End CANSEC1.
