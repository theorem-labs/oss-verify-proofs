(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_base RF_fse_rd_cnt1 RdChk.
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
Ltac chkeq := lazymatch goal with |- context [bv_eqb (Z_to_bv 64 ?A) (Z_to_bv 64 ?B)] =>
let EQ := fresh "EQ" in
assert (EQ : Z_to_bv 64 A = Z_to_bv 64 B);
[ apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64);
rewrite ?swrap32_eq; Z.div_mod_to_equations; lia
| rewrite EQ; clear EQ; if_true ] end.
Let cnt_hb := cnt_hb C POST.
Let cnt_fin := cnt_fin C OK POST.
#[using="OK Htl cnt_hb cnt_fin"] Lemma cnt_store : forall s m1 msvw tlw count0 addb fl (x6 x13 x14 x16 x24 x28 : word),
rd_inv C m1 (r_nc s) msvw tlw -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
0 <= count0 <= r_remaining s -> 1 <= addb <= 16 ->
x13 = Z_to_bv 64 (r_remaining s + (if 0 <? count0 then 1 - count0 else -1)) -> x16 = Z_to_bv 64 (count0 + -1) ->
rcount_rest buf msv1 s count0 (r_bitCount s + addb) = Ok fl ->
(forall s' m2 y1 y6 y13 y14 y16 y25 y28 y29, fl = Brk s' -> rd_inv C m2 (r_nc s') msvw tlw -> rd_brk_ok C s' ->
evt usegs POST (rd_exit C s' m2 y1 y6 y13 y14 y16 y25 y28 y29)) ->
(forall s' m2 y1 y6 y14 y16 y28, fl = Cont s' -> rd_inv C m2 (r_nc s') msvw tlw ->
evt usegs POST (rd_head C s' m2 y1 y6 y14 y16 y28)) ->
evt usegs POST (rd_lst C 0x142cc m1 (Z_to_bv 64 (BUF + r_ip s)) x6 (Z_to_bv 64 (r_charnum s)) x13 x14 x16
x24 (Z_to_bv 64 (r_threshold s)) (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 addb) x28 (Z_to_bv 64 (r_nbBits s))).
Proof.
intros s m1 msvw tlw count0 addb fl x6 x13 x14 x16 x24 x28 INV HC HP HB32 Hc0 Haddb -> -> RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & (NP0 & NP2) & (MP0 & MP4) & (TP0 & TP4) & BP0).
unfold RD_STACK in *.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
set (DR := if 0 <? count0 then 1 - count0 else -1) in *.
assert (RDR : - 2^31 <= DR <= 0 /\ 1 <= rem + DR) by (subst DR; destruct (Z.ltb_spec 0 count0); lia).
unfold rd_lst.
zstep. zstep. rewrite (shl32_shr31 cn) by lia.
zstep.
zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. zstep. zstep.
replace (0 <? NC) with true by (symmetry; apply Z.ltb_lt; lia).
replace (NC + 2 * cn <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. change (Z.lxor 1 0) with 1.
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
zstep. replace (Z.land (NC + 2 * cn) 1) with ((NC + 2 * cn) mod 2) by (symmetry; exact (Z.land_ones (NC + 2 * cn) 1 ltac:(lia))).
assert (EV : (NC + 2 * cn) mod 2 = 0) by (Z.div_mod_to_equations; lia).
zstep. if_cases G4; zify_cond G4; [exfalso; apply G4; exact EV|].
zstep. rewrite (swrap32_small (bc + addb)) by lia.
zstep. sw32 (rem + DR).
zstep. rewrite (swrap32_small (cn + 1)) by lia.
destruct INV as (ARR & LNC & HBUF & HMSV & HTL & (junk0 & junk16 & FR) & ST & MU & WM & MI). unfold rd_W, RD_STACK in MU.
assert (LWS : length (map (Z_to_bv 64) nc) = length (c_rt0 C)) by (rewrite length_map; exact LNC).
assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
pose proof (u16arr_store_ok usegs _ NC _ cn (wa (NC + 2 * cn)) ARR ltac:(rewrite LWS; lia) eq_refl) as SOK.
zstep.
pose proof (u16arr_write usegs _ NC _ cn (Z_to_bv 64 (count0 + -1)) ARR ltac:(rewrite LWS; lia)) as ARR2.
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
split; [exact HBUF|]. split; [exact HMSV|]. split; [exact HTL|]. split; [exists junk0, junk16; exact FR|].
split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
clear ARR2 HBUF HMSV HTL FR ST MU WM MI.
zstep.
if_cases B1; zify_lts B1.
-
replace (rem + DR <? thr) with false in RR by (symmetry; apply Z.ltb_ge; lia). cbn [bind] in RR.
eapply (cnt_fin (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) thr nb (count0 + -1 =? 0)) m msvw tlw (count0 + -1) fl);
cbnR; try eassumption; try lia; try reflexivity.
- replace (rem + DR <? thr) with true in RR by (symmetry; apply Z.ltb_lt; lia).
zstep. zstep.
if_cases B2; zify_lts B2.
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
eapply HBK; [lia|]. intros y13 y14 y25 y29 -> ->.
eapply (cnt_fin (FseNCount.mkR nc' ip bs (bc + addb) (cn + 1) (rem + DR) (2 ^ Z.log2 (rem + DR)) (Z.log2 (rem + DR) + 1) (count0 + -1 =? 0)) m msvw tlw (count0 + -1) fl);
cbnR; try eassumption; try lia; try reflexivity.
Qed.
#[using="OK Htl cnt_hb cnt_fin"] Lemma cnt_tail : forall s m1 msvw tlw count0 addb fl (x6 x13 x14 x16 x27 x28 : word),
rd_inv C m1 (r_nc s) msvw tlw -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
0 <= count0 <= r_remaining s -> 1 <= addb <= 16 ->
x14 = Z_to_bv 64 count0 -> x27 = Z_to_bv 64 addb ->
rcount_rest buf msv1 s count0 (r_bitCount s + addb) = Ok fl ->
(forall s' m2 y1 y6 y13 y14 y16 y25 y28 y29, fl = Brk s' -> rd_inv C m2 (r_nc s') msvw tlw -> rd_brk_ok C s' ->
evt usegs POST (rd_exit C s' m2 y1 y6 y13 y14 y16 y25 y28 y29)) ->
(forall s' m2 y1 y6 y14 y16 y28, fl = Cont s' -> rd_inv C m2 (r_nc s') msvw tlw ->
evt usegs POST (rd_head C s' m2 y1 y6 y14 y16 y28)) ->
evt usegs POST (rd_lst C 0x142a0 m1 (Z_to_bv 64 (BUF + r_ip s)) x6 (Z_to_bv 64 (r_charnum s)) x13 x14 x16
(Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (r_threshold s)) (Z_to_bv 64 (r_bitCount s)) x27 x28 (Z_to_bv 64 (r_nbBits s))).
Proof.
intros s m1 msvw tlw count0 addb fl x6 x13 x14 x16 x27 x28 INV HC HP HB32 Hc0 Haddb -> -> RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof (cnt_store s m1 msvw tlw count0 addb fl) as ST.
unfold rd_lst in ST |- *.
zstep. rewrite (swrap32_small (count0 + -1)) by lia.
zstep. sw32 count0.
zstep. if_cases B1; zify_lts B1; [exfalso; lia|].
zstep. if_cases B2; zify_lts B2.
-
zstep. zstep. zstep. chk64.
eapply ST; try eassumption; try lia; try reflexivity.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
-
zstep. zstep. zstep. chkeq.
eapply ST; try eassumption; try lia; try reflexivity.
f_equal. destruct (Z.ltb_spec 0 count0); lia.
Qed.
#[using="OK Htl cnt_hb cnt_fin"] Lemma count_run : forall s m1 msvw tlw fl (x6 x14 x16 x27 : word),
rd_inv C m1 (r_nc s) msvw tlw -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
x16 = Z_to_bv 64 (2 * r_threshold s - 1) ->
rcount_block buf msv1 s = Ok fl ->
(forall s' m2 y1 y6 y13 y14 y16 y25 y28 y29, fl = Brk s' -> rd_inv C m2 (r_nc s') msvw tlw -> rd_brk_ok C s' ->
evt usegs POST (rd_exit C s' m2 y1 y6 y13 y14 y16 y25 y28 y29)) ->
(forall s' m2 y1 y6 y14 y16 y28, fl = Cont s' -> rd_inv C m2 (r_nc s') msvw tlw ->
evt usegs POST (rd_head C s' m2 y1 y6 y14 y16 y28)) ->
evt usegs POST (rd_cnt C s m1 x6 x14 x16 x27).
Proof.
intros s m1 msvw tlw fl x6 x14 x16 x27 INV HC HP HB32 -> RR KB KC.
rewrite rcount_block_split in RR.
pose proof (fun c0 ab => cnt_tail s m1 msvw tlw c0 ab fl) as TAIL.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
unfold rcount_decode in RR. unfold rd_cnt.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lst in TAIL |- *.
assert (RL : 0 <= Z.land bs (thr + -1) < thr).
{ rewrite Ethr.
replace (2 ^ (nb - 1) + -1) with (2 ^ (nb - 1) - 1) by lia. rewrite land_ones_mod by lia. apply Z.mod_pos_bound. lia. }
assert (P2 : 2 ^ (nb - 1 + 1) = 2 * 2 ^ (nb - 1)) by (apply pow2_S; lia). replace (nb - 1 + 1) with nb in P2 by lia.
assert (RC : 0 <= Z.land bs (2 * thr - 1) < 2 * thr).
{ rewrite Ethr. replace (2 * 2 ^ (nb - 1) - 1) with (2 ^ nb - 1) by lia.
rewrite land_ones_mod by lia. rewrite <- P2. apply Z.mod_pos_bound. lia. }
replace (thr - 1) with (thr + -1) in RR by lia.
rewrite (u32_id (2 * thr - 1 - rem)) in RR by lia.
zstep.
zstep. rewrite (land_swrap32 bs (thr + -1)) by lia.
zstep. sw32 (Z.land bs (thr + -1)).
zstep. sw32 (2 * thr - 1 - rem).
zstep.
if_cases K; zify_cond K.
-
replace (Z.land bs (thr + -1) <? 2 * thr - 1 - rem) with false in RR by (symmetry; apply Z.ltb_ge; lia).
cbn [fst snd] in RR.
set (c := Z.land bs (2 * thr - 1)) in *. set (mx := 2 * thr - 1 - rem) in *.
zstep. rewrite (land_swrap32 bs (2 * thr - 1)) by lia. fold c.
zstep. sw32 c.
zstep. if_cases K2; zify_lts K2.
+
replace (thr <=? c) with true in RR by (symmetry; apply Z.leb_le; lia).
zstep. zstep. zstep. chk64.
zstep. zstep.
eapply (TAIL (c - mx) nb); try eassumption; try lia; try reflexivity.
+
replace (thr <=? c) with false in RR by (symmetry; apply Z.leb_gt; lia).
zstep. zstep.
eapply (TAIL c nb); try eassumption; try lia; try reflexivity.
-
replace (Z.land bs (thr + -1) <? 2 * thr - 1 - rem) with true in RR by (symmetry; apply Z.ltb_lt; lia).
cbn [fst snd] in RR.
zstep. zstep.
eapply (TAIL (Z.land bs (thr + -1)) (nb + -1)); try eassumption; try lia; try reflexivity.
Qed.
End Count.
