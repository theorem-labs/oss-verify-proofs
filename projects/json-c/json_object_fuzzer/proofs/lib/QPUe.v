(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcGV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcGV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNLn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtIP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtIP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU91.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU91.
Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section Stat.
Context {RC__ : RC.RunConsts}.
Variable L : JH.heap_layout_A.
Notation HL := (JH.hla_base L).
Notation segs := (HI.hl_segs HL).
Variables bot top : Z.
Variable STATC : list (Z * list byte).

Definition STAT_A (m : word -> option byte) : Prop :=
Forall (fun c => bytes_at segs m (fst c) (snd c)) STATC
/\ (forall g, bot / 8 <= g -> 8 * g < Z.max (top + 2^22) (2^47) -> 8 * g < 2^47 -> bytes_at segs m (g + JH.hl_sb L) [Z_to_bv 8 0])
/\ (forall g, HI.hl_img_lo HL <= 8 * g -> 8 * g + 8 <= HI.hl_img_hi HL ->
bytes_at segs m (g + JH.hl_sb L) [Z_to_bv 8 (JH.img_shadow_val (JH.hl_reg_globals L) g)]).

Definition in_stat (x : Z) : Prop :=
(exists c, In c STATC /\ fst c <= x < fst c + Z.of_nat (length (snd c)))
\/ (exists g, bot / 8 <= g /\ 8 * g < Z.max (top + 2^22) (2^47) /\ 8 * g < 2^47 /\ x = g + JH.hl_sb L)
\/ (exists g, HI.hl_img_lo HL <= 8 * g /\ 8 * g + 8 <= HI.hl_img_hi HL /\ x = g + JH.hl_sb L).

Lemma bytes_at_agree : forall m m' a bs, bytes_at segs m a bs ->
(forall x, a <= x < a + Z.of_nat (length bs) -> m' (wa x) = m (wa x)) -> bytes_at segs m' a bs.
Proof.
intros m m' a bs (H0 & H1 & HB) E. split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (HB i Hi).
unfold mrd. rewrite (E (a + Z.of_nat i)) by lia. reflexivity.
Qed.

Lemma stat_agree : forall m m', STAT_A m -> (forall x, in_stat x -> m' (wa x) = m (wa x)) -> STAT_A m'.
Proof.
intros m m' (SC & SS & SI) E. split; [| split].
- rewrite Forall_forall in SC |- *. intros c Hc. apply (bytes_at_agree m m' _ _ (SC c Hc)). intros x Hx. apply E. left. exists c. auto.
- intros g G1 G2 G3. apply (bytes_at_agree m m' _ _ (SS g G1 G2 G3)). intros x Hx. cbn [length] in Hx. apply E. right; left. exists g. repeat split; try assumption. lia.
- intros g G1 G2. apply (bytes_at_agree m m' _ _ (SI g G1 G2)). intros x Hx. cbn [length] in Hx. apply E. right; right. exists g. repeat split; try assumption. lia.
Qed.

Lemma stat_cells : forall m, STAT_A m -> Forall (fun c => bytes_at segs m (fst c) (snd c)) STATC.
Proof. intros m (SC & _). exact SC. Qed.

Variable DL : dlayout.
Hypothesis L_sb : JH.hl_sb L = kShadowOffset.
Hypothesis RUN_bot : RC.alloc_ceiling <= bot.
Hypothesis L_statc_data : forall c x, In c STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) -> dl_client_data DL x.
Hypothesis L_imgsh_data : forall g, HI.hl_img_lo HL <= 8 * g -> 8 * g + 8 <= HI.hl_img_hi HL -> dl_client_data DL (g + JH.hl_sb L).

Lemma in_stat_dkeep : forall x, in_stat x -> dkeepA RC.alloc_ceiling DL x.
Proof.
intros x [(c & Hc & Hx)|[(g & G1 & G2 & G3 & ->)|(g & G1 & G2 & ->)]].
- left. exact (L_statc_data c x Hc Hx).
- right; left. rewrite L_sb. unfold SH. pose proof (@RC.alloc_ceiling_range RC__) as Hc.
assert (RC.alloc_ceiling / 8 <= bot / 8) by (apply Z.div_le_mono; lia).
change (2^47 / 8) with (2^44). lia.
- left. exact (L_imgsh_data g G1 G2).
Qed.

Hypothesis L_statc_range : forall c x, In c STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) -> 0 <= x < 2^64.
Hypothesis L_img_range : 0 <= HI.hl_img_lo HL /\ HI.hl_img_hi HL <= 2^47.

Lemma in_stat_range : forall x, in_stat x -> 0 <= x < 2^64.
Proof.
intros x [(c & Hc & Hx)|[(g & G1 & G2 & G3 & ->)|(g & G1 & G2 & ->)]]; [exact (L_statc_range c x Hc Hx)| |]; rewrite L_sb; unfold kShadowOffset.
- pose proof (@RC.alloc_ceiling_range RC__) as Hc. assert (0 <= bot / 8) by (apply Z.div_pos; lia). lia.
- destruct L_img_range as [I1 I2]. lia.
Qed.

Theorem stat_asan : forall (m m' : word -> option byte),
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
STAT_A m -> STAT_A m'.
Proof.
intros m m' Hcd ST. apply (stat_agree m m' ST). intros x Hx. exact (proj1 (Hcd x (in_stat_range x Hx) (in_stat_dkeep x Hx))).
Qed.

Variable LA : ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Hypothesis LL0 : ll_ok LA LV 0 PERM0 TMAX NMAX.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis segs_low : forall y : word, kLowEnd < bv_unsigned y < KHI -> find_segment segs (bv_unsigned y) 1 = None.
Variable RE : aentry.
Variable DCo : donor_core RC.alloc_ceiling segs (at_nodeA LV segs) DL.
Variable FR0 : list (Z * Z).
Hypothesis FR0_off : H_off_segments segs (Fof LV FR0).
Variable S : MGI.mng_sig.
Variable BAUX : Z.
Notation H63 := (HEAPA63 L LV PERM0 TMAX NMAX DL RE DCo FR0 S BAUX STAT_A).

Lemma heapA63_stat : forall A LB LM FR B m c, H63 A LB LM FR B m c -> STAT_A m.
Proof. intros A LB LM FR B m c ((g & Lg & H & Bc & Tc & Nc & s & LB0 & HP) & _). do 16 (destruct HP as [_ HP]). exact HP. Qed.

Variable G : word.
Hypothesis L_globals : JH.hl_globals L = [].
Hypothesis L_consts : HI.hl_consts HL = [].
Hypothesis L_can_got : In (HI.hl_got_guard HL, le8 (Z_to_bv 64 (HI.hl_guard HL))) (dl_rtc DL).
Hypothesis L_can_guard : In (HI.hl_guard HL, le8 G) (dl_rtc DL).
Hypothesis L_can_copy : In (HI.hl_tp HL - 16, le8 G) STATC.
Hypothesis L_need_locks : In (HI.hl_libc HL + 3, [Z_to_bv 8 0]) STATC.

Theorem stat_static : JH.hia_static L unit H63 top bot.
Proof.
constructor.
-  intros A LB LM FR B m c _. rewrite L_globals. constructor.
-  intros A LB LM FR B m c HP. pose proof (heapA63_stat _ _ _ _ _ _ _ HP) as (SC & _).
destruct HP as (HP1 & _). pose proof (heapA1_rtc_cells L LA LV PERM0 TMAX NMAX LL0 Hsegs segs_low DL RE DCo FR0 FR0_off S BAUX STAT_A _ _ _ _ _ _ _ HP1) as RT.
rewrite Forall_forall in RT, SC. exists G. split; [exact (RT _ L_can_got)|]. split; [exact (RT _ L_can_guard)| exact (SC _ L_can_copy)].
-  intros A LB LM FR B m c HP. pose proof (heapA63_stat _ _ _ _ _ _ _ HP) as (SC & _). rewrite Forall_forall in SC. exact (SC _ L_need_locks).
-  intros A LB LM FR B m c _. rewrite L_consts. constructor.
-  intros A LB LM FR B m c a n HP Hb Ht H47 Hn. pose proof (heapA63_stat _ _ _ _ _ _ _ HP) as (_ & SS & _).
pose proof (@RC.alloc_ceiling_range RC__) as Hc. unfold JH.shad.
assert (Ha8 : 0 <= a / 8) by (apply Z.div_pos; lia).
assert (Hq : a / 8 <= (a + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (Hq2 : 8 * ((a + n - 1) / 8) <= a + n - 1) by (pose proof (Z.mul_div_le (a + n - 1) 8 ltac:(lia)); lia).
apply (bytes_at_singles L m _ _ (Z_to_bv 8 0)).
+ rewrite L_sb. unfold kShadowOffset. lia.
+ rewrite repeat_length, Z2Nat.id by lia. rewrite L_sb. unfold kShadowOffset. lia.
+ intros i Hi. rewrite repeat_length in Hi. rewrite nth_repeat.
replace (a / 8 + JH.hl_sb L + Z.of_nat i) with (a / 8 + Z.of_nat i + JH.hl_sb L) by lia.
apply SS; [assert (bot / 8 <= a / 8) by (apply Z.div_le_mono; lia); lia| lia| lia].
-  intros A LB LM FR B m c g HP G1 G2. pose proof (heapA63_stat _ _ _ _ _ _ _ HP) as (_ & _ & SI). exact (SI g G1 G2).
Qed.

Hypothesis FR0_ok : Forall (fr_ok LA PERM0) FR0.
Hypothesis IMG_low : MGI.mg_img_hi S <= kLowEnd.
Hypothesis L_statc_hull : forall c x, In c STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) ->
MGI.mg_data_lo S <= x < MGI.mg_img_hi S /\ ~ MGI.in_ivs (MGI.mg_wstat S) x.
Hypothesis RUN_bot8 : bot mod 8 = 0.
Hypothesis RUN_base_stack : exists iv, In iv (lv_base LV) /\ fst iv <= bot /\ 2^47 <= snd iv.
Hypothesis RUN_base_img : exists iv, In iv (lv_base LV) /\ fst iv <= HI.hl_img_lo HL /\ HI.hl_img_hi HL <= snd iv.
Hypothesis L_img8 : HI.hl_img_lo HL mod 8 = 0 /\ HI.hl_img_hi HL <= kLowEnd.

Definition in_stat_sh (g : Z) : Prop :=
(bot / 8 <= g /\ 8 * g < Z.max (top + 2^22) (2^47) /\ 8 * g < 2^47) \/ (HI.hl_img_lo HL <= 8 * g /\ 8 * g + 8 <= HI.hl_img_hi HL).

Lemma stat_sh_band : forall g, in_stat_sh g -> kLowEnd < g + JH.hl_sb L < KHI.
Proof.
intros g Hg. rewrite L_sb. unfold kShadowOffset, kLowEnd, KHI, Qqcs.Mq0.kHighMemBeg. pose proof (@RC.alloc_ceiling_range RC__) as Hc.
destruct Hg as [(G1 & G2 & G3)|(G1 & G2)].
- assert (0 <= bot / 8) by (apply Z.div_pos; lia). lia.
- destruct L_img_range as [I1 I2]. lia.
Qed.

Lemma stat_sh_base : forall g, in_stat_sh g -> exists iv, In iv (lv_base LV) /\ fst iv <= 8 * g < snd iv.
Proof.
intros g [(G1 & G2 & G3)|(G1 & G2)].
- destruct RUN_base_stack as (iv & Hiv & B1 & B2). exists iv. split; [exact Hiv|].
pose proof (Z.div_mod bot 8 ltac:(lia)) as D. rewrite RUN_bot8 in D. lia.
- destruct RUN_base_img as (iv & Hiv & B1 & B2). exists iv. split; [exact Hiv| lia].
Qed.

Lemma stat_sh_notH : forall GH Lg g0 c H m B T N g, KLA LV PERM0 TMAX NMAX GH Lg g0 c H m B T N -> in_stat_sh g ->
H (wa (g + JH.hl_sb L)) = false.
Proof.
intros GH Lg g0 c H m B T N g KL Hg. destruct (H (wa (g + JH.hl_sb L))) eqn:E; [|reflexivity]. exfalso.
pose proof (stat_sh_band g Hg) as Hb. unfold kLowEnd, KHI, Qqcs.Mq0.kHighMemBeg in Hb.
destruct (kla_Hex _ _ _ _ _ _ _ _ _ _ _ _ _ KL _ E) as (b & l & Hin & Hsh).
destruct (kla_groups _ _ _ _ _ _ _ _ _ _ _ _ _ KL b l Hin) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
unfold in_sh, sh_lo, sh_hi in Hsh. rewrite (mmap_len_aligned l G1) in Hsh. rewrite wa_unsigned in Hsh by lia. rewrite L_sb in Hsh.
apply andb_prop in Hsh as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2.
assert (Hb8 : b mod 8 = 0) by (pose proof (Z.div_mod b 4096 ltac:(lia)) as D; rewrite G4 in D; rewrite D; rewrite Z.add_0_r; replace (4096 * (b / 4096)) with (512 * (b / 4096) * 8) by lia; apply Z.mod_mul; lia).
assert (Hl8 : (b + l) mod 8 = 0).
{ pose proof (Z.div_mod b 4096 ltac:(lia)) as D1. pose proof (Z.div_mod l 4096 ltac:(lia)) as D2. rewrite G4 in D1. rewrite G1 in D2.
replace (b + l) with ((512 * (b / 4096) + 512 * (l / 4096)) * 8) by lia. apply Z.mod_mul. lia. }
assert (Hlo : b <= 8 * g).
{ pose proof (Z.div_mod b 8 ltac:(lia)) as D. rewrite Hb8 in D. lia. }
assert (Hhi : 8 * g < b + l).
{ pose proof (Z.div_mod (b + l) 8 ltac:(lia)) as D. rewrite Hl8 in D.
assert ((b + l - 1) / 8 = (b + l) / 8 - 1).
{ replace (b + l - 1) with (((b + l) / 8 - 1) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
lia. }
destruct (stat_sh_base g Hg) as (iv & Hiv & Hr).
exact (proj1 (G8 iv (8 * g) Hiv ltac:(lia)) Hr).
Qed.

Lemma stat_sh_some : forall m g v, in_stat_sh g -> bytes_at segs m (g + JH.hl_sb L) [v] -> m (wa (g + JH.hl_sb L)) <> None.
Proof.
intros m g v Hg (_ & _ & HB). pose proof (stat_sh_band g Hg) as Hb. unfold kLowEnd, KHI, Qqcs.Mq0.kHighMemBeg in Hb.
specialize (HB 0%nat ltac:(cbn; lia)). cbn [nth_error] in HB. rewrite Z.add_0_r in HB. unfold mrd in HB.
destruct (m (wa (g + JH.hl_sb L))); [discriminate|]. exfalso.
unfold seg_rom, memory_read in HB. change (Z.of_N 1) with 1 in HB. rewrite segs_low in HB; [discriminate|].
rewrite wa_unsigned by lia. unfold kLowEnd, KHI, Qqcs.Mq0.kHighMemBeg. lia.
Qed.

Theorem stat_mng : forall Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' (LBx : list MB.block),
KLA LV PERM0 TMAX NMAX (fun _ => false) Lg g c H m B T N ->
KLA LV PERM0 TMAX NMAX (GHof FR0 S m Lg H lo) Lg' g c' H' m2 B' T' N' ->
MI segs (GHof FR0 S m Lg H lo) m H Lg m2 H' Lg' ->
RC.alloc_ceiling <= lo ->
MGI.mpres segs S LBx sp (mrestrict (HG (GHof FR0 S m Lg H lo) H) m) (mrestrict (HG (GHof FR0 S m Lg H lo) H') m2) ->
STAT_A m -> STAT_A m2.
Proof.
intros Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI Hlo PRES ST.
pose proof (@RC.alloc_ceiling_range RC__) as Hc.
assert (SHK : forall g0, in_stat_sh g0 -> forall v, bytes_at segs m (g0 + JH.hl_sb L) [v] -> m2 (wa (g0 + JH.hl_sb L)) = m (wa (g0 + JH.hl_sb L))).
{ intros g0 Hg v HB. apply (proj1 HMI). pose proof (stat_sh_band g0 Hg) as Hb. unfold kLowEnd, KHI, Qqcs.Mq0.kHighMemBeg in Hb.
unfold GHof. pose proof (stat_sh_some m g0 v Hg HB) as Hm. destruct (m (wa (g0 + JH.hl_sb L))) as [b0|]; [| contradiction]. cbn [andb].
rewrite (stat_sh_notH _ Lg g c H m B T N g0 KL Hg). cbn [negb]. rewrite andb_true_r. apply negb_true_iff.
unfold PK. rewrite wa_unsigned by lia. unfold kLowEnd in IMG_low.
destruct (Z.ltb_spec (g0 + JH.hl_sb L) (MGI.mg_img_hi S)) as [X|X]; [lia|]. rewrite andb_false_r. cbn [orb].
destruct (Z.leb_spec lo (g0 + JH.hl_sb L)) as [X2|X2]; [lia|]. cbn [orb].
destruct (in_regs (QtIP.FRof FR0 Lg) (wa (g0 + JH.hl_sb L))) eqn:ER; [| reflexivity]. exfalso.
destruct (regs_place LA LV PERM0 TMAX NMAX LL0 FR0 FR0_ok _ Lg g c H m B T N _ KL ER) as (rlo & rhi & Hz & Hp).
rewrite wa_unsigned in Hz by lia. unfold kLowEnd, KHI, Qqcs.Mq0.kHighMemBeg in Hp. lia. }
apply (stat_agree m m2 ST). intros x [(cl & Hcl & Hx)|[(g0 & G1 & G2 & G3 & ->)|(g0 & G1 & G2 & ->)]].
-
destruct (L_statc_hull cl x Hcl Hx) as [Hh Hnw]. pose proof (L_statc_range cl x Hcl Hx) as Hr.
destruct (PRES x Hr ltac:(right; left; split; [exact Hh| exact Hnw])) as [E _].
assert (NH : forall H0 GH0 Lg0 g1 c0 m0 B0 T0 N0, KLA LV PERM0 TMAX NMAX GH0 Lg0 g1 c0 H0 m0 B0 T0 N0 -> HG (GHof FR0 S m Lg H lo) H0 (wa x) = false).
{ intros H0 GH0 Lg0 g1 c0 m0 B0 T0 N0 K0. unfold HG. apply orb_false_iff. split.
- destruct (H0 (wa x)) eqn:EH; [|reflexivity]. pose proof (kla_Hrange _ _ _ _ _ _ _ _ _ _ _ _ _ K0 _ EH) as R. rewrite wa_unsigned in R by lia. unfold kLowEnd in *. lia.
- unfold GHof, PK. rewrite wa_unsigned by lia.
destruct (Z.leb_spec (MGI.mg_data_lo S) x) as [X|X]; [| lia]. destruct (Z.ltb_spec x (MGI.mg_img_hi S)) as [X2|X2]; [| lia].
cbn [andb orb negb]. rewrite andb_false_r. reflexivity. }
unfold mrestrict in E. rewrite (NH H _ _ _ _ _ _ _ _ KL), (NH H' _ _ _ _ _ _ _ _ KL') in E. exact E.
- destruct ST as (_ & SS & _). exact (SHK g0 (or_introl (conj G1 (conj G2 G3))) _ (SS g0 G1 G2 G3)).
- destruct ST as (_ & _ & SI). exact (SHK g0 (or_intror (conj G1 G2)) _ (SI g0 G1 G2)).
Qed.

Hypothesis L_statc_priv : forall c x, In c STATC -> fst c <= x < fst c + Z.of_nat (length (snd c)) ->
HI.hl_img_lo HL <= x < HI.hl_img_hi HL /\ ~ HI.hl_client_static HL x /\ ~ HI.hl_scratch HL x.

Theorem stat_client : forall m m' : word -> option byte,
(forall x, stat_like L bot x -> m' (wa x) = m (wa x)) -> STAT_A m -> STAT_A m'.
Proof.
intros m m' Hs ST. apply (stat_agree m m' ST). intros x [(cl & Hcl & Hx)|[(g & G1 & G2 & G3 & ->)|(g & G1 & G2 & ->)]]; apply Hs.
- left. exact (L_statc_priv cl x Hcl Hx).
- right. exists g. split; [reflexivity|]. left. split; [exact G1| exact G3].
- right. exists g. split; [reflexivity|]. right. split; assumption.
Qed.
End Stat.
