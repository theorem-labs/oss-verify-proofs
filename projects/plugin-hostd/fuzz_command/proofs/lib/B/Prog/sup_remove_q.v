(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AF0x.v, with its module paths changed; 177 of its 210 lines of code are new or changed and 539 lines of the source are left out. *)
(* sup_remove's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan,
   BASE + AF_sup_remove = 0x8b258), the post at answer's return 0x8b3a0 (SR_T) from the posts of record(), arg_s()
   and answer() (sr_q_stmt, sup_remove_s1.v): no symbolic execution.

   Between record's return and answer's entry, arg_s adds one fresh block (p, ni) (ni = |dec id| + 1) that the
   recorder owns ((p, ni) :: O1), apart from every block live at arg_s's entry; it may be a block record() freed
   (Fr, a part of O). answer frees the old answer (start old: 0, or the start of one of the recorder's blocks at
   its entry) and adds the copies p1 (the recorder's) and p2 (the caller's) of the text t. The live bytes and the
   meter add up as LIVE_SUP_REMOVE = LIVE_ARG_S + LIVE_ANSWER and XM_SUP_REMOVE = XM_RECORD + XM_ARG_S + XM_ANSWER
   (sup_remove_c.v:77, :84).

   The block lemmas over AR and the recorder's representation are copies of the B sup_remove_all walk's
   lib/B/Prog/sup_remove_all_s1.v (bsra_answer_cell, bsra_in_answer, bsra_call_blocks, bsra_rep_blocks,
   bsra_blk, bsra_same_start, bsra_nodup2, bsra_rep_live), under sr_q_ names; the 8-byte sum is B's YF0x.v
   le_bytes8_sum. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecAns sup_remove_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---- the answer cell's value is the one 8-byte value it holds (YF0x.v:475 le_bytes8_sum) ---- *)
Lemma sr_q_le8 : forall z, 0 <= z < 2 ^ 64 ->
YG0f.le_byte z 8 0 + 256 * (YG0f.le_byte z 8 1 + 256 * (YG0f.le_byte z 8 2 + 256 * (YG0f.le_byte z 8 3 +
  256 * (YG0f.le_byte z 8 4 + 256 * (YG0f.le_byte z 8 5 + 256 * (YG0f.le_byte z 8 6 + 256 * YG0f.le_byte z 8 7)))))) = z.
Proof.
intros z Hz. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with (256 * 256).
change (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256). change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256). change (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256).
rewrite Z.div_1_r. rewrite <- !Z.div_div by lia.
assert (H7 : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
{ change (2 ^ 64) with (256 * 256 * 256 * 256 * 256 * 256 * 256 * 256) in Hz.
repeat (apply Z.div_lt_upper_bound; [lia|]). lia. }
rewrite (Z.mod_small (z / 256 / 256 / 256 / 256 / 256 / 256 / 256)) by (split; [repeat (apply Z.div_pos; [|lia]); lia | exact H7]).
pose proof (Z.div_mod z 256 ltac:(lia)) as E0.
pose proof (Z.div_mod (z / 256) 256 ltac:(lia)) as E1.
pose proof (Z.div_mod (z / 256 / 256) 256 ltac:(lia)) as E2.
pose proof (Z.div_mod (z / 256 / 256 / 256) 256 ltac:(lia)) as E3.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E4.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E5.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E6.
lia.
Qed.

Lemma sr_q_aval_uniq : forall (rd : reader) a v v', aval_mem rd a 8 v -> aval_mem rd a 8 v' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
intros rd a v v' H H' Hv Hv'.
assert (E : forall k, (k < 8)%nat -> YG0f.le_byte v 8 k = YG0f.le_byte v' 8 k).
{ intros k Hk. pose proof (H k Hk) as E1. pose proof (H' k Hk) as E2. rewrite E1 in E2.
  injection E2 as E2. exact E2. }
rewrite <- (sr_q_le8 v Hv), <- (sr_q_le8 v' Hv').
rewrite !E by lia. reflexivity.
Qed.

(* ---- the block conjuncts of sr_post, over the block lists alone ----
   bl0: the entry's blocks; blc: record's return, the entry's less the blocks Fr that record() freed (all of them
   the recorder's, O); bl3: arg_s's return, blc and arg_s's fresh (p, ni), which is not one of blc; bl4: answer's
   return; O1, (p, ni) :: O1, O': the recorder's blocks at record's return, at answer's entry and after it; old: the
   answer the recorder held at answer's entry (0 or the start of one of (p, ni) :: O1); p1, p2: answer's two fresh
   copies of the text (n bytes), p2 the caller's. *)
Lemma sr_q_blocks : forall (bl0 blc bl3 bl4 O O1 O' Fr : list (Z * Z)) (p ni old p1 p2 n : Z),
  Permutation bl0 (blc ++ Fr) ->
  (forall pn, In pn Fr -> In pn O) ->
  (forall pn, In pn O1 <-> In pn O /\ ~ In pn Fr) ->
  (forall pn, In pn O1 -> In pn blc) ->
  (forall pn, In pn blc -> In pn Fr -> False) ->
  Permutation bl3 ((p, ni) :: blc) ->
  ~ In (p, ni) blc ->
  (forall pn, In pn bl3 -> fst pn <> 0) ->
  (old = 0 \/ exists pn0, In pn0 ((p, ni) :: O1) /\ old = fst pn0) ->
  (forall q a b, In (q, a) bl3 -> In (q, b) bl3 -> a = b) ->
  (forall q a b, In (q, a) bl4 -> In (q, b) bl4 -> a = b) ->
  p1 <> p2 ->
  (forall pn, In pn bl3 -> fst pn <> old -> pn <> (p1, n) /\ pn <> (p2, n)) ->
  (forall pn, In pn bl4 <-> (In pn bl3 /\ fst pn <> old) \/ pn = (p1, n) \/ pn = (p2, n)) ->
  (forall pn, In pn O' <-> (In pn ((p, ni) :: O1) /\ fst pn <> old) \/ pn = (p1, n)) ->
  (forall pn, In pn O' -> In pn bl0 -> In pn O) /\
  (forall pn, In pn bl4 -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = (p2, n)) /\
  (forall pn, In pn bl0 -> ~ In pn O -> In pn bl4) /\
  In (p2, n) bl4 /\
  (In (p2, n) bl0 -> In (p2, n) O) /\
  ~ In p2 (map fst O').
Proof.
intros bl0 blc bl3 bl4 O O1 O' Fr p ni old p1 p2 n HP HF HO1 HO1c ND HP3 Hpn H0 OLD SAME3 SAME4 Gne Gfr GBL GO.
assert (Dz : forall x y : Z * Z, {x = y} + {x <> y}) by (intros x y; decide equality; apply Z.eq_dec).
assert (I3 : forall pn, In pn bl3 <-> pn = (p, ni) \/ In pn blc).
{ intros pn. split; intros H.
  - apply (Permutation_in _ HP3) in H. destruct H as [H | H]; [left; symmetry; exact H | right; exact H].
  - apply (Permutation_in _ (Permutation_sym HP3)). destruct H as [H | H]; [left; symmetry; exact H | right; exact H]. }
assert (I0 : forall pn, In pn bl0 -> In pn blc \/ In pn Fr).
{ intros pn H. apply (Permutation_in _ HP) in H. apply in_app_iff in H. exact H. }
assert (Ic0 : forall pn, In pn blc -> In pn bl0).
{ intros pn H. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact H. }
(* a block of record's return that starts at the old answer is one of the recorder's O1 *)
assert (K : forall pn, In pn blc -> fst pn = old -> In pn O1).
{ intros pn Hc Eo.
  assert (Hc3 : In pn bl3) by (apply I3; right; exact Hc).
  destruct OLD as [E0 | (pn0 & Hp0 & E0)].
  - exfalso. exact (H0 pn Hc3 (eq_trans Eo E0)).
  - assert (Hp03 : In pn0 bl3).
    { apply I3. destruct Hp0 as [Hp0 | Hp0]; [left; symmetry; exact Hp0 | right; exact (HO1c _ Hp0)]. }
    destruct pn as [q a], pn0 as [q0 b]. cbn [fst] in Eo, E0.
    subst old. subst q0.
    pose proof (SAME3 q a b Hc3 Hp03) as Eab. subst b.
    destruct Hp0 as [Hp0 | Hp0]; [|exact Hp0].
    exfalso. apply Hpn. rewrite Hp0. exact Hc. }
split.
{ intros pn Ho Hb. apply GO in Ho as [([Ep | Hp] & Hno) | Ep].
  - subst pn. destruct (I0 _ Hb) as [Hc | Hf]; [exfalso; exact (Hpn Hc) | exact (HF _ Hf)].
  - exact (proj1 (proj1 (HO1 _) Hp)).
  - subst pn. destruct (I0 _ Hb) as [Hc | Hf]; [|exact (HF _ Hf)].
    destruct (Z.eq_dec p1 old) as [Eo | Eo].
    + exact (proj1 (proj1 (HO1 _) (K _ Hc Eo))).
    + exfalso. exact (proj1 (Gfr (p1, n) (proj2 (I3 _) (or_intror Hc)) Eo) eq_refl). }
split.
{ intros pn Hb4. apply GBL in Hb4 as [(H3 & Ho) | [Ep | Ep]].
  - apply I3 in H3 as [Ep | Hc].
    + right; left. apply GO. left. split; [left; symmetry; exact Ep | exact Ho].
    + destruct (in_dec Dz pn O1) as [H1 | H1].
      * right; left. apply GO. left. split; [right; exact H1 | exact Ho].
      * left. split; [exact (Ic0 _ Hc)|]. intros HO.
        destruct (in_dec Dz pn Fr) as [Hf | Hf]; [exact (ND _ Hc Hf) | exact (H1 (proj2 (HO1 _) (conj HO Hf)))].
  - right; left. apply GO. right. exact Ep.
  - right; right. exact Ep. }
split.
{ intros pn Hb Hno. destruct (I0 _ Hb) as [Hc | Hf]; [|exfalso; exact (Hno (HF _ Hf))].
  apply GBL. left. split; [apply I3; right; exact Hc|].
  intros Eo. exact (Hno (proj1 (proj1 (HO1 _) (K _ Hc Eo)))). }
split; [apply GBL; right; right; reflexivity|].
split.
{ intros Hb. destruct (I0 _ Hb) as [Hc | Hf]; [|exact (HF _ Hf)].
  destruct (Z.eq_dec p2 old) as [Eo | Eo].
  - exact (proj1 (proj1 (HO1 _) (K _ Hc Eo))).
  - exfalso. exact (proj2 (Gfr (p2, n) (proj2 (I3 _) (or_intror Hc)) Eo) eq_refl). }
intros Hm. apply in_map_iff in Hm as ([q a] & Eq & Hq). cbn [fst] in Eq. subst q.
apply GO in Hq as [(Hq & Ho) | Ep].
- assert (Hq3 : In (p2, a) bl3).
  { apply I3. destruct Hq as [Hq | Hq]; [left; symmetry; exact Hq | right; exact (HO1c _ Hq)]. }
  assert (H4a : In (p2, a) bl4) by (apply GBL; left; split; [exact Hq3 | exact Ho]).
  assert (H4n : In (p2, n) bl4) by (apply GBL; right; right; reflexivity).
  pose proof (SAME4 p2 a n H4a H4n) as Ea. subst a.
  exact (proj2 (Gfr _ Hq3 Ho) eq_refl).
- injection Ep as E1 _. exact (Gne (eq_sym E1)).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.

(* ---- over AR (sup_remove_all_s1.v:219-264; rca_blk and rca_same_start are CmdRecAns's) ---- *)

(* no block is listed twice in a permutation of the live blocks *)
Lemma sr_q_nodup2 : forall ly S (W : world SEGS) mem md (l1 l2 : list (Z * Z)) pn, AR SEGS B ly S W mem md ->
  Permutation (ablocks B ly S) (l1 ++ l2) -> In pn l1 -> In pn l2 -> False.
Proof.
intros ly S W mem md l1 l2 pn HAR HP H1 H2.
apply in_split in H1 as (a1 & b1 & E1). apply in_split in H2 as (a2 & b2 & E2). subst l1 l2.
assert (HP2 : Permutation (pn :: pn :: (a1 ++ b1 ++ a2 ++ b2)) ((a1 ++ pn :: b1) ++ a2 ++ pn :: b2)).
{ rewrite <- app_assoc. cbn [app]. apply Permutation_cons_app.
  assert (E : a1 ++ b1 ++ a2 ++ pn :: b2 = (a1 ++ b1 ++ a2) ++ pn :: b2) by (rewrite <- !app_assoc; reflexivity).
  rewrite E. apply Permutation_cons_app. rewrite <- !app_assoc. apply Permutation_refl. }
pose proof (Permutation_trans HP (Permutation_sym HP2)) as HP3.
pose proof (sep_blocks_perm SEGS B LAWS ly S W mem md pn pn _ HAR HP3) as Hd.
assert (Hin : In pn (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP3)); left; reflexivity).
destruct pn as [p n]. destruct (rca_blk (PI := PI) B LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & R1).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the recorder's blocks are live blocks *)
Lemma sr_q_rep_live : forall ly S rd R O pn, rec_repA B ly S rd R O -> In pn O -> In pn (ablocks B ly S).
Proof. intros ly S rd R O pn (Q & HQ & HO) Hin. exact (rca_rep_blocks _ _ _ _ _ _ pn HQ (proj1 (HO pn) Hin)). Qed.

(* ---- the post at answer's return ---- *)
Theorem sr_q : sr_q_stmt B MT.
Proof.
unfold sr_q_stmt.
intros ly S W regs mem md ch id R O lyc Sc Wc memc mdc Fr O1 ly3 S3 p Wa mema mda old ly4 S4 W4 regs4 mem4 md4 p1 p2 O'.
cbv zeta.
intros HPRE HARc HRECD Hp HP3 HAP HBB3 HMLE3 HAR3 HREP3 Hold Hob HAR4 G10 G4096 Gne Gfr GBL GREP GO GSTR GBB GMLE.
destruct HPRE as (HAFN & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HAFN as (HAR & _).
destruct HRECD as (HPERM & _ & HFR & HREP1 & HO1 & HBBc & HMLEc).
assert (HO1c : forall pn, In pn O1 -> In pn (ablocks B lyc Sc))
  by (intros pn Hin; exact (sr_q_rep_live _ _ _ _ _ pn HREP1 Hin)).
assert (ND : forall pn, In pn (ablocks B lyc Sc) -> In pn Fr -> False)
  by (intros pn H1 H2; exact (sr_q_nodup2 ly S W mem md (ablocks B lyc Sc) Fr pn HAR HPERM H1 H2)).
(* arg_s's block is apart from every block live at its entry, so it is none of them *)
assert (Hpn : ~ In (p, Z.of_nat (length (dec id)) + 1) (ablocks B lyc Sc)).
{ intros Hin. rewrite Forall_forall in HAP. specialize (HAP _ Hin). cbn [fst snd] in HAP.
  unfold iv_apart in HAP. lia. }
assert (H0 : forall pn, In pn (ablocks B ly3 S3) -> fst pn <> 0).
{ intros [q a] Hq. destruct (rca_blk (PI := PI) B LAWS ly3 S3 Wa mema mda q a HAR3 Hq) as (B1 & _). cbn [fst]. lia. }
(* old: 0 or the start of one of the recorder's blocks at answer's entry *)
assert (OLD : old = 0 \/ exists pn0, In pn0 ((p, Z.of_nat (length (dec id)) + 1) :: O1) /\ old = fst pn0).
{ pose proof HREP3 as (Q & HQ & HQO).
  destruct (rca_answer_cell _ _ _ _ HQ) as (old' & Hold' & Hc').
  assert (OLD' : old' = 0 \/ exists pn0, In pn0 ((p, Z.of_nat (length (dec id)) + 1) :: O1) /\ old' = fst pn0).
  { destruct Hc' as [(_ & E0) | (pn0 & Ea & E0)]; [left; exact E0|]. right. exists pn0. split; [|exact E0].
    apply HQO. apply rca_in_answer. rewrite Ea. cbn [oblk]. left. reflexivity. }
  assert (Hob' : 0 <= old' < 2 ^ 64).
  { destruct OLD' as [E0 | ([q a] & Hq & E0)]; [rewrite E0; lia|]. rewrite E0. cbn [fst].
    pose proof (sr_q_rep_live _ _ _ _ _ _ HREP3 Hq) as Hq3.
    destruct (rca_blk (PI := PI) B LAWS ly3 S3 Wa mema mda q a HAR3 Hq3) as (B1 & B2 & _ & B4).
    pose proof (@alloc_ceiling_lt rc). lia. }
  replace old with old' by exact (sr_q_aval_uniq _ _ _ _ Hold' Hold Hob' Hob).
  exact OLD'. }
unfold sr_post. cbv beta.
exists (fst (rec_answer (rec_record R REC_REMOVE [dec id]) (REC_REMOVE, [dec id]) REC_MOD_HOST_SHAPE true)), O', p2.
split; [unfold sup_remove_m, rec_stub; apply surjective_pairing|].
cbv zeta.
destruct (sr_q_blocks (ablocks B ly S) (ablocks B lyc Sc) (ablocks B ly3 S3) (ablocks B ly4 S4) O O1 O' Fr
  p _ old p1 p2 _ HPERM HFR HO1 HO1c ND HP3 Hpn H0 OLD
  (fun q a b => rca_same_start (PI := PI) B LAWS ly3 S3 Wa mema mda q a b HAR3)
  (fun q a b => rca_same_start (PI := PI) B LAWS ly4 S4 W4 mem4 md4 q a b HAR4)
  Gne Gfr GBL GO) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
split; [exact G10|]. split; [exact G4096|]. split; [exact GREP|].
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
split; [exact Q6|]. split; [exact GSTR|]. split; [unfold LIVE_SUP_REMOVE; lia|].
unfold XM_SUP_REMOVE. exact (mle_station MT S S3 S4 _ _ MTL (mle_station MT S Sc S3 _ _ MTL HMLEc HMLE3) GMLE).
Qed.
End e.
End f.
End d.
