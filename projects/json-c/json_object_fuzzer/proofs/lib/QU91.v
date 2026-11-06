(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3 QCcH QZsi QQIi Qcrs QUcd Qsn5 QBrp Q2ui Q1KO Q6sh QzgH QgTJ QCrt QtIP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import QQIi.
Import Qcrs QUcd Qsn5 QBrp Q2ui Q1KO.
Import Q6sh QzgH.
Import QgTJ.Mq1 QCrt.
Import QtIP.
Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Section Handoff.
Context {RC__ : RC.RunConsts}.
Variable L : JH.heap_layout_A.
Notation segs := (HI.hl_segs (JH.hla_base L)).
Variable LA : ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Variable DL : dlayout.
Variable RE : aentry.
Variable DCo : donor_core RC.alloc_ceiling segs (at_nodeA LV segs) DL.
Variable FR0 : list (Z * Z).
Variable S : QtIP.MGI.mng_sig.
Variable BAUX : Z.
Variable STAT : (word -> option byte) -> Prop.

Definition handoff_static : Prop :=
ll_ok LA LV 0 PERM0 TMAX NMAX
/\ wx_segs_nowrap segs /\ segs_in_base LV segs /\ shoff_ok LV /\ bands_excl LV /\ bands_cover LV
/\ (forall iv, In iv (lv_base LV) -> 0 <= fst iv /\ snd iv <= 2^47)
/\ (forall y : word, kLowEnd < bv_unsigned y < KHI -> find_segment segs (bv_unsigned y) 1 = None)
/\ Forall (fr_ok LA PERM0) FR0
/\ H_off_segments segs (Fof LV FR0)
/\ (forall x, Fof LV FR0 x = true -> bv_unsigned x < RC.alloc_ceiling)
/\ ae_L RE = LA.

Definition handoff_heap (k0 : Z) (LM0 : list HI.blk) (B0 : JH.bud) (c : config) : Prop :=
HEAPA1 L LV PERM0 TMAX NMAX DL RE DCo FR0 S BAUX STAT
k0 [] LM0 [] B0 (ms_mem (msview LV (cfg_model c) (cfg_ms c))) c.

End Handoff.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZsi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsTj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYZ0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnPO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4en. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkRc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9kF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.

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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzgH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvsx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvsx.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLiw.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGaR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGaR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVJy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVJy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCrt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCrt.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFL8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFL8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmAH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmAH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcGV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcGV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNLn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNLn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtIP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtIP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsCz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZ6y.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTtp.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCVR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Module IR := QkRc.
Module MO := Ql2m.Mq3.
Module MCO := QsTj.
Module MIC := QBv7.
Module MLI := QnPO.
Module AMI := QPjm.Mq4.

Section Inst1.
Context {RC__ : RC.RunConsts}.
Variable L : JH.heap_layout_A.
Notation HL := (JH.hla_base L).
Notation segs := (HI.hl_segs HL).

Variable LA : ALay.
Variable LV : lvp.
Variable PERM0 : list (Z * Z).
Variables TMAX NMAX : Z.
Hypothesis LL0 : ll_ok LA LV 0 PERM0 TMAX NMAX.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.
Hypothesis Hbase47 : forall iv, In iv (lv_base LV) -> 0 <= fst iv /\ snd iv <= 2^47.
Hypothesis segs_low : forall y : word, kLowEnd < bv_unsigned y < KHI -> find_segment segs (bv_unsigned y) 1 = None.
Variable DL : dlayout.
Variable RE : aentry.
Hypothesis RE_L : ae_L RE = LA.
Variable DCo : donor_core RC.alloc_ceiling segs (at_nodeA LV segs) DL.

Variable FR0 : list (Z * Z).
Hypothesis FR0_ok : Forall (fr_ok LA PERM0) FR0.
Hypothesis FR0_off : H_off_segments segs (Fof LV FR0).
Hypothesis FR0_low : forall x, Fof LV FR0 x = true -> bv_unsigned x < RC.alloc_ceiling.

Notation FRof := (FRof FR0).
Notation KLA0 := (KLA LV PERM0 TMAX NMAX (fun _ => false)).

Lemma fr_ok_mono : forall Lg r, fr_ok LA PERM0 r -> fr_ok LA (PERMc PERM0 Lg) r.
Proof.
intros Lg r (H1 & H2' & p & Hp & H3 & H4 & H5 & H6). split; [exact H1|]. split; [exact H2'|].
exists p. split; [unfold PERMc; apply in_app_iff; right; exact Hp|]. auto.
Qed.

Lemma group_entry_disj : forall GH Lg g c H m B T N b l lo hi,
KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N -> In (b, l) (KV.ld_groups Lg) ->
(exists r, In r PERM0 /\ fst r <= lo /\ hi <= snd r) -> lo < hi ->
zdisj (civ (b, l)) (lo, hi).
Proof.
intros GH Lg g c H m B T N b l lo hi KL Hin (r & Hr & Hlo & Hhi) Hlt.
pose proof (kla_ki _ _ _ _ _ _ _ _ _ _ _ _ _ KL) as K.
destruct (kla_groups _ _ _ _ _ _ _ _ _ _ _ _ _ KL b l Hin) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
assert (Hp : In (civ (b, l)) (PERMc PERM0 Lg)) by (unfold PERMc; apply in_app_iff; left; apply in_map; exact Hin).
assert (Hr' : In r (PERMc PERM0 Lg)) by (unfold PERMc; apply in_app_iff; right; exact Hr).
destruct (ki_perm LV B _ T N _ _ K _ Hp) as (_ & Hdis & _).
destruct (ki_perm LV B _ T N _ _ K _ Hr') as (Hrin & _).
destruct (llo_perm LA LV 0 PERM0 TMAX NMAX LL0 r Hr) as (R1 & R2 & R3). rewrite kCeil_val in R3.
destruct (Hdis _ Hrin) as [E|D].
- exfalso. apply G9. assert (Er : r = civ (b, l)); [| rewrite <- Er; exact Hr].
unfold z2w, civ in E. cbn [fst snd] in E. pose proof (f_equal fst E) as E1. pose proof (f_equal snd E) as E2. cbn [fst snd] in E1, E2.
replace (b + l - b) with l in E2 by lia.
unfold kMaxChunk in G2. rewrite kCeil_val in G6.
apply w64_inj in E1; [| lia| lia]. apply w64_inj in E2; [| lia| lia].
unfold civ. cbn [fst snd]. destruct r as [r1 r2]. cbn [fst snd] in *. f_equal; lia.
- rewrite (wiv2z_z2w r) in D by lia. unfold zdisj, civ in *. cbn [fst snd] in *. lia.
Qed.

Lemma KLA_fr_ok : forall GH Lg g c H m B T N, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N ->
Forall (fr_ok LA (PERMc PERM0 Lg)) (FRof Lg).
Proof.
intros GH Lg g c H m B T N KL. unfold QtIP.FRof. apply Forall_app. split.
- apply Forall_forall. intros r Hr. apply in_map_iff in Hr as ([b l] & <- & Hin).
destruct (kla_groups _ _ _ _ _ _ _ _ _ _ _ _ _ KL b l Hin) as (G1 & G2 & G3 & G4 & G5 & G6 & _).
unfold fr_ok, civ. cbn [fst snd]. split; [lia|]. split; [exact G5|].
exists (civ (b, l)). split; [unfold PERMc; apply in_app_iff; left; apply in_map; exact Hin|].
unfold civ. cbn [fst snd]. split; [lia|]. split; [lia|].
destruct (llo_space LA LV 0 PERM0 TMAX NMAX LL0) as (rs & Hrs & _ & S1 & S2).
destruct (llo_parr LA LV 0 PERM0 TMAX NMAX LL0) as (rp & Hrp & _ & P1 & P2).
split.
+ apply (group_entry_disj GH Lg g c H m B T N b l _ _ KL Hin); [exists rs; auto| lia].
+ apply (group_entry_disj GH Lg g c H m B T N b l _ _ KL Hin); [exists rp; auto| lia].
- apply Forall_forall. intros r Hr. apply fr_ok_mono. exact (proj1 (Forall_forall _ _) FR0_ok r Hr).
Qed.

Lemma zin_sh_civ : forall b l y, l mod 4096 = 0 -> zin (bv_unsigned y) (sh_iv LV (civ (b, l))) = in_sh b l y.
Proof.
intros b l y Hal. unfold zin, sh_iv, civ, in_sh, shz, sh_lo, sh_hi. cbn [fst snd].
rewrite (llo_shoff LA LV 0 PERM0 TMAX NMAX LL0), (mmap_len_aligned l Hal). reflexivity.
Qed.

Definition in_shg (Lg : KV.mled) (y : word) : bool := existsb (fun bl : Z * Z => in_sh (fst bl) (snd bl) y) (KV.ld_groups Lg).

Lemma in_shg_true : forall Lg y, in_shg Lg y = true <-> exists b l, In (b, l) (KV.ld_groups Lg) /\ in_sh b l y = true.
Proof.
intros Lg y. unfold in_shg. rewrite existsb_exists. split.
- intros ([b l] & Hin & Hs). exists b, l. auto.
- intros (b & l & Hin & Hs). exists (b, l). auto.
Qed.

Lemma Fof_FRof : forall GH Lg g c H m B T N y, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N ->
Fof LV (FRof Lg) y = in_grp Lg y || in_shg Lg y || Fof LV FR0 y.
Proof.
intros GH Lg g c H m B T N y KL. unfold Fof, QtIP.FRof. rewrite existsb_app. f_equal.
unfold in_grp, in_shg. pose proof (kla_groups _ _ _ _ _ _ _ _ _ _ _ _ _ KL) as HG. revert HG.
induction (KV.ld_groups Lg) as [|[b l] gs IH]; intros HG; [reflexivity|].
cbn [map existsb fst snd]. rewrite IH by (intros b' l' Hin; apply HG; right; exact Hin).
destruct (HG b l (or_introl eq_refl)) as (G1 & _).
unfold fr_in. rewrite (zin_sh_civ b l y G1). unfold zin, civ. cbn [fst snd].
destruct ((b <=? bv_unsigned y) && (bv_unsigned y <? b + l)), (in_sh b l y), (existsb _ gs), (existsb _ gs); reflexivity.
Qed.

Lemma KLA_H_shg : forall GH Lg g c H m B T N y, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N -> H y = in_shg Lg y.
Proof.
intros GH Lg g c H m B T N y KL. destruct (H y) eqn:E.
- symmetry. apply in_shg_true. exact (kla_Hex _ _ _ _ _ _ _ _ _ _ _ _ _ KL y E).
- destruct (in_shg Lg y) eqn:E2; [|reflexivity]. apply in_shg_true in E2 as (b & l & Hin & Hs).
rewrite (kla_Hsh _ _ _ _ _ _ _ _ _ _ _ _ _ KL b l y Hin Hs) in E. discriminate.
Qed.

Lemma KLA_grp_facts : forall GH Lg g c H m B T N y, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N -> in_grp Lg y = true ->
find_segment segs (bv_unsigned y) 1 = None /\ bv_unsigned y < RC.alloc_ceiling /\ ~ (kLowEnd <= bv_unsigned y < KHI)
/\ forall iv, In iv (lv_base LV) -> ~ (fst iv <= bv_unsigned y < snd iv).
Proof.
intros GH Lg g c H m B T N y KL Hy. apply in_grp_true in Hy as (b & l & Hin & Hr).
destruct (kla_groups _ _ _ _ _ _ _ _ _ _ _ _ _ KL b l Hin) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
destruct (KLA_group_map LV PERM0 TMAX NMAX GH Lg g c H m B T N b l KL Hin) as (Hmap & Ub & Ul).
pose proof (ki_x LV B _ T N _ _ (kla_ki _ _ _ _ _ _ _ _ _ _ _ _ _ KL)) as [_ (_ & _ & [_ Hbt])]. specialize (Hbt _ Hmap).
unfold cent in Hbt. cbn [fst snd] in Hbt. rewrite Ub, Ul, (kla_top _ _ _ _ _ _ _ _ _ _ _ _ _ KL) in Hbt.
assert (Hb : forall iv, In iv (lv_base LV) -> ~ (fst iv <= bv_unsigned y < snd iv)) by (intros iv Hiv; exact (proj1 (G8 iv _ Hiv Hr))).
split; [| split; [lia| split; [unfold kLowEnd, KHI, Qqcs.Mq0.kHighMemBeg in *; lia| exact Hb]]].
destruct (find_segment segs (bv_unsigned y) 1) as [seg|] eqn:Ef; [|reflexivity]. exfalso.
apply find_segment_some_spec in Ef as (Hseg & S1 & S2). destruct (Hsegs seg Hseg) as (iv & Hiv & I1 & I2).
apply (Hb iv Hiv). lia.
Qed.

Lemma KLA_shg_facts : forall GH Lg g c H m B T N y, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N -> in_shg Lg y = true ->
kLowEnd < bv_unsigned y < KHI.
Proof.
intros GH Lg g c H m B T N y KL Hy. rewrite <- (KLA_H_shg GH Lg g c H m B T N y KL) in Hy.
exact (kla_Hrange _ _ _ _ _ _ _ _ _ _ _ _ _ KL y Hy).
Qed.

Lemma KLA_F_off : forall GH Lg g c H m B T N, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N -> H_off_segments segs (Fof LV (FRof Lg)).
Proof.
intros GH Lg g c H m B T N KL y Hy. rewrite (Fof_FRof GH Lg g c H m B T N y KL) in Hy.
apply orb_prop in Hy as [Hy|Hy]; [apply orb_prop in Hy as [Hy|Hy]|].
- exact (proj1 (KLA_grp_facts GH Lg g c H m B T N y KL Hy)).
- apply segs_low. exact (KLA_shg_facts GH Lg g c H m B T N y KL Hy).
- exact (FR0_off y Hy).
Qed.

Lemma KLA_F_low : forall GH Lg g c H m B T N, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N ->
forall x, Fof LV (FRof Lg) x = true -> bv_unsigned x < RC.alloc_ceiling.
Proof.
intros GH Lg g c H m B T N KL y Hy. rewrite (Fof_FRof GH Lg g c H m B T N y KL) in Hy.
apply orb_prop in Hy as [Hy|Hy]; [apply orb_prop in Hy as [Hy|Hy]|].
- exact (proj1 (proj2 (KLA_grp_facts GH Lg g c H m B T N y KL Hy))).
- pose proof (KLA_shg_facts GH Lg g c H m B T N y KL Hy). pose proof (@RC.alloc_ceiling_range RC__).
unfold KHI, Qqcs.Mq0.kHighMemBeg in *. lia.
- exact (FR0_low y Hy).
Qed.

Section HideO.
Variable K : word -> bool.
Hypothesis K_off : H_off_segments segs K.

Lemma wr_at_hide : forall m a n, (forall x, a <= x < a + n -> K (wa x) = false) -> wr_at segs m a n -> wr_at segs (mrestrict K m) a n.
Proof.
intros m a n HK (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|]. intros i Hi.
unfold wview. rewrite (mrestrict_off K m _ (HK (a + i) ltac:(lia))). exact (HW i Hi).
Qed.

Lemma rw_cells_unhide : forall m A cs, OT.rw_cells segs (mrestrict K m) A cs -> OT.rw_cells segs m A cs.
Proof.
intros m A cs [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
- exact (bytes_at_unhide segs K K_off m A _ HB).
- exact (wr_at_unhide segs K K_off m A _ HW).
Qed.

Lemma rw_cells_hide : forall m A cs, (forall x, A <= x < A + Z.of_nat (OC.cells_size cs) -> K (wa x) = false) ->
OT.rw_cells segs m A cs -> OT.rw_cells segs (mrestrict K m) A cs.
Proof.
intros m A cs HK [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
- apply (bytes_at_hide segs K m A _); [| exact HB]. intros x Hx. apply HK.
rewrite (OC.cells_bytes_length cs Hwf) in Hx. exact Hx.
- apply wr_at_hide; assumption.
Qed.

Lemma wr_at_hidden_offK : forall m a n, wr_at segs (mrestrict K m) a n -> forall x, a <= x < a + n -> K (wa x) = false.
Proof.
intros m a n (_ & _ & HW) x Hx. destruct (K (wa x)) eqn:E; [|reflexivity]. exfalso.
apply (HW (x - a) ltac:(lia)). replace (a + (x - a)) with x by lia. unfold wview, mrestrict. rewrite E, (K_off _ E). reflexivity.
Qed.

Lemma mem_inv_unhideK : forall m, mem_inv segs (mrestrict K m) -> mem_inv segs m.
Proof.
intros m HI a b E. destruct (K a) eqn:Ka.
- unfold ro_addr. rewrite (K_off a Ka). reflexivity.
- apply (HI a b). unfold mrestrict. rewrite Ka. exact E.
Qed.
End HideO.

Variable S : MGI.mng_sig.
Variable BAUX : Z.
Variable STAT : (word -> option byte) -> Prop.
Hypothesis ML : MGI.mng_laws segs S.
Notation RATP := (MGI.mg_tp S).
Notation RDATA_LO := (MGI.mg_data_lo S).
Notation RIMG_HI := (MGI.mg_img_hi S).
Notation RHEAP := (MGI.mg_heap S).
Notation rauxv_ok := (MGI.mg_auxv S).
Notation wstat := (MGI.in_ivs (MGI.mg_wstat S)).
Notation HEAPA1 := (HEAPA1 L LV PERM0 TMAX NMAX DL RE DCo FR0 S BAUX STAT).
Hypothesis L_malloc2 : HI.hl_malloc2 HL = MGI.mg_malloc S.
Hypothesis L_free2 : HI.hl_free2 HL = MGI.mg_free S.
Hypothesis L_tp2 : HI.hl_tp HL = RATP.
Hypothesis L_stack2 : MGI.mg_stack S <= HI.hl_stack HL.

Hypothesis IMG_low : RIMG_HI <= kLowEnd.
Hypothesis IMG_seg_G : forall z, z + 1 <= MGI.mg_img_lo S \/ RIMG_HI <= z -> find_segment segs z 1 = None.
Hypothesis IMG_rw : forall y : word, find_segment segs (bv_unsigned y) 1 <> None -> ro_addr segs y = false ->
RDATA_LO <= bv_unsigned y < RIMG_HI.
Hypothesis IMG_base : exists iv, In iv (lv_base LV) /\ fst iv <= RDATA_LO /\ RIMG_HI <= snd iv.

Lemma IMG_data : 0x10000 <= RDATA_LO /\ RDATA_LO <= RIMG_HI /\ RIMG_HI <= kLowEnd.
Proof. destruct (MGI.ml_hull segs S ML) as (H1 & H2' & H3). split; [lia|]. split; [exact H3| exact IMG_low]. Qed.

Definition mng_static (a : Z) : Prop := MGI.in_ivs (MGI.mg_rstat S) a.
Notation mng_dyn := MGI.mng_dyn.
Notation doranges := MGI.doranges.

Lemma stat_in_hull : forall a, mng_static a \/ wstat a -> RDATA_LO <= a < RIMG_HI.
Proof.
intros a Ha. pose proof (MGI.ml_stat_in segs S ML) as HF. rewrite Forall_forall in HF.
destruct Ha as [(iv & Hiv & Hr)|(iv & Hiv & Hr)]; (destruct (HF iv ltac:(apply in_app_iff; auto)) as [F1 F2]; lia).
Qed.

Lemma wstat_iff : forall a, wstat a <-> (fst (MGI.mg_ctx S) <= a < snd (MGI.mg_ctx S) \/ RATP + -164 <= a < RATP + -164 + 4).
Proof.
intros a. unfold MGI.in_ivs, MGI.mg_wstat. split.
- intros (iv & [<-|[<-|[]]] & Hr); [left| right]; exact Hr.
- intros [Hr|Hr]; [exists (MGI.mg_ctx S)| exists (RATP + -164, RATP + -164 + 4)]; (split; [cbn; auto| exact Hr]).
Qed.

Lemma wstat_dec : forall a, wstat a \/ ~ wstat a.
Proof.
intros a. destruct (Z.lt_ge_cases a (fst (MGI.mg_ctx S))) as [A1|A1]; destruct (Z.lt_ge_cases a (snd (MGI.mg_ctx S))) as [A2|A2];
destruct (Z.lt_ge_cases a (RATP + -164)) as [A3|A3]; destruct (Z.lt_ge_cases a (RATP + -164 + 4)) as [A4|A4];
first [left; apply wstat_iff; lia | right; rewrite wstat_iff; lia].
Qed.

Lemma OBL_MNG_AGREE : forall s Lg LB0 m m', RHEAP s LB0 m -> SG.HSIM s Lg LB0 ->
(forall b l, In (b, l) (KV.ld_groups Lg) -> l mod 4096 = 0) ->
(forall a, 0 <= a < 2^64 -> mng_static a \/ mng_dyn Lg a -> m' (wa a) = m (wa a)) -> RHEAP s LB0 m'.
Proof. exact (MGI.ml_agree segs S ML). Qed.

Definition PK (Lg : KV.mled) (lo : Z) (y : word) : bool :=
((RDATA_LO <=? bv_unsigned y) && (bv_unsigned y <? RIMG_HI)) || (lo <=? bv_unsigned y) || in_regs (FRof Lg) y.
Definition GHof (m : word -> option byte) (Lg : KV.mled) (H : word -> bool) (lo : Z) (y : word) : bool :=
match m y with Some _ => true | None => false end && negb (PK Lg lo y) && negb (H y).

Lemma in_regs_FRof : forall Lg y, in_regs (FRof Lg) y = in_grp Lg y || in_regs FR0 y.
Proof.
intros Lg y. unfold in_regs, QtIP.FRof. rewrite existsb_app. f_equal. unfold in_grp.
induction (KV.ld_groups Lg) as [|[b l] gs IH]; [reflexivity|]. cbn [map existsb fst snd]. rewrite IH.
unfold zin, civ. cbn [fst snd]. reflexivity.
Qed.

Lemma in_regs_Fof : forall FR y, in_regs FR y = true -> Fof LV FR y = true.
Proof.
intros FR y Hy. unfold in_regs in Hy. apply existsb_exists in Hy as (r & Hr & Hz). unfold Fof. apply existsb_exists.
exists r. split; [exact Hr|]. unfold fr_in. rewrite Hz. reflexivity.
Qed.

Lemma GHof_off : forall m Lg H lo, mem_inv segs m -> H_off_segments segs (GHof m Lg H lo).
Proof.
intros m Lg H lo MI y Hy. unfold GHof in Hy. apply andb_prop in Hy as [Hy _]. apply andb_prop in Hy as [Hm Hp].
destruct (m y) as [b|] eqn:Em; [|discriminate]. apply negb_true_iff in Hp.
destruct (find_segment segs (bv_unsigned y) 1) as [seg|] eqn:Ef; [|reflexivity]. exfalso.
pose proof (IMG_rw y ltac:(rewrite Ef; discriminate) (MI y b Em)) as Hr.
unfold PK in Hp. apply orb_false_elim in Hp as [Hp _]. apply orb_false_elim in Hp as [Hp _].
apply andb_false_iff in Hp as [Hp|Hp]; [apply Z.leb_gt in Hp| apply Z.ltb_ge in Hp]; lia.
Qed.

Lemma KLA_GHof : forall Lg g c H m B T N lo, KLA0 Lg g c H m B T N ->
KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg g c H m B T N.
Proof.
intros Lg g c H m B T N lo KL. apply (KLA_GH LV PERM0 TMAX NMAX _ _ Lg g c H m B T N KL).
intros y Hy. unfold GHof in Hy. apply andb_prop in Hy as [Hy Hh]. apply andb_prop in Hy as [Hm Hp].
apply negb_true_iff in Hh, Hp. split; [destruct (m y); [discriminate| discriminate Hm]|]. split; [| exact Hh].
unfold PK in Hp. apply orb_false_elim in Hp as [_ Hp]. rewrite in_regs_FRof in Hp. apply orb_false_elim in Hp as [Hp _]. exact Hp.
Qed.

Lemma wa_u : forall y : word, wa (bv_unsigned y) = y.
Proof. intros y. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

Lemma H_place : forall GH Lg g c H m B T N y, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N -> H y = true ->
~ (RDATA_LO <= bv_unsigned y < RIMG_HI) /\ bv_unsigned y < RC.alloc_ceiling /\ Fof LV (FRof Lg) y = true.
Proof.
intros GH Lg g c H m B T N y KL Hy. pose proof (kla_Hrange _ _ _ _ _ _ _ _ _ _ _ _ _ KL y Hy) as Hr.
pose proof (@RC.alloc_ceiling_range RC__) as Hc. destruct IMG_data as (_ & _ & I3).
split; [lia|]. split; [unfold KHI, Qqcs.Mq0.kHighMemBeg in *; lia|].
rewrite (Fof_FRof GH Lg g c H m B T N y KL), <- (KLA_H_shg GH Lg g c H m B T N y KL), Hy. rewrite orb_true_r. reflexivity.
Qed.

Lemma GHof_true : forall m Lg H lo y, m y <> None -> ~ (RDATA_LO <= bv_unsigned y < RIMG_HI) -> bv_unsigned y < lo ->
in_regs (FRof Lg) y = false -> H y = false -> GHof m Lg H lo y = true.
Proof.
intros m Lg H lo y Hm Hh Hlo Hr HH. unfold GHof, PK. rewrite Hr, HH. destruct (m y); [| contradiction].
replace (lo <=? bv_unsigned y) with false by (symmetry; apply Z.leb_gt; lia).
destruct (Z.leb_spec RDATA_LO (bv_unsigned y)); destruct (Z.ltb_spec (bv_unsigned y) RIMG_HI); cbn; try reflexivity. exfalso. lia.
Qed.

Lemma GHof_notPK : forall m Lg H lo y, GHof m Lg H lo y = true ->
m y <> None /\ ~ (RDATA_LO <= bv_unsigned y < RIMG_HI) /\ bv_unsigned y < lo /\ in_regs (FRof Lg) y = false /\ H y = false.
Proof.
intros m Lg H lo y Hy. unfold GHof in Hy. apply andb_prop in Hy as [Hy Hh]. apply andb_prop in Hy as [Hm Hp].
apply negb_true_iff in Hh, Hp. unfold PK in Hp. apply orb_false_elim in Hp as [Hp Hr]. apply orb_false_elim in Hp as [Hd Hl].
apply Z.leb_gt in Hl. split; [destruct (m y); [discriminate| discriminate Hm]|]. split; [| auto].
intros [D1 D2]. apply andb_false_iff in Hd as [Hd|Hd]; [apply Z.leb_gt in Hd| apply Z.ltb_ge in Hd]; lia.
Qed.

Lemma wview_cases : forall m (x : word), mem_inv segs m -> wview segs m x <> None -> m x <> None \/ RDATA_LO <= bv_unsigned x < RIMG_HI.
Proof.
intros m x MI Hw. destruct (m x) as [b|] eqn:E; [left; discriminate|]. right. unfold wview in Hw. rewrite E in Hw.
destruct (find_segment segs (bv_unsigned x) 1) as [seg|] eqn:Ef; [| contradiction].
destruct (seg_writable seg) eqn:Ew; [| contradiction].
apply IMG_rw; [rewrite Ef; discriminate| unfold ro_addr; rewrite Ef, Ew; reflexivity].
Qed.

Lemma wview_eq : forall m m' (x : word), m' x = m x -> wview segs m' x = wview segs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

Definition WMNG : list (Z * Z) := (RC.alloc_ceiling, 2^64) :: MGI.mg_wstat S.

Lemma outside_WMNG : forall z, outside WMNG z -> ~ (RC.alloc_ceiling <= z < 2^64) /\ ~ wstat z.
Proof.
intros z Ho. unfold WMNG, MGI.mg_wstat in Ho. rewrite wstat_iff. destruct (MGI.mg_ctx S) as [c1 c2]. cbn [outside fst snd] in *.
destruct Ho as (O1 & O2 & O3 & _). split; [exact O1| lia].
Qed.

Lemma mng_frame : forall Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' (LBx : list MB.block),
KLA0 Lg g c H m B T N ->
KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' ->
MI segs (GHof m Lg H lo) m H Lg m2 H' Lg' ->
mem_inv segs m -> mem_inv segs m2 ->
RC.alloc_ceiling <= lo -> lo <= sp ->
MGI.mpres segs S LBx sp (mrestrict (HG (GHof m Lg H lo) H) m) (mrestrict (HG (GHof m Lg H lo) H') m2) ->
stk segs m2 lo sp ->
(forall a, wstat a -> wview segs m2 (wa a) <> None) ->
munch WMNG (mrestrict (Fof LV (FRof Lg)) m) (mrestrict (Fof LV (FRof Lg')) m2)
/\ wmono segs (mrestrict (Fof LV (FRof Lg)) m) (mrestrict (Fof LV (FRof Lg')) m2).
Proof.
intros Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' [X1 X3] MI MI2 Hlo Hsp PRES STK HST.
set (GH := GHof m Lg H lo) in *.
pose proof (@RC.alloc_ceiling_range RC__) as Hc. destruct IMG_data as (I1 & I2 & I3). destruct IMG_base as (iv0 & Hiv0 & B1 & B2).
pose proof (Fof_FRof (fun _ => false) Lg g c H m B T N) as EF. pose proof (Fof_FRof GH Lg' g c' H' m2 B' T' N') as EF'.
pose proof (KLA_H_shg (fun _ => false) Lg g c H m B T N) as EH. pose proof (KLA_H_shg GH Lg' g c' H' m2 B' T' N') as EH'.

assert (NH : forall y : word, (RDATA_LO <= bv_unsigned y < RIMG_HI \/ lo <= bv_unsigned y) ->
HG GH H y = false /\ HG GH H' y = false).
{ intros y Hy. unfold HG.
assert (G0 : GH y = false).
{ destruct (GH y) eqn:E; [|reflexivity]. exfalso. destruct (GHof_notPK _ _ _ _ _ E) as (_ & N1 & N2 & _). lia. }
assert (H0 : H y = false).
{ destruct (H y) eqn:E; [|reflexivity]. exfalso. destruct (H_place _ _ _ _ _ _ _ _ _ y KL E) as (P1 & P2 & _). lia. }
assert (H0' : H' y = false).
{ destruct (H' y) eqn:E; [|reflexivity]. exfalso. destruct (H_place _ _ _ _ _ _ _ _ _ y KL' E) as (P1 & P2 & _). lia. }
rewrite G0, H0, H0'. auto. }

assert (PR : forall y : word, (sp <= bv_unsigned y \/ (RDATA_LO <= bv_unsigned y < RIMG_HI /\ ~ wstat (bv_unsigned y))) ->
m2 y = m y /\ (wview segs m y <> None -> wview segs m2 y <> None)).
{ intros y Hy. pose proof (bv_unsigned_in_range _ y) as Hr. unfold bv_modulus in Hr.
destruct (PRES (bv_unsigned y) ltac:(lia) ltac:(destruct Hy as [Hy|Hy]; [left; exact Hy| right; left; exact Hy])) as [E W].
change (OM.wa (bv_unsigned y)) with (wa (bv_unsigned y)) in E, W. rewrite (wa_u y) in E, W.
destruct (NH y ltac:(destruct Hy as [Hy|[Hy _]]; [right; lia| left; exact Hy])) as [N1 N2].
unfold mrestrict in E. rewrite N1, N2 in E. split; [exact E|].
unfold wview, mrestrict in W. rewrite N1, N2 in W. exact W. }

assert (NEW : forall y, Fof LV (FRof Lg) y = false -> Fof LV (FRof Lg') y = true -> m y = None).
{ intros y Fy Fy'. destruct (m y) as [b|] eqn:Em; [|reflexivity]. exfalso.
rewrite (EF y KL) in Fy. apply orb_false_elim in Fy as [Fy F0]. apply orb_false_elim in Fy as [Fg Fs].
rewrite (EF' y KL'), F0, orb_false_r in Fy'.
assert (Hreg : in_regs (FRof Lg) y = false).
{ rewrite in_regs_FRof, Fg. destruct (in_regs FR0 y) eqn:E; [|reflexivity]. rewrite (in_regs_Fof FR0 y E) in F0. discriminate. }
assert (Hnh : ~ (RDATA_LO <= bv_unsigned y < RIMG_HI)).
{ intros Hd. apply orb_prop in Fy' as [Fy'|Fy'].
- destruct (KLA_grp_facts _ Lg' g c' H' m2 B' T' N' y KL' Fy') as (_ & _ & _ & Hb). apply (Hb iv0 Hiv0). lia.
- pose proof (KLA_shg_facts _ Lg' g c' H' m2 B' T' N' y KL' Fy'). lia. }
assert (Hlt : bv_unsigned y < lo) by (pose proof (KLA_F_low _ Lg' g c' H' m2 B' T' N' KL' y ltac:(rewrite (EF' y KL'), F0, orb_false_r; exact Fy')); lia).
assert (GHy : GH y = true) by (apply GHof_true; [rewrite Em; discriminate| exact Hnh| exact Hlt| exact Hreg| rewrite (EH y KL); exact Fs]).
destruct (kla_G _ _ _ _ _ _ _ _ _ _ _ _ _ KL' y GHy) as (_ & G2 & G3). rewrite (EH' y KL') in G3. rewrite G2, G3 in Fy'. discriminate. }

assert (OLD : forall y, Fof LV (FRof Lg) y = true -> Fof LV (FRof Lg') y = false -> m2 y = None).
{ intros y Fy Fy'. destruct (m2 y) as [b|] eqn:Em; [|reflexivity]. exfalso.
pose proof (KLA_F_off _ Lg g c H m B T N KL y Fy) as Hoff.
rewrite (EF' y KL') in Fy'. apply orb_false_elim in Fy' as [Fy' F0]. apply orb_false_elim in Fy' as [Fg' Fs'].
rewrite (EF y KL), F0, orb_false_r in Fy.
destruct (X3 y ltac:(unfold offseg; rewrite Hoff; reflexivity) ltac:(rewrite Em; discriminate)) as [Hh|[Hg|(_ & Hg & Hh)]].
- rewrite (EH' y KL') in Hh. congruence.
- congruence.
- rewrite (EH y KL) in Hh. rewrite Hg, Hh in Fy. discriminate. }

assert (SAME : forall y, Fof LV (FRof Lg) y = false -> Fof LV (FRof Lg') y = false -> bv_unsigned y < lo ->
~ (RDATA_LO <= bv_unsigned y < RIMG_HI) -> m2 y = m y).
{ intros y Fy Fy' Hlt Hnh.
assert (Hreg : in_regs (FRof Lg) y = false).
{ destruct (in_regs (FRof Lg) y) eqn:E; [|reflexivity]. rewrite (in_regs_Fof _ y E) in Fy. discriminate. }
assert (HHy : H y = false).
{ destruct (H y) eqn:E; [|reflexivity]. destruct (H_place _ _ _ _ _ _ _ _ _ y KL E) as (_ & _ & P3). congruence. }
destruct (m y) as [b|] eqn:Em.
- rewrite <- Em. apply X1. apply GHof_true; [rewrite Em; discriminate| exact Hnh| exact Hlt| exact Hreg| exact HHy].
- destruct (m2 y) as [b2|] eqn:Em2; [|reflexivity]. exfalso.
destruct (find_segment segs (bv_unsigned y) 1) as [seg|] eqn:Ef.
+ apply Hnh. apply IMG_rw; [rewrite Ef; discriminate| exact (MI2 y b2 Em2)].
+ rewrite (EF' y KL') in Fy'. apply orb_false_elim in Fy' as [Fy' F0]. apply orb_false_elim in Fy' as [Fg' Fs'].
destruct (X3 y ltac:(unfold offseg; rewrite Ef; reflexivity) ltac:(rewrite Em2; discriminate)) as [Hh|[Hg|(Hm & _)]].
* rewrite (EH' y KL') in Hh. congruence.
* congruence.
* apply Hm. exact Em. }
split.
-
intros y Hout. destruct (outside_WMNG _ Hout) as [O1 OW].
pose proof (bv_unsigned_in_range _ y) as Hr. unfold bv_modulus in Hr.
unfold mrestrict. destruct (Fof LV (FRof Lg) y) eqn:Fy; destruct (Fof LV (FRof Lg') y) eqn:Fy'.
+ reflexivity.
+ exact (OLD y Fy Fy').
+ symmetry. exact (NEW y Fy Fy').
+ destruct (Z.lt_ge_cases (bv_unsigned y) RDATA_LO) as [Hd|Hd]; [apply SAME; auto; lia|].
destruct (Z.lt_ge_cases (bv_unsigned y) RIMG_HI) as [Hd2|Hd2]; [| apply SAME; auto; lia].
apply (PR y). right. split; [lia| exact OW].
-
intros y Hw. pose proof (bv_unsigned_in_range _ y) as Hr. unfold bv_modulus in Hr.
unfold wview, mrestrict in Hw |- *. destruct (Fof LV (FRof Lg) y) eqn:Fy.
{ exfalso. rewrite (KLA_F_off _ Lg g c H m B T N KL y Fy) in Hw. apply Hw. reflexivity. }
fold (wview segs m y) in Hw.
destruct (Fof LV (FRof Lg') y) eqn:Fy'.
{ exfalso. unfold wview in Hw. rewrite (NEW y Fy Fy'), (KLA_F_off _ Lg' g c' H' m2 B' T' N' KL' y Fy') in Hw. apply Hw. reflexivity. }
fold (wview segs m2 y).
destruct (Z.le_gt_cases sp (bv_unsigned y)) as [Hs|Hs]; [apply (PR y); [left; exact Hs| exact Hw]|].
destruct (Z.le_gt_cases lo (bv_unsigned y)) as [Hl|Hl].
{ destruct STK as (_ & _ & HS). destruct (HS (bv_unsigned y) ltac:(lia)) as [W _]. rewrite (wa_u y) in W. exact W. }
destruct (Z.lt_ge_cases (bv_unsigned y) RDATA_LO) as [Hd|Hd]; [rewrite (wview_eq m m2 y (SAME y Fy Fy' Hl ltac:(lia))); exact Hw|].
destruct (Z.lt_ge_cases (bv_unsigned y) RIMG_HI) as [Hd2|Hd2]; [| rewrite (wview_eq m m2 y (SAME y Fy Fy' Hl ltac:(lia))); exact Hw].
destruct (wstat_dec (bv_unsigned y)) as [SW|SW].
+ rewrite <- (wa_u y). apply HST. exact SW.
+ apply (PR y); [right; split; [lia| exact SW]| exact Hw].
Qed.

Hypothesis L_img : HI.hl_img_lo HL = dl_img_lo DL /\ HI.hl_img_hi HL = dl_img_hi DL.
Hypothesis IMG_hull : HI.hl_img_lo HL <= RDATA_LO /\ RIMG_HI <= HI.hl_img_hi HL /\
forall y, find_segment segs y 1 <> None -> HI.hl_img_lo HL <= y < HI.hl_img_hi HL.
Hypothesis L_static2 : forall a, HI.hl_client_static HL a -> RDATA_LO <= a < RIMG_HI /\ ~ wstat a.

Definition in_rtc (a : Z) : Prop := exists c, In c (MGI.mg_rtc S) /\ fst c <= a < fst c + Z.of_nat (length (snd c)).
Hypothesis OBL_R1P : forall a, (mng_static a /\ ~ in_rtc a) \/ fst (MGI.mg_ctx S) <= a < snd (MGI.mg_ctx S) -> dl_client_data DL a.

Hypothesis L_rtc : incl (MGI.mg_rtc S) (dl_rtc DL).
Hypothesis IMG_rtc_wr : forall m : word -> option byte, Forall (fun c => wr_at segs m (fst c) (Z.of_nat (length (snd c)))) (MGI.mg_rtc S).
Hypothesis L_errno : dl_errno DL = HI.hl_tp HL - 164.
Hypothesis FR0_off_data : forall x, Fof LV FR0 x = true -> ~ (RDATA_LO <= bv_unsigned x < RIMG_HI).

Hypothesis L_dpn : 0 <= dl_depot_n DL /\ dl_depot_n DL + 4 <= RC.alloc_ceiling.
Hypothesis L_dpn_hull : dl_img_lo DL <= dl_depot_n DL /\ dl_depot_n DL + 4 <= dl_img_hi DL.
Hypothesis L_dpn_wstat : Forall (fun iv : Z * Z => snd iv <= dl_depot_n DL \/ dl_depot_n DL + 4 <= fst iv) (MGI.mg_wstat S).
Hypothesis L_dpn_priv : forall x, dl_depot_n DL <= x < dl_depot_n DL + 4 -> ~ HI.hl_client_static HL x /\ ~ HI.hl_scratch HL x.

Lemma F_off_data : forall GH Lg g c H m B T N y, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N ->
Fof LV (FRof Lg) y = true -> ~ (RDATA_LO <= bv_unsigned y < RIMG_HI).
Proof.
intros GH Lg g c H m B T N y KL Hy Hd. rewrite (Fof_FRof GH Lg g c H m B T N y KL) in Hy.
apply orb_prop in Hy as [Hy|Hy]; [apply orb_prop in Hy as [Hy|Hy]|].
- destruct (KLA_grp_facts GH Lg g c H m B T N y KL Hy) as (_ & _ & _ & Hb). destruct IMG_base as (iv & Hiv & B1 & B2).
apply (Hb iv Hiv). lia.
- pose proof (KLA_shg_facts GH Lg g c H m B T N y KL Hy). lia.
- exact (FR0_off_data y Hy Hd).
Qed.

Lemma implM_get_inv {A} (f : MG.PState -> MO.M MG.PState A) s Q ms :
MO.implM segs (MO.mbind MO.mget f) s Q ms -> MO.implM segs (f s) s Q ms.
Proof. intros H. exact H. Qed.
Lemma implM_upd_ret_inv {A} (g : MG.PState -> MG.PState) (v : A) s Q ms :
MO.implM segs (MO.mbind (MO.mupd g) (fun _ => MO.mret v)) s Q ms -> O.evt segs (Q v (g s)) ms.
Proof. intros H. exact H. Qed.
Lemma implM_upd_inv (g : MG.PState -> MG.PState) s Q ms :
MO.implM segs (MO.mupd g) s Q ms -> O.evt segs (Q tt (g s)) ms.
Proof. intros H. exact H. Qed.

Lemma coarse_nothid : forall Lg g c H m B T N lo y, KLA0 Lg g c H m B T N -> RC.alloc_ceiling <= lo ->
PK Lg lo y = true -> HG (GHof m Lg H lo) H y = false.
Proof.
intros Lg g c H m B T N lo y KL Hlo Hp. unfold HG. apply orb_false_intro.
- destruct (H y) eqn:E; [|reflexivity]. exfalso. destruct (H_place _ _ _ _ _ _ _ _ _ y KL E) as (P1 & P2 & P3).
unfold PK in Hp. apply orb_prop in Hp as [Hp|Hp]; [apply orb_prop in Hp as [Hp|Hp]|].
+ apply andb_prop in Hp as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2. lia.
+ apply Z.leb_le in Hp. lia.
+ rewrite in_regs_FRof in Hp. pose proof (kla_Hrange _ _ _ _ _ _ _ _ _ _ _ _ _ KL y E) as Hband.
apply orb_prop in Hp as [Hp|Hp].
* destruct (KLA_grp_facts _ Lg g c H m B T N y KL Hp) as (_ & _ & Nb & _). lia.
* unfold in_regs in Hp. apply existsb_exists in Hp as (r & Hr & Hz). apply zin_true in Hz.
destruct (proj1 (Forall_forall _ _) FR0_ok r Hr) as (_ & Hpl & _). lia.
- unfold GHof. rewrite Hp. cbn. rewrite andb_false_r. reflexivity.
Qed.

Lemma PK_hull : forall Lg lo a, 0 <= a < 2^64 -> RDATA_LO <= a < RIMG_HI -> PK Lg lo (wa a) = true.
Proof.
intros Lg lo a Ha Hd. unfold PK. rewrite (wa_unsigned a Ha).
replace (RDATA_LO <=? a) with true by (symmetry; apply Z.leb_le; lia). replace (a <? RIMG_HI) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma PK_stack : forall Lg lo a, 0 <= a < 2^64 -> lo <= a -> PK Lg lo (wa a) = true.
Proof.
intros Lg lo a Ha Hd. unfold PK. rewrite (wa_unsigned a Ha).
replace (lo <=? a) with true by (symmetry; apply Z.leb_le; lia). rewrite orb_true_r. reflexivity.
Qed.
Lemma PK_regs : forall Lg lo y, in_regs (FRof Lg) y = true -> PK Lg lo y = true.
Proof. intros Lg lo y Hy. unfold PK. rewrite Hy. apply orb_true_r. Qed.

Lemma mng_dyn_regs : forall Lg a, 0 <= a < 2^64 ->
(forall r y, In r (doranges Lg) -> fst r <= bv_unsigned y < fst r + snd r -> in_regs FR0 y = true) ->
mng_dyn Lg a -> in_regs (FRof Lg) (wa a) = true.
Proof.
intros Lg a Ha HOR [(b & l & Hin & Hr)|(r & Hr & Hy)]; rewrite in_regs_FRof.
- replace (in_grp Lg (wa a)) with true; [reflexivity|]. symmetry. apply in_grp_true. exists b, l. rewrite (wa_unsigned a Ha). auto.
- rewrite (HOR r (wa a) Hr ltac:(rewrite (wa_unsigned a Ha); exact Hy)). apply orb_true_r.
Qed.

Lemma coarse_pre : forall Lg g c H m B T N lo sp s LB0 (errv : word),
KLA0 Lg g c H m B T N -> RC.alloc_ceiling <= lo -> lo <= sp -> sp <= BAUX ->
(forall r y, In r (doranges Lg) -> fst r <= bv_unsigned y < fst r + snd r -> in_regs FR0 y = true) ->
RHEAP s LB0 m -> SG.HSIM s Lg LB0 -> rauxv_ok m BAUX -> stk segs m lo sp ->
OT.rw_cells segs m (RATP - 164) [OC.C4 errv] -> mem_inv segs m ->
let mc := mrestrict (HG (GHof m Lg H lo) H) m in
RHEAP s LB0 mc /\ rauxv_ok mc BAUX /\ stk segs mc lo sp /\ OT.rw_cells segs mc (RATP - 164) [OC.C4 errv] /\ mem_inv segs mc.
Proof.
intros Lg g c H m B T N lo sp s LB0 errv KL Hlo Hsp HB HOR RH SIM AUX STK ERR MI mc.
pose proof (@RC.alloc_ceiling_range RC__) as Hc. destruct IMG_data as (D1 & D2 & D3). unfold kLowEnd in D3.
assert (NH : forall a, 0 <= a < 2^64 -> PK Lg lo (wa a) = true -> HG (GHof m Lg H lo) H (wa a) = false)
by (intros a _ Hp; exact (coarse_nothid Lg g c H m B T N lo _ KL Hlo Hp)).
split; [| split; [| split; [| split]]].
- apply (OBL_MNG_AGREE s Lg LB0 m mc RH SIM); [intros b0 l0 Hbl0; exact (proj1 (kla_groups _ _ _ _ _ _ _ _ _ _ _ _ _ KL b0 l0 Hbl0))|]. intros a Ha Hf. unfold mc, mrestrict. rewrite NH; [reflexivity| exact Ha|].
destruct Hf as [Hs|Hd]; [apply PK_hull; [exact Ha| apply stat_in_hull; left; exact Hs]|].
apply PK_regs. exact (mng_dyn_regs Lg a Ha HOR Hd).
- apply (MGI.ml_auxv_agree segs S ML m mc BAUX AUX). intros a Ha Hf. unfold mc, mrestrict. rewrite NH; [reflexivity| exact Ha|].
destruct Hf as [Hb|Hs]; [apply PK_stack; [exact Ha| lia]| apply PK_hull; [exact Ha| apply stat_in_hull; left; exact Hs]].
- apply stk_hide; [| exact STK]. intros x Hx. destruct STK as (K0 & K1 & _).
assert (Hx64 : 0 <= x < 2^64) by lia. apply (NH x Hx64). apply PK_stack; [exact Hx64| lia].
- apply rw_cells_hide; [| exact ERR]. intros x Hx. change (Z.of_nat (OC.cells_size [OC.C4 errv])) with 4 in Hx.
assert (Hh : RDATA_LO <= x < RIMG_HI) by (apply stat_in_hull; right; apply wstat_iff; right; lia).
assert (Hx64 : 0 <= x < 2^64) by lia. apply (NH x Hx64). apply PK_hull; [exact Hx64| exact Hh].
- apply mem_inv_hide. exact MI.
Qed.

Lemma post_nothid : forall Lg Lg' g c c' H H' m m2 lo B T N B' T' N' y,
KLA0 Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' -> RC.alloc_ceiling <= lo ->
PK Lg lo y = true \/ in_grp Lg' y = true -> HG (GHof m Lg H lo) H' y = false.
Proof.
intros Lg Lg' g c c' H H' m m2 lo B T N B' T' N' y KL KL' Hlo Hy. unfold HG. apply orb_false_intro.
- destruct (H' y) eqn:E; [|reflexivity]. exfalso. destruct (H_place _ _ _ _ _ _ _ _ _ y KL' E) as (P1 & P2 & _).
pose proof (kla_Hrange _ _ _ _ _ _ _ _ _ _ _ _ _ KL' y E) as Hband.
destruct Hy as [Hp|Hg].
+ unfold PK in Hp. apply orb_prop in Hp as [Hp|Hp]; [apply orb_prop in Hp as [Hp|Hp]|].
* apply andb_prop in Hp as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.ltb_lt in Q2. lia.
* apply Z.leb_le in Hp. lia.
* rewrite in_regs_FRof in Hp. apply orb_prop in Hp as [Hp|Hp].
-- destruct (KLA_grp_facts _ Lg g c H m B T N y KL Hp) as (_ & _ & Nb & _). lia.
-- unfold in_regs in Hp. apply existsb_exists in Hp as (r & Hr & Hz). apply zin_true in Hz.
destruct (proj1 (Forall_forall _ _) FR0_ok r Hr) as (_ & Hpl & _). lia.
+ destruct (KLA_grp_facts _ Lg' g c' H' m2 B' T' N' y KL' Hg) as (_ & _ & Nb & _). lia.
- destruct (GHof m Lg H lo y) eqn:E; [|reflexivity]. exfalso. destruct Hy as [Hp|Hg].
+ unfold GHof in E. rewrite Hp in E. cbn in E. rewrite andb_false_r in E. discriminate.
+ destruct (kla_G _ _ _ _ _ _ _ _ _ _ _ _ _ KL' y E) as (_ & G2 & _). congruence.
Qed.

Lemma asan_byte_keep : forall Lg Lg' g c c' H H' m m2 lo B T N B' T' N' y,
KLA0 Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' ->
MI segs (GHof m Lg H lo) m H Lg m2 H' Lg' -> mem_inv segs m -> RC.alloc_ceiling <= lo ->
wview segs m y <> None -> Fof LV (FRof Lg) y = false ->
(bv_unsigned y < HI.hl_img_lo HL \/ HI.hl_img_hi HL <= bv_unsigned y) -> bv_unsigned y < RC.alloc_ceiling ->
m2 y = m y /\ Fof LV (FRof Lg') y = false.
Proof.
intros Lg Lg' g c c' H H' m m2 lo B T N B' T' N' y KL KL' [X1 _] MI Hlo Hw Fy Himg Hc.
destruct IMG_hull as (U1 & U2 & _).
assert (Hnh : ~ (RDATA_LO <= bv_unsigned y < RIMG_HI)) by lia.
assert (Hm : m y <> None) by (destruct (wview_cases m y MI Hw) as [Hm|Hd]; [exact Hm| contradiction]).
assert (Hreg : in_regs (FRof Lg) y = false).
{ destruct (in_regs (FRof Lg) y) eqn:E; [|reflexivity]. rewrite (in_regs_Fof _ y E) in Fy. discriminate. }
assert (HHy : H y = false).
{ destruct (H y) eqn:E; [|reflexivity]. destruct (H_place _ _ _ _ _ _ _ _ _ y KL E) as (_ & _ & P3). congruence. }
pose proof (GHof_true m Lg H lo y Hm Hnh ltac:(lia) Hreg HHy) as GHy.
split; [exact (X1 y GHy)|].
destruct (kla_G _ _ _ _ _ _ _ _ _ _ _ _ _ KL' y GHy) as (_ & G2 & G3).
rewrite (Fof_FRof _ Lg' g c' H' m2 B' T' N' y KL'), G2, <- (KLA_H_shg _ Lg' g c' H' m2 B' T' N' y KL'), G3.
rewrite (Fof_FRof _ Lg g c H m B T N y KL) in Fy. apply orb_false_elim in Fy as [_ F0]. rewrite F0. reflexivity.
Qed.

Lemma mng_pres : forall Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' (LBx : list MB.block) y,
KLA0 Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' ->
RC.alloc_ceiling <= lo -> lo <= sp ->
MGI.mpres segs S LBx sp (mrestrict (HG (GHof m Lg H lo) H) m) (mrestrict (HG (GHof m Lg H lo) H') m2) ->
MGI.mclient S LBx sp (bv_unsigned y) ->
PK Lg lo y = true ->
m2 y = m y /\ (wview segs m y <> None -> wview segs m2 y <> None).
Proof.
intros Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx y KL KL' Hlo Hsp PRES Hcl Hp.
pose proof (bv_unsigned_in_range _ y) as Hr. unfold bv_modulus in Hr.
destruct (PRES (bv_unsigned y) ltac:(lia) Hcl) as [E W].
change (OM.wa (bv_unsigned y)) with (wa (bv_unsigned y)) in E, W. rewrite (wa_u y) in E, W.
pose proof (coarse_nothid Lg g c H m B T N lo y KL Hlo Hp) as N1.
pose proof (post_nothid Lg Lg' g c c' H H' m m2 lo B T N B' T' N' y KL KL' Hlo (or_introl Hp)) as N2.
unfold mrestrict in E. rewrite N1, N2 in E. split; [exact E|].
unfold wview, mrestrict in W. rewrite N1, N2 in W. exact W.
Qed.

Lemma heapA0g_ledger : forall Bc P Tc Nc FRl RSV g LB LM FR B m c,
HEAPA0g L LV Bc P Tc Nc DL RE DCo FRl RSV g LB LM FR B m c ->
g_spent g + JH.bB B + RSV <= Bc /\ zlen (g_chunks g) + 1 <= kMaxCnt /\ 0 <= JH.bB B.
Proof.
intros Bc P Tc Nc FRl RSV g LB LM FR B m c (ps & LBd & FSd & _ & _ & _ & AI & [[GP GSP] _] & Hcap & Hbud & _ & _ & _ & _ & _ & _ & Hb0 & Hd0 & Hn0).
set (X := map ablk_id LBd) in *.
assert (HlenX : zlen X <= kCapN) by (unfold X, zlen in *; rewrite length_map; lia).
pose proof (cap_ok_reg X _ AI (cap_ok_of_len X HlenX)) as Hreg.
destruct AI as [AIx _]. pose proof (SP_le (ps_a ps) (ai_cls _ _ _ _ AIx) (proj1 (proj2 (ai_nres _ _ _ _ AIx)))) as HSP.
assert (Hlen : zlen (g_chunks g) = zlen (as_reg (ps_a ps))) by (unfold zlen; rewrite (Permutation_length GP), length_map; reflexivity).
split; [lia|]. split; [lia| exact Hb0].
Qed.

Lemma rauxv_unhide : forall Lg Lg' g c c' H H' m m2 lo B T N B' T' N',
KLA0 Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' -> RC.alloc_ceiling <= lo -> lo <= BAUX ->
rauxv_ok (mrestrict (HG (GHof m Lg H lo) H') m2) BAUX -> rauxv_ok m2 BAUX.
Proof.
intros Lg Lg' g c c' H H' m m2 lo B T N B' T' N' KL KL' Hlo HB AUX.
apply (MGI.ml_auxv_agree segs S ML _ m2 BAUX AUX). intros a Ha Hf. unfold mrestrict.
rewrite (post_nothid Lg Lg' g c c' H H' m m2 lo B T N B' T' N' (wa a) KL KL' Hlo); [reflexivity|]. left.
destruct Hf as [Hb|Hs]; [apply PK_stack; [exact Ha| lia]| apply PK_hull; [exact Ha| apply stat_in_hull; left; exact Hs]].
Qed.

Lemma lm_keep : forall Lg Lg' g c c' H H' m m2 lo B T N B' T' N' y,
KLA0 Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' ->
MI segs (GHof m Lg H lo) m H Lg m2 H' Lg' ->
in_regs (FRof Lg) y = true -> m2 y <> None -> in_regs (FRof Lg') y = true.
Proof.
intros Lg Lg' g c c' H H' m m2 lo B T N B' T' N' y KL KL' [_ X3] Hr Hm2.
rewrite in_regs_FRof in Hr |- *. apply orb_prop in Hr as [Hg|H0]; [| rewrite H0; apply orb_true_r].
destruct (KLA_grp_facts _ Lg g c H m B T N y KL Hg) as (Hoff & _ & Nb & _).
destruct (X3 y ltac:(unfold offseg; rewrite Hoff; reflexivity) Hm2) as [Hh|[Hg'|(_ & Hg0 & _)]].
- exfalso. pose proof (kla_Hrange _ _ _ _ _ _ _ _ _ _ _ _ _ KL' y Hh). lia.
- rewrite Hg'. reflexivity.
- congruence.
Qed.

Lemma newblk_regs : forall Lg Lg' g c c' H H' m m2 lo B T N B' T' N' y,
KLA0 Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' ->
MI segs (GHof m Lg H lo) m H Lg m2 H' Lg' ->
m2 y <> None -> HG (GHof m Lg H lo) H' y = false ->
(bv_unsigned y + 1 <= MGI.mg_img_lo S \/ RIMG_HI <= bv_unsigned y) -> bv_unsigned y < lo ->
in_regs (FRof Lg') y = true.
Proof.
intros Lg Lg' g c c' H H' m m2 lo B T N B' T' N' y KL KL' [_ X3] Hm2 Hnh Himg Hlt.
destruct (MGI.ml_hull segs S ML) as (D1 & D2 & D3).
unfold HG in Hnh. apply orb_false_elim in Hnh as [Hh' Hgh].
destruct (X3 y ltac:(unfold offseg; rewrite (IMG_seg_G _ Himg); reflexivity) Hm2) as [Hh|[Hg'|(Hm & Hg0 & Hh0)]].
- congruence.
- rewrite in_regs_FRof, Hg'. reflexivity.
- rewrite in_regs_FRof. replace (in_regs FR0 y) with true; [apply orb_true_r|]. symmetry.
destruct (in_regs (FRof Lg) y) eqn:Er.
+ rewrite in_regs_FRof, Hg0 in Er. exact Er.
+ exfalso. rewrite (GHof_true m Lg H lo y Hm ltac:(lia) Hlt Er Hh0) in Hgh. discriminate.
Qed.

Hypothesis OBL_STAT_mng : forall Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' (LBx : list MB.block),
KLA0 Lg g c H m B T N ->
KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' ->
MI segs (GHof m Lg H lo) m H Lg m2 H' Lg' ->
mem_inv segs m -> mem_inv segs m2 ->
RC.alloc_ceiling <= lo -> lo <= sp ->
MGI.mpres segs S LBx sp (mrestrict (HG (GHof m Lg H lo) H) m) (mrestrict (HG (GHof m Lg H lo) H') m2) ->
stk segs m2 lo sp ->
STAT m -> STAT m2.

Lemma stk_after_mng : forall Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' (LBx : list MB.block),
KLA0 Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' ->
MI segs (GHof m Lg H lo) m H Lg m2 H' Lg' -> mem_inv segs m ->
RC.alloc_ceiling <= lo -> lo <= sp ->
MGI.mpres segs S LBx sp (mrestrict (HG (GHof m Lg H lo) H) m) (mrestrict (HG (GHof m Lg H lo) H') m2) ->
stk segs m2 lo sp ->
stk segs m RC.alloc_ceiling (hi_top RE) -> stk segs m2 RC.alloc_ceiling (hi_top RE).
Proof.
intros Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx KL KL' HMI MI Hlo Hsp PRES STK2 (I0 & I1 & HI).
pose proof (@RC.alloc_ceiling_range RC__) as Hc. destruct IMG_data as (D1 & D2 & D3). unfold kLowEnd in D3.
split; [exact I0|]. split; [exact I1|]. intros a Ha. unfold hi_top in *.
destruct (Z.lt_ge_cases a lo) as [Hlt|Hge].
-
destruct (HI a Ha) as [W R]. set (y := wa a). assert (Ey : bv_unsigned y = a) by (unfold y; apply wa_unsigned; lia).
assert (Hm : m y <> None) by (destruct (wview_cases m y MI W) as [Hm|Hd]; [exact Hm| rewrite Ey in Hd; lia]).
assert (Hreg : in_regs (FRof Lg) y = false).
{ destruct (in_regs (FRof Lg) y) eqn:E; [|reflexivity]. pose proof (KLA_F_low _ Lg g c H m B T N KL y (in_regs_Fof _ y E)) as Hl. rewrite Ey in Hl. lia. }
assert (HHy : H y = false).
{ destruct (H y) eqn:E; [|reflexivity]. destruct (H_place _ _ _ _ _ _ _ _ _ y KL E) as (_ & _ & P3).
pose proof (KLA_F_low _ Lg g c H m B T N KL y P3) as Hl. rewrite Ey in Hl. lia. }
pose proof (GHof_true m Lg H lo y Hm ltac:(rewrite Ey; lia) ltac:(rewrite Ey; lia) Hreg HHy) as GHy.
pose proof (proj1 HMI y GHy) as E. unfold wview, mrd in *. fold y. rewrite E. split; assumption.
- destruct (Z.lt_ge_cases a sp) as [Hlt2|Hge2]; [apply STK2; lia|].
destruct (HI a Ha) as [W R]. set (y := wa a). assert (Ey : bv_unsigned y = a) by (unfold y; apply wa_unsigned; lia).
destruct (mng_pres Lg Lg' g c c' H H' m m2 lo sp B T N B' T' N' LBx y KL KL' Hlo Hsp PRES ltac:(left; rewrite Ey; exact Hge2) (PK_stack Lg lo a ltac:(lia) Hge)) as [E _].
unfold wview, mrd in *. fold y. rewrite E. split; assumption.
Qed.

Lemma heapA1_after : forall k k' Lg Lg' g c c' H H' m m2 lo sp Bc Tc Nc B' T' N' LB LM LM' FR B (LBx : list MB.block) s' LB0' (errv2 : word),
HEAPA0g L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) g LB LM FR B m c ->
KLA0 Lg g c H m Bc Tc Nc ->
KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' ->
MI segs (GHof m Lg H lo) m H Lg m2 H' Lg' ->
RC.alloc_ceiling <= lo -> lo <= sp ->
0 <= k' -> Bc - (k - k') * SC <= B' -> T' + k' * kMaxChunk <= TMAX -> N' + k' <= NMAX ->
(forall r y, In r (doranges Lg') -> fst r <= bv_unsigned y < fst r + snd r -> in_regs FR0 y = true) ->
MGI.mpres segs S LBx sp (mrestrict (HG (GHof m Lg H lo) H) m) (mrestrict (HG (GHof m Lg H lo) H') m2) ->
stk segs m2 lo sp -> (forall a, wstat a -> wview segs m2 (wa a) <> None) -> mem_inv segs m2 ->
OT.rw_cells segs m2 (RATP - 164) [OC.C4 errv2] ->
(forall a n, In (a, n) LM' -> MGI.mrange S a n /\ forall x, a <= x < a + n -> in_regs (FRof Lg') (wa x) = true /\ m2 (wa x) <> None) ->
Permutation LM' (map zblk LB0') -> RHEAP s' LB0' m2 -> SG.HSIM s' Lg' LB0' ->
Permutation (KV.ld_live Lg') (map MB.blk_slot LB0') -> List.NoDup (KV.ld_live Lg') -> Forall (fun b => 1 <= MB.blk_size b) LB0' ->
rauxv_ok m2 BAUX -> 25 + 8 * k' <= MSU.cntm (MG.ps_m s') ->
Forall (fun b : HI.blk => wr_at segs (mrestrict (Fof LV (FRof Lg)) m) (fst b) (snd b)
/\ (fst b + snd b <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= fst b)
/\ fst b + snd b <= RC.alloc_ceiling) (fr_ivs0 L FR) ->
STAT m ->
HEAPA1 k' LB LM' FR B m2 c'.
Proof.
intros k k' Lg Lg' g c c' H H' m m2 lo sp Bc Tc Nc B' T' N' LB LM LM' FR B LBx s' LB0' errv2
HA0 KL KL' HMI Hlo Hsp Hk' HBk HTk HNk HORd PRES STK2 HST MI2 ERRC HLM' PLM' RH2 SIM' PLV' NDL' SZ' AUX2 CNT' FRW STA.
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.
assert (MI : mem_inv segs m) by (destruct HA0 as (ps & LBd & FSd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _); exact MI).
destruct (mng_frame Lg Lg' g c c' H H' m m2 lo sp Bc Tc Nc B' T' N' LBx KL KL' HMI MI MI2 Hlo Hsp PRES STK2 HST) as [MU WM].
pose proof (asan_byte_keep Lg Lg' g c c' H H' m m2 lo Bc Tc Nc B' T' N') as KEEP.
assert (HA0' := HA0). destruct HA0 as (ps & LBd & FSd & RUN & ELB & EFR & AI & G & Hcap & Hbud & K & HC & Hh & _ & HWR & HLM & Hb).
exists g, Lg', H', B', T', N', s', LB0'.
split; [| split; [exact (KLA_GH_none LV PERM0 TMAX NMAX _ Lg' g c' H' m2 B' T' N' KL')|
split; [exact Hk'| split; [exact HTk| split; [exact HNk| split; [exact HORd| split; [exact HLM'|
split; [exact PLM'| split; [exact RH2| split; [exact SIM'| split; [exact PLV'| split; [exact NDL'|
split; [exact SZ'| split; [exact AUX2| split; [exact CNT'|]]]]]]]]]]]]]]].
-
exists ps, LBd, FSd.
split.
{
set (ma := mrestrict (Fof LV (FRof Lg)) m) in *. set (mb := mrestrict (Fof LV (FRof Lg')) m2) in *.
set (inE := fun x : word => (RATP - 164 <=? bv_unsigned x) && (bv_unsigned x <? RATP - 164 + 4)).
set (mi := fun x : word => if inE x then ma x else mb x).
assert (inE_iff : forall x, inE x = true <-> RATP - 164 <= bv_unsigned x < RATP - 164 + 4) by (intros x; unfold inE; lia).
assert (MU1 : munch [(RC.alloc_ceiling, 2^64); MGI.mg_ctx S] ma mi).
{ intros x Hout. unfold mi. destruct (inE x) eqn:Ex; [reflexivity|]. apply MU. unfold WMNG, MGI.mg_wstat.
destruct (MGI.mg_ctx S) as [c1 c2]. cbn [outside fst snd] in Hout |- *. destruct Hout as (O1 & O2 & _).
split; [exact O1|]. split; [exact O2|]. split; [| exact I].
intros Hx. assert (inE x = true) by (apply inE_iff; lia). congruence. }
assert (WM1 : wmono segs ma mi).
{ intros x Hw. unfold mi. destruct (inE x) eqn:Ex.
- unfold wview in Hw |- *. rewrite Ex. exact Hw.
- assert (Ew : wview segs (fun x0 : word => if inE x0 then ma x0 else mb x0) x = wview segs mb x) by (unfold wview; rewrite Ex; reflexivity).
rewrite Ew. exact (WM x Hw). }
assert (RUN1 : dc_run _ _ _ _ DCo ps LBd FSd RE mi).
{ apply (dc_run_frame _ _ _ _ DCo ps LBd FSd RE _ _ [(RC.alloc_ceiling, 2^64); MGI.mg_ctx S] RUN MU1 WM1).
constructor; [left; cbn [fst]; lia|]. constructor; [| constructor].
right; left. intros a Ha. apply OBL_R1P. right. exact Ha. }
apply (dc_errno_frame _ _ _ _ DCo ps LBd FSd RE mi mb errv2 RUN1).
- intros x Hout. unfold mi. destruct (inE x) eqn:Ex; [| reflexivity]. exfalso. apply inE_iff in Ex.
cbn [outside] in Hout. rewrite L_errno, L_tp2 in Hout. lia.
- intros x Hw. unfold mi in Hw. destruct (inE x) eqn:Ex.
+ apply (WM x). unfold wview in Hw |- *. rewrite Ex in Hw. exact Hw.
+ unfold wview in Hw |- *. rewrite Ex in Hw. exact Hw.
- rewrite L_errno, L_tp2. apply (proj1 (rw_cells_D segs mb (RATP - 164) [OC.C4 errv2])).
unfold mb. apply rw_cells_hide; [| exact ERRC].
intros x Hx. cbn [OC.cells_size OC.csize Nat.add] in Hx. change (Z.of_nat 4) with 4 in Hx.
destruct (Fof LV (FRof Lg') (wa x)) eqn:Fx; [| reflexivity]. exfalso.
pose proof (@RC.alloc_ceiling_range RC__) as Hcr.
assert (Hhull : RDATA_LO <= x < RIMG_HI) by (apply stat_in_hull; right; apply wstat_iff; right; lia).
apply (F_off_data _ Lg' g c' H' m2 B' T' N' (wa x) KL' Fx). destruct IMG_data as (I1 & I2 & I3). unfold kLowEnd in *.
rewrite wa_unsigned by lia. exact Hhull. }
split; [exact ELB|]. split; [exact EFR|]. split; [exact AI|]. split; [exact G|]. split; [exact Hcap|].
split; [nia|].
split; [exact (kla_ki _ _ _ _ _ _ _ _ _ _ _ _ _ KL')|]. split; [exact (kla_cinv _ _ _ _ _ _ _ _ _ _ _ _ _ KL')|].
split; [exact (kla_halt _ _ _ _ _ _ _ _ _ _ _ _ _ KL')|]. split; [exact MI2|].
split.
{ apply Forall_forall. intros b Hb0. destruct (proj1 (Forall_forall _ _) HWR b Hb0) as ((W0 & W1 & HWb) & HFb).
assert (Hin : In (ablk_addr b, ablk_size b) LB) by (rewrite ELB; apply in_map_iff; exists b; split; [reflexivity| exact Hb0]).
destruct (heapA0_blk L LV Bc _ Tc Nc DL RE DCo _ _ LB LM FR B m c _ _ (ex_intro _ g HA0') Hin) as (Bn & _ & Bp & Bc1 & _).
pose proof (heapA0_blk_img L LV Bc _ Tc Nc DL RE DCo _ _ L_img LB LM FR B m c _ _ (ex_intro _ g HA0') Hin) as Bimg.
assert (KB : forall i, 0 <= i < ablk_size b -> m2 (wa (ablk_addr b + i)) = m (wa (ablk_addr b + i)) /\ Fof LV (FRof Lg') (wa (ablk_addr b + i)) = false).
{ intros i Hi. apply (KEEP _ KL KL' HMI MI Hlo (HWb i Hi) (HFb (ablk_addr b + i) ltac:(lia))); rewrite wa_unsigned by lia; lia. }
split.
- split; [exact W0|]. split; [exact W1|]. intros i Hi. rewrite (wview_eq m m2 _ (proj1 (KB i Hi))). exact (HWb i Hi).
- intros x Hx. replace x with (ablk_addr b + (x - ablk_addr b)) by lia. apply KB. lia. }
split.
{ intros a n x Hin Hx. apply in_regs_Fof. exact (proj1 (proj2 (HLM' a n Hin) x Hx)). }
destruct Hb as (Hb1 & Hb2 & Hb3 & (dn & HDn & HDcap) & HSTK & HQ). split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb3|].
split.
{
exists dn. split; [| exact HDcap].
apply (depot_keep_of_munch segs DL WMNG _ _ MU WM); [| exact HDn]. unfold WMNG. constructor; [right; cbn [fst]; destruct L_dpn; lia| exact L_dpn_wstat]. }
split; [| exact HQ].
exact (stk_after_mng Lg Lg' g c c' H H' m m2 lo sp Bc Tc Nc B' T' N' LBx KL KL' HMI MI Hlo Hsp PRES STK2 HSTK).
-
split; [| exact (OBL_STAT_mng Lg Lg' g c c' H H' m m2 lo sp Bc Tc Nc B' T' N' LBx KL KL' HMI MI MI2 Hlo Hsp PRES STK2 STA)].
apply Forall_forall. intros b Hb0. destruct (proj1 (Forall_forall _ _) FRW b Hb0) as ((W0 & W1 & HWb) & Himg & Hc).
split; [| split; [exact Himg| exact Hc]].
split; [exact W0|]. split; [exact W1|]. intros i Hi. specialize (HWb i Hi).
assert (Fy : Fof LV (FRof Lg) (wa (fst b + i)) = false).
{ destruct (Fof LV (FRof Lg) (wa (fst b + i))) eqn:E; [|reflexivity]. exfalso. apply HWb. unfold wview, mrestrict. rewrite E.
rewrite (KLA_F_off _ Lg g c H m Bc Tc Nc KL _ E). reflexivity. }
assert (Hw : wview segs m (wa (fst b + i)) <> None) by (unfold wview, mrestrict in HWb |- *; rewrite Fy in HWb; exact HWb).
destruct (KEEP _ KL KL' HMI MI Hlo Hw Fy ltac:(rewrite wa_unsigned by lia; lia) ltac:(rewrite wa_unsigned by lia; lia)) as [E Fy'].
unfold wview, mrestrict. rewrite Fy', E. exact Hw.
Qed.

Lemma rheap_unhide_post : forall Lg Lg' g c c' H H' m m2 lo B T N B' T' N' s'' LBn,
KLA0 Lg g c H m B T N -> KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' -> RC.alloc_ceiling <= lo ->
(forall r y, In r (doranges Lg') -> fst r <= bv_unsigned y < fst r + snd r -> in_regs FR0 y = true) ->
SG.HSIM s'' Lg' LBn -> RHEAP s'' LBn (mrestrict (HG (GHof m Lg H lo) H') m2) -> RHEAP s'' LBn m2.
Proof.
intros Lg Lg' g c c' H H' m m2 lo B T N B' T' N' s'' LBn KL KL' Hlo HORd SIM RH.
apply (OBL_MNG_AGREE s'' Lg' LBn _ m2 RH SIM); [intros b0 l0 Hbl0; exact (proj1 (kla_groups _ _ _ _ _ _ _ _ _ _ _ _ _ KL' b0 l0 Hbl0))|]. intros a Ha Hf. unfold mrestrict.
rewrite (post_nothid Lg Lg' g c c' H H' m m2 lo B T N B' T' N' (wa a) KL KL' Hlo); [reflexivity|].
destruct Hf as [Hs|[(b & l & Hin & Hr)|(r & Hr & Hy)]].
- left. apply PK_hull; [exact Ha| apply stat_in_hull; left; exact Hs].
- right. apply in_grp_true. exists b, l. rewrite (wa_unsigned a Ha). auto.
- left. apply PK_regs. rewrite in_regs_FRof. rewrite (HORd r (wa a) Hr ltac:(rewrite (wa_unsigned a Ha); exact Hy)). apply orb_true_r.
Qed.

Lemma mng_heap_pres : forall k Lg Lg' g c c' H H' m m2 lo sp Bc Tc Nc B' T' N' LB LM LMx FR B (LB0 LBx : list MB.block),
HEAPA0g L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) g LB LM FR B m c ->
KLA0 Lg g c H m Bc Tc Nc -> KLA LV PERM0 TMAX NMAX (GHof m Lg H lo) Lg' g c' H' m2 B' T' N' ->
MI segs (GHof m Lg H lo) m H Lg m2 H' Lg' -> RC.alloc_ceiling <= lo -> lo <= sp ->
MGI.mpres segs S LBx sp (mrestrict (HG (GHof m Lg H lo) H) m) (mrestrict (HG (GHof m Lg H lo) H') m2) ->
(forall b, In b LB0 -> In b LBx) ->
(forall a n, In (a, n) LMx -> MGI.mrange S a n /\ forall x, a <= x < a + n -> in_regs (FRof Lg) (wa x) = true /\ m (wa x) <> None) ->
(forall a n, In (a, n) LMx -> exists b0, In b0 LB0 /\ MB.blk_addr b0 = a /\ MB.blk_size b0 = n) ->
Forall (fun b : HI.blk => wr_at segs (mrestrict (Fof LV (FRof Lg)) m) (fst b) (snd b)
/\ (fst b + snd b <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= fst b)
/\ fst b + snd b <= RC.alloc_ceiling) (fr_ivs0 L FR) ->
HI.heap_pres HL (LB ++ LMx ++ fr_ivs0 L FR) sp m m2.
Proof.
intros k Lg Lg' g c c' H H' m m2 lo sp Bc Tc Nc B' T' N' LB LM LMx FR B LB0 LBx HA0 KL KL' HMI Hlo Hsp PRES Hsub HLMr HLM0 FRW.
assert (MI : mem_inv segs m) by (destruct HA0 as (ps & LBd & FSd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _); exact MI).
pose proof (mng_pres Lg Lg' g c c' H H' m m2 lo sp Bc Tc Nc B' T' N' LBx) as PR.
pose proof (asan_byte_keep Lg Lg' g c c' H H' m m2 lo Bc Tc Nc B' T' N') as KEEP.
intros a Ha Hcl. change (OM.wa a) with (wa a).
assert (Ua : bv_unsigned (wa a) = a) by (apply wa_unsigned; exact Ha).
destruct Hcl as [Hs|[Hst|(b & Hb & Hr)]].
- apply (PR (wa a) KL KL' Hlo Hsp PRES); [rewrite Ua; left; exact Hs| apply PK_stack; [exact Ha| lia]].
- destruct (L_static2 a Hst) as [Hd Hns].
apply (PR (wa a) KL KL' Hlo Hsp PRES); [rewrite Ua; right; left; split; assumption| apply PK_hull; assumption].
- unfold HI.blk_addr, HI.blk_size in Hr. apply in_app_iff in Hb as [Hb|Hb]; [| apply in_app_iff in Hb as [Hb|Hb]].
+
assert (HA0' := HA0). destruct HA0 as (ps & LBd & FSd & _ & ELB & _ & _ & _ & _ & _ & _ & _ & _ & _ & HWR & _).
destruct b as [ba bn]. cbn [fst snd] in Hr.
destruct (heapA0_blk L LV Bc _ Tc Nc DL RE DCo _ _ LB LM FR B m c _ _ (ex_intro _ g HA0') Hb) as (Bn & _ & Bp & Bc1 & _).
pose proof (heapA0_blk_img L LV Bc _ Tc Nc DL RE DCo _ _ L_img LB LM FR B m c _ _ (ex_intro _ g HA0') Hb) as Bimg.
rewrite ELB in Hb. apply in_map_iff in Hb as (bd & Eb & Hbd). unfold blk_of in Eb. injection Eb as <- <-.
destruct (proj1 (Forall_forall _ _) HWR bd Hbd) as ((W0 & W1 & HWb) & HFb).
assert (Hw : wview segs m (wa a) <> None) by (replace a with (ablk_addr bd + (a - ablk_addr bd)) by lia; apply HWb; lia).
destruct (KEEP (wa a) KL KL' HMI MI Hlo Hw (HFb a Hr) ltac:(rewrite Ua; lia) ltac:(rewrite Ua; lia)) as [E _].
split; [exact E| rewrite (wview_eq m m2 _ E); auto].
+
destruct b as [ba bn]. cbn [fst snd] in Hr. destruct (HLM0 ba bn Hb) as (b0 & Hb0 & Ea & En).
apply (PR (wa a) KL KL' Hlo Hsp PRES).
* rewrite Ua. right; right. exists b0. split; [apply Hsub; exact Hb0| rewrite Ea, En; exact Hr].
* apply PK_regs. exact (proj1 (proj2 (HLMr ba bn Hb) a Hr)).
+
destruct (proj1 (Forall_forall _ _) FRW b Hb) as ((W0 & W1 & HWb) & Himg & Hc).
assert (HWa : wview segs (mrestrict (Fof LV (FRof Lg)) m) (wa a) <> None) by (replace a with (fst b + (a - fst b)) by lia; apply HWb; lia).
assert (Fy : Fof LV (FRof Lg) (wa a) = false).
{ destruct (Fof LV (FRof Lg) (wa a)) eqn:E; [|reflexivity]. exfalso. apply HWa. unfold wview, mrestrict. rewrite E.
rewrite (KLA_F_off _ Lg g c H m Bc Tc Nc KL _ E). reflexivity. }
assert (Hw : wview segs m (wa a) <> None) by (unfold wview, mrestrict in HWa |- *; rewrite Fy in HWa; exact HWa).
destruct (KEEP (wa a) KL KL' HMI MI Hlo Hw Fy ltac:(rewrite Ua; lia) ltac:(rewrite Ua; lia)) as [E _].
split; [exact E| rewrite (wview_eq m m2 _ E); auto].
Qed.

Theorem hiA_malloc2_1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (n lo : Z) (errv : word),
HEAPA1 k LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - HI.hl_stack HL ->
bv_unsigned sp <= BAUX ->
OT.rw_cells segs m (HI.hl_tp HL - 164) [OC.C4 errv] ->
tp = Z_to_bv 64 (HI.hl_tp HL) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 4096 ->
1 <= k ->
(forall ms' m' c' (r : Z) (errv' : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 r) m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 HI.ENOMEMv /\ HEAPA1 (k - 1) LB LM FR B m' c')
\/ (r <> 0 /\ (exists junk, OT.rw_cells segs m' r [OC.CB (Z.to_nat n) junk]) /\ HEAPA1 (k - 1) LB ((r, n) :: LM) FR B m' c') ) ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_malloc2 HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B n lo errv
HP Hstk Hlo Hlo2 HB ERR Htp Ha0 Hn Hk HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil. pose proof (MGI.ml_stack segs S ML) as Hst0.
assert (MI : mem_inv segs m) by (destruct HA0 as (ps & LBd & FSd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI & _); exact MI).
set (GH := GHof m Lg H lo).
pose proof (GHof_off m Lg H lo MI) as GHoff. fold GH in GHoff.
pose proof (KLA_GHof Lg g c H m Bc Tc Nc lo KL) as KLg. fold GH in KLg.
rewrite L_tp2 in ERR, Htp.
destruct (coarse_pre Lg g c H m Bc Tc Nc lo (bv_unsigned sp) s LB0 errv KL Hlo ltac:(lia) HB HOR RH SIM AUX Hstk ERR MI) as (RHc & AUXc & STKc & ERRc & MIc).
fold GH in RHc, AUXc, STKc, ERRc, MIc.
assert (Uerr : (bv_unsigned tp + (-164)) = RATP - 164).
{ rewrite Htp. destruct IMG_data as (D1 & D2 & D3). unfold kLowEnd in D3.
pose proof (stat_in_hull (RATP + -164) ltac:(right; apply wstat_iff; right; lia)) as Hh.
rewrite unsigned_lit by lia. reflexivity. }
pose proof (MGI.ml_malloc segs S ML ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc
(mrestrict (HG GH H) m) s LB0 n lo BAUX errv RHc AUXc HB STKc Hlo ltac:(lia)
ltac:(rewrite Uerr; exact ERRc) MIc Htp Ha0 ltac:(lia)) as IMPL.
rewrite <- L_malloc2 in IMPL.
match goal with |- AJv _ _ _ _ ?st => set (msv := st) end.
match type of IMPL with MO.implM _ _ _ _ ?st => change st with (restrict (HG GH H) msv) in IMPL end.
unfold MG.raw_malloc in IMPL. apply implM_get_inv in IMPL. apply IR.implM_bind_inv in IMPL.
pose proof SIM as (st & BL & LS & LB1 & PB1 & Est & INV & CORR0).
pose proof (SG.cmalloc_ctreeI st Lg BL LS n INV (SG.HSIM_live_sub Lg LB0 st BL LB1 PB1 CORR0 PLV) ltac:(lia)) as CT. rewrite Est in CT.
assert (Hnth : 0 <= n < SM.MMAP_THRESHOLD) by (unfold SM.MMAP_THRESHOLD; lia).
pose proof (cmalloc_tree_supp (MG.ps_m s) n Lg _ ltac:(lia) Hnth CT) as TS.
destruct (heapA0g_ledger _ _ _ _ _ _ _ _ _ _ _ _ _ HA0) as (Hsp & Hreg & HbB0).
unfold AJv.
refine (membed_vj_coarse segs LA LV PERM0 TMAX NMAX LL0 Hwx Hsegs Hsh Hbx Hbc Hbase47 GH GHoff (JS segs T) (js_nclosed segs T) segs_low
(SM.cmalloc (MG.ps_m s) n) 1%nat _ s _ msv c g Lg H Bc Tc Nc IMPL CT TS KLg _ _ _ _ _).
{ change (Z.of_nat 1) with 1. fold SC. assert (HSC0 : 0 <= SC) by (vm_compute; discriminate). nia. }
{ intros _. exact Hreg. }
{ change (Z.of_nat 1) with 1. assert (0 <= kMaxChunk) by (unfold kMaxChunk; lia). nia. }
{ change (Z.of_nat 1) with 1. lia. }
intros [cs' oc] s' msv' Lg' c' H' B' T' N' Hleaf HPost CP Em Eb KL' HB' HT' HN' HOR' HMI HVO HVS. cbn [snd] in HPost.
apply implM_upd_ret_inv in Hleaf.
refine (vj_coarse_evt segs LV PERM0 TMAX NMAX Hwx Hsegs GH GHoff (JS segs T) (js_nclosed segs T) segs_low Lg' g c' H' msv' B' T' N' _ KL' Hleaf _).
intros ms2 PM KL2 Hh2 Hn2.
pose proof (MI_evt segs GH _ _ _ _ _ _ _ HMI Hh2 Hn2) as HMI2.
destruct PM as (u0 & u1 & u2 & ra0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m'c & errv' & Ems & MI' & ST' & ERR' & AUX' & PRES & RES).
destruct (restrict_MS_inv (HG GH H') ms2 _ _ _ _ _ _ _ Ems) as [Ems2 Em'c]. set (m2 := ms_mem ms2) in *. subst m'c.
change (ms_mem msv) with m in HMI2.
assert (HGoff' : H_off_segments segs (HG GH H')).
{ intros y Hy. unfold HG in Hy. apply orb_prop in Hy as [Hy|Hy]; [apply segs_low; exact (kla_Hrange _ _ _ _ _ _ _ _ _ _ _ _ _ KL2 y Hy)| exact (GHoff y Hy)]. }
pose proof (mem_inv_unhideK _ HGoff' m2 MI') as MI2.
pose proof (stk_unhide segs _ HGoff' m2 lo _ ST') as STK2.
rewrite Uerr in ERR'. pose proof (rw_cells_unhide _ HGoff' m2 _ _ ERR') as ERR2.
pose proof (rauxv_unhide Lg Lg' g c c' H H' m m2 lo Bc Tc Nc B' T' N' KL KL2 Hlo ltac:(lia) AUX') as AUX2.
pose proof (MCO.cmalloc_count_cpath (MG.ps_m s) n Lg Lg' (cs', oc) ltac:(lia) Hnth CP) as CNT'. cbn [fst] in CNT'.
pose proof (Q4en.cpath_live CP) as LIVE'.
rewrite <- Est in CP. destruct (MIC.cmalloc_leaf_INVL st Lg BL LS n Lg' cs' oc INV ltac:(lia) CP) as (_ & st1 & LS1 & Est1 & RES1).
destruct HVO as (V1 & V2 & V3 & V4 & V5 & V6).
assert (HVM : HI.model_vm_only (cfg_model c) (cfg_model c')) by (unfold HI.model_vm_only; repeat split; try assumption; exact (vmst_init_sp _ _ HVS)).
assert (HORd : forall r y, In r (doranges Lg') -> fst r <= bv_unsigned y < fst r + snd r -> in_regs FR0 y = true).
{ destruct HOR' as (_ & O2 & O3). unfold doranges in *. rewrite O2, O3. exact HOR. }
assert (HLM0 : forall a n0, In (a, n0) LM -> exists b0, In b0 LB0 /\ MB.blk_addr b0 = a /\ MB.blk_size b0 = n0).
{ intros a n0 Hin. pose proof (Permutation_in _ PLM Hin) as Hi. apply in_map_iff in Hi as (b0 & E & Hb0). unfold zblk in E. injection E as E1 E2. exists b0. auto. }
assert (Hsp' : lo <= bv_unsigned sp) by lia.
assert (HERRW : forall a, RATP + -164 <= a < RATP + -164 + 4 -> wview segs m2 (wa a) <> None).
{ intros a Ha. destruct ERR2 as [_ (E0 & E1 & EW)]. replace a with (RATP - 164 + (a - (RATP - 164))) by lia. apply EW. cbn. lia. }
assert (HB1 : Bc - SC <= B') by (unfold SC; change (Z.of_nat 1) with 1 in HB'; lia).
assert (HT1 : T' <= Tc + kMaxChunk) by (change (Z.of_nat 1) with 1 in HT'; lia).
assert (HN1 : N' <= Nc + 1) by (change (Z.of_nat 1) with 1 in HN'; lia).
assert (HOLD : forall Lx, KLA LV PERM0 TMAX NMAX GH Lx g c' H' m2 B' T' N' -> QNLn.Mq0.MI segs GH m H Lg m2 H' Lx ->
forall a n0, In (a, n0) LM -> MGI.mrange S a n0 /\
forall x, a <= x < a + n0 -> in_regs (FRof Lx) (wa x) = true /\ m2 (wa x) <> None).
{ intros Lx KLx HMIx a n0 Hin. destruct (HLMr a n0 Hin) as [Hrng Hb]. split; [exact Hrng|]. intros x Hx.
destruct (Hb x Hx) as [Hr Hm]. destruct (HLM0 a n0 Hin) as (b0 & Hb0 & Ea & En). destruct Hrng as (G1 & _ & G3 & G4 & _).
assert (Hx64 : 0 <= x < 2^64) by lia.
destruct (mng_pres Lg Lx g c c' H H' m m2 lo (bv_unsigned sp) Bc Tc Nc B' T' N' LB0 (wa x) KL KLx Hlo Hsp' PRES) as [E _].
{ rewrite (wa_unsigned x Hx64). right; right. exists b0. split; [exact Hb0| rewrite Ea, En; exact Hx]. }
{ apply PK_regs. exact Hr. }
split; [| rewrite E; exact Hm].
apply (lm_keep Lg Lx g c c' H H' m m2 lo Bc Tc Nc B' T' N' (wa x) KL KLx HMIx Hr). rewrite E. exact Hm. }
destruct oc as [c0|]; cbv beta iota in RES.
-
destruct RES as (Ar & junk & -> & RNG & RH' & BLK).
destruct RES1 as (off1 & _ & INV1 & _).
set (L'' := KV.set_live (c0 :: KV.ld_live Lg') Lg').
assert (KL'' : KLA LV PERM0 TMAX NMAX GH L'' g c' H' m2 B' T' N') by (apply KLA_set_live; exact KL2).
assert (SIM'' : SG.HSIM (MG.set_m cs' s') L'' (((c0, Q7S0.Mq1.fresh_off cs' c0 n), Ar, n) :: LB0)).
{ destruct (MGI.ml_hinv segs S ML _ _ _ RH') as (stn & LBa & Pa & Estn & HINVn). apply SG.HSIM_set_live.
exact (SG.HSIM_intro (MGI.mg_resv S) (MG.set_m cs' s') Lg' _ stn LBa _ st1 Lg' _ LS1 Pa Estn HINVn Est1 INV1 eq_refl). }
pose proof (rheap_unhide_post Lg L'' g c c' H H' m m2 lo Bc Tc Nc B' T' N' _ _ KL KL'' Hlo HORd SIM'' RH') as RH2.
pose proof (rw_cells_unhide _ HGoff' m2 _ _ BLK) as BLK2.
pose proof RNG as (R1 & R2 & R3 & R4 & R5).
apply (HK ms2 m2 c' Ar errv').
+ unfold HI.ret_state. exists u0, u1, u2, ua1, ua2, ua3, ua4, ua5, ua6, ua7, u3, u4, u5, u6. exact Ems2.
+ exact HVM.
+ exact STK2.
+ exact (mng_heap_pres k Lg L'' g c c' H H' m m2 lo (bv_unsigned sp) Bc Tc Nc B' T' N' LB LM LM FR B LB0 LB0 HA0 KL KL'' HMI2 Hlo Hsp' PRES (fun b Hb => Hb) HLMr HLM0 FRW).
+ rewrite L_tp2. exact ERR2.
+ right. split; [lia|]. split; [exists junk; exact BLK2|].
refine (heapA1_after k (k - 1) Lg L'' g c c' H H' m m2 lo (bv_unsigned sp) Bc Tc Nc B' T' N' LB LM ((Ar, n) :: LM) FR B LB0
(MG.set_m cs' s') (((c0, Q7S0.Mq1.fresh_off cs' c0 n), Ar, n) :: LB0) _
HA0 KL KL'' HMI2 Hlo Hsp' _ _ _ _ HORd PRES STK2 _ MI2 ERR2 _ _ RH2 SIM'' _ _ _ AUX2 _ FRW STA).
* lia.
* replace (k - (k - 1)) with 1 by lia. lia.
* unfold kMaxChunk in *. lia.
* lia.
* intros a Ha. apply wstat_iff in Ha as [Hc|He]; [exact (MGI.ml_ctx_wr segs S ML _ _ m2 a RH2 Hc)| exact (HERRW a He)].
* intros a n0 [E|Hin]; [| exact (HOLD L'' KL'' HMI2 a n0 Hin)]. injection E as <- <-. split; [exact RNG|]. intros x Hx.
assert (Hx64 : 0 <= x < 2^64) by lia.
assert (Hm2 : m2 (wa x) <> None).
{ destruct BLK2 as [_ (W0 & W1 & WB)]. cbn [OC.cells_size OC.csize Nat.add] in WB. rewrite Nat.add_0_r, Z2Nat.id in WB by lia.
specialize (WB (x - Ar) ltac:(lia)). replace (Ar + (x - Ar)) with x in WB by lia.
destruct (wview_cases m2 (wa x) MI2 WB) as [Hm|Hd]; [exact Hm|]. exfalso. rewrite (wa_unsigned x Hx64) in Hd.
destruct (MGI.ml_hull segs S ML) as (U1 & U2 & U3). lia. }
split; [| exact Hm2].
apply (newblk_regs Lg L'' g c c' H H' m m2 lo Bc Tc Nc B' T' N' (wa x) KL KL'' HMI2 Hm2).
-- destruct BLK as [_ WBc]. cbn [OC.cells_size OC.csize Nat.add] in WBc. rewrite Nat.add_0_r, Z2Nat.id in WBc by lia.
exact (wr_at_hidden_offK _ HGoff' m2 Ar n WBc x Hx).
-- rewrite (wa_unsigned x Hx64). lia.
-- rewrite (wa_unsigned x Hx64). lia.
* cbn [map]. unfold zblk at 1. cbn [MB.blk_addr MB.blk_size fst snd]. apply perm_skip. exact PLM.
* subst L''. cbn [KV.set_live KV.ld_live map MB.blk_slot fst]. rewrite LIVE'. apply perm_skip. exact PLV.
* subst L''. cbn [KV.set_live KV.ld_live]. constructor; [exact HPost| rewrite LIVE'; exact NDL].
* constructor; [cbn [MB.blk_size snd]; lia| exact SZ].
* cbn [MG.ps_m MG.set_m]. lia.
-
destruct RES as (-> & -> & RH').
assert (SIM'' : SG.HSIM (MG.set_m cs' s') Lg' LB0).
{ destruct (MGI.ml_hinv segs S ML _ _ _ RH') as (stn & LBa & Pa & Estn & HINVn).
exact (SG.HSIM_intro (MGI.mg_resv S) (MG.set_m cs' s') Lg' _ stn LBa _ st1 Lg' _ LS1 Pa Estn HINVn Est1 RES1 eq_refl). }
pose proof (rheap_unhide_post Lg Lg' g c c' H H' m m2 lo Bc Tc Nc B' T' N' _ _ KL KL2 Hlo HORd SIM'' RH') as RH2.
apply (HK ms2 m2 c' 0 (Z_to_bv 64 12)).
+ unfold HI.ret_state. exists u0, u1, u2, ua1, ua2, ua3, ua4, ua5, ua6, ua7, u3, u4, u5, u6. exact Ems2.
+ exact HVM.
+ exact STK2.
+ exact (mng_heap_pres k Lg Lg' g c c' H H' m m2 lo (bv_unsigned sp) Bc Tc Nc B' T' N' LB LM LM FR B LB0 LB0 HA0 KL KL2 HMI2 Hlo Hsp' PRES (fun b Hb => Hb) HLMr HLM0 FRW).
+ rewrite L_tp2. exact ERR2.
+ left. split; [reflexivity|]. split; [reflexivity|].
refine (heapA1_after k (k - 1) Lg Lg' g c c' H H' m m2 lo (bv_unsigned sp) Bc Tc Nc B' T' N' LB LM LM FR B LB0
(MG.set_m cs' s') LB0 _ HA0 KL KL2 HMI2 Hlo Hsp' _ _ _ _ HORd PRES STK2 _ MI2 ERR2 _ PLM RH2 SIM'' _ _ SZ AUX2 _ FRW STA).
* lia.
* replace (k - (k - 1)) with 1 by lia. lia.
* unfold kMaxChunk in *. lia.
* lia.
* intros a Ha. apply wstat_iff in Ha as [Hc|He]; [exact (MGI.ml_ctx_wr segs S ML _ _ m2 a RH2 Hc)| exact (HERRW a He)].
* exact (HOLD Lg' KL2 HMI2).
* rewrite LIVE'. exact PLV.
* rewrite LIVE'. exact NDL.
* cbn [MG.ps_m MG.set_m]. lia.
Qed.

Theorem hiA_free2_1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (p n lo : Z) (errv : word),
HEAPA1 k LB LM FR B m c -> In (p, n) LM ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - HI.hl_stack HL ->
bv_unsigned sp <= BAUX ->
OT.rw_cells segs m (HI.hl_tp HL - 164) [OC.C4 errv] ->
tp = Z_to_bv 64 (HI.hl_tp HL) ->
a0 = Z_to_bv 64 p ->
(forall ms' m' c' (r : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc r m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ HI.lb_remove p LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv] ->
HEAPA1 k LB (HI.lb_remove p LM) FR B m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_free2 HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B p n lo errv
HP HIN Hstk Hlo Hlo2 HB ERR Htp Ha0 HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil. pose proof (MGI.ml_stack segs S ML) as Hst0.
assert (MIm : mem_inv segs m) by (destruct HA0 as (ps & LBd & FSd & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI0 & _); exact MI0).
set (GH := GHof m Lg H lo).
pose proof (GHof_off m Lg H lo MIm) as GHoff. fold GH in GHoff.
pose proof (KLA_GHof Lg g c H m Bc Tc Nc lo KL) as KLg. fold GH in KLg.
rewrite L_tp2 in ERR, Htp.
destruct (coarse_pre Lg g c H m Bc Tc Nc lo (bv_unsigned sp) s LB0 errv KL Hlo ltac:(lia) HB HOR RH SIM AUX Hstk ERR MIm) as (RHc & AUXc & STKc & ERRc & MIc).
fold GH in RHc, AUXc, STKc, ERRc, MIc.
assert (Uerr : (bv_unsigned tp + (-164)) = RATP - 164).
{ rewrite Htp. destruct IMG_data as (D1 & D2 & D3). unfold kLowEnd in D3.
pose proof (stat_in_hull (RATP + -164) ltac:(right; apply wstat_iff; right; lia)) as Hh.
rewrite unsigned_lit by lia. reflexivity. }

assert (Hb0 : exists b0, In b0 LB0 /\ zblk b0 = (p, n)).
{ pose proof (Permutation_in _ PLM HIN) as Hi. apply in_map_iff in Hi as (b0 & E & Hin0). exists b0. auto. }
destruct Hb0 as (b0 & Hin0 & Eb0).
pose proof (MGI.ml_nodup segs S ML _ _ _ RH) as NDI.
destruct (MLI.lb_remove_split b0 LB0 Hin0 NDI) as (l1 & l2 & ELB0 & ERM).
assert (NDA : List.NoDup (map fst LM)).
{ eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PLM|].
rewrite map_map. change (fun x => fst (zblk x)) with MB.blk_addr.
apply MLI.blk_addr_nodup; [exact NDI| intros b1 b2 H1 H2' NE; exact (MGI.ml_disjoint segs S ML _ _ _ b1 b2 RH H1 H2' NE)| exact SZ]. }
assert (PRM : Permutation (HI.lb_remove p LM) (map zblk (AMI.lb_remove (MB.blk_id b0) LB0))).
{ apply (Permutation_cons_inv (a:=(p, n))).
eapply Permutation_trans; [apply Permutation_sym; apply (MLI.zlb_remove_perm LM p n NDA HIN)|].
eapply Permutation_trans; [exact PLM|]. rewrite ERM, ELB0, !map_app. cbn [map]. rewrite Eb0.
apply Permutation_sym. apply Permutation_middle. }
destruct b0 as [[pb Ab] nb]. unfold zblk, MB.blk_addr, MB.blk_size in Eb0. cbn [fst snd] in Eb0. injection Eb0 as -> ->.
unfold MB.blk_id in ERM, PRM. cbn [fst] in ERM, PRM.
set (c0 := fst pb).
assert (LIVEc : In c0 (KV.ld_live Lg)).
{ eapply Permutation_in; [apply Permutation_sym; exact PLV|]. apply in_map_iff. exists (pb, p, n). split; [reflexivity| exact Hin0]. }
pose proof SIM as (st & BL & LS & LB1 & PB1 & Est & INV & CORR0).
assert (Hin1 : In (pb, p, n) LB1) by (eapply Permutation_in; [apply Permutation_sym; exact PB1| exact Hin0]).
destruct (SG.HSIM_block st LB1 BL (pb, p, n) CORR0 Hin1) as (off & HkBL & _). unfold MB.blk_slot, MB.blk_size in HkBL. cbn [fst snd] in HkBL. fold c0 in HkBL.
pose proof (MGI.ml_free segs S ML ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc
(mrestrict (HG GH H) m) s LB0 pb p n lo BAUX errv RHc Hin0 AUXc HB STKc Hlo ltac:(lia)
ltac:(rewrite Uerr; exact ERRc) MIc Htp Ha0) as IMPL.
rewrite <- L_free2 in IMPL.
match goal with |- AJv _ _ _ _ ?st0 => set (msv := st0) end.
match type of IMPL with MO.implM _ _ _ _ ?st0 => change st0 with (restrict (HG GH H) msv) in IMPL end.
unfold MG.raw_free in IMPL. apply implM_get_inv in IMPL. apply IR.implM_bind_inv in IMPL.
pose proof (MIC.cfree_ctree st Lg BL LS c0 off n INV HkBL) as CT. rewrite Est in CT.
change (fst pb) with c0 in IMPL.
pose proof (cfree_tree_supp (MG.ps_m s) (Some c0) Lg _ CT) as TS.
destruct (heapA0g_ledger _ _ _ _ _ _ _ _ _ _ _ _ _ HA0) as (Hsp & Hreg & HbB0).
assert (HSC0 : 0 <= SC) by (vm_compute; discriminate).
unfold AJv.
refine (membed_vj_coarse segs LA LV PERM0 TMAX NMAX LL0 Hwx Hsegs Hsh Hbx Hbc Hbase47 GH GHoff (JS segs T) (js_nclosed segs T) segs_low
(SM.cfree (MG.ps_m s) (Some c0)) 0%nat _ s _ msv c g Lg H Bc Tc Nc IMPL CT TS KLg _ _ _ _ _).
{ change (Z.of_nat 0) with 0. nia. }
{ intros Hne. exfalso. apply Hne. reflexivity. }
{ change (Z.of_nat 0) with 0. assert (0 <= kMaxChunk) by (unfold kMaxChunk; lia). nia. }
{ change (Z.of_nat 0) with 0. lia. }
intros cs' s' msv' Lg' c' H' B' T' N' Hleaf _ CP Em Eb KL' HB' HT' HN' HOR' HMI HVO HVS.
apply implM_upd_inv in Hleaf.
refine (vj_coarse_evt segs LV PERM0 TMAX NMAX Hwx Hsegs GH GHoff (JS segs T) (js_nclosed segs T) segs_low Lg' g c' H' msv' B' T' N' _ KL' Hleaf _).
intros ms2 PM KL2 Hh2 Hn2.
pose proof (MI_evt segs GH _ _ _ _ _ _ _ HMI Hh2 Hn2) as HMI2.
destruct PM as (u0 & u1 & u2 & ra0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m'c & Ems & MI' & ST' & ERR' & AUX' & PRES & RH').
destruct (restrict_MS_inv (HG GH H') ms2 _ _ _ _ _ _ _ Ems) as [Ems2 Em'c]. set (m2 := ms_mem ms2) in *. subst m'c.
change (ms_mem msv) with m in HMI2.
assert (HGoff' : H_off_segments segs (HG GH H')).
{ intros y Hy. unfold HG in Hy. apply orb_prop in Hy as [Hy|Hy]; [apply segs_low; exact (kla_Hrange _ _ _ _ _ _ _ _ _ _ _ _ _ KL2 y Hy)| exact (GHoff y Hy)]. }
pose proof (mem_inv_unhideK _ HGoff' m2 MI') as MI2.
pose proof (stk_unhide segs _ HGoff' m2 lo _ ST') as STK2.
rewrite Uerr in ERR'. pose proof (rw_cells_unhide _ HGoff' m2 _ _ ERR') as ERR2.
pose proof (rauxv_unhide Lg Lg' g c c' H H' m m2 lo Bc Tc Nc B' T' N' KL KL2 Hlo ltac:(lia) AUX') as AUX2.
pose proof (MCO.cfree_count_cpath (MG.ps_m s) (Some c0) Lg Lg' cs' CP) as CNT'.
pose proof (Q4en.cpath_live CP) as LIVE'.
rewrite <- Est in CP. destruct (MIC.cfree_leaf_INVL st Lg BL LS c0 off n Lg' cs' INV HkBL CP) as (_ & st1 & LS1 & Est1 & INV1).
destruct HVO as (V1 & V2 & V3 & V4 & V5 & V6).
assert (HVM : HI.model_vm_only (cfg_model c) (cfg_model c')) by (unfold HI.model_vm_only; repeat split; try assumption; exact (vmst_init_sp _ _ HVS)).
assert (HORd : forall r y, In r (doranges Lg') -> fst r <= bv_unsigned y < fst r + snd r -> in_regs FR0 y = true).
{ destruct HOR' as (_ & O2 & O3). unfold MGI.doranges in *. rewrite O2, O3. exact HOR. }
assert (Hsp' : lo <= bv_unsigned sp) by lia.
assert (HERRW : forall a, RATP + -164 <= a < RATP + -164 + 4 -> wview segs m2 (wa a) <> None).
{ intros a Ha. destruct ERR2 as [_ (E0 & E1 & EW)]. replace a with (RATP - 164 + (a - (RATP - 164))) by lia. apply EW. cbn. lia. }
set (L'' := KV.set_live (KV.ap_remove c0 (KV.ld_live Lg')) Lg').
assert (KL'' : KLA LV PERM0 TMAX NMAX GH L'' g c' H' m2 B' T' N') by (apply KLA_set_live; exact KL2).
assert (SIM'' : SG.HSIM (MG.set_m cs' s') L'' (AMI.lb_remove pb LB0)).
{ destruct (MGI.ml_hinv segs S ML _ _ _ RH') as (stn & LBa & Pa & Estn & HINVn). apply SG.HSIM_set_live.
exact (SG.HSIM_intro (MGI.mg_resv S) (MG.set_m cs' s') Lg' _ stn LBa _ st1 Lg' _ LS1 Pa Estn HINVn Est1 INV1 eq_refl). }
pose proof (rheap_unhide_post Lg L'' g c c' H H' m m2 lo Bc Tc Nc B' T' N' _ _ KL KL'' Hlo HORd SIM'' RH') as RH2.

assert (HLMsub : forall a n0, In (a, n0) (HI.lb_remove p LM) -> In (a, n0) LM).
{ intros a n0. clear. induction LM as [|b LM' IH]; cbn [HI.lb_remove]; [tauto|]. destruct (HI.blk_addr b =? p); [intros Hi; right; exact Hi|].
intros [E|Hi]; [left; exact E| right; exact (IH Hi)]. }
assert (HLM0 : forall a n0, In (a, n0) (HI.lb_remove p LM) -> exists b1, In b1 (AMI.lb_remove pb LB0) /\ MB.blk_addr b1 = a /\ MB.blk_size b1 = n0).
{ intros a n0 Hin. pose proof (Permutation_in _ PRM Hin) as Hi. apply in_map_iff in Hi as (b1 & E & Hb1). unfold zblk in E. injection E as E1 E2. exists b1. auto. }
assert (HLMr' : forall a n0, In (a, n0) (HI.lb_remove p LM) -> MGI.mrange S a n0 /\
forall x, a <= x < a + n0 -> in_regs (FRof Lg) (wa x) = true /\ m (wa x) <> None)
by (intros a n0 Hin; exact (HLMr a n0 (HLMsub a n0 Hin))).
assert (HOLD : forall a n0, In (a, n0) (HI.lb_remove p LM) -> MGI.mrange S a n0 /\
forall x, a <= x < a + n0 -> in_regs (FRof L'') (wa x) = true /\ m2 (wa x) <> None).
{ intros a n0 Hin. destruct (HLMr' a n0 Hin) as [Hrng Hb]. split; [exact Hrng|]. intros x Hx.
destruct (Hb x Hx) as [Hr Hm]. destruct (HLM0 a n0 Hin) as (b1 & Hb1 & Ea & En). destruct Hrng as (G1 & _ & G3 & G4 & _).
assert (Hx64 : 0 <= x < 2^64) by lia.
destruct (mng_pres Lg L'' g c c' H H' m m2 lo (bv_unsigned sp) Bc Tc Nc B' T' N' (AMI.lb_remove pb LB0) (wa x) KL KL'' Hlo Hsp' PRES) as [E _].
{ rewrite (wa_unsigned x Hx64). right; right. exists b1. split; [exact Hb1| rewrite Ea, En; exact Hx]. }
{ apply PK_regs. exact Hr. }
split; [| rewrite E; exact Hm].
apply (lm_keep Lg L'' g c c' H H' m m2 lo Bc Tc Nc B' T' N' (wa x) KL KL'' HMI2 Hr). rewrite E. exact Hm. }
apply (HK ms2 m2 c' ra0).
- unfold HI.ret_state. exists u0, u1, u2, ua1, ua2, ua3, ua4, ua5, ua6, ua7, u3, u4, u5, u6. exact Ems2.
- exact HVM.
- exact STK2.
- exact (mng_heap_pres k Lg L'' g c c' H H' m m2 lo (bv_unsigned sp) Bc Tc Nc B' T' N' LB LM (HI.lb_remove p LM) FR B
(AMI.lb_remove pb LB0) (AMI.lb_remove pb LB0) HA0 KL KL'' HMI2 Hlo Hsp' PRES (fun b Hb => Hb) HLMr' HLM0 FRW).
- rewrite L_tp2. exact ERR2.
- refine (heapA1_after k k Lg L'' g c c' H H' m m2 lo (bv_unsigned sp) Bc Tc Nc B' T' N' LB LM (HI.lb_remove p LM) FR B (AMI.lb_remove pb LB0)
(MG.set_m cs' s') (AMI.lb_remove pb LB0) _ HA0 KL KL'' HMI2 Hlo Hsp' Hk0 _ _ _ HORd PRES STK2 _ MI2 ERR2 HOLD PRM RH2 SIM'' _ _ _ AUX2 _ FRW STA).
+ replace (k - k) with 0 by lia. change (Z.of_nat 0) with 0 in HB'. lia.
+ change (Z.of_nat 0) with 0 in HT'. unfold kMaxChunk in *. lia.
+ change (Z.of_nat 0) with 0 in HN'. lia.
+ intros a Ha. apply wstat_iff in Ha as [Hc|He]; [exact (MGI.ml_ctx_wr segs S ML _ _ m2 a RH2 Hc)| exact (HERRW a He)].
+ subst L''. cbn [KV.set_live KV.ld_live]. rewrite LIVE'. apply (Permutation_cons_inv (a:=c0)).
eapply Permutation_trans; [apply Permutation_sym; apply MLI.ap_remove_perm; exact LIVEc|].
eapply Permutation_trans; [exact PLV|]. rewrite ERM, ELB0, !map_app. cbn [map]. unfold MB.blk_slot at 2. cbn [fst]. fold c0.
apply Permutation_sym. apply Permutation_middle.
+ subst L''. cbn [KV.set_live KV.ld_live]. rewrite LIVE'. apply MLI.ap_remove_nodup. exact NDL.
+ rewrite ERM. rewrite ELB0 in SZ. apply Forall_app in SZ as [S1 S2]. inversion S2 as [|xb lb Sx Sl]. apply Forall_app. split; assumption.
+ cbn [MG.ps_m MG.set_m]. lia.
Qed.

Hypothesis OBL_STAT_asan : forall Lg g c H m m' Bc Tc Nc sp (LBall : list HI.blk),
KLA0 Lg g c H m Bc Tc Nc ->
(forall x, Fof LV (FRof Lg) x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
HI.heap_pres HL LBall sp m m' ->
STAT m -> STAT m'.

Lemma heapA1_asan_step_fr : forall k g g' Lg H Bc Tc Nc s LB0 LB' LM FR' B' m m' c c' sp (LBall : list HI.blk),
KLA0 Lg g c H m Bc Tc Nc ->
0 <= k -> Tc + k * kMaxChunk <= TMAX -> Nc + k <= NMAX ->
(forall r y, In r (doranges Lg) -> fst r <= bv_unsigned y < fst r + snd r -> in_regs FR0 y = true) ->
(forall a n, In (a, n) LM -> MGI.mrange S a n /\ forall x, a <= x < a + n -> in_regs (FRof Lg) (wa x) = true /\ m (wa x) <> None) ->
Permutation LM (map zblk LB0) -> RHEAP s LB0 m -> SG.HSIM s Lg LB0 ->
Permutation (KV.ld_live Lg) (map MB.blk_slot LB0) -> List.NoDup (KV.ld_live Lg) -> Forall (fun b => 1 <= MB.blk_size b) LB0 ->
rauxv_ok m BAUX -> 25 + 8 * k <= MSU.cntm (MG.ps_m s) ->
STAT m ->
HEAPA0g L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) g' LB' LM FR' B' m' c' ->
vmst (cfg_model c) (cfg_model c') ->
(forall x, Fof LV (FRof Lg) x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
HI.heap_pres HL LBall sp m m' ->
Forall (fun b : HI.blk => wr_at segs (mrestrict (Fof LV (FRof Lg)) m') (fst b) (snd b)
/\ (fst b + snd b <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= fst b)
/\ fst b + snd b <= RC.alloc_ceiling) (fr_ivs0 L FR') ->
HEAPA1 k LB' LM FR' B' m' c'.
Proof.
intros k g g' Lg H Bc Tc Nc s LB0 LB' LM FR' B' m m' c c' sp LBall KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT STA HA0' Hvm HFm Hcd HPRES FRW'.
assert (KL' : KLA0 Lg g' c' H m' Bc Tc Nc).
{ destruct HA0' as (ps & LBd & FSd & _ & _ & _ & _ & _ & _ & _ & K' & HC' & Hh' & _).
apply (KLA_asan_step LV PERM0 TMAX NMAX Lg g g' c c' H m m' Bc Tc Nc KL K' HC' Hh' Hvm).
intros y Hy. apply HFm. exact (proj2 (proj2 (H_place _ _ _ _ _ _ _ _ _ y KL Hy))). }
assert (HDYN : forall a, 0 <= a < 2^64 -> mng_dyn Lg a -> Fof LV (FRof Lg) (wa a) = true).
{ intros a Ha Hd. apply in_regs_Fof. exact (mng_dyn_regs Lg a Ha HOR Hd). }
exists g', Lg, H, Bc, Tc, Nc, s, LB0.
split; [exact HA0'|]. split; [exact KL'|]. split; [exact Hk0|]. split; [exact HTr|]. split; [exact HNr|]. split; [exact HOR|].
split.
{ intros a n Hin. destruct (HLMr a n Hin) as [Hrng Hb]. split; [exact Hrng|]. intros x Hx. destruct (Hb x Hx) as [Hr Hm].
split; [exact Hr|]. rewrite (HFm _ (in_regs_Fof _ _ Hr)). exact Hm. }
split; [exact PLM|].
split.
{
apply (MGI.ml_agree_rt segs S ML s Lg LB0 m m' RH SIM).
- intros b0 l0 Hbl0; exact (proj1 (kla_groups _ _ _ _ _ _ _ _ _ _ _ _ _ KL b0 l0 Hbl0)).
- intros a Ha [Hs|Hd] _ Hnr.
+ exact (proj1 (Hcd a Ha (or_introl (OBL_R1P a (or_introl (conj Hs Hnr)))))).
+ exact (HFm _ (HDYN a Ha Hd)).
- destruct HA0' as (ps & LBd & FSd & RUN' & _).
pose proof (dc_rt_consts _ _ _ _ DCo ps LBd FSd RE _ RUN') as RTC.
pose proof (IMG_rtc_wr m') as RTW. rewrite Forall_forall in RTC, RTW. apply Forall_forall. intros cl Hcl. split.
+ exact (bytes_at_unhide segs _ (KLA_F_off _ Lg g c H m Bc Tc Nc KL) m' (fst cl) (snd cl) (RTC cl (L_rtc cl Hcl))).
+ exact (RTW cl Hcl).
- intros a Ha Hd Hw. rewrite (wview_eq m m' _ (HFm _ (HDYN a Ha Hd))). exact Hw. }
split; [exact SIM|]. split; [exact PLV|]. split; [exact NDL|]. split; [exact SZ|].
split.
{ exact (MGI.ml_auxv_mem segs S ML m m' BAUX AUX). }
split; [exact CNT|].
split; [exact FRW'| exact (OBL_STAT_asan Lg g c H m m' Bc Tc Nc sp _ KL HFm Hcd HPRES STA)].
Qed.

Lemma heapA1_asan_step : forall k g g' Lg H Bc Tc Nc s LB0 LB' LM FR B' m m' c c' sp (LBp : list HI.blk),
KLA0 Lg g c H m Bc Tc Nc ->
0 <= k -> Tc + k * kMaxChunk <= TMAX -> Nc + k <= NMAX ->
(forall r y, In r (doranges Lg) -> fst r <= bv_unsigned y < fst r + snd r -> in_regs FR0 y = true) ->
(forall a n, In (a, n) LM -> MGI.mrange S a n /\ forall x, a <= x < a + n -> in_regs (FRof Lg) (wa x) = true /\ m (wa x) <> None) ->
Permutation LM (map zblk LB0) -> RHEAP s LB0 m -> SG.HSIM s Lg LB0 ->
Permutation (KV.ld_live Lg) (map MB.blk_slot LB0) -> List.NoDup (KV.ld_live Lg) -> Forall (fun b => 1 <= MB.blk_size b) LB0 ->
rauxv_ok m BAUX -> 25 + 8 * k <= MSU.cntm (MG.ps_m s) ->
Forall (fun b : HI.blk => wr_at segs (mrestrict (Fof LV (FRof Lg)) m) (fst b) (snd b)
/\ (fst b + snd b <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= fst b)
/\ fst b + snd b <= RC.alloc_ceiling) (fr_ivs0 L FR) ->
STAT m ->
HEAPA0g L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) g' LB' LM FR B' m' c' ->
vmst (cfg_model c) (cfg_model c') ->
(forall x, Fof LV (FRof Lg) x = true -> m' x = m x) ->
(forall a, 0 <= a < 2^64 -> dkeepA RC.alloc_ceiling DL a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None)) ->
HI.heap_pres HL (LBp ++ LM ++ fr_ivs0 L FR) sp m m' -> sp <= BAUX ->
HEAPA1 k LB' LM FR B' m' c'.
Proof.
intros k g g' Lg H Bc Tc Nc s LB0 LB' LM FR B' m m' c c' sp LBp KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT FRW STA HA0' Hvm HFm Hcd HPRES HB.
apply (heapA1_asan_step_fr k g g' Lg H Bc Tc Nc s LB0 LB' LM FR B' m m' c c' sp _ KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT STA HA0' Hvm HFm Hcd HPRES).
apply Forall_forall. intros b Hb0. destruct (proj1 (Forall_forall _ _) FRW b Hb0) as (HW & Himg & Hc).
split; [| split; [exact Himg| exact Hc]]. pose proof HW as (W0 & W1 & HWb).
split; [exact W0|]. split; [exact W1|]. intros i Hi.
pose proof (wr_at_hidden_offK _ (KLA_F_off _ Lg g c H m Bc Tc Nc KL) m _ _ HW (fst b + i) ltac:(lia)) as Fy.
specialize (HWb i Hi). unfold wview, mrestrict in HWb |- *. rewrite Fy in HWb |- *.
apply (HPRES (fst b + i) ltac:(lia)); [| exact HWb].
right; right. exists b. split; [apply in_app_iff; right; apply in_app_iff; right; exact Hb0| unfold HI.blk_addr, HI.blk_size; lia].
Qed.

Hypothesis L_malloc : HI.hl_malloc HL = dl_malloc DL.
Hypothesis L_free : HI.hl_free HL = dl_free DL.
Hypothesis L_calloc : HI.hl_calloc HL = dl_calloc DL.
Hypothesis L_tp : HI.hl_tp HL = dl_tp DL.
Hypothesis L_gp : JH.hl_gp L = dl_gp DL.
Hypothesis L_stack : dl_malloc_stack DL <= JH.hl_stack_A L /\ dl_free_stack DL <= JH.hl_stack_A L /\ dl_calloc_stack DL <= JH.hl_stack_A L.
Hypothesis L_static : forall a, HI.hl_client_static HL a -> dl_client_data DL a.

Variable BOTJ : Z.
Hypothesis RUN_botj : RC.alloc_ceiling <= BOTJ.
Hypothesis L_stackA : 64 <= JH.hl_stack_A L.
Hypothesis L_sb : JH.hl_sb L = kShadowOffset.

Lemma kla_layer0_facts : forall Lg g c H m Bc Tc Nc, KLA0 Lg g c H m Bc Tc Nc ->
ll_ok LA LV Bc (PERMc PERM0 Lg) Tc Nc /\ Forall (fr_ok LA (PERMc PERM0 Lg)) (FRof Lg) /\
H_off_segments segs (Fof LV (FRof Lg)) /\ (forall x, Fof LV (FRof Lg) x = true -> bv_unsigned x < RC.alloc_ceiling).
Proof.
intros Lg g c H m Bc Tc Nc KL.
split; [exact (KLA_ll LA LV PERM0 TMAX NMAX LL0 _ Lg g c H m Bc Tc Nc KL)|].
split; [exact (KLA_fr_ok _ Lg g c H m Bc Tc Nc KL)|].
split; [exact (KLA_F_off _ Lg g c H m Bc Tc Nc KL)| exact (KLA_F_low _ Lg g c H m Bc Tc Nc KL)].
Qed.

Lemma rsv_nonneg : forall k, 0 <= k -> 0 <= k * SC.
Proof. intros k Hk. assert (0 <= SC) by (vm_compute; discriminate). nia. Qed.

Theorem hiA_malloc_1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (n lo : Z) (u : JH.uwd),
HEAPA1 k LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
bv_unsigned sp <= BAUX ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
lo <= hi_top RE ->
1 <= JH.bN B -> JH.acostA n <= JH.bB B -> JH.uw_cost u <= JH.bD B -> n + 8192 <= JH.bQ B ->
(forall ms' m' c' (r : Z) (errv' : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 r) m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv'] ->
r <> 0 -> (exists junk, OT.rw_cells segs m' r [OC.CB (Z.to_nat n) junk]) ->
HEAPA1 k ((r, n) :: LB) LM FR (JH.chargeQ (JH.charge B (JH.acostA n) (JH.uw_cost u) 1) (n + 8192)) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_malloc HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B n lo u
HP Hstk Hlo Hlo2 HB Htp Hgp Ha0 Hn Htop HbN HbB HbD HbQ HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc). pose proof (rsv_nonneg k Hk0) as HRSV.
eapply (hiA_malloc0 L LA LV Bc (PERMc PERM0 Lg) Tc Nc LLc Hwx Hsegs Hsh Hbx Hbc DL RE RE_L DCo (FRof Lg) HFRc Foffc Flowc)
with (RSV := k * SC) (g := g) (u := u) (LB := LB) (LM := LM) (FR := FR) (B := B) (n := n) (lo := lo); try eassumption.
intros ms' m' c' g' r errv' Hret Hvo Hstk' Hpres Hvm HFm Hcd Herr Hr0 Hblk HA0'.
apply (HK ms' m' c' r errv'); try assumption.
exact (heapA1_asan_step k g g' Lg H Bc Tc Nc s LB0 _ LM FR _ m m' c c' (bv_unsigned sp) LB KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT FRW STA HA0' Hvm HFm Hcd Hpres HB).
Qed.

Theorem hiA_calloc_1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (cnt sz lo : Z) (u : JH.uwd),
let n := cnt * sz in
HEAPA1 k LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
bv_unsigned sp <= BAUX ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^32 -> 0 <= sz < 2^32 -> 1 <= n <= 2^26 ->
lo <= hi_top RE ->
1 <= JH.bN B -> JH.acostA n <= JH.bB B -> JH.uw_cost u <= JH.bD B -> n + 8192 <= JH.bQ B ->
(forall ms' m' c' (r : Z) (errv' : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 r) m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv'] ->
r <> 0 -> OT.rw_cells segs m' r [OC.CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
HEAPA1 k ((r, n) :: LB) LM FR (JH.chargeQ (JH.charge B (JH.acostA n) (JH.uw_cost u) 1) (n + 8192)) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_calloc HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B cnt sz lo u n
HP Hstk Hlo Hlo2 HB Htp Hgp Ha0 Ha1 Hcnt Hsz Hn Htop HbN HbB HbD HbQ HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc). pose proof (rsv_nonneg k Hk0) as HRSV.
eapply (hiA_calloc0 L LA LV Bc (PERMc PERM0 Lg) Tc Nc LLc Hwx Hsegs Hsh Hbx Hbc DL RE RE_L DCo (FRof Lg) HFRc Foffc Flowc)
with (RSV := k * SC) (g := g) (u := u) (LB := LB) (LM := LM) (FR := FR) (B := B) (cnt := cnt) (sz := sz) (lo := lo); try eassumption.
intros ms' m' c' g' r errv' Hret Hvo Hstk' Hpres Hvm HFm Hcd Herr Hr0 Hblk HA0'.
apply (HK ms' m' c' r errv'); try assumption.
exact (heapA1_asan_step k g g' Lg H Bc Tc Nc s LB0 _ LM FR _ m m' c c' (bv_unsigned sp) LB KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT FRW STA HA0' Hvm HFm Hcd Hpres HB).
Qed.

Theorem hiA_free_1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (p n lo : Z) (errv : word) (u : JH.uwd),
HEAPA1 k LB LM FR B m c ->
In (p, n) LB ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
bv_unsigned sp <= BAUX ->
OT.rw_cells segs m (HI.hl_tp HL - 164) [OC.C4 errv] ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 p ->
lo <= hi_top RE ->
JH.uw_cost u <= JH.bD B ->
(forall ms' m' c' (r : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc r m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (HI.lb_remove p LB ++ LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv] ->
HEAPA1 k (HI.lb_remove p LB) LM FR (JH.charge B 0 (JH.uw_cost u) 0) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_free HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B p n lo errv u
HP HIN Hstk Hlo Hlo2 HB ERR Htp Hgp Ha0 Htop HbD HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc). pose proof (rsv_nonneg k Hk0) as HRSV.
eapply (hiA_free0 L LA LV Bc (PERMc PERM0 Lg) Tc Nc LLc Hwx Hsegs Hsh Hbx Hbc DL RE RE_L DCo (FRof Lg) HFRc Foffc Flowc)
with (RSV := k * SC) (g := g) (u := u) (LB := LB) (LM := LM) (FR := FR) (B := B) (p := p) (n := n) (lo := lo) (errv := errv); try eassumption.
intros ms' m' c' g' r Hret Hvo Hstk' Hpres Hvm HFm Hcd Herr HA0'.
apply (HK ms' m' c' r); try assumption.
exact (heapA1_asan_step k g g' Lg H Bc Tc Nc s LB0 _ LM FR _ m m' c c' (bv_unsigned sp) (HI.lb_remove p LB) KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT FRW STA HA0' Hvm HFm Hcd Hpres HB).
Qed.

Theorem hiA_free_null_1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (lo : Z) (errv : word) (u : JH.uwd),
HEAPA1 k LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
bv_unsigned sp <= BAUX ->
OT.rw_cells segs m (HI.hl_tp HL - 164) [OC.C4 errv] ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 0 ->
lo <= hi_top RE ->
(forall ms' m' (r : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc r m' ms' ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv] ->
HEAPA1 k LB LM FR (JH.charge B 0 0 0) m' c ->
AJv segs LV T c ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_free HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B lo errv u
HP Hstk Hlo Hlo2 HB ERR Htp Hgp Ha0 Htop HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc). pose proof (rsv_nonneg k Hk0) as HRSV.
eapply (hiA_free_null0 L LV Bc (PERMc PERM0 Lg) Tc Nc)
with (RSV := k * SC) (g := g) (u := u) (LB := LB) (LM := LM) (FR := FR) (B := B) (lo := lo) (errv := errv) (FRl := FRof Lg); try eassumption.
intros ms' m' r Hret Hstk' Hpres HFm Hcd Herr HA0'.
apply (HK ms' m' r); try assumption.
exact (heapA1_asan_step k g g Lg H Bc Tc Nc s LB0 _ LM FR _ m m' c c (bv_unsigned sp) LB KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT FRW STA HA0' (vmst_refl _) HFm Hcd Hpres HB).
Qed.

Lemma heapA1_A0 : forall k LB LM FR B m c, HEAPA1 k LB LM FR B m c ->
exists Lg Bc Tc Nc, HEAPA0 L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) LB LM FR B m c.
Proof. intros k LB LM FR B m c (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & _). exists Lg, Bc, Tc, Nc, g. exact HA0. Qed.

Lemma heapA1_cok : forall k LB LM FR B m c, HEAPA1 k LB LM FR B m c -> CKv LV c.
Proof. intros k LB LM FR B m c HP. destruct (heapA1_A0 _ _ _ _ _ _ _ HP) as (Lg & Bc & Tc & Nc & H0). exact (heapA0_cok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0). Qed.

Lemma heapA1_mem_inv : forall k LB LM FR B m c, HEAPA1 k LB LM FR B m c -> mem_inv segs m.
Proof. intros k LB LM FR B m c HP. destruct (heapA1_A0 _ _ _ _ _ _ _ HP) as (Lg & Bc & Tc & Nc & H0). exact (heapA0_mem_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0). Qed.

Lemma heapA1_budget : forall k LB LM FR B m c, HEAPA1 k LB LM FR B m c -> 0 <= JH.bB B /\ 0 <= JH.bD B /\ 0 <= JH.bN B.
Proof. intros k LB LM FR B m c HP. destruct (heapA1_A0 _ _ _ _ _ _ _ HP) as (Lg & Bc & Tc & Nc & H0). exact (heapA0_budget _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0). Qed.

Lemma heapA1_lm : forall k LB LM FR B m c a n, HEAPA1 k LB LM FR B m c -> In (a, n) LM ->
MGI.mrange S a n /\ wr_at segs m a n /\ exists Lg, forall x, a <= x < a + n -> in_regs (FRof Lg) (wa x) = true.
Proof.
intros k LB LM FR B m c a n (g & Lg & H & Bc & Tc & Nc & s & LB0 & _ & _ & _ & _ & _ & _ & HLMr & _) Hin.
destruct (HLMr a n Hin) as [Hrng Hb]. split; [exact Hrng|]. pose proof (@RC.alloc_ceiling_range RC__) as Hc.
destruct Hrng as (R1 & _ & R3 & R4 & _). split.
- split; [lia|]. split; [lia|]. intros i Hi. destruct (Hb (a + i) ltac:(lia)) as [_ Hm].
unfold wview. destruct (m (wa (a + i))); [discriminate| contradiction].
- exists Lg. intros x Hx. exact (proj1 (Hb x Hx)).
Qed.

Lemma heapA1_blk : forall k LB LM FR B m c a n, HEAPA1 k LB LM FR B m c -> In (a, n) (LB ++ LM) ->
0 <= n /\ a mod 16 = 0 /\ 0 < a /\ a + n <= RC.alloc_ceiling /\ wr_at segs m a n.
Proof.
intros k LB LM FR B m c a n HP Hin. apply in_app_or in Hin as [Hin|Hin].
- destruct (heapA1_A0 _ _ _ _ _ _ _ HP) as (Lg & Bc & Tc & Nc & H0). exact (heapA0_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a n H0 Hin).
- destruct (heapA1_lm _ _ _ _ _ _ _ a n HP Hin) as ((R1 & R2 & R3 & R4 & _) & Hw & _).
split; [exact R3| split; [exact R2| split; [exact R1| split; [exact R4| exact Hw]]]].
Qed.

Lemma heapA1_blk_le26 : forall k LB LM FR B m c a n, HEAPA1 k LB LM FR B m c -> In (a, n) LB -> n <= 2^26.
Proof. intros k LB LM FR B m c a n HP Hin. destruct (heapA1_A0 _ _ _ _ _ _ _ HP) as (Lg & Bc & Tc & Nc & H0). exact (heapA0_blk_le26 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a n H0 Hin). Qed.

Lemma heapA1_shadow_blk : forall k LB LM FR B m c a n, HEAPA1 k LB LM FR B m c -> In (a, n) LB ->
bytes_at segs m (JH.shad L a) (JH.shadow_bytes n).
Proof.
intros k LB LM FR B m c a n (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & _) Hin.
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (_ & _ & Foffc & _).
eapply (heapA0_shadow_blk L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) Foffc L_sb); [exists g; exact HA0| exact Hin].
Qed.

Hypothesis L_hull_eq : HI.hl_img_lo HL = MGI.mg_img_lo S /\ HI.hl_img_hi HL = MGI.mg_img_hi S.
Lemma heapA1_cross : forall k LB LM FR B m c a n a' n' x, HEAPA1 k LB LM FR B m c ->
In (a, n) LB -> In (a', n') LM -> a <= x < a + n -> a' <= x < a' + n' -> False.
Proof.
intros k LB LM FR B m c a n a' n' x (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & _) H1 H2 Hx Hx'.
destruct HA0 as (ps & LBd & FSd & _ & ELB & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOFF & HIN & _).
rewrite ELB in H1. apply in_map_iff in H1 as (b & Eb & Hb). unfold blk_of in Eb. inversion Eb; subst a n.
pose proof (proj1 (List.Forall_forall _ _) HOFF b Hb) as [_ Hoff].
specialize (Hoff x Hx). rewrite (HIN a' n' x H2 Hx') in Hoff. discriminate.
Qed.

Lemma heapA1_blk_img : forall k LB LM FR B m c a n, HEAPA1 k LB LM FR B m c -> In (a, n) (LB ++ LM) ->
a + n <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= a.
Proof.
intros k LB LM FR B m c a n HP Hin. apply in_app_or in Hin as [Hin|Hin].
- destruct (heapA1_A0 _ _ _ _ _ _ _ HP) as (Lg & Bc & Tc & Nc & H0). exact (heapA0_blk_img L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) L_img _ _ _ _ _ _ a n H0 Hin).
- destruct (heapA1_lm _ _ _ _ _ _ _ a n HP Hin) as ((_ & _ & _ & _ & R5) & _). destruct L_hull_eq as [E1 E2]. rewrite E1, E2. exact R5.
Qed.

Lemma heapA1_lm_disjoint : forall k LB LM FR B m c a n a' n', HEAPA1 k LB LM FR B m c ->
In (a, n) LM -> In (a', n') LM -> a <> a' -> a + n <= a' \/ a' + n' <= a.
Proof.
intros k LB LM FR B m c a n a' n' (g & Lg & H & Bc & Tc & Nc & s & LB0 & _ & _ & _ & _ & _ & _ & _ & PLM & RH & _) H1 H2 Hne.
pose proof (Permutation_in _ PLM H1) as I1. pose proof (Permutation_in _ PLM H2) as I2.
apply in_map_iff in I1 as (b1 & E1 & Hb1). apply in_map_iff in I2 as (b2 & E2 & Hb2).
unfold zblk in E1, E2. inversion E1; subst a n. inversion E2; subst a' n'.
apply (MGI.ml_disjoint segs S ML _ _ _ b1 b2 RH Hb1 Hb2). intros Eid.
pose proof (MGI.ml_nodup segs S ML _ _ _ RH) as ND.
assert (b1 = b2); [| subst b2; apply Hne; reflexivity].
clear - ND Hb1 Hb2 Eid. induction LB0 as [|b l IH]; [destruct Hb1|]. cbn [map] in ND. inversion ND as [|x l' Hni ND']; subst.
destruct Hb1 as [<-|Hb1]; destruct Hb2 as [<-|Hb2]; [reflexivity| | |exact (IH Hb1 Hb2 ND')].
- exfalso. apply Hni. rewrite Eid. apply in_map. exact Hb2.
- exfalso. apply Hni. rewrite <- Eid. apply in_map. exact Hb1.
Qed.

Lemma heapA1_blk_disjoint : forall k LB LM FR B m c a n a' n', HEAPA1 k LB LM FR B m c ->
Forall (fun b : HI.blk => 1 <= snd b) LB ->
In (a, n) (LB ++ LM) -> In (a', n') (LB ++ LM) -> a <> a' -> a + n <= a' \/ a' + n' <= a.
Proof.
intros k LB LM FR B m c a n a' n' HP SZB H1 H2 Hne.
assert (SZM : forall a0 n0, In (a0, n0) LM -> 1 <= n0).
{ destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & _ & _ & _ & _ & _ & _ & _ & PLM & _ & _ & _ & _ & SZ & _).
intros a0 n0 Hin. pose proof (Permutation_in _ PLM Hin) as I. apply in_map_iff in I as (b & E & Hb).
unfold zblk in E. inversion E; subst. exact (proj1 (List.Forall_forall _ _) SZ b Hb). }
apply in_app_or in H1 as [H1|H1]; apply in_app_or in H2 as [H2|H2].
- destruct (heapA1_A0 _ _ _ _ _ _ _ HP) as (Lg & Bc & Tc & Nc & H0). exact (heapA0_blk_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a n a' n' H0 H1 H2 Hne).
- pose proof (proj1 (List.Forall_forall _ _) SZB _ H1) as S1. cbn [snd] in S1. pose proof (SZM _ _ H2) as S2.
destruct (Z.le_gt_cases (a + n) a') as [D|D]; [left; exact D|]. destruct (Z.le_gt_cases (a' + n') a) as [D'|D']; [right; exact D'|].
exfalso. apply (heapA1_cross k LB LM FR B m c a n a' n' (Z.max a a') HP H1 H2); lia.
- pose proof (proj1 (List.Forall_forall _ _) SZB _ H2) as S2. cbn [snd] in S2. pose proof (SZM _ _ H1) as S1.
destruct (Z.le_gt_cases (a + n) a') as [D|D]; [left; exact D|]. destruct (Z.le_gt_cases (a' + n') a) as [D'|D']; [right; exact D'|].
exfalso. apply (heapA1_cross k LB LM FR B m c a' n' a n (Z.max a a') HP H2 H1); lia.
- exact (heapA1_lm_disjoint k LB LM FR B m c a n a' n' HP H1 H2 Hne).
Qed.

Lemma nodup_app_intro : forall (A : Type) (l l' : list A), List.NoDup l -> List.NoDup l' -> (forall x, In x l -> In x l' -> False) -> List.NoDup (l ++ l').
Proof.
intros A l l' N1 N2 HX. induction l as [|y l IH]; [exact N2|]. cbn [app]. inversion N1 as [|z t Hni N1']; subst. constructor.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hni Hin)| exact (HX y (or_introl eq_refl) Hin)].
- apply IH; [exact N1'| intros x H1 H2; exact (HX x (or_intror H1) H2)].
Qed.

Lemma heapA1_blk_nodup : forall k LB LM FR B m c, HEAPA1 k LB LM FR B m c -> Forall (fun b : HI.blk => 1 <= snd b) LB ->
List.NoDup (map HI.blk_addr (LB ++ LM)).
Proof.
intros k LB LM FR B m c HP SZB. rewrite map_app. apply nodup_app_intro.
- destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & _).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & _).
apply (heapA0_blk_nodup L LA LV Bc (PERMc PERM0 Lg) Tc Nc LLc DL RE RE_L DCo (FRof Lg) HFRc (k * SC) LB LM FR B m c). exists g. exact HA0.
- destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & _ & _ & _ & _ & _ & _ & _ & PLM & RH & _ & _ & _ & SZ & _).
assert (PA : Permutation (map HI.blk_addr LM) (map MB.blk_addr LB0)).
{ eapply Permutation_trans; [apply Permutation_map; exact PLM|]. rewrite map_map. apply Permutation_refl. }
apply (Permutation_NoDup (Permutation_sym PA)).
apply MLI.blk_addr_nodup; [exact (MGI.ml_nodup segs S ML _ _ _ RH)| intros b1 b2 H1 H2 NE; exact (MGI.ml_disjoint segs S ML _ _ _ b1 b2 RH H1 H2 NE)| exact SZ].
- intros x H1 H2. apply in_map_iff in H1 as ([a n] & E1 & H1). apply in_map_iff in H2 as ([a' n'] & E2 & H2).
unfold HI.blk_addr in E1, E2. cbn [fst] in E1, E2. subst a a'.
pose proof (proj1 (List.Forall_forall _ _) SZB _ H1) as S1. cbn [snd] in S1.
assert (S2 : 1 <= n').
{ destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & _ & _ & _ & _ & _ & _ & _ & PLM & _ & _ & _ & _ & SZ & _).
pose proof (Permutation_in _ PLM H2) as I. apply in_map_iff in I as (b & E & Hb). unfold zblk in E. inversion E; subst.
exact (proj1 (List.Forall_forall _ _) SZ b Hb). }
apply (heapA1_cross k LB LM FR B m c x n x n' x HP H1 H2); lia.
Qed.

Lemma heapA1_blk_not_static : forall k LB LM FR B m c a n i, HEAPA1 k LB LM FR B m c -> In (a, n) (LB ++ LM) -> 0 <= i < n ->
~ HI.hl_client_static HL (a + i).
Proof.
intros k LB LM FR B m c a n i HP Hin Hi Hs. pose proof (HI.hl_static_in_img HL _ Hs) as Himg.
pose proof (heapA1_blk_img k LB LM FR B m c a n HP Hin) as D. lia.
Qed.

Lemma heapA1_perm : forall k LB LB' LM LM' FR FR' B m c, HEAPA1 k LB LM FR B m c ->
Permutation LB LB' -> Permutation LM LM' -> Permutation FR FR' -> HEAPA1 k LB' LM' FR' B m c.
Proof.
intros k LB LB' LM LM' FR FR' B m c (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA) P1 P2 P3.
exists g, Lg, H, Bc, Tc, Nc, s, LB0.
split. { apply (heapA0g_perm_lm_fr L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) g LB' LM LM' FR FR'); [| exact P2| exact P3].
exact (heapA0g_perm_lb L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) g LB LB' LM FR B m c HA0 P1). }
split; [exact KL|]. split; [exact Hk0|]. split; [exact HTr|]. split; [exact HNr|]. split; [exact HOR|].
split. { intros a n Hin. apply HLMr. eapply Permutation_in; [apply Permutation_sym; exact P2| exact Hin]. }
split. { eapply Permutation_trans; [apply Permutation_sym; exact P2| exact PLM]. }
split; [exact RH|]. split; [exact SIM|]. split; [exact PLV|]. split; [exact NDL|]. split; [exact SZ|]. split; [exact AUX|]. split; [exact CNT|]. split; [| exact STA].
refine (Permutation_Forall _ FRW). unfold fr_ivs0. apply Permutation_flat_map. exact P3.
Qed.

Lemma heapA1_cfg_next : forall k LB LM FR B m c c', HEAPA1 k LB LM FR B m c -> CNEXTv LV c c' -> HEAPA1 k LB LM FR B m c'.
Proof.
intros k LB LM FR B m c c' (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Rest) HN.
pose proof (heapA0g_cfg_next L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) g LB LM FR B m c c' HA0 HN) as HA0'.
exists g, Lg, H, Bc, Tc, Nc, s, LB0. split; [exact HA0'|]. split; [| exact Rest].
destruct HA0' as (ps & LBd & FSd & _ & _ & _ & _ & _ & _ & _ & K' & HC' & Hh' & _).
destruct HN as [_ [Vm _]].
apply (KLA_asan_step LV PERM0 TMAX NMAX Lg g g c c' H m m Bc Tc Nc KL K' HC' Hh'); [| intros y _; reflexivity].
split; rewrite Vm; reflexivity.
Qed.

Lemma khi_val : KHI = 0x10007fff8000. Proof. reflexivity. Qed.

Lemma regs_place : forall GH Lg g c H m B T N x, KLA LV PERM0 TMAX NMAX GH Lg g c H m B T N -> in_regs (FRof Lg) x = true ->
exists lo hi, lo <= bv_unsigned x < hi /\ (hi <= kLowEnd \/ KHI <= lo).
Proof.
intros GH Lg g c H m B T N x KL Hx. pose proof (KLA_fr_ok GH Lg g c H m B T N KL) as HF. rewrite Forall_forall in HF.
unfold in_regs in Hx. apply existsb_exists in Hx as ([lo hi] & Hin & Hz). apply zin_true in Hz. cbn [fst snd] in Hz.
destruct (HF _ Hin) as (_ & Hpl & _). cbn [fst snd] in Hpl. exists lo, hi. split; [exact Hz| exact Hpl].
Qed.

Lemma heapA1_blk_appmem : forall k LB LM FR B m c a n, HEAPA1 k LB LM FR B m c -> In (a, n) (LB ++ LM) ->
a + n + 8 <= JH.hl_sb L \/ (2^47 - 1) / 8 + JH.hl_sb L + 1 <= a.
Proof.
intros k LB LM FR B m c a n HP Hin. rewrite L_sb. pose proof khi_val as EK. unfold kShadowOffset, kLowEnd in *.
apply in_app_or in Hin as [Hin|Hin].
- destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & (ps & LBd & FSd & RUN & ELB & _) & _).
rewrite ELB in Hin. apply in_map_iff in Hin as ([[pid A] nd] & Eb & Hbd). unfold blk_of in Eb. cbn [ablk_addr ablk_size fst snd] in Eb. injection Eb as -> ->.
destruct (dc_block_range _ _ _ _ DCo _ _ _ _ _ _ RUN Hbd) as (((Hpl & _) & _) & _). cbn [ablk_addr ablk_size fst snd] in Hpl.
unfold kLowEnd in Hpl. destruct Hpl as [[_ Hl]|Hh]; [left; lia| right; lia].
- destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & _ & KL & _ & _ & _ & _ & HLMr & PLM & _ & _ & _ & _ & SZ & _).
destruct (HLMr a n Hin) as [(R1 & _ & R3 & R4 & _) Hb].
assert (Hn : 1 <= n).
{ pose proof (Permutation_in _ PLM Hin) as Hi. apply in_map_iff in Hi as (b0 & E & Hb0). unfold zblk in E. injection E as _ <-.
exact (proj1 (Forall_forall _ _) SZ b0 Hb0). }
pose proof (@RC.alloc_ceiling_range RC__) as Hc.
destruct (regs_place _ Lg g c H m Bc Tc Nc (wa (a + n - 1)) KL (proj1 (Hb (a + n - 1) ltac:(lia)))) as (lo1 & hi1 & Hz1 & Hp1).
rewrite wa_unsigned in Hz1 by lia. unfold kLowEnd in Hp1.
destruct Hp1 as [Hl1|Hh1]; [left; lia|]. right.
destruct (Z.lt_ge_cases a KHI) as [Hlt|Hge]; [| lia]. exfalso.

set (y := Z.max a 0x7fff7000).
assert (Hy : a <= y < a + n) by (unfold y; lia).
destruct (regs_place _ Lg g c H m Bc Tc Nc (wa y) KL (proj1 (Hb y Hy))) as (lo2 & hi2 & Hz2 & Hp2).
rewrite wa_unsigned in Hz2 by lia. unfold kLowEnd in Hp2. unfold y in *. destruct Hp2 as [Hl2|Hh2]; lia.
Qed.

Lemma heapA1_shadow_sep : forall k LB LM FR B m c a n i, HEAPA1 k LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
~ HI.client_addr HL (LB ++ LM) RC.alloc_ceiling (JH.shad L a + i)
/\ (JH.shad L a + i < HI.hl_img_lo HL \/ HI.hl_img_hi HL <= JH.shad L a + i).
Proof.
intros k LB LM FR B m c a n i HP Hin Hi. pose proof khi_val as EK. pose proof (@RC.alloc_ceiling_range RC__) as Hc.
pose proof (heapA1_blk _ _ _ _ _ _ _ a n HP (in_or_app _ _ _ (or_introl Hin))) as (B0 & _ & B2 & B3 & _).
pose proof (heapA1_blk_appmem _ _ _ _ _ _ _ a n HP (in_or_app _ _ _ (or_introl Hin))) as Happ.
destruct L_hull_eq as [_ Ehi]. pose proof IMG_low as Hlow. unfold kLowEnd in Hlow.
unfold JH.shad. rewrite L_sb in *. unfold kShadowOffset in *.
assert (Hx : 0x7fff8000 <= a / 8 + 2147450880 + i < 0x10007fff8000) by lia.
split; [| right; rewrite Ehi; lia].
intros [Hs|[Hs|(b & Hb & Hr)]].
- lia.
- pose proof (HI.hl_static_in_img HL _ Hs) as Himg. rewrite Ehi in Himg. lia.
- destruct b as [a' n']. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
pose proof (heapA1_blk_appmem _ _ _ _ _ _ _ a' n' HP Hb) as Happ'. rewrite L_sb in Happ'. unfold kShadowOffset in Happ'. lia.
Qed.

Lemma heapA1_rtc_cells : forall k LB LM FR B m c, HEAPA1 k LB LM FR B m c ->
Forall (fun cl => bytes_at segs m (fst cl) (snd cl)) (dl_rtc DL).
Proof.
intros k LB LM FR B m c (g & Lg & H & Bc & Tc & Nc & s & LB0 & (ps & LBd & FSd & RUN & _) & KL & _).
pose proof (dc_rt_consts _ _ _ _ DCo ps LBd FSd RE _ RUN) as RTC. rewrite Forall_forall in RTC. apply Forall_forall. intros cl Hcl.
exact (bytes_at_unhide segs _ (KLA_F_off _ Lg g c H m Bc Tc Nc KL) m (fst cl) (snd cl) (RTC cl Hcl)).
Qed.

Variable SM : Z -> Z.
Variable SM_stack : Z.
Hypothesis DFs : donor_fs RC.alloc_ceiling segs (at_nodeA LV segs) DL DCo SM SM_stack.
Hypothesis L_sm : forall k, 0 <= k <= 3 -> JH.hl_stack_malloc L k = SM k.
Hypothesis L_sm_stack : SM_stack <= JH.hl_stack_A L.

Lemma fr_shadow_len_ff : forall k, JH.fr_shadow_len k = ff_size k / 8.
Proof. intros k. unfold JH.fr_shadow_len, ff_size. replace (64 * 2 ^ k) with (8 * 2 ^ k * 8) by lia. rewrite Z.div_mul by lia. reflexivity. Qed.

Lemma in_fr_ivs0_body : forall FR Fa kc, In (Fa, kc) FR -> In (Fa, JH.fr_size kc - 8) (fr_ivs0 L FR).
Proof. intros FR Fa kc H. unfold fr_ivs0. apply in_flat_map. exists (Fa, kc). split; [exact H| left; reflexivity]. Qed.
Lemma in_fr_ivs0_shadow : forall FR Fa kc, In (Fa, kc) FR -> In (JH.shad L Fa, JH.fr_shadow_len kc) (fr_ivs0 L FR).
Proof. intros FR Fa kc H. unfold fr_ivs0. apply in_flat_map. exists (Fa, kc). split; [exact H| right; left; reflexivity]. Qed.

Lemma heapA1_frame_place : forall k LB LM FR B m c Fa kc, HEAPA1 k LB LM FR B m c -> In (Fa, kc) FR ->
let fs := ae_fs_base RE in
((0 < fs /\ fs + 0xb09000 <= kLowEnd) \/ KHI <= fs) /\ (fs + 0xb09000 <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= fs) /\ fs + 0xb09000 <= RC.alloc_ceiling
/\ fs + 0x9000 <= Fa /\ Fa + ff_size kc <= fs + 0xb00000 /\ Fa mod 64 = 0 /\ (kc <= 6 -> Fa mod ff_size kc = 0).
Proof.
intros k LB LM FR B m c Fa kc (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & _) Hin fs.
destruct (heapA0g_entry_facts _ _ _ _ _ _ _ _ _ _ _ _ _ DFs _ _ _ _ _ _ _ HA0) as ((E1 & E2) & E3).
destruct (heapA0g_frame_range _ _ _ _ _ _ _ _ _ _ _ _ _ DFs _ _ _ _ _ _ _ Fa kc HA0 Hin) as ((R1 & R2 & R3 & _) & R5).
destruct L_img as [Elo Ehi]. rewrite <- Elo, <- Ehi in E2. fold fs in E1, E2, E3, R1, R2.
repeat split; assumption.
Qed.

Theorem heapA1_frame : forall k LB LM FR B m c Fa kc, HEAPA1 k LB LM FR B m c -> In (Fa, kc) FR -> 0 <= kc <= 3 ->
Fa mod JH.fr_size kc = 0 /\ 0 < Fa /\ Fa + JH.fr_size kc <= RC.alloc_ceiling /\
(Fa + JH.fr_size kc <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= Fa) /\
wr_at segs m Fa (JH.fr_size kc - 8) /\
wr_at segs m (JH.shad L Fa) (JH.fr_shadow_len kc) /\
(exists fp, bytes_at segs m (Fa + JH.fr_size kc - 8) (le8 (Z_to_bv 64 fp)) /\ 0 < fp < 2^64 /\
~ HI.client_addr HL (LB ++ LM) RC.alloc_ceiling fp /\ (fp < HI.hl_img_lo HL \/ HI.hl_img_hi HL <= fp) /\
~ HI.hl_scratch HL fp /\
(forall F' k', In (F', k') FR -> ~ (F' <= fp < F' + JH.fr_size k') /\ ~ (JH.shad L F' <= fp < JH.shad L F' + JH.fr_shadow_len k'))).
Proof.
intros k LB LM FR B m c Fa kc HP Hin Hkc.
pose proof (heapA1_frame_place _ _ _ _ _ _ _ Fa kc HP Hin) as (P1 & P2 & P3 & P4 & P5 & P6 & P7). cbv zeta in *.
pose proof khi_val as EK. pose proof (@RC.alloc_ceiling_range RC__) as Hc. unfold kLowEnd in *.
pose proof HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & _ & _ & _ & _ & HLMr & _ & _ & _ & _ & _ & _ & _ & _ & FRW & _).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (_ & _ & Foffc & _).
rewrite Forall_forall in FRW.
change (JH.fr_size kc) with (ff_size kc) in *.
assert (Hsz : 64 <= ff_size kc) by (unfold ff_size; assert (1 <= 2 ^ kc) by (apply Z.pow_le_mono_r with (b := 0); lia); lia).
split; [apply P7; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (wr_at_unhide segs _ Foffc m _ _ (proj1 (FRW _ (in_fr_ivs0_body FR Fa kc Hin))))|].
split; [exact (wr_at_unhide segs _ Foffc m _ _ (proj1 (FRW _ (in_fr_ivs0_shadow FR Fa kc Hin))))|].
destruct (heapA0g_frame_flag _ _ _ _ _ _ _ _ _ _ Foffc _ _ _ DFs _ _ _ _ _ _ _ Fa kc HA0 Hin) as (flag & HB & Hr & Fflag & _ & _).
pose proof (bv_unsigned_in_range 64 flag) as Hfr. unfold bv_modulus in Hfr. change (2 ^ Z.of_N 64) with (2^64) in Hfr.
exists (bv_unsigned flag). rewrite Z_to_bv_bv_unsigned. split; [exact HB|]. split; [lia|].
split.
{ intros [Hs|[Hs|(b & Hb & Hrb)]].
- lia.
- pose proof (HI.hl_static_in_img HL _ Hs) as Himg. lia.
- destruct b as [a n]. unfold HI.blk_addr, HI.blk_size in Hrb. cbn [fst snd] in Hrb. apply in_app_or in Hb as [Hb|Hb].
+ pose proof (heapA0g_fs_blk_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ DFs _ _ _ _ _ _ _ a n HA0 Hb). lia.
+ destruct (HLMr a n Hb) as [_ Hreg]. destruct (Hreg _ Hrb) as [Hreg1 _]. apply in_regs_Fof in Hreg1.
unfold wa in Hreg1. rewrite Z_to_bv_bv_unsigned in Hreg1. rewrite Hreg1 in Fflag. discriminate. }
split; [lia|].
split. { intros Hsc. pose proof (HI.hl_scratch_in_img HL _ Hsc) as Hd. lia. }
intros F' k' Hin'. pose proof (heapA1_frame_place _ _ _ _ _ _ _ F' k' HP Hin') as (_ & _ & _ & Q4 & Q5 & Q6 & _). cbv zeta in *.
change (JH.fr_size k') with (ff_size k'). rewrite fr_shadow_len_ff. unfold JH.shad. rewrite L_sb. unfold kShadowOffset.
assert (Hs' : 0 <= ff_size k') by (unfold ff_size; assert (0 <= 2 ^ k') by (apply Z.pow_nonneg; lia); lia).
split; [lia|].
assert (E8 : F' = 8 * (F' / 8)) by (apply Z.div_exact; [lia|]; apply (Zmod_divides F' 64 ltac:(lia)) in Q6 as [q ->]; replace (64 * q) with (8 * q * 8) by lia; apply Z.mod_mul; lia).
assert (D8 : ff_size k' = 8 * (ff_size k' / 8)) by (rewrite <- fr_shadow_len_ff; unfold ff_size, JH.fr_shadow_len; lia).
lia.
Qed.

Theorem heapA1_frame_disjoint : forall k LB LM FR B m c Fa kc a n, HEAPA1 k LB LM FR B m c -> In (Fa, kc) FR -> 0 <= kc -> In (a, n) (LB ++ LM) ->
Fa + JH.fr_size kc <= a \/ a + n <= Fa.
Proof.
intros k LB LM FR B m c Fa kc a n HP Hin Hkc Hb. change (JH.fr_size kc) with (ff_size kc).
pose proof HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & _ & _ & _ & _ & HLMr & PLM & _ & _ & _ & _ & SZ & _ & _ & FRW & _).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (_ & _ & Foffc & _).
apply in_app_or in Hb as [Hb|Hb]; [exact (heapA0g_frame_blk_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ DFs _ _ _ _ _ _ _ Fa kc a n HA0 Hin Hb)|].
assert (Hn : 1 <= n).
{ pose proof (Permutation_in _ PLM Hb) as Hi. apply in_map_iff in Hi as (b0 & E & Hb0). unfold zblk in E. injection E as _ <-.
exact (proj1 (Forall_forall _ _) SZ b0 Hb0). }
assert (Hsz : 64 <= ff_size kc) by (unfold ff_size; assert (1 <= 2 ^ kc) by (apply Z.pow_le_mono_r with (b := 0); lia); lia).
destruct (Z.le_gt_cases (Fa + ff_size kc) a) as [|H1]; [left; assumption|]. destruct (Z.le_gt_cases (a + n) Fa) as [|H2]; [right; assumption|]. exfalso.
set (x := Z.max a Fa). assert (Hx : a <= x < a + n /\ Fa <= x < Fa + ff_size kc) by (unfold x; lia).
destruct (HLMr a n Hb) as [_ Hreg]. destruct (Hreg x (proj1 Hx)) as [Hreg1 _]. apply in_regs_Fof in Hreg1.
rewrite Forall_forall in FRW.
destruct (Z.lt_ge_cases x (Fa + ff_size kc - 8)) as [Hbody|Hslot].
- pose proof (wr_at_hidden_offK _ Foffc m _ _ (proj1 (FRW _ (in_fr_ivs0_body FR Fa kc Hin))) x) as Hoff. cbn [fst snd] in Hoff.
change (JH.fr_size kc) with (ff_size kc) in Hoff. rewrite Hoff in Hreg1 by lia. discriminate.
- destruct (heapA0g_frame_flag _ _ _ _ _ _ _ _ _ _ Foffc _ _ _ DFs _ _ _ _ _ _ _ Fa kc HA0 Hin) as (flag & _ & _ & _ & _ & Hoff).
rewrite Hoff in Hreg1 by lia. discriminate.
Qed.

Theorem heapA1_frame_apart : forall k LB LM FR B m c Fa kc Fa' kc', HEAPA1 k LB LM FR B m c -> In (Fa, kc) FR -> In (Fa', kc') FR -> Fa <> Fa' ->
Fa + JH.fr_size kc <= Fa' \/ Fa' + JH.fr_size kc' <= Fa.
Proof.
intros k LB LM FR B m c Fa kc Fa' kc' (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & _) H1 H2 Hne.
exact (heapA0g_frame_apart _ _ _ _ _ _ _ _ _ _ _ _ _ DFs _ _ _ _ _ _ _ Fa kc Fa' kc' HA0 H1 H2 Hne).
Qed.

Theorem heapA1_frame_nodup : forall k LB LM FR B m c, HEAPA1 k LB LM FR B m c -> List.NoDup (map JH.fr_base FR).
Proof.
intros k LB LM FR B m c (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & _).
exact (heapA0g_frame_nodup _ _ _ _ _ _ _ _ _ _ _ _ _ DFs _ _ _ _ _ _ _ HA0).
Qed.

Theorem heapA1_frame_appmem : forall k LB LM FR B m c Fa kc, HEAPA1 k LB LM FR B m c -> In (Fa, kc) FR ->
Fa + JH.fr_size kc + 8 <= JH.hl_sb L \/ (2^47 - 1) / 8 + JH.hl_sb L + 1 <= Fa.
Proof.
intros k LB LM FR B m c Fa kc HP Hin. change (JH.fr_size kc) with (ff_size kc).
pose proof (heapA1_frame_place _ _ _ _ _ _ _ Fa kc HP Hin) as (P1 & P2 & P3 & P4 & P5 & P6 & P7). cbv zeta in *.
pose proof khi_val as EK. rewrite L_sb. unfold kShadowOffset, kLowEnd in *. lia.
Qed.

Theorem heapA1_frame_shadow_sep : forall k LB LM FR B m c Fa kc i, HEAPA1 k LB LM FR B m c -> In (Fa, kc) FR -> 0 <= i < JH.fr_shadow_len kc ->
~ HI.client_addr HL (LB ++ LM) RC.alloc_ceiling (JH.shad L Fa + i)
/\ (JH.shad L Fa + i < HI.hl_img_lo HL \/ HI.hl_img_hi HL <= JH.shad L Fa + i).
Proof.
intros k LB LM FR B m c Fa kc i HP Hin Hi. pose proof khi_val as EK. pose proof (@RC.alloc_ceiling_range RC__) as Hc.
pose proof (heapA1_frame_place _ _ _ _ _ _ _ Fa kc HP Hin) as (P1 & P2 & P3 & P4 & P5 & P6 & P7). cbv zeta in *.
destruct L_hull_eq as [_ Ehi]. pose proof IMG_low as Hlow. unfold kLowEnd in *.
rewrite fr_shadow_len_ff in Hi. unfold JH.shad. rewrite L_sb in *. unfold kShadowOffset in *.
assert (Hs' : 0 <= ff_size kc) by (unfold ff_size; assert (0 <= 2 ^ kc) by (apply Z.pow_nonneg; lia); lia).
assert (E8 : Fa = 8 * (Fa / 8)) by (apply Z.div_exact; [lia|]; apply (Zmod_divides Fa 64 ltac:(lia)) in P6 as [q ->]; replace (64 * q) with (8 * q * 8) by lia; apply Z.mod_mul; lia).
assert (D8 : ff_size kc = 8 * (ff_size kc / 8)) by (rewrite <- fr_shadow_len_ff; unfold ff_size, JH.fr_shadow_len; lia).
assert (Hx : 0x7fff8000 <= Fa / 8 + 2147450880 + i < 0x10007fff8000) by lia.
split; [| right; rewrite Ehi; lia].
intros [Hs|[Hs|(b & Hb & Hr)]].
- lia.
- pose proof (HI.hl_static_in_img HL _ Hs) as Himg. rewrite Ehi in Himg. lia.
- destruct b as [a' n']. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
pose proof (heapA1_blk_appmem _ _ _ _ _ _ _ a' n' HP Hb) as Happ'. rewrite L_sb in Happ'. unfold kShadowOffset in Happ'. lia.
Qed.

Theorem heapA1_blk_slack : forall k LB LM FR B m c a n, HEAPA1 k LB LM FR B m c -> In (a, n) (LB ++ LM) ->
exists junk, bytes_at segs m (a + n) junk /\ Z.of_nat (length junk) = (16 - n mod 16) mod 16.
Proof.
intros k LB LM FR B m c a n (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & _ & _ & _ & _ & _ & PLM & RH & _) Hin.
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (_ & _ & Foffc & _).
apply in_app_or in Hin as [Hin|Hin].
- exact (heapA0g_blk_slack _ _ _ _ _ _ _ _ _ _ Foffc _ _ _ DFs _ _ _ _ _ _ _ a n HA0 Hin).
- pose proof (Permutation_in _ PLM Hin) as Hi. apply in_map_iff in Hi as (b0 & E & Hb0). unfold zblk in E. injection E as <- <-.
exact (MGI.ml_slack segs S ML s LB0 m b0 RH Hb0).
Qed.

Theorem heapA1_shadow_words : forall k LB LM FR B m c a n i, HEAPA1 k LB LM FR B m c -> In (a, n) LB -> 0 <= i < (n + 7) / 8 ->
exists w : list byte, length w = 8%nat /\ bytes_at segs m ((JH.shad L a + i) / 8 * 8) w.
Proof.
intros k LB LM FR B m c a n i (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & _) Hin Hi.
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (_ & _ & Foffc & _).
exact (heapA0g_shadow_words _ _ _ _ _ _ _ _ _ _ Foffc L_sb _ _ _ DFs _ _ _ _ _ _ _ a n i HA0 Hin Hi).
Qed.

Lemma frw_keep : forall (Fh : word -> bool) (FRx : list JH.frame) (LBx : list HI.blk) sp m m',
H_off_segments segs Fh ->
HI.heap_pres HL (LBx ++ fr_ivs0 L FRx) sp m m' ->
Forall (fun b : HI.blk => wr_at segs (mrestrict Fh m) (fst b) (snd b)
/\ (fst b + snd b <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= fst b)
/\ fst b + snd b <= RC.alloc_ceiling) (fr_ivs0 L FRx) ->
Forall (fun b : HI.blk => wr_at segs (mrestrict Fh m') (fst b) (snd b)
/\ (fst b + snd b <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= fst b)
/\ fst b + snd b <= RC.alloc_ceiling) (fr_ivs0 L FRx).
Proof.
intros Fh FRx LBx sp m m' Foff HPRES FRW. apply Forall_forall. intros b Hb0. destruct (proj1 (Forall_forall _ _) FRW b Hb0) as (HW & Himg & Hc).
split; [| split; [exact Himg| exact Hc]]. pose proof HW as (W0 & W1 & HWb).
split; [exact W0|]. split; [exact W1|]. intros i Hi.
pose proof (wr_at_hidden_offK _ Foff m _ _ HW (fst b + i) ltac:(lia)) as Fy.
specialize (HWb i Hi). unfold wview, mrestrict in HWb |- *. rewrite Fy in HWb |- *.
apply (HPRES (fst b + i) ltac:(lia)); [| exact HWb].
right; right. exists b. split; [apply in_app_iff; right; exact Hb0| unfold HI.blk_addr, HI.blk_size; lia].
Qed.

Theorem hiA_stack_malloc_1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (kc size lo : Z),
HEAPA1 k LB LM FR B m c ->
0 <= kc <= 2 \/ (kc = 3 /\ JH.hl_stack_malloc L 3 <> 0) -> 0 < size <= JH.fr_size kc -> size mod 8 = 0 ->
Z.of_nat (length FR) < fframe_cap kc ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
bv_unsigned sp <= BAUX -> lo <= hi_top RE ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 size ->
(forall ms' m' (Fa : Z),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 Fa) m' ms' ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
Fa <> 0 ->
(exists junk, OT.rw_cells segs m' Fa [OC.CB (Z.to_nat (JH.fr_size kc - 8)) junk]) ->
bytes_at segs m' (JH.shad L Fa) (repeat (Z_to_bv 8 0) (Z.to_nat (JH.fr_shadow_len kc))) ->
HEAPA1 k LB LM ((Fa, kc) :: FR) B m' c ->
AJv segs LV T c ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (JH.hl_stack_malloc L kc)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B kc size lo
HP Hkc Hsz Hsz8 Hcap Hstk Hlo Hlo2 HB Htop Htp Hgp Ha0 HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc). pose proof (rsv_nonneg k Hk0) as HRSV.
change (JH.fr_size kc) with (ff_size kc) in Hsz.
eapply (hiA_stack_malloc0 L LV Bc (PERMc PERM0 Lg) Tc Nc)
with (RSV := k * SC) (SM := SM) (SM_stack := SM_stack) (g := g) (LB := LB) (LM := LM) (FR := FR) (B := B) (lo := lo) (size := size); try eassumption.
intros ms' m' Fa junk Hret Hstk' Hpres HFm Hcd Hrng Hbody Hshad HA0'.
pose proof khi_val as EK. pose proof (@RC.alloc_ceiling_range RC__) as Hc.
destruct Hrng as (R1 & R2 & R3 & [Rl Rimg] & R5). destruct L_img as [Elo Ehi]. rewrite <- Elo, <- Ehi in Rimg.
destruct L_hull_eq as [_ Ehi2]. pose proof IMG_low as Hlow. unfold kLowEnd in *.
assert (Hs64 : 64 <= ff_size kc) by (unfold ff_size; assert (1 <= 2 ^ kc) by (apply Z.pow_le_mono_r with (b := 0); lia); lia).
assert (E8 : Fa = 8 * (Fa / 8)) by (apply Z.div_exact; [lia|]; apply (Zmod_divides Fa 64 ltac:(lia)) in R3 as [q ->]; replace (64 * q) with (8 * q * 8) by lia; apply Z.mod_mul; lia).
assert (D8 : ff_size kc = 8 * (ff_size kc / 8)) by (rewrite <- fr_shadow_len_ff; unfold ff_size, JH.fr_shadow_len; lia).
apply (HK ms' m' Fa Hret Hstk' Hpres).
- lia.
- exists junk. change (JH.fr_size kc) with (ff_size kc). apply (rw_cells_D segs m' _ [OC.CB (Z.to_nat (ff_size kc - 8)) junk]). cbn [map cellD].
destruct Hbody as [[Hwf Hb] Hw]. split; [split; [exact Hwf| exact (bytes_at_unhide segs _ Foffc m' _ _ Hb)]| exact (wr_at_unhide segs _ Foffc m' _ _ Hw)].
- destruct Hshad as [[_ Hb] _]. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb.
unfold JH.shad. rewrite L_sb, fr_shadow_len_ff. exact (bytes_at_unhide segs _ Foffc m' _ _ Hb).
- apply (heapA1_asan_step_fr k g g Lg H Bc Tc Nc s LB0 LB LM ((Fa, kc) :: FR) B m m' c c (bv_unsigned sp) _ KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT STA HA0' (vmst_refl _) HFm Hcd Hpres).
unfold fr_ivs0. cbn [flat_map app]. fold (fr_ivs0 L FR). unfold JH.fr_base, JH.fr_class. cbn [fst snd].
constructor; [| constructor].
+ cbn [fst snd]. change (JH.fr_size kc) with (ff_size kc). destruct Hbody as [_ Hw]. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by lia.
split; [exact Hw|]. split; lia.
+ cbn [fst snd]. destruct Hshad as [_ Hw]. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by lia.
unfold JH.shad. rewrite L_sb, fr_shadow_len_ff. unfold SH in Hw. split; [exact Hw|]. unfold kShadowOffset. split; [right; rewrite Ehi2; lia| lia].
+ apply (frw_keep _ FR (LB ++ LM) (bv_unsigned sp) m m' Foffc); [rewrite <- app_assoc; exact Hpres| exact FRW].
Qed.

Lemma fr_remove_incl : forall Fa (FR : list JH.frame) f, In f (JH.fr_remove Fa FR) -> In f FR.
Proof.
intros Fa FR. induction FR as [|f0 FR IH]; intros f Hf; [exact Hf|]. cbn [JH.fr_remove] in Hf.
destruct (Z.eqb (JH.fr_base f0) Fa); [right; exact Hf|]. destruct Hf as [<-|Hf]; [left; reflexivity| right; exact (IH f Hf)].
Qed.

Theorem hiA_frame_release_1 : forall (R Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (Fa kc fp pc : Z) (rX : bv 5),
HEAPA1 k LB LM FR B m c -> In (Fa, kc) FR ->
bytes_at segs m (Fa + JH.fr_size kc - 8) (le8 (Z_to_bv 64 fp)) ->
0 <= fp < 2^64 ->
LinuxProcessSemantics.Riscv.Sem.reg_get R rX = Z_to_bv 64 fp -> bv_unsigned rX <> 0 ->
OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt.code_at segs pc [0x23 + Z.shiftl (bv_unsigned rX) 15] ->
(forall m',
HEAPA1 k LB LM (JH.fr_remove Fa FR) B m' c ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
AJv segs LV T c (MS R Fr (Z_to_bv 64 (pc + 4)) fc None m' (seg_rom segs))) ->
AJv segs LV T c (MS R Fr (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
intros R Fr fc m c T k LB LM FR B Fa kc fp pc rX HP Hin HBy Hfp Hreg Hx0 Hcode HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc).
change (JH.fr_size kc) with (ff_size kc) in HBy.
destruct (heapA0g_frame_release L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) Foffc L_static L_sb L_dpn (k * SC) SM SM_stack DFs L_dpn_hull g LB LM FR B m c Fa kc (Z_to_bv 64 fp) HA0 Hin HBy)
as (HA0' & WVm & Fflag & HFm & Hcd & HPRES).
set (m' := write_to_mem m (Z_to_bv 64 fp) [Z_to_bv 8 0]) in *.
unfold AJv. apply (vj_evt segs LV Hwx Hsegs _ (silent_closed_srealizes segs LV T)).
apply (QYz7.sb_zero_evt segs _ R Fr pc fc m (seg_rom segs) rX (Z_to_bv 64 fp) (proj1 Hcode) Hx0 Hreg WVm).
apply evt_done. fold m'. apply (HK m').
- apply (heapA1_asan_step_fr k g g Lg H Bc Tc Nc s LB0 LB LM (JH.fr_remove Fa FR) B m m' c c RC.alloc_ceiling _ KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT STA HA0' (vmst_refl _) HFm Hcd HPRES).
apply Forall_forall. intros b Hb.
assert (Hb0 : In b (fr_ivs0 L FR)).
{ unfold fr_ivs0 in Hb |- *. apply in_flat_map in Hb as (f & Hf & Hbf). apply in_flat_map. exists f. split; [exact (fr_remove_incl Fa FR f Hf)| exact Hbf]. }
destruct (proj1 (Forall_forall _ _) FRW b Hb0) as (HW & Himg & Hc). split; [| split; [exact Himg| exact Hc]].
unfold m'. rewrite (mrestrict_write1 LV (FRof Lg) m (Z_to_bv 64 fp) (Z_to_bv 8 0) Fflag). exact (wr_at_write segs _ _ _ _ _ HW).
- intros a Ha Hne. unfold m'. rewrite write1_spec. destruct (bv_eqb (wa a) (Z_to_bv 64 fp)) eqn:E; [| reflexivity]. exfalso. apply Hne.
apply bv_eqb_true in E. apply (f_equal bv_unsigned) in E. rewrite wa_unsigned in E by lia. rewrite Z_to_bv_unsigned, bv_wrap_small in E by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia). exact E.
- intros x Hw. unfold m'. exact (wview_write_mono segs m _ _ x Hw).
Qed.

Definition stat_like (x : Z) : Prop :=
(HI.hl_img_lo HL <= x < HI.hl_img_hi HL /\ ~ HI.hl_client_static HL x /\ ~ HI.hl_scratch HL x)
\/ (exists g, x = g + JH.hl_sb L /\ ((BOTJ / 8 <= g /\ 8 * g < 2^47) \/ (HI.hl_img_lo HL <= 8 * g /\ 8 * g + 8 <= HI.hl_img_hi HL))).

Lemma stat_like_range : forall x, stat_like x -> 0 <= x < 2^64.
Proof.
intros x Hx. pose proof (HI.hl_img_range HL) as [I1 I2]. pose proof (@RC.alloc_ceiling_range RC__) as Hc. pose proof RUN_botj as Hb.
destruct Hx as [(H1 & _)|(g & -> & [(G1 & G2)|(G1 & G2)])]; [lia| |]; rewrite L_sb; unfold kShadowOffset.
- assert (0 <= BOTJ / 8) by (apply Z.div_pos; lia). lia.
- lia.
Qed.

Lemma heapA1_not_client : forall k LB LM FR B m c x, HEAPA1 k LB LM FR B m c -> stat_like x ->
~ HI.client_addr HL (LB ++ LM) RC.alloc_ceiling x /\ ~ HI.hl_scratch HL x /\
~ (exists Fa k0, In (Fa, k0) FR /\ (Fa <= x < Fa + JH.fr_size k0 - 8 \/ JH.shad L Fa <= x < JH.shad L Fa + JH.fr_shadow_len k0)).
Proof.
intros k LB LM FR B m c x HP Hx. pose proof khi_val as EK. pose proof (@RC.alloc_ceiling_range RC__) as Hc. pose proof RUN_botj as Hbot.
pose proof (HI.hl_img_range HL) as [I1 I2]. destruct L_hull_eq as [_ Ehi]. pose proof IMG_low as Hlow. rewrite <- Ehi in Hlow. unfold kLowEnd in *.
assert (FRM : forall Fa k0, In (Fa, k0) FR ->
(Fa + ff_size k0 <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= Fa) /\ (Fa + ff_size k0 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= Fa)
/\ Fa + ff_size k0 <= RC.alloc_ceiling /\ 0 <= Fa /\ Fa = 8 * (Fa / 8) /\ ff_size k0 = 8 * (ff_size k0 / 8) /\ 0 <= ff_size k0).
{ intros Fa k0 Hin. pose proof (heapA1_frame_place _ _ _ _ _ _ _ Fa k0 HP Hin) as (P1 & P2 & P3 & P4 & P5 & P6 & P7). cbv zeta in *. unfold kLowEnd in P1.
assert (Hs' : 0 <= ff_size k0) by (unfold ff_size; assert (0 <= 2 ^ k0) by (apply Z.pow_nonneg; lia); lia).
assert (E8 : Fa = 8 * (Fa / 8)) by (apply Z.div_exact; [lia|]; apply (Zmod_divides Fa 64 ltac:(lia)) in P6 as [q ->]; replace (64 * q) with (8 * q * 8) by lia; apply Z.mod_mul; lia).
assert (D8 : ff_size k0 = 8 * (ff_size k0 / 8)) by (rewrite <- fr_shadow_len_ff; unfold ff_size, JH.fr_shadow_len; lia).
repeat split; try assumption; lia. }
assert (BLK : forall a n, In (a, n) (LB ++ LM) -> (a + n <= HI.hl_img_lo HL \/ HI.hl_img_hi HL <= a) /\ (a + n + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= a)).
{ intros a n Hin. split; [exact (heapA1_blk_img _ _ _ _ _ _ _ a n HP Hin)|].
pose proof (heapA1_blk_appmem _ _ _ _ _ _ _ a n HP Hin) as Happ. rewrite L_sb in Happ. unfold kShadowOffset in Happ. lia. }
destruct Hx as [(H1 & H2 & H3)|(g & -> & Hg)].
-
split; [| split; [exact H3|]].
+ intros [Hs|[Hs|(b & Hb & Hr)]]; [lia| exact (H2 Hs)|]. destruct b as [a n]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
destruct (BLK a n Hb) as [Bi _]. lia.
+ intros (Fa & k0 & Hin & Hr). destruct (FRM Fa k0 Hin) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
change (JH.fr_size k0) with (ff_size k0) in Hr. rewrite fr_shadow_len_ff in Hr. unfold JH.shad in Hr. rewrite L_sb in Hr. unfold kShadowOffset in Hr. lia.
-
rewrite L_sb. unfold kShadowOffset.
assert (Hband : 0x7fff8000 <= g + 2147450880 < 0x10007fff8000).
{ destruct Hg as [(G1 & G2)|(G1 & G2)]; [assert (0 <= BOTJ / 8) by (apply Z.div_pos; lia); lia| lia]. }
split; [| split].
+ intros [Hs|[Hs|(b & Hb & Hr)]]; [lia| pose proof (HI.hl_static_in_img HL _ Hs); lia|]. destruct b as [a n]. unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
destruct (BLK a n Hb) as [_ Ba]. lia.
+ intros Hsc. pose proof (HI.hl_scratch_in_img HL _ Hsc). lia.
+ intros (Fa & k0 & Hin & Hr). destruct (FRM Fa k0 Hin) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
change (JH.fr_size k0) with (ff_size k0) in Hr. rewrite fr_shadow_len_ff in Hr. unfold JH.shad in Hr. rewrite L_sb in Hr. unfold kShadowOffset in Hr.
destruct Hr as [Hr|Hr]; [lia|].
destruct Hg as [(G1 & G2)|(G1 & G2)].
* assert (BOTJ - 7 <= 8 * (BOTJ / 8)) by (pose proof (Z.div_mod BOTJ 8 ltac:(lia)); pose proof (Z.mod_pos_bound BOTJ 8 ltac:(lia)); lia).
lia.
* lia.
Qed.

Variable SIVS : list (Z * Z).
Hypothesis L_sivs_cover : forall a, HI.hl_client_static HL a -> exists iv, In iv SIVS /\ fst iv <= a < snd iv.
Hypothesis L_sivs_data : forall iv a, In iv SIVS -> fst iv <= a < snd iv -> dl_client_data DL a.

Hypothesis L_scratch : forall a, HI.hl_scratch HL a -> HI.hl_tp HL - 164 <= a < HI.hl_tp HL - 160.
Hypothesis IMG_errno_any : forall m : word -> option byte, exists v : word, rw_cells segs m (HI.hl_tp HL - 164) [C4 v].
Hypothesis L_rstat_priv : forall a, mng_static a -> ~ HI.hl_client_static HL a /\ ~ HI.hl_scratch HL a.
Hypothesis L_scratch_data : forall a, HI.hl_scratch HL a -> RDATA_LO <= a < RIMG_HI.

Hypothesis OBL_STAT_client : forall m m' : word -> option byte,
(forall x, stat_like x -> m' (wa x) = m (wa x)) -> STAT m -> STAT m'.

Lemma heapA1_client_frame : forall k LB LM FR B m m' c, HEAPA1 k LB LM FR B m c ->
(forall a, 0 <= a < 2^64 ->
~ HI.client_addr HL (LB ++ LM) RC.alloc_ceiling a -> ~ HI.hl_scratch HL a ->
~ (exists Fa k0, In (Fa, k0) FR /\ (Fa <= a < Fa + JH.fr_size k0 - 8 \/ JH.shad L Fa <= a < JH.shad L Fa + JH.fr_shadow_len k0)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
mem_inv segs m' ->
HEAPA1 k LB LM FR B m' c.
Proof.
intros k LB LM FR B m m' c HP0 Hsame Hwm MI'.
assert (HAG : forall x, stat_like x -> m' (wa x) = m (wa x)).
{ intros x Hx. destruct (heapA1_not_client _ _ _ _ _ _ _ x HP0 Hx) as (N1 & N2 & N3). exact (Hsame x (stat_like_range x Hx) N1 N2 N3). }
assert (STA' : STAT m -> STAT m') by (apply OBL_STAT_client; exact HAG).
destruct HP0 as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc).
pose proof (@RC.alloc_ceiling_range RC__) as Hceil.

assert (KEEP : forall y : word, find_segment segs (bv_unsigned y) 1 = None -> m y <> None -> m' y <> None).
{ intros y Hs Hm. assert (Hw : wview segs m y <> None) by (unfold wview; destruct (m y); [discriminate| contradiction]).
apply Hwm in Hw. unfold wview in Hw. destruct (m' y); [discriminate|]. rewrite Hs in Hw. contradiction. }
exists g, Lg, H, Bc, Tc, Nc, s, LB0.
split.
{ apply (heapA0g_client_frame L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) Foffc L_errno L_sb (k * SC) SIVS L_sivs_cover L_sivs_data L_scratch IMG_errno_any g LB LM FR B m m' c HA0 Hsame Hwm MI').
-
intros dn HDn. apply (depot_n_agree L DL _ _ dn HDn). intros x Hx. unfold mrestrict. destruct (Fof LV (FRof Lg) (wa x)); [reflexivity|].
apply HAG. left. destruct L_img as [Elo Ehi]. destruct L_dpn_hull as [D1 D2]. rewrite Elo, Ehi. split; [lia| exact (L_dpn_priv x Hx)].
-
pose proof HA0 as (ps0 & LBd0 & FSd0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (I0 & I1 & HI) & _).
split; [exact I0|]. split; [exact I1|]. intros a Ha. destruct (HI a Ha) as [W _]. pose proof (Hwm _ W) as W'. split; [exact W'|].
destruct IMG_data as (D1 & D2 & D3). unfold kLowEnd in D3. unfold hi_top in Ha, I1.
unfold wview in W'. unfold mrd. destruct (m' (wa a)) as [b|]; [exists b; reflexivity|]. exfalso. apply W'.
rewrite wa_unsigned by lia. rewrite (IMG_seg_G a) by (right; lia). reflexivity. }
split. { destruct KL as [k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13]. constructor; try assumption.
- intros y Hy. apply KEEP; [apply segs_low; exact (k9 y Hy)| exact (k10 y Hy)].
- intros y Hy. discriminate. }
split; [exact Hk0|]. split; [exact HTr|]. split; [exact HNr|]. split; [exact HOR|].
split. { intros a n Hin. destruct (HLMr a n Hin) as [Hrng Hb]. split; [exact Hrng|]. intros x Hx. destruct (Hb x Hx) as [Hr Hm].
split; [exact Hr|]. apply KEEP; [| exact Hm]. apply Foffc. exact (in_regs_Fof _ _ Hr). }
split; [exact PLM|].
split.
{ apply (MGI.ml_agree_blk segs S ML s Lg LB0 m m' RH SIM); [intros b0 l0 Hbl0; exact (proj1 (kla_groups _ _ _ _ _ _ _ _ _ _ _ _ _ KL b0 l0 Hbl0))| | intros a Ha _ Hw; exact (Hwm _ Hw)].
intros a Ha Hsd NB. apply (Hsame a Ha).
-
intros [Hst|[Hcs|Hib]].
+  destruct Hsd as [Hs|Hd].
* pose proof (stat_in_hull a (or_introl Hs)). unfold kLowEnd in IMG_low. lia.
* pose proof (Flowc (wa a) (in_regs_Fof _ _ (mng_dyn_regs Lg a Ha HOR Hd))) as Hl. rewrite (wa_unsigned a Ha) in Hl. lia.
+  destruct Hsd as [Hs|Hd].
* exact (proj1 (L_rstat_priv a Hs) Hcs).
* apply (F_off_data _ Lg g c H m Bc Tc Nc (wa a) KL (in_regs_Fof _ _ (mng_dyn_regs Lg a Ha HOR Hd))).
rewrite (wa_unsigned a Ha). exact (proj1 (L_static2 a Hcs)).
+  destruct Hib as ([ab nb] & Hinb & Hr). unfold HI.blk_addr, HI.blk_size in Hr. cbn [fst snd] in Hr.
apply in_app_or in Hinb as [Hinb|Hinb].
*
destruct Hsd as [Hs|Hd].
-- pose proof (stat_in_hull a (or_introl Hs)) as Hh.
pose proof (heapA0_blk_img L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) (k * SC) L_img LB LM FR B m c ab nb (ex_intro _ g HA0) Hinb) as Di.
destruct IMG_hull as (U1 & U2 & _). lia.
-- destruct HA0 as (ps & LBd & FSd & _ & ELB & _ & _ & _ & _ & _ & _ & _ & _ & _ & HOFF & _).
rewrite ELB in Hinb. apply in_map_iff in Hinb as (bd & Eb & Hbd). unfold blk_of in Eb. inversion Eb; subst ab nb.
pose proof (proj2 (proj1 (List.Forall_forall _ _) HOFF bd Hbd) a Hr) as Hoff.
rewrite (in_regs_Fof _ _ (mng_dyn_regs Lg a Ha HOR Hd)) in Hoff. discriminate.
*
apply NB. pose proof (Permutation_in _ PLM Hinb) as I. apply in_map_iff in I as (b & E & Hb). unfold zblk in E. inversion E; subst ab nb.
exists b. split; [exact Hb| exact Hr].
-
intros Hsc. destruct Hsd as [Hs|Hd].
+ exact (proj2 (L_rstat_priv a Hs) Hsc).
+ apply (F_off_data _ Lg g c H m Bc Tc Nc (wa a) KL (in_regs_Fof _ _ (mng_dyn_regs Lg a Ha HOR Hd))).
rewrite (wa_unsigned a Ha). exact (L_scratch_data a Hsc).
-
intros (Fa & k0 & HinF & Hr).
assert (HIV : exists b : HI.blk, In b (fr_ivs0 L FR) /\ fst b <= a < fst b + snd b).
{ destruct Hr as [Hr|Hr]; [exists (Fa, JH.fr_size k0 - 8) | exists (JH.shad L Fa, JH.fr_shadow_len k0)];
(split; [unfold fr_ivs0; apply in_flat_map; exists (Fa, k0); split; [exact HinF| cbn; auto] | cbn [fst snd]; lia]). }
destruct HIV as (b & Hb & Hrb). pose proof (proj1 (List.Forall_forall _ _) FRW b Hb) as (Wb & Ib & _).
destruct Hsd as [Hs|Hd].
+ pose proof (stat_in_hull a (or_introl Hs)) as Hh. destruct IMG_hull as (U1 & U2 & _). lia.
+ pose proof (wr_at_hidden_off L LV (FRof Lg) Foffc m (fst b) (snd b) Wb a Hrb) as Hoff.
rewrite (in_regs_Fof _ _ (mng_dyn_regs Lg a Ha HOR Hd)) in Hoff. discriminate. }
split; [exact SIM|]. split; [exact PLV|]. split; [exact NDL|]. split; [exact SZ|].
split; [exact (MGI.ml_auxv_mem segs S ML m m' BAUX AUX)|]. split; [exact CNT|]. split; [| exact (STA' STA)].

apply Forall_forall. intros b Hb. destruct (proj1 (List.Forall_forall _ _) FRW b Hb) as (Wb & Ib & Cb).
split; [| split; [exact Ib| exact Cb]]. destruct Wb as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi.
specialize (W3 i Hi). unfold wview, mrestrict in W3 |- *.
destruct (Fof LV (FRof Lg) (wa (fst b + i))) eqn:EF.
- exact W3.
- assert (Hw : wview segs m (wa (fst b + i)) <> None) by (unfold wview; exact W3). apply Hwm in Hw. exact Hw.
Qed.

Variables SD SD_stack RL RL_stack : Z.
Hypothesis DT2 : donor_t2 RC.alloc_ceiling segs (at_nodeA LV segs) DL DCo SD SD_stack RL RL_stack.
Hypothesis L_strdup : JH.hl_strdup L = SD.
Hypothesis L_realloc : HI.hl_realloc HL = RL.
Hypothesis L_t2_stack : SD_stack <= JH.hl_stack_A L /\ RL_stack <= JH.hl_stack_A L.

Theorem hiA_strdup_1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (src ab nb lo : Z) (str : list byte) (u : JH.uwd),
let n := Z.of_nat (length str) + 1 in
HEAPA1 k LB LM FR B m c ->
In (ab, nb) LB -> ab <= src -> src + Z.of_nat (length str) + 1 <= ab + nb ->
bytes_at segs m src (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> n <= 2^26 ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
bv_unsigned sp <= BAUX ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 src ->
lo <= hi_top RE ->
1 <= JH.bN B -> JH.acostA n <= JH.bB B -> JH.uw_cost u <= JH.bD B -> n + 8192 <= JH.bQ B ->
(forall ms' m' c' (r : Z) (errv' : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 r) m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv'] ->
r <> 0 -> bytes_at segs m' r (str ++ [Z_to_bv 8 0]) ->
HEAPA1 k ((r, n) :: LB) LM FR (JH.chargeQ (JH.charge B (JH.acostA n) (JH.uw_cost u) 1) (n + 8192)) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (JH.hl_strdup L)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B src ab nb lo str u n
HP Hinb Hs1 Hs2 Hsrc Hnz Hn Hstk Hlo Hlo2 HB Htp Hgp Ha0 Htop HbN HbB HbD HbQ HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc). pose proof (rsv_nonneg k Hk0) as HRSV.
eapply (hiA_strdup0 L LA LV Bc (PERMc PERM0 Lg) Tc Nc LLc Hwx Hsegs Hsh Hbx Hbc DL RE RE_L DCo (FRof Lg) HFRc Foffc Flowc)
with (RSV := k * SC) (g := g) (u := u) (LB := LB) (LM := LM) (FR := FR) (B := B) (src := src) (ab := ab) (nb := nb) (lo := lo) (str := str); try eassumption.
intros ms' m' c' g' r errv' Hret Hvo Hstk' Hpres Hvm HFm Hcd Herr Hr0 Hblk HA0'.
apply (HK ms' m' c' r errv'); try assumption.
exact (heapA1_asan_step k g g' Lg H Bc Tc Nc s LB0 _ LM FR _ m m' c c' (bv_unsigned sp) LB KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT FRW STA HA0' Hvm HFm Hcd Hpres HB).
Qed.

Theorem hiA_realloc_1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (p n0 n lo : Z) (old junk0 : list byte) (u : JH.uwd),
HEAPA1 k LB LM FR B m c ->
In (p, n0) LB ->
OT.rw_cells segs m p [OC.CB (Z.to_nat n0) (old ++ junk0)] ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
bv_unsigned sp <= BAUX ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
lo <= hi_top RE ->
1 <= JH.bN B -> JH.acostA n <= JH.bB B -> JH.uw_cost u <= JH.bD B -> n + 8192 <= JH.bQ B ->
(forall ms' m' c' (r : Z) (errv' : word),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 r) m' ms' ->
HI.model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (HI.lb_remove p LB ++ LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
OT.rw_cells segs m' (HI.hl_tp HL - 164) [OC.C4 errv'] ->
r <> 0 ->
(exists junk, OT.rw_cells segs m' r [OC.CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n (Z.of_nat (length old)))) old ++ junk)]) ->
HEAPA1 k ((r, n) :: HI.lb_remove p LB) LM FR (JH.chargeQ (JH.charge B (JH.acostA n) (JH.uw_cost u) 1) (n + 8192)) m' c' ->
AJv segs LV T c' ms') ->
AJv segs LV T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (HI.hl_realloc HL)) fc None m (seg_rom segs)).
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B p n0 n lo old junk0 u
HP HIN Hold Hstk Hlo Hlo2 HB Htp Hgp Ha0 Ha1 Hn Htop HbN HbB HbD HbQ HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc). pose proof (rsv_nonneg k Hk0) as HRSV.
eapply (hiA_realloc0 L LA LV Bc (PERMc PERM0 Lg) Tc Nc LLc Hwx Hsegs Hsh Hbx Hbc DL RE RE_L DCo (FRof Lg) HFRc Foffc Flowc)
with (RSV := k * SC) (g := g) (u := u) (LB := LB) (LM := LM) (FR := FR) (B := B) (p := p) (n0 := n0) (n := n) (lo := lo) (old := old) (junk0 := junk0); try eassumption.
intros ms' m' c' g' r errv' Hret Hvo Hstk' Hpres Hvm HFm Hcd Herr Hr0 Hblk HA0'.
apply (HK ms' m' c' r errv'); try assumption.
exact (heapA1_asan_step k g g' Lg H Bc Tc Nc s LB0 _ LM FR _ m m' c c' (bv_unsigned sp) (HI.lb_remove p LB) KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT FRW STA HA0' Hvm HFm Hcd Hpres HB).
Qed.

Definition HEAPA63 (_ : unit) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (m : word -> option byte) (c : config) : Prop :=
HEAPA1 (JH.bM B) LB LM FR B m c
/\ Forall (fun b : HI.blk => 1 <= snd b) LB /\ Forall (fun b : HI.blk => snd b < 2^40) LM
/\ JH.bB B + 2^23 <= 2^39 /\ 0 <= JH.bQ B
/\ Forall (fun f : JH.frame => 0 <= JH.fr_class f <= 3) FR.

Variable TOPJ : Z.
Hypothesis RUN_topj : RC.alloc_ceiling < TOPJ /\ TOPJ <= 2^47.
Hypothesis L_baux : TOPJ + 64 <= BAUX.
Hypothesis RUN_top_re : TOPJ + 64 <= ae_stack_top RE + JH.hl_stack_A L.

Lemma topj_lo : forall lo sp, lo <= sp - JH.hl_stack_A L -> sp < TOPJ + 64 -> lo <= hi_top RE.
Proof. intros lo sp H1 H2. unfold hi_top. lia. Qed.

Notation J63 := (aj_base_vj segs LV Hwx Hsegs).

Variable STATC : list (Z * list byte).
Hypothesis OBL_STAT_cells : forall m, STAT m -> Forall (fun c => bytes_at segs m (fst c) (snd c)) STATC.
Hypothesis L_rtc_all : forall c, In c (JH.hl_rt_consts L) -> In c (dl_rtc DL) \/ In c STATC.
Hypothesis L_sb_cells : In (JH.hl_got_sb L, le8 (Z_to_bv 64 (JH.hl_sb_cell L))) (dl_rtc DL) /\ In (JH.hl_sb_cell L, le8 (Z_to_bv 64 (JH.hl_sb L))) (dl_rtc DL) /\
In (JH.hl_got_uar L, le8 (Z_to_bv 64 (JH.hl_uar_cell L))) (dl_rtc DL) /\ In (JH.hl_uar_cell L, le4 (Z_to_bv 64 1)) (dl_rtc DL).
Hypothesis OBL_STATIC : JH.hia_static L unit HEAPA63 TOPJ BOTJ.
Hypothesis OBL_FREE2_NULL : JH.hiA_free2_null_ty L J63 unit HEAPA63 TOPJ.

Lemma lb_remove_notin : forall p (LB : list HI.blk), (forall b, In b LB -> HI.blk_addr b <> p) -> HI.lb_remove p LB = LB.
Proof.
intros p LB. induction LB as [|b LB IH]; intros Hn; [reflexivity|]. cbn [HI.lb_remove].
destruct (Z.eqb_spec (HI.blk_addr b) p) as [E|E]; [exfalso; exact (Hn b (or_introl eq_refl) E)|].
rewrite IH; [reflexivity|]. intros b' Hb'. apply Hn. right. exact Hb'.
Qed.
Lemma lb_remove_incl : forall p (LB : list HI.blk) b, In b (HI.lb_remove p LB) -> In b LB.
Proof.
intros p LB. induction LB as [|b0 LB IH]; intros b Hb; [exact Hb|]. cbn [HI.lb_remove] in Hb.
destruct (Z.eqb (HI.blk_addr b0) p); [right; exact Hb|]. destruct Hb as [<-|Hb]; [left; reflexivity| right; exact (IH b Hb)].
Qed.
Lemma Forall_lb_remove : forall (P : HI.blk -> Prop) p LB, Forall P LB -> Forall P (HI.lb_remove p LB).
Proof. intros P p LB HF. apply Forall_forall. intros b Hb. exact (proj1 (Forall_forall _ _) HF b (lb_remove_incl p LB b Hb)). Qed.

Lemma fcl_in : forall (FR : list JH.frame) Fa kc, Forall (fun f : JH.frame => 0 <= JH.fr_class f <= 3) FR -> In (Fa, kc) FR -> 0 <= kc <= 3.
Proof. intros FR Fa kc FCL Hin. exact (proj1 (Forall_forall _ _) FCL (Fa, kc) Hin). Qed.
Lemma fcl_remove : forall Fa (FR : list JH.frame), Forall (fun f : JH.frame => 0 <= JH.fr_class f <= 3) FR -> Forall (fun f : JH.frame => 0 <= JH.fr_class f <= 3) (JH.fr_remove Fa FR).
Proof. intros Fa FR FCL. apply Forall_forall. intros f Hf. exact (proj1 (Forall_forall _ _) FCL f (fr_remove_incl Fa FR f Hf)). Qed.

Theorem hiA_frame_release_63x : forall (R : bvmap 5 word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config)
(T : OSA.TSet) (A : unit) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (Fa kc fp pc : Z) (rX : bv 5),
HEAPA63 A LB LM FR B m c -> In (Fa, kc) FR ->
bytes_at segs m (Fa + JH.fr_size kc - 8) (le8 (Z_to_bv 64 fp)) ->
0 <= fp < 2^64 ->
LinuxProcessSemantics.Riscv.Sem.reg_get R rX = Z_to_bv 64 fp -> bv_unsigned rX <> 0 ->
OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt.code_at segs pc [0x23 + Z.shiftl (bv_unsigned rX) 15] ->
(forall m' A',
HEAPA63 A' LB LM (JH.fr_remove Fa FR) B m' c ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
JH.AJ J63 T c (MS R Fr (Z_to_bv 64 (pc + 4)) fc None m' (seg_rom segs))) ->
JH.AJ J63 T c (MS R Fr (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
intros R Fr fc m c T A LB LM FR B Fa kc fp pc rX (HP1 & FLB & FLM & HBB & HQ0 & FCL) Hin HBy Hfp Hreg Hx0 Hcode HK.
apply (hiA_frame_release_1 R Fr fc m c T (JH.bM B) LB LM FR B Fa kc fp pc rX HP1 Hin HBy Hfp Hreg Hx0 Hcode).
intros m' HP1' Hoff Hwv. apply (HK m' tt); [| exact Hoff| exact Hwv].
split; [exact HP1'|]. split; [exact FLB|]. split; [exact FLM|]. split; [exact HBB|]. split; [exact HQ0| exact (fcl_remove Fa FR FCL)].
Qed.

Theorem donorx_v63 : JH.hia_donorx L unit HEAPA63.
Proof.
constructor.
- intros A LB LM FR B m c a n (HP & _) Hin. exact (heapA1_blk_slack _ _ _ _ _ _ _ a n HP Hin).
- intros A LB LM FR B m c a n i (HP & _) Hin Hi. exact (heapA1_shadow_words _ _ _ _ _ _ _ a n i HP Hin Hi).
Qed.

Theorem heapA63_errno : forall A LB LM FR B m c, HEAPA63 A LB LM FR B m c -> exists errv : word, OT.rw_cells segs m (HI.hl_tp HL - 164) [OC.C4 errv].
Proof.
intros A LB LM FR B m c ((g & Lg & H & Bc & Tc & Nc & s & LB0 & (ps & LBd & FSd & RUN & _) & KL & _) & _).
destruct (dc_errno _ _ _ _ DCo _ _ _ _ _ RUN) as [errv Herr]. exists errv. rewrite L_errno in Herr.
apply (rw_cells_D segs m _ [OC.C4 errv]). cbn [map cellD]. destruct Herr as [[Hwf Hb] Hw].
pose proof (KLA_F_off _ Lg g c H m Bc Tc Nc KL) as Foffc.
split; [split; [exact Hwf| exact (bytes_at_unhide segs _ Foffc m _ _ Hb)]| exact (wr_at_unhide segs _ Foffc m _ _ Hw)].
Qed.

Theorem tier1_v63 : JH.hia_tier1 L J63 unit HEAPA63 TOPJ.
Proof.
constructor.
-  intros A LB LM FR B m c Fa kc (HP & _ & _ & _ & _ & FCL) Hin. pose proof (fcl_in FR Fa kc FCL Hin) as Hkc.
split; [exact Hkc|]. exact (heapA1_frame _ _ _ _ _ _ _ Fa kc HP Hin Hkc).
-  intros A LB LM FR B m c Fa kc a n (HP & _ & _ & _ & _ & FCL) Hin Hb.
exact (heapA1_frame_disjoint _ _ _ _ _ _ _ Fa kc a n HP Hin (proj1 (fcl_in FR Fa kc FCL Hin)) Hb).
-  intros A LB LM FR B m c Fa kc Fa' kc' (HP & _) H1 H2 Hne. exact (heapA1_frame_apart _ _ _ _ _ _ _ Fa kc Fa' kc' HP H1 H2 Hne).
-  intros A LB LM FR B m c (HP & _). apply NoDup_ListNoDup. exact (heapA1_frame_nodup _ _ _ _ _ _ _ HP).
-  intros A LB LM FR B m c Fa kc (HP & _) Hin. exact (heapA1_frame_appmem _ _ _ _ _ _ _ Fa kc HP Hin).
-  intros A LB LM FR B m c Fa kc i (HP & _) Hin Hi. exact (heapA1_frame_shadow_sep _ _ _ _ _ _ _ Fa kc i HP Hin Hi).
-
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B kc bytes lo
(HP1 & FLB & FLM & HBB & HQ0 & FCL) Hkc Hby Hby8 Hlen Hstk Hlo Hlo2 Hal Htop Htp Hgp Ha0 HK. pose proof (topj_lo _ _ Hlo2 Htop) as Htop'.
assert (Hcap : Z.of_nat (length FR) < fframe_cap kc).
{ unfold fframe_cap. destruct Hkc as [Hkc2 | (-> & _ & Hlen3)]; [assert (2 ^ 12 <= 2 ^ (14 - kc)) by (apply Z.pow_le_mono_r; lia); lia | change (2 ^ (14 - 3)) with 2048; exact Hlen3]. }
assert (HkcT : 0 <= kc <= 2 \/ (kc = 3 /\ JH.hl_stack_malloc L 3 <> 0)) by (clear - Hkc; destruct Hkc as [H|(H1 & H2 & _)]; [left; exact H | right; split; [exact H1 | exact H2]]).
assert (Hkc3 : 0 <= kc <= 3) by (clear - Hkc; lia).
apply (hiA_stack_malloc_1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B kc bytes lo
HP1 HkcT ltac:(lia) Hby8 Hcap Hstk Hlo Hlo2 ltac:(lia) Htop' Htp Hgp Ha0).
intros ms' m' Fa RS ST HPR Hnz BLK SHB HP1'.
apply (HK ms' m' tt Fa RS ST HPR Hnz BLK SHB).
split; [exact HP1'|]. split; [exact FLB|]. split; [exact FLM|]. split; [exact HBB|]. split; [exact HQ0|].
constructor; [unfold JH.fr_class; cbn [snd]; exact Hkc3| exact FCL].
-  exact hiA_frame_release_63x.
Qed.

Theorem tier2_v63 : JH.hia_tier2 L J63 unit HEAPA63 TOPJ.
Proof.
constructor.
-
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B p n0 n lo errv old junk0 u
HP HIN Hold Hstk Hlo Hlo2 Hal Htop Herr Htp Hgp Ha0 Ha1 Hn Hpre Hok HbN HbB HbD HbQ HK.
destruct HP as (HP1 & FLB & FLM & HBB & HQ0 & FCL). pose proof (topj_lo _ _ Hlo2 Htop) as Htop'.
apply (hiA_realloc_1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B p n0 n lo old junk0 u
HP1 HIN Hold Hstk Hlo Hlo2 ltac:(lia) Htp Hgp Ha0 Ha1 Hn Htop' HbN HbB HbD HbQ).
intros ms' m' c' r errv' RS VM ST HPR ERR Hr BLK HP1'.
apply (HK ms' m' c' tt r errv' RS VM ST ERR Hr HPR BLK).
split; [exact HP1'|]. split; [constructor; [cbn [snd]; lia| exact (Forall_lb_remove _ p LB FLB)]|]. split; [exact FLM|].
cbn [JH.chargeQ JH.charge JH.bB JH.bQ]. pose proof (JH.acostA_nonneg n ltac:(lia)). split; [lia|]. split; [lia| exact FCL].
-
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B src ab nb lo str errv u
HP Hinb Hs1 Hs2 Hsrc Hnz Hn Hstk Hlo Hlo2 Hal Htop Herr Htp Hgp Ha0 Hpre Hok HbN HbB HbD HbQ HK.
destruct HP as (HP1 & FLB & FLM & HBB & HQ0 & FCL). pose proof (topj_lo _ _ Hlo2 Htop) as Htop'.
apply (hiA_strdup_1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B src ab nb lo str u
HP1 Hinb Hs1 Hs2 Hsrc Hnz Hn Hstk Hlo Hlo2 ltac:(lia) Htp Hgp Ha0 Htop' HbN HbB HbD HbQ).
intros ms' m' c' r errv' RS VM ST HPR ERR Hr BLK HP1'.
apply (HK ms' m' c' tt r errv' RS VM ST HPR ERR Hr BLK).
split; [exact HP1'|]. split; [constructor; [cbn [snd]; lia| exact FLB]|]. split; [exact FLM|].
cbn [JH.chargeQ JH.charge JH.bB JH.bQ]. pose proof (JH.acostA_nonneg (Z.of_nat (length str) + 1) ltac:(lia)). split; [lia|]. split; [lia| exact FCL].
Qed.

Hypothesis RUN_bot_top : BOTJ mod 8 = 0 /\ BOTJ <= TOPJ.

Hypothesis L_img_lo_small : HI.hl_img_lo HL <= 0xb09000.
Theorem heapA63_frame_above : forall A LB LM FR B m c Fa kc, HEAPA63 A LB LM FR B m c -> In (Fa, kc) FR -> HI.hl_img_hi HL <= Fa.
Proof.
intros A LB LM FR B m c Fa kc (HP & _) Hin.
pose proof (heapA1_frame_place _ _ _ _ _ _ _ Fa kc HP Hin) as (P1 & P2 & P3 & P4 & P5 & P6 & P7). cbv zeta in *.
pose proof khi_val as EK. unfold kLowEnd in *.
destruct P2 as [P2|P2]; [|lia]. destruct P1 as [P1|P1]; lia.
Qed.

Definition hiA_v63 : JH.heap_iface_A L.
Proof.
refine {| JH.hiA_J := J63; JH.ASA := unit; JH.HEAPA := HEAPA63;
JH.hiA_top := TOPJ; JH.hiA_bot := BOTJ;
JH.heapA_blk_slack := JH.dx_heapA_blk_slack _ _ _ donorx_v63;
JH.heapA_shadow_words := JH.dx_heapA_shadow_words _ _ _ donorx_v63;
JH.heapA_errno := heapA63_errno;
JH.heapA_frame_above := heapA63_frame_above;
JH.heapA_shadow_glob := JH.st_heapA_shadow_glob _ _ _ _ _ OBL_STATIC;
JH.heapA_canary := JH.st_heapA_canary _ _ _ _ _ OBL_STATIC;
JH.heapA_need_locks := JH.st_heapA_need_locks _ _ _ _ _ OBL_STATIC;
JH.heapA_consts := JH.st_heapA_consts _ _ _ _ _ OBL_STATIC;
JH.heapA_shadow_stack := JH.st_heapA_shadow_stack _ _ _ _ _ OBL_STATIC;
JH.heapA_shadow_img := JH.st_heapA_shadow_img _ _ _ _ _ OBL_STATIC;
JH.heapA_frame := JH.t1_heapA_frame _ _ _ _ _ tier1_v63;
JH.heapA_frame_disjoint := JH.t1_heapA_frame_disjoint _ _ _ _ _ tier1_v63;
JH.heapA_frame_apart := JH.t1_heapA_frame_apart _ _ _ _ _ tier1_v63;
JH.heapA_frame_nodup := JH.t1_heapA_frame_nodup _ _ _ _ _ tier1_v63;
JH.heapA_frame_appmem := JH.t1_heapA_frame_appmem _ _ _ _ _ tier1_v63;
JH.heapA_frame_shadow_sep := JH.t1_heapA_frame_shadow_sep _ _ _ _ _ tier1_v63;
JH.hiA_stack_malloc := JH.t1_hiA_stack_malloc _ _ _ _ _ tier1_v63;
JH.hiA_frame_release := JH.t1_hiA_frame_release _ _ _ _ _ tier1_v63;
JH.hiA_realloc := JH.t2_hiA_realloc _ _ _ _ _ tier2_v63;
JH.hiA_strdup := JH.t2_hiA_strdup _ _ _ _ _ tier2_v63 |}.
-  exact (proj1 RUN_topj).
-  exact (proj2 RUN_topj).
-  exact RUN_bot_top.
-  intros A LB LM FR B m c (HP & _). exact (heapA1_cok _ _ _ _ _ _ _ HP).
-  intros A LB LM FR B m c (HP & _). exact (heapA1_mem_inv _ _ _ _ _ _ _ HP).
-  intros A LB LM FR B m c (HP & _ & _ & _ & HQ0 & _). pose proof (heapA1_budget _ _ _ _ _ _ _ HP) as (B1 & B2 & B3).
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & _ & _ & Hk0 & _). auto.
-  intros A LB LM FR B m c (_ & _ & _ & HBB & _). exact HBB.
-  intros A LB LM FR B m c c' (HP & R) HN. split; [exact (heapA1_cfg_next _ _ _ _ _ _ _ _ HP HN)| exact R].
-  intros A LB LM FR B m c a n (HP & _ & FLM & _) Hin. apply in_app_or in Hin as [Hin|Hin].
+ pose proof (heapA1_blk_le26 _ _ _ _ _ _ _ a n HP Hin). lia.
+ exact (proj1 (Forall_forall _ _) FLM (a, n) Hin).
-  intros A LB LM FR B m c a n (HP & _) Hin. exact (heapA1_blk_le26 _ _ _ _ _ _ _ a n HP Hin).
-  intros A LB LM FR B m c a n (HP & _) Hin. exact (heapA1_blk _ _ _ _ _ _ _ a n HP Hin).
-  intros A LB LM FR B m c a n (HP & _) Hin. exact (heapA1_blk_img _ _ _ _ _ _ _ a n HP Hin).
-  intros A LB LM FR B m c a n a' n' (HP & FLB & _) H1 H2 Hne. exact (heapA1_blk_disjoint _ _ _ _ _ _ _ a n a' n' HP FLB H1 H2 Hne).
-  intros A LB LM FR B m c (HP & FLB & _). exact (heapA1_blk_nodup _ _ _ _ _ _ _ HP FLB).
-  intros A LB LM FR B m c a n i (HP & _) Hin Hi. exact (heapA1_blk_not_static _ _ _ _ _ _ _ a n i HP Hin Hi).
-  intros A LB LB' LM LM' FR FR' B m c (HP & FLB & FLM & HBB & HQ0 & FCL) P1 P2 P3.
split; [exact (heapA1_perm _ _ _ _ _ _ _ _ _ _ HP P1 P2 P3)|]. split; [exact (Permutation_Forall P1 FLB)|]. split; [exact (Permutation_Forall P2 FLM)|]. split; [exact HBB|]. split; [exact HQ0| exact (Permutation_Forall P3 FCL)].
-  intros A LB LM FR B m c a n (HP & _) Hin. exact (heapA1_shadow_blk _ _ _ _ _ _ _ a n HP Hin).
-  intros A LB LM FR B m c a n i (HP & _) Hin Hi. exact (heapA1_shadow_sep _ _ _ _ _ _ _ a n i HP Hin Hi).
-  intros A LB LM FR B m c (HP & _). pose proof (heapA1_rtc_cells _ _ _ _ _ _ _ HP) as RT. rewrite Forall_forall in RT.
destruct L_sb_cells as (I1 & I2 & I3 & I4). split; [exact (RT _ I1)|]. split; [exact (RT _ I2)|]. split; [exact (RT _ I3)| exact (RT _ I4)].
-  intros A LB LM FR B m m' c (HP & R) Hsame Hwm MI'. split; [| exact R].
exact (heapA1_client_frame _ _ _ _ _ m m' _ HP Hsame Hwm MI').
-  intros A LB LM FR B m c (HP & _). pose proof (heapA1_rtc_cells _ _ _ _ _ _ _ HP) as RT. rewrite Forall_forall in RT.
assert (STA : STAT m) by (destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HP); do 16 (destruct HP as [_ HP]); exact HP).
pose proof (OBL_STAT_cells m STA) as SC. rewrite Forall_forall in SC.
apply Forall_forall. intros cl Hcl. destruct (L_rtc_all cl Hcl) as [I|I]; [exact (RT cl I)| exact (SC cl I)].
-  intros A LB LM FR B m c a n (HP & _) Hin. exact (heapA1_blk_appmem _ _ _ _ _ _ _ a n HP Hin).
-
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B n lo errv u HP Hstk Hlo Hlo2 Hal Htop Herr Htp Hgp Ha0 Hn Hpre Hok HbN HbB HbD HbQ HK.
destruct HP as (HP1 & FLB & FLM & HBB & HQ0 & FCL). pose proof (topj_lo _ _ Hlo2 Htop) as Htop'.
apply (hiA_malloc_1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B n lo u HP1 Hstk Hlo Hlo2 ltac:(lia) Htp Hgp Ha0 Hn Htop' HbN HbB HbD HbQ).
intros ms' m' c' r errv' RS VM ST HPR ERR Hr BLK HP1'.
apply (HK ms' m' c' tt r errv' RS VM ST HPR ERR Hr BLK).
split; [exact HP1'|]. split; [constructor; [cbn [snd]; lia| exact FLB]|]. split; [exact FLM|].
cbn [JH.chargeQ JH.charge JH.bB JH.bQ]. pose proof (JH.acostA_nonneg n ltac:(lia)). split; [lia|]. split; [lia| exact FCL].
-
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B p lo errv u HP HIN Hstk Hlo Hlo2 Hal Htop Herr Htp Hgp Ha0 [Hpre Hok] HbD HK.
destruct (Z.eq_dec p 0) as [Ep|Ep].
+
subst p.
pose proof HP as (HP1 & FLB & FLM & HBB & HQ0 & FCL). pose proof (topj_lo _ _ Hlo2 Htop) as Htop'.
apply (hiA_free_null_1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B lo errv u HP1 Hstk Hlo Hlo2 ltac:(lia) Herr Htp Hgp Ha0 Htop').
intros ms' m' r RS ST HPR ERR HP1'.
assert (ELB : HI.lb_remove 0 LB = LB).
{ apply lb_remove_notin. intros [ba bn] Hb E. unfold HI.blk_addr in E. cbn [fst] in E. subst ba.
pose proof (heapA1_blk _ _ _ _ _ _ _ 0 bn HP1 (in_or_app _ _ _ (or_introl Hb))). lia. }
apply (HK ms' m' c tt r RS (HI.model_vm_only_refl _) ST); [rewrite ELB; exact HPR| exact ERR|].
rewrite ELB. split; [exact HP1'|]. split; [exact FLB|]. split; [exact FLM|]. cbn [JH.charge JH.bB JH.bQ Z.eqb]. split; [lia|]. split; [lia| exact FCL].
+ destruct HIN as [E0|[n Hin]]; [contradiction|].
destruct HP as (HP1 & FLB & FLM & HBB & HQ0 & FCL). pose proof (topj_lo _ _ Hlo2 Htop) as Htop'.
assert (Ez : Z.eqb p 0 = false) by (apply Z.eqb_neq; exact Ep). rewrite Ez in HbD.
apply (hiA_free_1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B p n lo errv u HP1 Hin Hstk Hlo Hlo2 ltac:(lia) Herr Htp Hgp Ha0 Htop' HbD).
intros ms' m' c' r RS VM ST HPR ERR HP1'.
apply (HK ms' m' c' tt r RS VM ST HPR ERR). rewrite Ez.
split; [exact HP1'|]. split; [exact (Forall_lb_remove _ p LB FLB)|]. split; [exact FLM|]. cbn [JH.charge JH.bB JH.bQ]. split; [lia|]. split; [lia| exact FCL].
-
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B cnt sz lo errv u HP Hstk Hlo Hlo2 Hal Htop Herr Htp Hgp Ha0 Ha1 Hcnt Hsz Hn Hpre Hok HbN HbB HbD HbQ HK.
destruct HP as (HP1 & FLB & FLM & HBB & HQ0 & FCL). pose proof (topj_lo _ _ Hlo2 Htop) as Htop'.
apply (hiA_calloc_1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B cnt sz lo u HP1 Hstk Hlo Hlo2 ltac:(lia) Htp Hgp Ha0 Ha1 Hcnt Hsz Hn Htop' HbN HbB HbD HbQ).
intros ms' m' c' r errv' RS VM ST HPR ERR Hr BLK HP1'.
apply (HK ms' m' c' tt r errv' RS VM ST HPR ERR Hr BLK).
split; [exact HP1'|]. split; [constructor; [cbn [snd]; lia| exact FLB]|]. split; [exact FLM|].
cbn [JH.chargeQ JH.charge JH.bB JH.bQ]. pose proof (JH.acostA_nonneg (cnt * sz) ltac:(lia)). split; [lia|]. split; [lia| exact FCL].
-
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B n lo errv HP Hstk Hlo Hlo2 Hal Htop Herr Htp Hgp Ha0 Hn HLM HbM HK.
destruct HP as (HP1 & FLB & FLM & HBB & HQ0 & FCL).
apply (hiA_malloc2_1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B n lo errv HP1 Hstk Hlo Hlo2 ltac:(lia) Herr Htp Ha0 Hn HbM).
intros ms' m' c' r errv' RS VM ST HPR ERR RES.
apply (HK ms' m' c' tt r errv' RS VM ST HPR ERR).
destruct RES as [(E1 & E2 & HP1')|(E1 & BLK & HP1')]; [left| right].
+ split; [exact E1|]. split; [exact E2|]. split; [exact HP1'|]. split; [exact FLB|]. split; [exact FLM|]. split; [exact HBB|]. split; [exact HQ0| exact FCL].
+ split; [exact E1|]. split; [exact BLK|]. split; [exact HP1'|]. split; [exact FLB|]. split; [constructor; [cbn [snd]; lia| exact FLM]|]. split; [exact HBB|]. split; [exact HQ0| exact FCL].
-
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B p lo errv HP HIN Hstk Hlo Hlo2 Hal Htop Herr Htp Hgp Ha0 HK.
destruct (Z.eq_dec p 0) as [Ep|Ep].
{ exact (OBL_FREE2_NULL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B p lo errv Ep HP HIN Hstk Hlo Hlo2 Hal Htop Herr Htp Hgp Ha0 HK). }
destruct HIN as [E0|[n Hin]]; [contradiction|].
destruct HP as (HP1 & FLB & FLM & HBB & HQ0 & FCL).
apply (hiA_free2_1 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B p n lo errv HP1 Hin Hstk Hlo Hlo2 ltac:(lia) Herr Htp Ha0).
intros ms' m' c' r RS VM ST HPR ERR HP1'.
apply (HK ms' m' c' tt r RS VM ST HPR ERR).
split; [exact HP1'|]. split; [exact FLB|]. split; [exact (Forall_lb_remove _ p LM FLM)|]. split; [exact HBB|]. split; [exact HQ0| exact FCL].
Defined.

Theorem hiA_stack_malloc_1_G : forall (Jf : OSA.TSet -> config -> Prop) (Jf_sc : forall T, silent_closed LV segs (Jf T)),
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (kc size lo : Z),
HEAPA1 k LB LM FR B m c ->
0 <= kc <= 2 \/ (kc = 3 /\ JH.hl_stack_malloc L 3 <> 0) -> 0 < size <= JH.fr_size kc -> size mod 8 = 0 ->
Z.of_nat (length FR) < fframe_cap kc ->
stk segs m lo (bv_unsigned sp) -> RC.alloc_ceiling <= lo -> lo <= bv_unsigned sp - JH.hl_stack_A L ->
bv_unsigned sp <= BAUX -> lo <= hi_top RE ->
tp = Z_to_bv 64 (HI.hl_tp HL) -> gp = Z_to_bv 64 (JH.hl_gp L) ->
a0 = Z_to_bv 64 size ->
(forall ms' m' (Fa : Z),
HI.ret_state HL ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Fr fc (Z_to_bv 64 Fa) m' ms' ->
stk segs m' lo (bv_unsigned sp) ->
HI.heap_pres HL (LB ++ LM ++ fr_ivs0 L FR) (bv_unsigned sp) m m' ->
Fa <> 0 ->
(exists junk, OT.rw_cells segs m' Fa [OC.CB (Z.to_nat (JH.fr_size kc - 8)) junk]) ->
bytes_at segs m' (JH.shad L Fa) (repeat (Z_to_bv 8 0) (Z.to_nat (JH.fr_shadow_len kc))) ->
HEAPA1 k LB LM ((Fa, kc) :: FR) B m' c ->
VJ LV (Jf T) c ms') ->
VJ LV (Jf T) c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 (JH.hl_stack_malloc L kc)) fc None m (seg_rom segs)).
Proof.
intros Jf Jf_sc.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T k LB LM FR B kc size lo
HP Hkc Hsz Hsz8 Hcap Hstk Hlo Hlo2 HB Htop Htp Hgp Ha0 HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc). pose proof (rsv_nonneg k Hk0) as HRSV.
change (JH.fr_size kc) with (ff_size kc) in Hsz.
eapply (hiA_stack_malloc0_G L LV Bc (PERMc PERM0 Lg) Tc Nc)
with (Jf := Jf) (Jf_sc := Jf_sc) (RSV := k * SC) (SM := SM) (SM_stack := SM_stack) (g := g) (LB := LB) (LM := LM) (FR := FR) (B := B) (lo := lo) (size := size); try eassumption.
intros ms' m' Fa junk Hret Hstk' Hpres HFm Hcd Hrng Hbody Hshad HA0'.
pose proof khi_val as EK. pose proof (@RC.alloc_ceiling_range RC__) as Hc.
destruct Hrng as (R1 & R2 & R3 & [Rl Rimg] & R5). destruct L_img as [Elo Ehi]. rewrite <- Elo, <- Ehi in Rimg.
destruct L_hull_eq as [_ Ehi2]. pose proof IMG_low as Hlow. unfold kLowEnd in *.
assert (Hs64 : 64 <= ff_size kc) by (unfold ff_size; assert (1 <= 2 ^ kc) by (apply Z.pow_le_mono_r with (b := 0); lia); lia).
assert (E8 : Fa = 8 * (Fa / 8)) by (apply Z.div_exact; [lia|]; apply (Zmod_divides Fa 64 ltac:(lia)) in R3 as [q ->]; replace (64 * q) with (8 * q * 8) by lia; apply Z.mod_mul; lia).
assert (D8 : ff_size kc = 8 * (ff_size kc / 8)) by (rewrite <- fr_shadow_len_ff; unfold ff_size, JH.fr_shadow_len; lia).
apply (HK ms' m' Fa Hret Hstk' Hpres).
- lia.
- exists junk. change (JH.fr_size kc) with (ff_size kc). apply (rw_cells_D segs m' _ [OC.CB (Z.to_nat (ff_size kc - 8)) junk]). cbn [map cellD].
destruct Hbody as [[Hwf Hb] Hw]. split; [split; [exact Hwf| exact (bytes_at_unhide segs _ Foffc m' _ _ Hb)]| exact (wr_at_unhide segs _ Foffc m' _ _ Hw)].
- destruct Hshad as [[_ Hb] _]. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb.
unfold JH.shad. rewrite L_sb, fr_shadow_len_ff. exact (bytes_at_unhide segs _ Foffc m' _ _ Hb).
- apply (heapA1_asan_step_fr k g g Lg H Bc Tc Nc s LB0 LB LM ((Fa, kc) :: FR) B m m' c c (bv_unsigned sp) _ KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT STA HA0' (vmst_refl _) HFm Hcd Hpres).
unfold fr_ivs0. cbn [flat_map app]. fold (fr_ivs0 L FR). unfold JH.fr_base, JH.fr_class. cbn [fst snd].
constructor; [| constructor].
+ cbn [fst snd]. change (JH.fr_size kc) with (ff_size kc). destruct Hbody as [_ Hw]. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by lia.
split; [exact Hw|]. split; lia.
+ cbn [fst snd]. destruct Hshad as [_ Hw]. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r, Z2Nat.id in Hw by lia.
unfold JH.shad. rewrite L_sb, fr_shadow_len_ff. unfold SH in Hw. split; [exact Hw|]. unfold kShadowOffset. split; [right; rewrite Ehi2; lia| lia].
+ apply (frw_keep _ FR (LB ++ LM) (bv_unsigned sp) m m' Foffc); [rewrite <- app_assoc; exact Hpres| exact FRW].
Qed.
Theorem hiA_frame_release_1_G : forall (Jf : OSA.TSet -> config -> Prop) (Jf_sc : forall T, silent_closed LV segs (Jf T)),
forall (R Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : OSA.TSet)
(k : Z) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (Fa kc fp pc : Z) (rX : bv 5),
HEAPA1 k LB LM FR B m c -> In (Fa, kc) FR ->
bytes_at segs m (Fa + JH.fr_size kc - 8) (le8 (Z_to_bv 64 fp)) ->
0 <= fp < 2^64 ->
LinuxProcessSemantics.Riscv.Sem.reg_get R rX = Z_to_bv 64 fp -> bv_unsigned rX <> 0 ->
OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt.code_at segs pc [0x23 + Z.shiftl (bv_unsigned rX) 15] ->
(forall m',
HEAPA1 k LB LM (JH.fr_remove Fa FR) B m' c ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
VJ LV (Jf T) c (MS R Fr (Z_to_bv 64 (pc + 4)) fc None m' (seg_rom segs))) ->
VJ LV (Jf T) c (MS R Fr (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
intros Jf Jf_sc.
intros R Fr fc m c T k LB LM FR B Fa kc fp pc rX HP Hin HBy Hfp Hreg Hx0 Hcode HK.
destruct HP as (g & Lg & H & Bc & Tc & Nc & s & LB0 & HA0 & KL & Hk0 & HTr & HNr & HOR & HLMr & PLM & RH & SIM & PLV & NDL & SZ & AUX & CNT & FRW & STA).
destruct (kla_layer0_facts Lg g c H m Bc Tc Nc KL) as (LLc & HFRc & Foffc & Flowc).
change (JH.fr_size kc) with (ff_size kc) in HBy.
destruct (heapA0g_frame_release L LV Bc (PERMc PERM0 Lg) Tc Nc DL RE DCo (FRof Lg) Foffc L_static L_sb L_dpn (k * SC) SM SM_stack DFs L_dpn_hull g LB LM FR B m c Fa kc (Z_to_bv 64 fp) HA0 Hin HBy)
as (HA0' & WVm & Fflag & HFm & Hcd & HPRES).
set (m' := write_to_mem m (Z_to_bv 64 fp) [Z_to_bv 8 0]) in *.
apply (vj_evt segs LV Hwx Hsegs _ (Jf_sc T)).
apply (QYz7.sb_zero_evt segs _ R Fr pc fc m (seg_rom segs) rX (Z_to_bv 64 fp) (proj1 Hcode) Hx0 Hreg WVm).
apply evt_done. fold m'. apply (HK m').
- apply (heapA1_asan_step_fr k g g Lg H Bc Tc Nc s LB0 LB LM (JH.fr_remove Fa FR) B m m' c c RC.alloc_ceiling _ KL Hk0 HTr HNr HOR HLMr PLM RH SIM PLV NDL SZ AUX CNT STA HA0' (vmst_refl _) HFm Hcd HPRES).
apply Forall_forall. intros b Hb.
assert (Hb0 : In b (fr_ivs0 L FR)).
{ unfold fr_ivs0 in Hb |- *. apply in_flat_map in Hb as (f & Hf & Hbf). apply in_flat_map. exists f. split; [exact (fr_remove_incl Fa FR f Hf)| exact Hbf]. }
destruct (proj1 (Forall_forall _ _) FRW b Hb0) as (HW & Himg & Hc). split; [| split; [exact Himg| exact Hc]].
unfold m'. rewrite (mrestrict_write1 LV (FRof Lg) m (Z_to_bv 64 fp) (Z_to_bv 8 0) Fflag). exact (wr_at_write segs _ _ _ _ _ HW).
- intros a Ha Hne. unfold m'. rewrite write1_spec. destruct (bv_eqb (wa a) (Z_to_bv 64 fp)) eqn:E; [| reflexivity]. exfalso. apply Hne.
apply bv_eqb_true in E. apply (f_equal bv_unsigned) in E. rewrite wa_unsigned in E by lia. rewrite Z_to_bv_unsigned, bv_wrap_small in E by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2^64); lia). exact E.
- intros x Hw. unfold m'. exact (wview_write_mono segs m _ _ x Hw).
Qed.
Theorem hiA_frame_release_63x_G : forall (Jf : OSA.TSet -> config -> Prop) (Jf_sc : forall T, silent_closed LV segs (Jf T)) (Jf_conseq : forall T T' c, OSA.t_eq T T' -> Jf T c -> Jf T' c),
forall (R : bvmap 5 word) (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config)
(T : OSA.TSet) (A : unit) (LB LM : list HI.blk) (FR : list JH.frame) (B : JH.bud) (Fa kc fp pc : Z) (rX : bv 5),
HEAPA63 A LB LM FR B m c -> In (Fa, kc) FR ->
bytes_at segs m (Fa + JH.fr_size kc - 8) (le8 (Z_to_bv 64 fp)) ->
0 <= fp < 2^64 ->
LinuxProcessSemantics.Riscv.Sem.reg_get R rX = Z_to_bv 64 fp -> bv_unsigned rX <> 0 ->
OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt.code_at segs pc [0x23 + Z.shiftl (bv_unsigned rX) 15] ->
(forall m' A',
HEAPA63 A' LB LM (JH.fr_remove Fa FR) B m' c ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m' (wa a) = m (wa a)) ->
(forall x, wview segs m x <> None -> wview segs m' x <> None) ->
JH.AJ (QsCz.aj_base_g segs LV Hwx Hsegs Jf Jf_sc Jf_conseq) T c (MS R Fr (Z_to_bv 64 (pc + 4)) fc None m' (seg_rom segs))) ->
JH.AJ (QsCz.aj_base_g segs LV Hwx Hsegs Jf Jf_sc Jf_conseq) T c (MS R Fr (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
intros Jf Jf_sc Jf_conseq.
intros R Fr fc m c T A LB LM FR B Fa kc fp pc rX (HP1 & FLB & FLM & HBB & HQ0 & FCL) Hin HBy Hfp Hreg Hx0 Hcode HK.
apply (hiA_frame_release_1_G Jf Jf_sc R Fr fc m c T (JH.bM B) LB LM FR B Fa kc fp pc rX HP1 Hin HBy Hfp Hreg Hx0 Hcode).
intros m' HP1' Hoff Hwv. apply (HK m' tt); [| exact Hoff| exact Hwv].
split; [exact HP1'|]. split; [exact FLB|]. split; [exact FLM|]. split; [exact HBB|]. split; [exact HQ0| exact (fcl_remove Fa FR FCL)].
Qed.
Theorem tier1_G : forall (Jf : OSA.TSet -> config -> Prop) (Jf_sc : forall T, silent_closed LV segs (Jf T)) (Jf_conseq : forall T T' c, OSA.t_eq T T' -> Jf T c -> Jf T' c), JH.hia_tier1 L (QsCz.aj_base_g segs LV Hwx Hsegs Jf Jf_sc Jf_conseq) unit HEAPA63 TOPJ.
Proof.
intros Jf Jf_sc Jf_conseq.
constructor.
-  intros A LB LM FR B m c Fa kc (HP & _ & _ & _ & _ & FCL) Hin. pose proof (fcl_in FR Fa kc FCL Hin) as Hkc.
split; [exact Hkc|]. exact (heapA1_frame _ _ _ _ _ _ _ Fa kc HP Hin Hkc).
-  intros A LB LM FR B m c Fa kc a n (HP & _ & _ & _ & _ & FCL) Hin Hb.
exact (heapA1_frame_disjoint _ _ _ _ _ _ _ Fa kc a n HP Hin (proj1 (fcl_in FR Fa kc FCL Hin)) Hb).
-  intros A LB LM FR B m c Fa kc Fa' kc' (HP & _) H1 H2 Hne. exact (heapA1_frame_apart _ _ _ _ _ _ _ Fa kc Fa' kc' HP H1 H2 Hne).
-  intros A LB LM FR B m c (HP & _). apply NoDup_ListNoDup. exact (heapA1_frame_nodup _ _ _ _ _ _ _ HP).
-  intros A LB LM FR B m c Fa kc (HP & _) Hin. exact (heapA1_frame_appmem _ _ _ _ _ _ _ Fa kc HP Hin).
-  intros A LB LM FR B m c Fa kc i (HP & _) Hin Hi. exact (heapA1_frame_shadow_sep _ _ _ _ _ _ _ Fa kc i HP Hin Hi).
-
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T A LB LM FR B kc bytes lo
(HP1 & FLB & FLM & HBB & HQ0 & FCL) Hkc Hby Hby8 Hlen Hstk Hlo Hlo2 Hal Htop Htp Hgp Ha0 HK. pose proof (topj_lo _ _ Hlo2 Htop) as Htop'.
assert (Hcap : Z.of_nat (length FR) < fframe_cap kc).
{ unfold fframe_cap. destruct Hkc as [Hkc2 | (-> & _ & Hlen3)]; [assert (2 ^ 12 <= 2 ^ (14 - kc)) by (apply Z.pow_le_mono_r; lia); lia | change (2 ^ (14 - 3)) with 2048; exact Hlen3]. }
assert (HkcT : 0 <= kc <= 2 \/ (kc = 3 /\ JH.hl_stack_malloc L 3 <> 0)) by (clear - Hkc; destruct Hkc as [H|(H1 & H2 & _)]; [left; exact H | right; split; [exact H1 | exact H2]]).
assert (Hkc3 : 0 <= kc <= 3) by (clear - Hkc; lia).
apply (hiA_stack_malloc_1_G Jf Jf_sc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Fr fc m c T (JH.bM B) LB LM FR B kc bytes lo
HP1 HkcT ltac:(lia) Hby8 Hcap Hstk Hlo Hlo2 ltac:(lia) Htop' Htp Hgp Ha0).
intros ms' m' Fa RS ST HPR Hnz BLK SHB HP1'.
apply (HK ms' m' tt Fa RS ST HPR Hnz BLK SHB).
split; [exact HP1'|]. split; [exact FLB|]. split; [exact FLM|]. split; [exact HBB|]. split; [exact HQ0|].
constructor; [unfold JH.fr_class; cbn [snd]; exact Hkc3| exact FCL].
-  exact (hiA_frame_release_63x_G Jf Jf_sc Jf_conseq).
Qed.

Theorem heap_loop_rule_v63 : QCVR.heap_loop_rule6 L hiA_v63.
Proof.
intros VV T c0 ms0 H0 Hbody.
apply (QZ6y.loop_rule_base segs LV Hwx Hsegs VV T c0 ms0 H0).
intros c ms HV.
exact (Hbody (QCVR.LK6 L hiA_v63 VV T
(QZ6y.aj_base_loop segs LV Hwx Hsegs VV T) QZ6y.lwit QZ6y.lTw QZ6y.lTn QZ6y.lwit_w QZ6y.lwit_n
(fun c H => H) (fun c c' H => H)
(QZ6y.loop_exit segs LV Hwx Hsegs VV T) (QZ6y.loop_back segs LV Hwx Hsegs VV T)
(tier1_G (QTtp.Mq0.JLP segs LV VV T)
(QTtp.Mq0.jlp_silent_closed segs LV VV T)
(fun X X' c E H => QTtp.Mq0.jlp_conseq segs LV VV T X X' c E H))
(fun F fc => @QZ6y.loop_getrandom F fc segs LV Hwx Hsegs VV T)) c ms HV).
Qed.

End Inst1.
