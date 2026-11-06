(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainG3.v (commit ce1a656b52b7, file sha256 8262e5c8ea52) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainG3.v (commit 9259077395a9, Quarantine::Drain walk set; file sha256 0aeb58cc6713) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainG3.v at commit 257c1d78b5c, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the GEOMETRY facts Drain's entry shell asks - where the caches'
   first and last batches sit, the two counts, and the global list's last batch (YFgj.free_hyps' fh_glast) - from
   DMiface.qview's qv_geom / qv_wf / qv_bytes / qv_bpres / qv_cells and layout_ok, instead of cgif's allocator
   relation (the released YFev.g_facts / t_facts, YFev.v:152-176, read them off Wf).  DMdrainE takes these as its
   hypotheses HGF / HGL / HTF / HTL / HGcnt / HTcnt / Hglast.
   rule 24: no function proved (kind: geometry and cell facts; the lane's reuse search is
   the internal file LOOKUP-B1-drain.txt, `proof-index MergeBatches Recycle QuarantineCallback_Recycle Drain`
   2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM).
   Additive: no existing file is touched. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj YFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF DMdrainK DMdrainT1 DMdrainT4 DMdrainG1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Ltac splits := repeat lazymatch goal with |- _ /\ _ => split end.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Open Scope am_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variables (ly : alayout) (X : astate) (W : world tfibsegs) (mem : word -> option byte).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation SB := (ly_space ly).
Local Notation gq := (st_qglobal X).
Local Notation tq := (st_qthread X).
Local Notation G := (qc_list (st_qglobal X)).
Local Notation Tq := (qc_list (st_qthread X)).
Hypothesis LY : layout_ok ly.
(* qview's geometry, well-formedness, byte bound, batch presence and cells *)
Hypothesis GEO : rg_alloc_user (reg X kBatchClass) <= kFreeArrayOffset /\
  forall b, In b (all_batches X) ->
  0 <= b_self b - region_off kBatchClass /\ b_self b - region_off kBatchClass + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
  (b_self b - region_off kBatchClass) mod kBatchBytes = 0.
Hypothesis WF : qc_bytes tq = sum_bytes Tq /\ qc_bytes gq = sum_bytes G /\
  Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) (all_batches X) /\
  Forall (fun k => 0 <= ck_n k) (q_items X).
Hypothesis BYTES : qc_bytes tq + qc_bytes gq <= 2 ^ 31.
Hypothesis BP : forall b a, In b (all_batches X) -> ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> apresent (w_H W) mem a.
Hypothesis QC : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (quar_cells X).
(* the drain is entered because the thread cache is over its max *)
Hypothesis HTB : kQuarantineCacheMax < qc_bytes tq.

Lemma RO : region_off kBatchClass = 103079215104.
Proof. vm_compute. reflexivity. Qed.

(* Every batch of the quarantine sits in the primary space, 8192 aligned. *)
Lemma baddr : forall b, In b (all_batches X) ->
ly_prim ly <= SB + b_self b /\ SB + b_self b + kBatchBytes <= SB + kSpaceSize /\ (SB + b_self b) mod 8192 = 0 /\
0 <= SB + b_self b < ASAN_CEIL.
Proof.
intros b Hb. destruct GEO as [G0 GB]. destruct (GB b Hb) as (A1 & A2 & A3).
pose proof (LYB2 ly LY) as (P1 & P2 & _). pose proof (SPACE ly LY) as (S1 & S2 & S3).
rewrite RO in A1, A2, A3. unfold kBatchBytes, kFreeArrayOffset in *.
destruct (proj1 (Z.mod_divide _ 8192 ltac:(lia)) A3) as [q1 E1].
destruct (proj1 (Z.mod_divide _ 65536 ltac:(lia)) S3) as [q2 E2].
ceil; unfold kSpaceSize, ASAN_CEIL, kHighMemBeg in *.
splits; try lia.
Qed.

Lemma in_G : forall b, In b G -> In b (all_batches X).
Proof. intros b Hb. unfold all_batches. apply in_app_iff. right. exact Hb. Qed.
Lemma in_T : forall b, In b Tq -> In b (all_batches X).
Proof. intros b Hb. unfold all_batches. apply in_app_iff. left. exact Hb. Qed.

Lemma first_range : forall l, (forall b, In b l -> In b (all_batches X)) ->
0 <= (match l with [] => 0 | b :: _ => SB + b_self b end) < ASAN_CEIL /\
(match l with [] => 0 | b :: _ => SB + b_self b end) mod 8192 = 0.
Proof.
intros [|b t] Hl.
- ceil. unfold ASAN_CEIL in *. split; [lia | reflexivity].
- destruct (baddr b (Hl b (or_introl eq_refl))) as (_ & _ & A3 & A4). split; [exact A4 | exact A3].
Qed.

Lemma last_range : forall l, (forall b, In b l -> In b (all_batches X)) ->
0 <= (match rev l with [] => 0 | b :: _ => SB + b_self b end) < ASAN_CEIL /\
(match rev l with [] => 0 | b :: _ => SB + b_self b end) mod 8192 = 0.
Proof.
intros l Hl. destruct (rev l) as [|b t] eqn:ER.
- ceil. unfold ASAN_CEIL in *. split; [lia | reflexivity].
- assert (Hin : In b l) by (rewrite <- (rev_involutive l), ER; cbn [rev]; apply in_app_iff; right; left; reflexivity).
  destruct (baddr b (Hl b Hin)) as (_ & _ & A3 & A4). split; [exact A4 | exact A3].
Qed.

Lemma GF_range : 0 <= YFgj.GFv ly gq < ASAN_CEIL /\ YFgj.GFv ly gq mod 8192 = 0.
Proof. exact (first_range G in_G). Qed.
Lemma GL_range : 0 <= YFgj.GLv ly gq < ASAN_CEIL /\ YFgj.GLv ly gq mod 8192 = 0.
Proof. exact (last_range G in_G). Qed.
Lemma TF_range : 0 <= YFgj.TFv ly tq < ASAN_CEIL /\ YFgj.TFv ly tq mod 8192 = 0.
Proof. exact (first_range Tq in_T). Qed.
Lemma TL_range : 0 <= YFgj.TLv ly tq < ASAN_CEIL /\ YFgj.TLv ly tq mod 8192 = 0.
Proof. exact (last_range Tq in_T). Qed.

(* the chunks' user sizes are not negative *)
Lemma nn_of : forall l, (forall b, In b l -> In b (all_batches X)) -> forall k, In k (flat_map b_items l) -> 0 <= ck_n k.
Proof.
intros l Hl k Hk. destruct WF as (_ & _ & _ & W4). apply (proj1 (Forall_forall _ _) W4).
unfold q_items. apply in_flat_map in Hk as (b & Hb & Hk). apply in_flat_map. exists b. split; [exact (Hl b Hb) | exact Hk].
Qed.

(* The two counts. *)
Lemma G_count : 0 <= YFgj.GSZv gq < 2 ^ 40.
Proof.
destruct WF as (W1 & W2 & _). pose proof (bytes_ge_count G (nn_of G in_G)) as HG.
pose proof (bytes_ge_count Tq (nn_of Tq in_T)) as HT.
unfold YFgj.GSZv. unfold kBatchBytes in *. lia.
Qed.
Lemma T_count : 1 <= YFgj.TSZv tq < 2 ^ 40.
Proof.
destruct WF as (W1 & W2 & _). pose proof (bytes_ge_count G (nn_of G in_G)) as HG.
pose proof (bytes_ge_count Tq (nn_of Tq in_T)) as HT. unfold YFgj.TSZv.
destruct Tq as [|b t] eqn:ET.
- exfalso. rewrite W1 in HTB. cbn in HTB. unfold kQuarantineCacheMax in HTB. lia.
- cbn [length] in *. unfold kBatchBytes in *. lia.
Qed.

(* The global list's last batch: placed, its next word 0, its next word present (YFgj.free_hyps' fh_glast). *)
Lemma G_lcn : lcn ly (iwB B ly) m0 G 0.
Proof.
apply lcn_of_cells. apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) QC).
unfold quar_cells. right; right. apply in_app_iff. right. unfold qc_cells. do 4 right. exact Hc.
Qed.

Lemma G_last : forall lastb initr, rev G = lastb :: initr ->
ly_prim ly <= YFgj.GLv ly gq /\ YFgj.GLv ly gq + kBatchBytes <= SB + kSpaceSize /\ YFgj.GLv ly gq mod 8192 = 0 /\
val_mem tfibsegs m0 (YFgj.GLv ly gq) 8 0 /\ (forall a, YFgj.GLv ly gq <= a < YFgj.GLv ly gq + 8 -> apresent (w_H W) mem a).
Proof.
intros lastb initr ER.
assert (EG : YFgj.GLv ly gq = SB + b_self lastb) by (unfold YFgj.GLv; rewrite ER; reflexivity).
assert (Hin : In lastb G) by (rewrite <- (rev_involutive G), ER; cbn [rev]; apply in_app_iff; right; left; reflexivity).
destruct (baddr lastb (in_G lastb Hin)) as (A1 & A2 & A3 & A4).
rewrite EG. splits; try assumption.
- assert (ESPLIT : G = rev initr ++ [lastb]) by (rewrite <- (rev_involutive G), ER; reflexivity).
  pose proof G_lcn as HL. rewrite ESPLIT in HL.
  destruct (lcn_app_split ly (iwB B ly) m0 (rev initr) [lastb] 0 HL) as [_ HL2].
  cbn [lcn] in HL2. destruct HL2 as [(V0 & _) _]. unfold addrb, fa in V0. exact V0.
- intros a Ha. apply (BP lastb a (in_G lastb Hin)). unfold kBatchBytes. lia.
Qed.
End g.
End f.
